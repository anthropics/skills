# 排查作业失败

## 作业状态与实际退出码

bash 脚本里 Python 崩了之后，bash 继续执行后面的行，作业以**最后一条命令**的退出码
结束。真实案例：

```
$ sacct -j <JOB_ID> --format=JobID,JobName,State,ExitCode,Elapsed
<JOB_ID> | example-job | COMPLETED | 0:0 | 00:34:32
```

该记录不能证明 Python 工作负载成功。Python 可能已在第 3 分钟抛出 `ValueError`，而日志末尾仍打印脚本中
写的 `===== COMPLETE =====`。

排查时先读取日志和工作负载退出码，再结合调度器 State 判断。

预防：脚本末尾写

```bash
rc=$?
echo "### python exit=$rc"
exit $rc
```

## 日志被进度条淹没时

`transformers` 加载权重的进度条写到 stderr，会刷出几万字符：

```bash
grep -v "Loading weights" job_123.err | tail -50
# 或者只看 Python traceback
grep -A30 "Traceback" job_123.err | head -60
```

## 按报错分类

### `QOSMinGRES`

```
sbatch: error: min tres(gres/dcu) request 0 exceeds per-job max tres limit 1
       for qos <QOS名>
sbatch: error: QOSMinGRES
```

该分区要求每个作业至少申请 1 张 DCU。补充 `--gres=dcu:N`；纯 CPU 负载也受该分区策略约束。

### `too much memory was requested relative to the number of CPUs`

违反 `--mem ≤ cpus-per-task × DEF_MEM_PER_CPU`（值见 profile）。
要么降 `--mem`，要么加 `--cpus-per-task`。

### `libmsgpackc.so.2` / `libgalaxyhip.so.5: cannot open shared object file`

三种可能：

1. **在登录节点跑 torch** —— 郑州集群最近实测是缺 `libgalaxyhip.so.5`，旧环境
   报过 `libmsgpackc.so.2`；即使 `module load` 之后也 import 不了。必须用
   `srun`/`sbatch`。
2. **忘了 `module load`** —— venv 激活前必须先
   `module load compiler/gcc/9.3.0 compiler/dtk/26.04`。
3. **顺序错了** —— 先激活 venv 再 module load 也会失败，顺序必须是 module 在前。

### `Name or service not known` / `Hugging Face Hub is in offline mode`

计算节点在访问外网。典型的是 `transformers` 的 kernel 下载机制：

```
ValueError: Version 4 of 'kernels-community/finegrained-fp8' is not available
           in the local cache and Hugging Face Hub is in offline mode
```

或者更慢的版本（httpx 超时后才报）：

```
httpcore.ConnectError: [Errno -2] Name or service not known
```

脚本里加 `export HF_HUB_OFFLINE=1` 让它立刻失败而不是慢慢超时。但根本问题是**这个
库需要运行时下载**，得找不依赖下载的替代路径。

### `cannot get address for 'hipDrvLaunchKernelEx' from libamdhip64.so`

Triton。DTK 26.04 的 HIP 运行时缺上游 ROCm 7 的 API，Triton 的 AMD backend 加载
即失败。该软件栈不能使用此 Triton 路径，依赖对应 Triton kernel 的框架也不适用（SGLang FP8、vLLM ROCm
MoE、transformers finegrained-fp8）。

郑州集群最近还会先报另一种缺库：

```
ImportError: libgcvm.so.17git: cannot open shared object file
```

本质相同，都是 Triton 在当前 DTK/DCU 软件栈上不可用，继续调整 Triton kernel 参数不能解决该运行时缺失。

### `torch._scaled_mm is only supported on CUDA devices with compute capability >= 9.0 or 8.9, or ROCm MI300+`

gfx936 不支持硬件 FP8 计算。需要软件反量化（把 FP8 权重转成 BF16 再算）。

### 退出码 53，且**完全没有日志文件**

`#SBATCH` 是注释行，**Slurm 不做变量展开**。日志路径里写 `$USER` 会被当成字面量
目录名，作业启动就失败：

```
$ sacct -j <ID> --format=State,ExitCode
FAILED|0:53
$ cat ~/scripts/logs/myjob_<ID>.log
cat: No such file or directory        ← 连日志都没有，因为写不进去
```

两个原因都会导致这个：

1. `--output` / `--error` 路径里有未展开的变量（`$USER`、`$HOME`）
2. **日志目录不存在** —— Slurm 不会自动创建

处理方法：`#SBATCH` 里写完整字面量路径，提交前 `mkdir -p <日志目录>`。
`scripts/new-job.sh` 会展开好用户名并提示建目录。

### `module load` 静默失败：作业返回 0 但 `ROCM_PATH` 没设置

某些集群的 module 函数只在 **login shell** 里定义。用普通 `#!/bin/bash` 时
`module load` 什么都不做，也不报错：

```
ROCM_PATH=未设置
--- 架构 ---           ← rocminfo 无输出
--- 显存 ---           ← rocm-smi 无输出
### python exit=0      ← 作业「成功」了
```

该现象可能返回退出码 0，因此还需检查模块环境变量和探针输出。该行为已在昆山集群观测。

处理方法：shebang 用 `#!/bin/bash -l`，或在 heredoc 内包一层 `bash -l`。
`scripts/new-job.sh` 生成的脚本已经用 `bash -l`。

自检：作业里打印 `echo "ROCM_PATH=${ROCM_PATH:-未设置}"`，未设置就说明没生效。

### `python3: command not found`（昆山计算节点）

昆山计算节点 `module purge` 后没有 `python3` 命令，裸 `python` 是 Python 2，
会再报：

```
SyntaxError: Non-ASCII character '\xe5' ... no encoding declared
```

处理方法：作业脚本里显式加载 Python 3 module：

```bash
module load python/3.8.10
```

`scripts/run-compute-probe.sh` 会自动从 `module avail` 探测 `python/3.*` 模块，
但普通业务作业仍需在 `MODULE_LOADS` 或 `PYTHON_MODULE` 里带上。

### `TIMEOUT`

`--time` 不够。注意大模型加载本身就很慢（DeepSeek V4 加载 154B 权重约 27 分钟），
`--time` 要留足加载 + 计算的总时间。

### OOM（进程被杀，日志突然截断）

```bash
sacct -j <ID> --format=JobID,State,MaxRSS,ReqMem -P
```

注意 `MaxRSS` **只出现在 `.batch` 子步骤那一行**，主作业行是空的：

```
JobID|MaxRSS|ReqMem
<JOB_ID>||115G              ← 主行没有 MaxRSS
<JOB_ID>.batch|120586316K|  ← 实际峰值在这里
```

`MaxRSS` 接近 `cpus × DEF_MEM_PER_CPU` 就是 CPU 内存不够，加 `--cpus-per-task`。
上例申请了 `--mem=115gb` 而实际用到 120GB —— 因为 cgroup 按
`32 × 3888MB = 121.5GB` 给（该集群 DEF_MEM_PER_CPU=3888），`--mem` 只是请求量。

GPU OOM 会有明确的 `torch.cuda.OutOfMemoryError`，看每卡分配：

```python
for i in range(torch.cuda.device_count()):
    print(i, torch.cuda.memory_allocated(i) / 1024**3, "GB")
```

### 作业一直 `PD (Priority)` 不动

该状态表示等待调度资源。查询预计启动时间：

```bash
squeue -j <ID> --start
sinfo -p <分区> -o "%n %t"           # 有几台 idle
```

`drain`/`drng` 状态的节点不参与调度，忙时可能等很久。

## 调试策略

按成本递增的顺序执行验证，避免使用完整模型诊断基础环境问题：

1. **纯逻辑**（不需要 GPU/torch）→ 本地 Python 直接跑
2. **需要 torch/DCU 但数据量小** → `srun` 交互式，约 5 秒拿到节点
3. **小规模真实数据** → 2 分钟的 `sbatch` 探针作业
4. **完整模型** → 最后才做

例如，反量化实现应先通过小规模数值测试，再运行完整模型。

**探针作业模板**：只读 metadata 不加载权重，几秒就出结果：

```python
from safetensors import safe_open
with safe_open(path, framework="pt", device="cpu") as f:
    sl = f.get_slice(key)
    print(key, sl.get_shape(), sl.get_dtype())   # 不读实际数据
```

## 检查作业真正在干什么

```bash
# 作业跑在哪个节点
squeue -j <ID> -o "%N"

# 在作业运行期间检查目标节点进程
ssh <节点名> 'top -b -n1 -u $USER | head -20'

# GPU 占用
srun --jobid=<ID> --overlap rocm-smi
```

`--overlap` 让新的 srun 步骤共享已有作业的资源分配，避免为诊断步骤重新申请一份资源。
