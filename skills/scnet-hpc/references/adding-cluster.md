# 新增一个集群

这套 skill 的集群参数都在 `clusters/*.conf`，脚本从 profile 读取。新增集群
通常只需增加一个 profile；若调度器或字段语义不同，仍需扩展脚本。

## 配置流程

### 1. 验证基础连接

用平台控制台下载的私钥，临时连一次：

```bash
chmod 600 <私钥>
ssh -i <私钥> -p <端口> <用户名>@<主机名> 'hostname; whoami'
```

连接失败时检查：私钥是否过期、本机 IP 是否在平台白名单、端口是否可达。

### 2. 添加临时 SSH 别名

```bash
cat >> ~/.ssh/config <<'EOF'

Host newcluster-tmp
  HostName <主机名>
  User <用户名>
  Port <端口>
  IdentityFile <私钥路径>
  IdentitiesOnly yes
EOF
```

### 3. 生成初始 profile

```bash
./scripts/probe-cluster.sh newcluster-tmp <集群短名> > clusters/<集群短名>.conf
```

脚本会自动填：SSH 参数、调度器类型、分区、`DEF_MEM_PER_CPU`、QOS 的 `MIN_GRES`、
节点规格、网络可达性、登录节点缺失的库、家目录容量。

**探测不到的项会留空并在文件末尾列出**，不填入推测值。

### 4. 补齐手工项

profile 末尾的注释列出了还需确认的。主要是：

**`SSH_HOST` / `SSH_PORT`** —— 固定连接参数，应写死。本机已配置 SSH 别名时，
可用 `ssh -G <别名>` 查出 `hostname` 和 `port` 后填进 profile。

**加速器型号和架构** —— 在计算节点跑：

```bash
# AMD/海光系
srun -p <分区> --gres=<类型>:1 --time=00:05:00 bash -lc 'module load <模块>; rocminfo | grep -i gfx'
# NVIDIA
srun -p <分区> --gres=gpu:1 --time=00:05:00 nvidia-smi --query-gpu=name --format=csv
```

**module 名** —— `ssh <集群> 'module avail 2>&1'` 中选择与目标环境匹配的编译器和加速器 SDK。

**`NEEDS_UPDATE_HOSTKEYS_NO`** —— 如果连接时看到
`client_global_hostkeys_prove_confirm: server gave bad signature`，设成 `yes`。

**`KEY_NAME_MARKER`** —— 根据私钥文件名格式设置。若形如
`zhangsan_xxx.scnet.cn_RsaKeyExpireTime_2027-01-01.txt`，则设
`KEY_NAME_MARKER="_<集群主机>_"`，脚本就能自动提取用户名。

### 5. 用正式流程重配连接

删掉第 2 步的临时段，然后：

```bash
./scripts/setup-ssh.sh --cluster <集群短名> <私钥文件> <用户名>
```

公开 profile 使用占位符时，`<用户名>` 必须显式传入；如果已在本地私有 profile
里填了真实 `KEY_NAME_MARKER`，可以省略。

### 6. 验证加速器能力并记录结论

加速器能力必须以目标计算节点的探针结果为准，不能从上游 ROCm、CUDA 或其他集群的结果推断。

所有探针和测试任务的临时文件必须放在共享家目录中，例如
`$HOME/.scnet-hpc/tmp/$SLURM_JOB_ID`。不要使用 `/tmp` 或从根目录创建临时目录；作业
启动后应导出 `TMPDIR`、`TMP`、`TEMP` 指向该目录。

用一个探针作业测这些：

```python
import torch
p = torch.cuda.get_device_properties(0)
print("arch:", getattr(p, "gcnArchName", "?"), "| major", p.major, "minor", p.minor)

# 低精度数据类型
for dt in ["float8_e4m3fn", "float8_e5m2", "float8_e8m0fnu", "bfloat16"]:
    print(dt, hasattr(torch, dt))

# 硬件加速的低精度 matmul
try:
    a = torch.randn(64, 128).to(torch.float8_e4m3fn).cuda()
    b = torch.randn(128, 64).to(torch.float8_e4m3fn).cuda().t().contiguous().t()
    torch._scaled_mm(a, b, scale_a=torch.tensor(1.).cuda(),
                     scale_b=torch.tensor(1.).cuda(), out_dtype=torch.bfloat16)
    print("_scaled_mm: OK")
except Exception as e:
    print("_scaled_mm:", type(e).__name__, str(e)[:120])

# Triton（很多推理框架的前提）
try:
    import triton, triton.language as tl
    @triton.jit
    def k(x, y, o, n, BLOCK: tl.constexpr):
        i = tl.program_id(0) * BLOCK + tl.arange(0, BLOCK)
        m = i < n
        tl.store(o + i, tl.load(x + i, mask=m) + tl.load(y + i, mask=m), mask=m)
    n = 4096
    x = torch.randn(n, device="cuda"); y = torch.randn(n, device="cuda")
    o = torch.empty_like(x)
    k[(triton.cdiv(n, 256),)](x, y, o, n, BLOCK=256)
    torch.cuda.synchronize()
    print("triton: OK, err", (o - (x + y)).abs().max().item())
except Exception as e:
    print("triton:", type(e).__name__, str(e)[:200])
```

把结论写进 profile 的 `KNOWN_LIMITATIONS`，格式参考已有的 profile。

Triton 是多种推理框架的运行前提；不可用时，对应的 Triton 执行路径也不可用（SGLang 的 FP8 路径、vLLM 的 ROCm MoE 后端、transformers 的 finegrained-fp8）。该结论应在框架适配前确认。

已有集群后续不必重跑完整流程，可用
`./scripts/refresh-cluster.sh --cluster <集群短名> --compute` 动态刷新调度器、
内存、分区、网络和计算节点能力，结果写到 `clusters/.cache/<集群短名>.auto.conf`。

## profile 字段参考

必填三项：`CLUSTER_ID`、`SSH_HOST`、`SSH_PORT`。其余留空则脚本跳过、文档显示为未探测。

影响脚本行为的关键项：

| 字段 | 谁用 | 留空的后果 |
|---|---|---|
| `MIN_GRES` | 文档提示 | 不提示 QOS 强制申请加速器 |
| `GRES_TYPE` | `new-job.sh` | 生成的脚本不含 `--gres` |
| `DEF_MEM_PER_CPU` | `new-job.sh` | 生成的脚本不含 `--mem`，需手填 |
| `MODULE_LOADS` | `new-job.sh` | 生成的脚本不含 `module load` |
| `PYTHON_MODULE` | `run-compute-probe.sh` | 计算节点缺 python3 时可能找不到解释器 |
| `DEFAULT_VENV` | `new-job.sh` | 生成的脚本不含 venv 激活 |
| `NODE_COUNT` | 运行时回退 | 实时查 TotalNodes 失败时使用该值 |
| `KEY_NAME_MARKER` | `setup-ssh.sh` | 无法从文件名推断用户名，需显式传 |
| `NEEDS_UPDATE_HOSTKEYS_NO` | `setup-ssh.sh` | 不写 `UpdateHostKeys no` |
| `COMPUTE_NODE_OFFLINE` | `new-job.sh` | 不设 `HF_HUB_OFFLINE` |

## 非 Slurm 调度器

目前 `new-job.sh` 只支持 Slurm（`SCHEDULER="slurm"`）。PBS/LSF 集群可以填
profile 的其他字段用于文档和连接，但作业脚本要手写。
