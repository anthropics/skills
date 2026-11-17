## 国产超算软件兼容性排查

### 验证顺序

1. **系统 ABI**：确认发行版、glibc、CPU 架构和节点类型；检查 wheel 的 `manylinux` 标签是否高于目标 glibc。
2. **工具链**：记录 GCC/Clang、DTK、HIP、CMake、MPI、Python 和框架版本；登录节点可用不等于计算节点可用。
3. **最小探针**：在目标计算节点验证 import、设备枚举、最小 kernel、一个真实功能和退出码。
4. **依赖路径**：区分 pip/conda 解析失败、运行时动态库失败、框架 kernel 不支持和模型/数据下载失败。
5. **端到端结果**：记录成功条件、性能、显存/内存、失败日志和未验证范围。

### 编译型软件的分层验证

- **把编译放到计算节点**：C++/HIP 大型构建的峰值内存可能远高于登录节点限额。
  编译器进程被 OOM kill 时，先换到有明确内存配额的计算作业，先排除资源限制，再判断源码问题。
- **只生成目标架构**：显式设置目标 `gfx` 架构。默认同时生成多个架构会成倍增加
  编译时间、产物体积和峰值内存。
- **升级工具链后重跑最小构建**：DTK/编译器升级可能改变 wrapper 头、host/device
  编译模式或默认链接路径。保存 verbose compile command，与上一版本逐项比较。
- **区分节点环境**：登录/CPU 节点可能加载得到 module，却缺少只在加速器节点完整
  可见的 HSA/HIP 库或符号链接。以目标计算节点解析到的真实库文件为准，必要时通过
  CMake cache 变量显式传入，不创建全局假链接。
- **先串行能力、后并行能力**：先完成无 MPI 的单卡最小构建和功能验证，再开启 MPI，
  最后测试 GPU-aware 通信与多卡扩展，以隔离编译器、运行库和通信栈问题。

### GPU-aware MPI 的验证边界

系统 MPI 能启动多进程，不代表它带加速器感知能力。先记录 MPI 构建参数，并做
GPU-aware on/off 对照。单节点验证可先固定共享内存与 self 传输，减少 UCX/IB
站点配置带来的变量；这只能证明单节点路径，不能外推到跨节点通信。

多卡扩展通常同时依赖足够大的问题规模、较高的计算/通信比以及可用的 GPU-aware
路径。小问题或低计算密度任务扩展不佳，不足以单独证明硬件或 MPI 配置错误。

### 数值与性能验收

加速器移植至少应同时报告：CPU/参考实现的关键数值偏差、守恒量或长期稳定性、
单卡问题规模扫描、固定规模的 1/2/单节点全卡强扩展、GPU-aware on/off 对照、
峰值内存/显存，以及每项测试的退出码和完整日志。性能通过不能替代正确性验证。

### 已验证的典型边界

- **gfx936 / BW1000**：Triton、硬件 FP8 `torch._scaled_mm`、部分 bitsandbytes INT8 路径可能不可用；纯 PyTorch 软件反量化可作为兼容路径，但需要单独做性能和精度验证。
- **gfx906 / Z100**：CentOS 7.6 的 glibc 2.17 会限制 manylinux wheel 版本；安装 Python 软件时优先选 manylinux2014 / manylinux_2_17 兼容包。MinerU 场景中，Python 3.10 + onnxruntime 1.16.3 是已验证方向，magika 版本/API 需要随源码适配。
- **GROMACS HIP**：先验证 CMake 最低版本、DTK 的 `lib`/`lib64` CMake 路径、目标架构、FFTW 预置和 SIMD；CUDA 兼容层与原生 HIP 的性能不可直接互相推断。

### 作业验证模板

```bash
set -o pipefail
python3 -c 'import torch; print(torch.__version__); print(torch.cuda.is_available())'
python3 -c 'import <target_package>; print("import ok")'
<minimal_function_test>
rc=$?
echo "test_exit_code=$rc"
exit "$rc"
```

不能只依据 `sacct` 的 `COMPLETED` 判定成功。脚本必须显式传递最后一个测试命令的退出码，并同时读取 `.out/.err`。

### 公开报告模板

标题采用“项目 + 加速器/平台 + 编译与性能/兼容性测试报告”。正文可按以下顺序：

1. 环境信息
2. 编译过程与主要难题
3. 最终方案与验证结果
4. 测试数据与资源占用
5. 已知限制与注意事项
6. 适用范围与可复用结论
7. 附录：快速复现命令

发布前扫描：

```bash
rg -n -i 'ssh|password|token|secret|/home/|/public/|/Users/|@[A-Za-z0-9.-]+|192\.168\.|10\.|172\.(1[6-9]|2[0-9]|3[0-1])\.|job [0-9]+|作业编号|节点名' report.html
```

将命中项替换为占位符或概括描述；保留版本、架构、错误类型、性能数据和验证边界。
