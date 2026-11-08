# 海光 DCU 开发与工具库索引

本页整理光合开发者社区的公开入口。站点内容会更新；版本、支持的操作系统、驱动、固件和安装包必须以官方页面当前选择结果为准，不要从本文复制旧版本组合。

## 使用顺序

1. 打开[开发指南](https://developer.sourcefind.cn/developer-channel)，选择 DCU 产品系列、操作系统和版本。
2. 按页面顺序完成驱动安装、固件更新、DTK 或 DAS 环境部署，再考虑容器化部署。
3. 打开 [DTK 资源页](https://developer.sourcefind.cn/dtk)，下载与目标系统匹配的 DTK，并从文档目录选择对应版本手册。
4. 在计算节点用最小探针验证驱动、运行时、编译器、目标架构和所需库；集群 module 中的实际版本优先于网页示例。
5. 需要模型、镜像、代码或课程时，从下方资源入口继续查找。

## 官方入口

| 入口 | 用途 |
|---|---|
| [开发指南](https://developer.sourcefind.cn/developer-channel) | 产品与系统选择；驱动、VBIOS、DTK、DAS、容器部署步骤 |
| [文档中心](https://developer.sourcefind.cn/document/) | 官方文档检索；页面可能要求浏览器会话或登录 |
| [DTK](https://developer.sourcefind.cn/dtk) | DTK 下载、文档、FAQ、教程和版本动态 |
| [DTK 下载目录](https://download.sourcefind.cn:65024/1/main) | 安装包与版本目录 |
| [DTK 最新文档目录](https://download.sourcefind.cn:65024/1/main/latest/Document) | 当前发布版文档集合 |
| [DCU 上手指南](https://developer.sourcefind.cn/gitbook/dcu_tutorial/index.html) | 入门教程；可能跳转统一登录 |
| [DAS](https://das.sourcefind.cn:55011/portal/) | 应用分析与相关工具入口 |
| [DAP](https://dap.sourcefind.cn/) | 开发与适配平台入口 |
| [代码仓库](https://developer.sourcefind.cn/codes/) | 示例、适配代码和项目 |
| [模型仓库](https://developer.sourcefind.cn/modelzoo/list) | DCU 模型资源 |
| [镜像仓库](https://harbor.sourcefind.cn:5443/) | 容器镜像；使用前确认登录和拉取权限 |
| [科学计算](https://dos.sourcefind.cn:50275/portal/#/home) | 科学计算软件与服务 |
| [C86 DevKit](https://c86.sourcefind.cn/documents) | 海光 CPU/C86 开发资料；不要与 DCU/DTK 文档混用 |
| [DTK 论坛答疑区](https://forum.sourcefind.cn/cate/1_42_43_44/seq/0) | 数学库、运行时、编译器与适配问题 |

## DTK 软件栈索引

DTK 是面向 DCU 应用开发、优化和部署的工具包。官方资源页将其能力分为以下几层。

| 类别 | 组件或主题 | 何时查 |
|---|---|---|
| 异构编程语言 | HIP、OpenCL、OpenACC、OpenMP；CUDA 兼容与迁移 | 新项目选编程模型，或移植 CUDA 程序 |
| 编译与运行时 | Fortran/C/C++ 编译器、HIP Runtime、运行时库、CUDA 兼容层 | 编译失败、运行时 API、设备与内存管理 |
| 基础数学库 | BLAS/rocBLAS、LAPACK、SPARSE | 线性代数、稀疏计算及性能调优 |
| AI/算子库 | CNN/卷积算子库 | 深度学习算子和 dynamic shape 性能 |
| C++ 并行库 | Thrust、CUB | 并行算法、扫描、归约和设备端原语 |
| 通信库 | 集合通信、DUSHMEM/单边低延迟通信 | 多卡、跨卡通信和 PGAS 风格访问 |
| 分析与调试 | 性能分析器、调试器、监控器、DAS | 定位热点、内存错误、同步错误和利用率问题 |
| 迁移工具 | GPUfusion、CUDA 兼容工具与移植流程 | 评估和转换 CUDA 工程 |
| 部署 | 国产操作系统、虚拟化、容器、高速互联 | 裸机/module 与容器环境选择 |

官方 DTK 页面当前直接列出的手册示例包括：

- `HIP Runtime API开发手册`
- `rocBLAS库使用手册`
- `DUSHMEM库使用手册`

不要把示例文件名当成完整目录。优先进入“最新文档目录”，再按已安装 DTK 版本选择同版本手册。

## 按任务选资料

| 任务 | 先查 | 随后验证 |
|---|---|---|
| 新装环境 | 开发指南 → DTK 下载 | `module list`、编译器版本、`rocminfo` |
| 写 HIP 程序 | HIP Runtime API、编译器文档 | 最小 kernel 编译与运行 |
| CUDA 项目迁移 | CUDA 兼容课程、GPUfusion、移植流程 | 构建系统、架构宏、CUDA 专属 API |
| 加速线性代数 | rocBLAS/BLAS、LAPACK、SPARSE 手册 | 数据类型、布局、目标架构、算法可用性 |
| 深度学习算子 | CNN/卷积算子库、框架适配文档 | dynamic shape、精度、workspace 和 fallback |
| 多卡通信 | 通信库、DUSHMEM 手册 | 拓扑、进程启动方式、跨节点支持 |
| 性能问题 | DAS、性能分析教程、监控工具 | 热点、传输、同步、占用率 |
| 容器部署 | 开发指南的容器化步骤、镜像仓库 | 设备映射、驱动/用户态兼容、Slurm 集成 |

## 安全与准确性

- 不公开记录账号、token、私钥、用户目录、作业 ID、内部地址或受限下载链接。
- 公开页面出现的版本号只是页面抓取时的状态；安装前重新选择产品和系统。
- 网页声明“支持”不等于目标集群可用。最终以计算节点实测和集群 profile 的 `KNOWN_LIMITATIONS` 为准。
- 不把 ROCm/CUDA 上游能力自动等同于 DTK 能力。对 Triton、FP8、INT8、通信算法和特定架构内核逐项探测。
