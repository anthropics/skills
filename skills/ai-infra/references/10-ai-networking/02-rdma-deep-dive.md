# RDMA 深入

> RDMA 让 GPU 之间的通信绕过 CPU 和操作系统内核——这是大规模 AI 训练实现微秒级低延迟的关键技术。

## 目录

- [RDMA 原理](#rdma-原理)
- [InfiniBand vs RoCE v2](#infiniband-vs-roce-v2)
- [RDMA 编程模型](#rdma-编程模型)
- [RoCE v2 网络配置](#roce-v2-网络配置)
- [NCCL 与 RDMA](#nccl-与-rdma)
- [性能调优](#性能调优)
- [延伸阅读](#延伸阅读)

---

## RDMA 原理

### 生活类比：快递直达 vs 转寄

```
传统网络 (TCP/IP) = 寄快递经过转运站:
  寄件人(GPU) → 前台(CPU内核) → 转运站(协议栈) → 快递员(NIC) → 收件人
  每个环节都要拆包检查、重新打包
  延迟: 50-100 μs

RDMA = 快递直达:
  寄件人(GPU) → 直接放入快递柜(NIC) → 收件人直接取
  不经过前台和转运站
  延迟: 1-5 μs

  关键优势:
    零拷贝: 数据不经过 CPU 内存
    内核旁路: 不经过操作系统网络栈
    CPU 卸载: CPU 几乎不参与数据传输
```

### RDMA 工作原理

```
┌─────────────────────────────────────────────────────────────────┐
│                   RDMA 工作原理                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  传统 TCP/IP 路径:                                               │
│  ┌──────┐ → ┌──────┐ → ┌──────┐ → ┌──────┐ → ┌──────┐        │
│  │ App  │   │ 内核  │   │TCP/IP│   │ 驱动  │   │ NIC  │        │
│  │ 缓冲 │   │ 拷贝  │   │ 协议 │   │      │   │      │        │
│  └──────┘   └──────┘   └──────┘   └──────┘   └──────┘        │
│  4 次内存拷贝 + 2 次上下文切换                                   │
│                                                                 │
│  RDMA 路径:                                                      │
│  ┌──────┐ ──────────────────────────────────→ ┌──────┐         │
│  │ App  │       HCA/NIC 直接 DMA               │ NIC  │         │
│  │ 缓冲 │  (内存注册后，NIC 直接读写应用内存)    │      │         │
│  └──────┘                                     └──────┘         │
│  0 次内存拷贝 + 0 次上下文切换                                   │
│                                                                 │
│  RDMA 操作类型:                                                  │
│    SEND/RECV: 类似传统消息传递（双方都参与）                     │
│    WRITE: 远程写（单方写入远端内存，远端 CPU 无感知）             │
│    READ: 远程读（单方读取远端内存，远端 CPU 无感知）              │
│                                                                 │
│  NCCL 主要使用 SEND/RECV 模式                                    │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## InfiniBand vs RoCE v2

### 详细对比

| 维度 | InfiniBand | RoCE v2 |
|------|-----------|---------|
| **协议层** | 原生 RDMA 协议栈 | RDMA over UDP/IP |
| **延迟** | ~1 μs | ~2-5 μs |
| **带宽** | HDR 200G, NDR 400G, XDR 800G | 100G, 200G, 400G |
| **无损传输** | 原生支持（基于信用的流控） | 需配置 PFC/ECN/DCQCN |
| **拥塞控制** | 硬件内置 | 需软件配置 (DCQCN) |
| **交换机** | 专用 IB 交换机 | 支持 RoCE 的以太网交换机 |
| **成本** | 高（专用设备） | 中（复用以太网基础设施） |
| **运维复杂度** | 中（专用工具链） | 高（需精细的网络配置） |
| **多租户** | 原生支持 (Partition Key) | 需 VLAN/VxLAN |
| **生态** | HPC 成熟，AI 主流 | 数据中心，增长快速 |

### 选型建议

```
选择 InfiniBand:
  ✓ 大规模训练集群 (256+ GPU)
  ✓ 追求最低延迟和最高带宽
  ✓ 有专业网络运维团队
  ✓ 预算充足

选择 RoCE v2:
  ✓ 中小规模集群 (64-256 GPU)
  ✓ 已有以太网基础设施
  ✓ 需要存储和计算共享网络
  ✓ 成本敏感
  注意: 需要精心配置 PFC/ECN 保证无损
```

---

## RDMA 编程模型

### Verbs API 核心概念

```
RDMA 编程核心概念:

  Protection Domain (PD): 资源隔离域
  Memory Region (MR): 注册给 NIC 的内存区域
  Queue Pair (QP): 发送队列 + 接收队列
  Completion Queue (CQ): 完成通知队列

  工作流:
  ┌──────────────────────────────────────────┐
  │  1. 创建 PD                              │
  │  2. 注册 MR (告诉 NIC 哪些内存可用)       │
  │  3. 创建 QP (建立通信通道)                │
  │  4. 交换 QP 信息 (地址信息)               │
  │  5. 发送 Work Request (WR) 到 SQ/RQ       │
  │  6. 轮询 CQ 获取完成事件                  │
  └──────────────────────────────────────────┘
```

### RDMA 性能测试

```bash
# RDMA 性能测试工具 (perftest)

# 安装
# apt-get install perftest  (Ubuntu)
# yum install perftest      (CentOS)

# 1. 带宽测试
# 服务端
ib_write_bw -d mlx5_0 -s 65536 -n 10000

# 客户端
ib_write_bw -d mlx5_0 -s 65536 -n 10000 <server_ip>

# 预期结果 (NDR 400G):
# BW peak: ~48 GB/s (接近线速 50 GB/s)

# 2. 延迟测试
# 服务端
ib_write_lat -d mlx5_0 -s 2

# 客户端
ib_write_lat -d mlx5_0 -s 2 <server_ip>

# 预期结果:
# IB: ~1.0-1.5 μs
# RoCE v2: ~2-3 μs

# 3. 多连接带宽测试
ib_write_bw -d mlx5_0 -s 65536 -n 10000 -q 4 <server_ip>

# 4. 查看 RDMA 设备信息
ibstat
ibv_devinfo

# 5. 网络状态查看
ibstatus
ibdiagnet  # InfiniBand 诊断工具
```

---

## RoCE v2 网络配置

### 关键配置项

```bash
# RoCE v2 无损网络配置

# === 交换机端配置（以 Mellanox SN 系列为例）===

# 1. 启用 PFC (Priority Flow Control)
# 为 RDMA 流量分配专用优先级（通常 Priority 3 或 4）
# interface ethernet 1/1
#   dcb priority-flow-control mode on force
#   dcb priority-flow-control priority 3 enable

# 2. 启用 ECN (Explicit Congestion Notification)
# interface ethernet 1/1
#   dcb ecn enable
#   dcb ecn threshold 150KB

# === 服务器端配置 ===

# 3. 配置 DSCP 和 ToS
# 将 RoCE 流量标记为特定 DSCP
mlnx_qos -i eth0 --trust dscp

# 4. 配置 PFC
mlnx_qos -i eth0 --pfc 0,0,0,1,0,0,0,0  # Priority 3 启用 PFC

# 5. 配置 TC (Traffic Class)
mlnx_qos -i eth0 --tc_bw 0,0,0,100,0,0,0,0

# 6. 配置 DCQCN 拥塞控制
echo 1 > /sys/class/net/eth0/ecn/roce_np/enable/3
echo 1 > /sys/class/net/eth0/ecn/roce_rp/enable/3

# 7. 设置 GID 索引（RoCE v2 使用 IPv4/IPv6）
# 查看 GID 表
cat /sys/class/infiniband/mlx5_0/ports/1/gids/*

# 8. MTU 优化
ip link set eth0 mtu 9000  # Jumbo Frame

# 验证配置
mlnx_qos -i eth0  # 查看 QoS 配置
ibv_devinfo        # 查看 RDMA 设备
ib_write_bw <peer> # 验证带宽
```

---

## NCCL 与 RDMA

### NCCL 网络选择

```bash
# NCCL 环境变量配置

# 选择网络接口
export NCCL_SOCKET_IFNAME=eth0        # TCP 后备接口
export NCCL_IB_HCA=mlx5_0,mlx5_1     # 指定 RDMA 设备

# 网络协议选择
export NCCL_NET_GDR_LEVEL=5           # GPUDirect RDMA 级别
export NCCL_IB_GID_INDEX=3            # RoCE v2 GID 索引

# 性能调优
export NCCL_IB_TIMEOUT=22             # IB 超时设置
export NCCL_IB_RETRY_CNT=7            # 重试次数
export NCCL_BUFFSIZE=8388608           # 缓冲区大小 (8MB)
export NCCL_NTHREADS=512               # NCCL 线程数

# 算法选择
export NCCL_ALGO=Ring                  # Ring / Tree / CollNet
export NCCL_PROTO=Simple               # Simple / LL / LL128

# 调试
export NCCL_DEBUG=INFO                 # 调试信息级别
export NCCL_DEBUG_SUBSYS=NET           # 网络相关调试

# 常见 NCCL 性能问题:
# 1. NCCL 选择了 TCP 而非 RDMA → 检查 IB 设备配置
# 2. 带宽远低于线速 → 检查 PFC/ECN/MTU 配置
# 3. 超时错误 → 检查防火墙、IB 端口状态
# 4. 偶发卡顿 → 检查 PFC 风暴、ECN 阈值
```

---

## 性能调优

### RDMA 性能调优清单

```
RDMA 性能调优 Top 10:

  1. ✅ 启用 Jumbo Frame (MTU 9000)
     → 减少包头开销，提升大消息吞吐

  2. ✅ 配置正确的 PFC 优先级 (RoCE)
     → 保证无损传输，避免丢包重传

  3. ✅ 启用 GPUDirect RDMA
     → GPU 直接访问 NIC，减少延迟

  4. ✅ 使用多 HCA/NIC
     → 多链路聚合，增加总带宽

  5. ✅ 调优 NCCL 缓冲区大小
     → 匹配消息大小，减少同步开销

  6. ✅ 选择正确的 NCCL 算法
     → Ring (大消息), Tree (小消息)

  7. ✅ CPU 亲和性绑定
     → GPU 和 NIC 在同一 NUMA 域

  8. ✅ 中断聚合 (Interrupt Coalescing)
     → 平衡延迟和 CPU 开销

  9. ✅ 内存页大小优化 (Huge Pages)
     → 减少 TLB miss，提升 RDMA 注册效率

  10. ✅ 监控 RDMA 计数器
      → 及时发现丢包、重传、错误
```

---

## 延伸阅读

- [RDMA Aware Networks Programming User Manual](https://docs.nvidia.com/networking/display/rdmacore50)
- [InfiniBand Architecture Specification](https://www.infinibandta.org/)
- [RoCE v2 Configuration Guide (Mellanox)](https://enterprise-support.nvidia.com/s/article/howto-configure-roce-v2)
- 论文: *Design Guidelines for High Performance RDMA Systems* (ATC '16)

---

*上一篇：[01-networking-fundamentals.md](01-networking-fundamentals.md)* | *下一篇：[03-network-topology.md](03-network-topology.md)*

*返回：[README.md](README.md) - 章节索引*
