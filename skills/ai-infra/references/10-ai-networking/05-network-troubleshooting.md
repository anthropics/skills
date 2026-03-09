# 网络故障排查

> 训练突然变慢 50%？NCCL 超时？丢包？——网络故障排查是 AI 集群运维最频繁的任务之一。

## 目录

- [常见网络问题分类](#常见网络问题分类)
- [诊断工具箱](#诊断工具箱)
- [NCCL 调试](#nccl-调试)
- [丢包分析](#丢包分析)
- [性能回退排查](#性能回退排查)
- [常见故障案例](#常见故障案例)
- [延伸阅读](#延伸阅读)

---

## 常见网络问题分类

```
┌─────────────────────────────────────────────────────────────────┐
│              AI 集群常见网络问题分类                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  致命问题（训练中断）:                                            │
│    ✗ NCCL 超时 → 某节点完全不通                                  │
│    ✗ 链路 Down → 线缆断开/交换机故障                             │
│    ✗ GPU 挂死 → GPUDirect RDMA 失败                              │
│                                                                 │
│  性能问题（训练变慢）:                                            │
│    ✗ 带宽下降 → 线缆劣化/配置错误/PFC 风暴                      │
│    ✗ 延迟升高 → 拥塞/路由次优/ECN 配置不当                      │
│    ✗ 偶发卡顿 → 间歇性丢包/PFC pause                            │
│                                                                 │
│  配置问题:                                                       │
│    ✗ NCCL 选择了 TCP → RDMA 设备未识别                           │
│    ✗ GDR 未启用 → nvidia-peermem 未加载                          │
│    ✗ MTU 不匹配 → 中间设备 MTU 小于端点                          │
│    ✗ RoCE PFC 未配置 → 丢包导致性能暴跌                          │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 诊断工具箱

### 基础诊断

```bash
# 网络诊断工具箱

# === RDMA 设备状态 ===
ibstat                           # IB 端口状态
ibstatus                         # 所有 IB 端口概览
ibv_devinfo                      # 详细设备信息

# === 链路状态 ===
ibdiagnet                        # IB 网络全面诊断
iblinkinfo                       # 所有链路信息
# 关注: State=Active, PhyState=LinkUp, Rate=NDR

# === 带宽测试 ===
# 服务端
ib_write_bw -d mlx5_0 -s 65536 -n 5000 --report_gbits
# 客户端
ib_write_bw -d mlx5_0 -s 65536 -n 5000 --report_gbits <server>
# 期望: NDR 400G → ~390 Gbps

# === 延迟测试 ===
ib_write_lat -d mlx5_0 -s 2 -n 5000 <server>
# 期望: IB ~1μs, RoCE ~2-3μs

# === GPU 拓扑检查 ===
nvidia-smi topo -m              # GPU 和 NIC 的 PCIe 拓扑
# 确认 GPU 和对应 NIC 在同一 PCIe Switch 下

# === 网络计数器 ===
ethtool -S eth0 | grep -i "err\|drop\|pause\|ecn"
# RoCE: 关注 rx_pause, tx_pause, rx_discards

# InfiniBand 端口计数器
perfquery -x                     # 扩展端口计数器
# 关注: PortRcvErrors, PortXmitDiscards, SymbolErrors
```

### 高级诊断

```bash
# 高级网络诊断

# === RDMA 连接追踪 ===
rdma resource show               # 查看 RDMA 资源使用

# === PFC 监控 (RoCE) ===
# 检查 PFC Pause 帧数量
ethtool -S eth0 | grep pause
# 大量 tx_pause_ctrl → 自己发了很多暂停帧 → 接收端拥塞
# 大量 rx_pause_ctrl → 对端发了暂停帧 → 自己可能被限速

# === 抓包分析 ===
# RoCE v2 基于 UDP，可以用 tcpdump
tcpdump -i eth0 udp port 4791 -c 100 -w roce_capture.pcap
# 用 Wireshark 分析 RoCE 流量

# === NCCL 性能测试 ===
# 全面的通信性能测试
nccl-tests/build/all_reduce_perf \
    -b 1M -e 4G -f 2 \
    -g 8 -n 100 \
    -w 50  # warmup

# 期望: 8 GPU 节点内 bus bandwidth 接近 NVLink 带宽
# 多节点: 接近网络带宽

# === PCIe 带宽验证 ===
nvidia-smi -q | grep -A5 "PCI"
# 确认 PCIe Gen5 x16 = 64 GB/s
```

---

## NCCL 调试

### NCCL 日志分析

```bash
# NCCL 调试环境变量
export NCCL_DEBUG=INFO               # INFO, WARN, TRACE
export NCCL_DEBUG_SUBSYS=ALL         # ALL, INIT, COLL, P2P, NET, GRAPH
export NCCL_DEBUG_FILE=/tmp/nccl_%h_%p.log  # 日志文件

# 关键日志信息:
# 1. 网络选择
#    "NET/IB : Using [0]mlx5_0:1/IB" → 使用 InfiniBand
#    "NET/Socket" → 退回到 TCP！需要检查 RDMA 配置

# 2. GDR 状态
#    "NET/IB : Using GPUDirect RDMA" → GDR 启用
#    "NET/IB : GPU Direct RDMA Disabled" → GDR 未启用

# 3. 算法选择
#    "NCCL INFO Ring" → Ring AllReduce
#    "NCCL INFO Tree" → Tree AllReduce

# 4. 超时错误
#    "NCCL WARN Watchdog caught collective operation timeout"
#    → 某个 rank 卡住了，检查该节点

# 常见 NCCL 问题排查:
# Q: NCCL 选择了 TCP 而非 RDMA
# A: 检查 NCCL_IB_HCA 环境变量，确认 IB 设备状态

# Q: NCCL 超时
# A: 检查所有节点网络连通性，防火墙，IB 端口状态

# Q: 带宽远低于预期
# A: 检查 MTU、PFC、ECN 配置，检查 PCIe/NVLink 拓扑
```

---

## 丢包分析

```
丢包对 AI 训练的影响:

  RDMA 丢包 → Go-Back-N 重传 → 延迟飙升
  1% 丢包率 → 吞吐下降 50%+
  → 所以 RoCE 必须配置无损网络 (PFC)

  丢包排查流程:
  ┌──────────────────────────────────────────────┐
  │  1. 检查端口错误计数器                        │
  │     perfquery / ethtool -S                    │
  │     看 errors, discards, drops                │
  │                                              │
  │  2. 检查 PFC 配置 (RoCE)                      │
  │     mlnx_qos -i eth0                          │
  │     确认正确优先级启用了 PFC                   │
  │                                              │
  │  3. 检查交换机端口                            │
  │     show interface counters errors            │
  │     看 CRC 错误、丢弃计数                     │
  │                                              │
  │  4. 检查线缆                                  │
  │     mlxlink -d mlx5_0 -p 1                    │
  │     看 BER (误码率)、信号质量                  │
  │     BER > 1e-12 → 线缆需要更换                │
  │                                              │
  │  5. 检查拥塞                                  │
  │     ECN 标记数量                              │
  │     PFC pause 持续时间                        │
  │     → PFC 风暴可能导致全网瘫痪                │
  └──────────────────────────────────────────────┘
```

---

## 性能回退排查

```
训练突然变慢的排查流程:

  Step 1: 确认是网络问题
    对比: 单机 vs 多机训练速度
    如果单机正常 → 网络问题
    如果单机也慢 → GPU/存储问题

  Step 2: 定位问题节点
    # 两两测试带宽
    for node in node1 node2 ... nodeN; do
        ssh $node ib_write_bw -d mlx5_0 <target_node>
    done
    # 找到带宽异常的节点

  Step 3: 深入排查异常节点
    nvidia-smi topo -m           # PCIe 拓扑是否正常
    ibstatus                     # IB 端口状态
    perfquery -x                 # 错误计数器
    mlxlink -d mlx5_0 -p 1      # 链路质量
    dmesg | grep -i "error\|warn\|nccl"  # 内核日志

  Step 4: 常见原因
    1. 线缆松动/劣化 → 更换线缆
    2. NIC 降速 → 重置 NIC
    3. PFC 风暴 → 调整 ECN 阈值
    4. GPU 降频 → 检查温度/功耗
    5. PCIe 降级 → 重新 reseat GPU/NIC
```

---

## 常见故障案例

### 案例 1：PFC 风暴

```
症状: 整个集群训练速度突然下降 80%
原因: 一个节点的 NIC 发生故障，持续发送 PFC Pause 帧
      → Pause 帧沿交换机传播 → 全网被暂停

排查:
  ethtool -S eth0 | grep pause
  # 发现某节点 tx_pause 计数暴增

修复:
  1. 隔离故障节点
  2. 交换机端配置 PFC watchdog（自动检测并关闭长时间 Pause 的端口）
  3. 更换故障 NIC

预防:
  - 交换机启用 PFC watchdog
  - 监控 PFC 计数器并设置告警
  - 定期检查线缆和 NIC 状态
```

### 案例 2：NCCL 选择了错误的网络

```
症状: 多节点训练速度只有预期的 1/10
原因: NCCL 选择了 TCP/管理网 而非 RDMA/高速网

排查:
  NCCL_DEBUG=INFO 查看日志
  "NET/Socket : Using [0]eth0" → 用了 TCP！

修复:
  export NCCL_IB_HCA=mlx5_0,mlx5_1    # 指定 RDMA 设备
  export NCCL_SOCKET_IFNAME=eth0       # TCP 后备接口
  export NCCL_IB_GID_INDEX=3           # RoCE v2 GID
```

---

## 延伸阅读

- [NCCL Troubleshooting Guide](https://docs.nvidia.com/deeplearning/nccl/user-guide/docs/troubleshooting.html)
- [Mellanox Performance Tuning Guide](https://enterprise-support.nvidia.com/s/article/performance-tuning-for-mellanox-adapters)
- [perftest GitHub](https://github.com/linux-rdma/perftest)

---

*上一篇：[04-gpudirect-technologies.md](04-gpudirect-technologies.md)* | *下一篇：[06-network-planning.md](06-network-planning.md)*

*返回：[README.md](README.md) - 章节索引*
