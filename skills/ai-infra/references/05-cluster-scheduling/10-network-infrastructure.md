# 网络基础设施

> AI 集群的网络决定了训练的天花板——网络有多快，大模型训练就能有多高效。

## 目录

- [数据中心网络架构](#数据中心网络架构)
- [RDMA 网络配置](#rdma-网络配置)
- [交换机选型](#交换机选型)
- [网络监控与故障排查](#网络监控与故障排查)
- [网络安全策略](#网络安全策略)

---

## 数据中心网络架构

### AI 集群网络分层

```
┌─────────────────────────────────────────────────────────────┐
│              AI 集群网络分层                                   │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  计算网络 (高性能):                                          │
│    用途: GPU 间通信 (AllReduce, 参数同步)                    │
│    技术: InfiniBand NDR / RoCE v2                            │
│    要求: 高带宽、低延迟、无丢包                              │
│                                                             │
│  存储网络:                                                   │
│    用途: 数据加载、Checkpoint 读写                            │
│    技术: 25/100 GbE 或 IB                                    │
│    要求: 高吞吐、稳定                                        │
│                                                             │
│  管理网络:                                                   │
│    用途: SSH、监控、日志、K8s 控制面                          │
│    技术: 1/10 GbE                                            │
│    要求: 可靠、安全                                          │
│                                                             │
│  BMC/IPMI 网络:                                              │
│    用途: 带外管理、远程开关机                                 │
│    技术: 1 GbE                                               │
│    要求: 独立隔离                                            │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## RDMA 网络配置

### RoCE v2 配置要点

```
RoCE v2 关键配置 (以太网 RDMA):

  必须配置:
  1. PFC (Priority Flow Control)
     → 防止 RDMA 数据包被丢弃
     → 交换机和网卡都要配置
     → 只对 RDMA 流量 (Priority 3) 开启

  2. ECN (Explicit Congestion Notification)
     → 拥塞通知，避免 PFC 死锁
     → 交换机标记拥塞包，网卡减速

  3. DCQCN (拥塞控制算法)
     → RoCE 专用拥塞控制
     → 在网卡上配置

  4. MTU 9000 (Jumbo Frame)
     → 减少包头开销，提升吞吐
     → 端到端所有设备都要配置
```

```bash
# Linux RoCE v2 配置示例

# 检查 RDMA 设备
rdma link show

# 配置 PFC
mlnx_qos -i eth0 --pfc 0,0,0,1,0,0,0,0  # Priority 3 开启 PFC

# 配置 ECN
echo 1 > /sys/class/net/eth0/ecn/roce_np/enable/3
echo 1 > /sys/class/net/eth0/ecn/roce_rp/enable/3

# 设置 MTU
ip link set eth0 mtu 9000

# 测试 RDMA 带宽
ib_write_bw -d mlx5_0 -p 18515  # 服务端
ib_write_bw -d mlx5_0 -p 18515 <server_ip>  # 客户端

# 测试 RDMA 延迟
ib_write_lat -d mlx5_0 -p 18515  # 服务端
ib_write_lat -d mlx5_0 -p 18515 <server_ip>  # 客户端
```

---

## 交换机选型

### AI 集群交换机推荐

| 交换机 | 类型 | 端口 | 适用场景 |
|--------|------|------|---------|
| **Mellanox QM9700** | IB NDR | 64×NDR | 大规模 IB 集群 |
| **Mellanox QM8700** | IB HDR | 40×HDR | 中型 IB 集群 |
| **Arista 7800R** | 以太网 | 400GbE | 大规模 RoCE |
| **Cisco Nexus 9000** | 以太网 | 400GbE | 企业级 RoCE |
| **Mellanox SN5600** | 以太网 | 64×400GbE | Spectrum-4 RoCE |

---

## 网络监控与故障排查

```
网络监控指标:

  计算网络:
  - AllReduce 带宽利用率 (通过 NCCL 日志)
  - RDMA 丢包率 (应该为 0)
  - 端口错误计数 (ibstat, ethtool)
  - 链路拍打 (link flapping)

  故障排查清单:
  1. 训练慢 → 检查 NCCL AllReduce 带宽
  2. 训练挂起 → 检查 RDMA 连接和丢包
  3. 间歇性卡顿 → 检查 PFC 和 ECN 配置
  4. 新节点连不上 → 检查 IB/RoCE 端口状态
```

```bash
# 常用网络诊断命令

# InfiniBand
ibstat                    # IB 端口状态
ibdiagnet                 # IB 网络诊断
ibswitches                # 列出 IB 交换机
iblinkinfo                # 链路状态信息
perfquery                 # 端口性能计数器

# 以太网 RoCE
ethtool -S eth0           # 网卡统计
show_gids                 # RDMA GID 表
rdma resource             # RDMA 资源状态

# NCCL 调试
NCCL_DEBUG=INFO python train.py  # 详细 NCCL 日志
NCCL_DEBUG_SUBSYS=NET python train.py  # 网络相关日志

# 性能测试
nccl-tests/build/all_reduce_perf -b 1M -e 4G -f 2 -g 8
```

---

## 网络安全策略

```
AI 集群网络安全:

  1. 网络隔离
     计算网络和管理网络物理隔离
     不同租户使用 VLAN 隔离

  2. 访问控制
     计算网络不暴露到公网
     SSH 跳板机访问
     K8s RBAC 权限控制

  3. 数据传输加密
     管理网络: TLS/SSH
     计算网络: 通常不加密 (性能考虑)
     → 依赖物理隔离保证安全

  4. 审计日志
     记录网络变更操作
     交换机配置版本管理
```

---

## 小结

```
网络基础设施核心要点:

1. 计算网络是 AI 集群的生命线
   IB NDR 是大规模训练的标配
   RoCE v2 是成本敏感场景的替代

2. RoCE 配置细节决定成败
   PFC + ECN + DCQCN 缺一不可
   配置错误 → 性能暴跌或死锁

3. 网络投资约占总成本 10-15%
   但网络问题造成的效率损失远大于此
   
4. 监控和故障排查能力很关键
   NCCL 日志 + IB/RoCE 工具是基础
   建立标准化的排查流程
```

---

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **NVIDIA.** *InfiniBand for AI Data Centers.*  
   https://www.nvidia.com/en-us/networking/infiniband/

2. **NVIDIA.** *Spectrum-X Ethernet for AI.*  
   https://www.nvidia.com/en-us/networking/spectrumx/

3. **Al-Fares, M., et al. (2008).** *A Scalable, Commodity Data Center Network Architecture.* ACM SIGCOMM.  
   https://dl.acm.org/doi/10.1145/1402958.1402967
