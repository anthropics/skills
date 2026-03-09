# 训练调试

> 训练调试就像医生看诊——Loss 曲线是"心电图"，梯度是"血压"，权重分布是"血检报告"，要综合分析才能找到病因。

## 目录

- [Loss 曲线分析](#loss-曲线分析)
- [NaN 与 Inf 检测](#nan-与-inf-检测)
- [梯度监控](#梯度监控)
- [权重与激活值分析](#权重与激活值分析)
- [分布式训练调试](#分布式训练调试)
- [常见训练问题排查](#常见训练问题排查)
- [延伸阅读](#延伸阅读)

---

## Loss 曲线分析

### 健康的 Loss 曲线

```
健康的训练 Loss 曲线特征

Loss ↑
  4.0│\
     │ \
  3.0│  \
     │   \
  2.0│    \___
     │        \____
  1.0│             \__________  ← 逐渐收敛，小幅波动
     │                        \___
  0.5│                            \___________
     └────────────────────────────────────────→ Steps

健康特征:
  ✅ 整体下降趋势
  ✅ 适度波动（不是直线下降）
  ✅ 最终趋于稳定
  ✅ Train Loss 和 Eval Loss 走势接近
```

### 异常 Loss 模式诊断

```
异常模式 1: Loss 爆炸 (Spike/Diverge)
Loss ↑
     │                    /
     │                   /
     │          ________/  ← Loss 突然飙升
     │         /
     │\       /
     │ \_____/
     └──────────────→ Steps

原因: 学习率太大 | 梯度爆炸 | 数据异常 | 数值不稳定
修复: 降低学习率 | 梯度裁剪 | 检查数据 | 使用 BF16

─────────────────────────────────────────────────

异常模式 2: Loss 不下降 (Plateau)
Loss ↑
  4.0│───────────────────────── ← 完全平坦
     │
     └──────────────────→ Steps

原因: 学习率太小 | 模型容量不足 | 数据有问题 | 梯度消失
修复: 增大学习率 | 增大模型 | 检查数据管线 | 检查梯度

─────────────────────────────────────────────────

异常模式 3: 过拟合
Loss ↑
     │ Train: ─────────────── (持续下降)
     │ Eval:  ──────────/     (先降后升)
     │                 /
     └──────────────────→ Steps

原因: 训练数据太少 | 模型过大 | 训练轮次太多
修复: 早停 | 增加数据 | 减小模型 | 正则化

─────────────────────────────────────────────────

异常模式 4: 周期性波动
Loss ↑
     │ /\  /\  /\  /\
     │/  \/  \/  \/  \
     └──────────────────→ Steps

原因: 学习率周期重启 | 批大小太小 | 数据顺序问题
修复: 检查 LR scheduler | 增大批大小 | 数据打乱
```

### Loss 监控代码

```python
class TrainingMonitor:
    """训练过程监控器"""
    
    def __init__(self, window_size: int = 100, spike_threshold: float = 3.0):
        self.losses = []
        self.grad_norms = []
        self.window_size = window_size
        self.spike_threshold = spike_threshold
    
    def log_step(self, loss: float, grad_norm: float = None, step: int = 0):
        """记录每步的指标"""
        self.losses.append(loss)
        if grad_norm is not None:
            self.grad_norms.append(grad_norm)
        
        # 检测异常
        alerts = self._check_anomalies(step)
        for alert in alerts:
            print(f"  ⚠️  Step {step}: {alert}")
        
        return alerts
    
    def _check_anomalies(self, step: int) -> list:
        alerts = []
        
        # NaN/Inf 检测
        if len(self.losses) > 0 and (
            self.losses[-1] != self.losses[-1] or  # NaN
            abs(self.losses[-1]) == float('inf')    # Inf
        ):
            alerts.append("Loss 出现 NaN/Inf！立即停止训练")
            return alerts
        
        # Loss spike 检测
        if len(self.losses) > self.window_size:
            recent_mean = sum(self.losses[-self.window_size:-1]) / (self.window_size - 1)
            recent_std = (sum((l - recent_mean)**2 for l in self.losses[-self.window_size:-1]) 
                         / (self.window_size - 1)) ** 0.5
            if self.losses[-1] > recent_mean + self.spike_threshold * max(recent_std, 0.01):
                alerts.append(f"Loss Spike 检测: {self.losses[-1]:.4f} >> 均值 {recent_mean:.4f}")
        
        # Loss 不下降检测
        if len(self.losses) > self.window_size * 2:
            first_half = sum(self.losses[-2*self.window_size:-self.window_size]) / self.window_size
            second_half = sum(self.losses[-self.window_size:]) / self.window_size
            if second_half >= first_half * 0.99:
                alerts.append(f"Loss 停滞: 最近 {self.window_size} 步无明显下降")
        
        return alerts
```

---

## NaN 与 Inf 检测

### NaN/Inf 的来源

```
NaN/Inf 产生的常见原因

1. 数值溢出
   ├── FP16 最大值 65504，超过则 Inf
   ├── exp(x) 当 x > 88 (FP32) 时溢出
   └── 解决: 使用 BF16（范围同 FP32）

2. 除零
   ├── LayerNorm 中方差为 0
   ├── 学习率调度器返回 0
   └── 解决: 添加 epsilon（1e-8）

3. Log 负数
   ├── log(负数或0) = NaN
   ├── 常见于交叉熵损失
   └── 解决: 数值裁剪 log(clamp(x, min=1e-8))

4. 梯度爆炸
   ├── 梯度值过大 → 权重更新过大 → 下一步更大
   ├── 正反馈循环导致 Inf
   └── 解决: 梯度裁剪 (max_grad_norm=1.0)
```

### NaN 检测工具

```python
import torch

# 方法 1: PyTorch 内置异常检测
torch.autograd.set_detect_anomaly(True)
# 注意: 会显著降低训练速度，仅调试时使用

# 方法 2: 自定义 NaN 检测 Hook
class NaNDetector:
    """NaN/Inf 检测器"""
    
    def __init__(self, model: torch.nn.Module):
        self.hooks = []
        for name, module in model.named_modules():
            hook = module.register_forward_hook(
                self._make_hook(name)
            )
            self.hooks.append(hook)
    
    def _make_hook(self, name: str):
        def hook(module, input, output):
            if isinstance(output, torch.Tensor):
                if torch.isnan(output).any():
                    raise RuntimeError(
                        f"NaN 检测到! 模块: {name}, "
                        f"形状: {output.shape}, "
                        f"NaN 数量: {torch.isnan(output).sum().item()}"
                    )
                if torch.isinf(output).any():
                    raise RuntimeError(
                        f"Inf 检测到! 模块: {name}, "
                        f"形状: {output.shape}, "
                        f"Inf 数量: {torch.isinf(output).sum().item()}"
                    )
        return hook
    
    def remove(self):
        for hook in self.hooks:
            hook.remove()

# 使用
detector = NaNDetector(model)
try:
    output = model(input_data)
except RuntimeError as e:
    print(f"发现问题: {e}")
finally:
    detector.remove()  # 清理 hooks

# 方法 3: 梯度 NaN 检测
for name, param in model.named_parameters():
    if param.grad is not None:
        if torch.isnan(param.grad).any():
            print(f"梯度 NaN: {name}")
        if torch.isinf(param.grad).any():
            print(f"梯度 Inf: {name}")
```

---

## 梯度监控

### 梯度范数追踪

```python
def monitor_gradients(model, step: int, log_interval: int = 100):
    """监控模型梯度"""
    if step % log_interval != 0:
        return
    
    grad_stats = {}
    total_norm = 0.0
    
    for name, param in model.named_parameters():
        if param.grad is not None:
            grad = param.grad.data
            grad_norm = grad.norm(2).item()
            total_norm += grad_norm ** 2
            
            grad_stats[name] = {
                "norm": grad_norm,
                "mean": grad.mean().item(),
                "std": grad.std().item(),
                "max": grad.abs().max().item(),
                "zero_ratio": (grad == 0).float().mean().item(),
            }
    
    total_norm = total_norm ** 0.5
    
    # 输出摘要
    print(f"\nStep {step} 梯度报告:")
    print(f"  总梯度范数: {total_norm:.4f}")
    
    # 检测异常
    if total_norm > 100:
        print(f"  ⚠️  梯度范数过大！可能梯度爆炸")
    elif total_norm < 1e-6:
        print(f"  ⚠️  梯度范数过小！可能梯度消失")
    
    # 找出梯度最大和最小的层
    sorted_by_norm = sorted(grad_stats.items(), key=lambda x: x[1]["norm"], reverse=True)
    print(f"  梯度最大的层: {sorted_by_norm[0][0]} ({sorted_by_norm[0][1]['norm']:.4f})")
    print(f"  梯度最小的层: {sorted_by_norm[-1][0]} ({sorted_by_norm[-1][1]['norm']:.6f})")

# 在训练循环中使用
for step, batch in enumerate(dataloader):
    loss = model(batch).loss
    loss.backward()
    
    # 监控梯度
    monitor_gradients(model, step)
    
    # 梯度裁剪
    torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
    
    optimizer.step()
    optimizer.zero_grad()
```

### 梯度爆炸 vs 梯度消失

```
梯度爆炸 vs 梯度消失

梯度爆炸:
  │                    /
  │                   /
  │ 梯度范数          /
  │                 /
  │     ___________/
  └──────────────────→ 层数（从输出到输入）
  
  表现: 深层梯度远大于浅层
  原因: 权重初始化不当、无归一化、学习率过大
  解决: 梯度裁剪 | Pre-LN | 权重初始化 | 降低学习率

梯度消失:
  │
  │ 梯度范数
  │ \
  │  \___
  │      \_________
  │                \____________
  └──────────────────→ 层数（从输出到输入）
  
  表现: 浅层梯度接近零
  原因: 激活函数饱和 | 层数过深 | 无残差连接
  解决: 残差连接 | Pre-LN | 使用 GeLU/SiLU
```

---

## 权重与激活值分析

### 权重分布监控

```python
import torch
from collections import defaultdict

class WeightWatcher:
    """权重分布监控器"""
    
    def __init__(self, model):
        self.model = model
        self.history = defaultdict(list)
    
    def snapshot(self, step: int):
        """记录当前权重快照"""
        for name, param in self.model.named_parameters():
            if "weight" in name and param.dim() >= 2:
                stats = {
                    "step": step,
                    "mean": param.data.mean().item(),
                    "std": param.data.std().item(),
                    "max": param.data.abs().max().item(),
                    "min": param.data.abs().min().item(),
                    "norm": param.data.norm(2).item(),
                }
                self.history[name].append(stats)
    
    def check_health(self) -> list:
        """检查权重健康状况"""
        issues = []
        
        for name, snapshots in self.history.items():
            if len(snapshots) < 2:
                continue
            
            latest = snapshots[-1]
            
            # 检查权重是否变化（是否在更新？）
            if len(snapshots) >= 10:
                first = snapshots[0]
                if abs(latest["norm"] - first["norm"]) < 1e-6:
                    issues.append(f"{name}: 权重未更新（冻结或梯度为零？）")
            
            # 检查权重分布
            if latest["std"] < 1e-6:
                issues.append(f"{name}: 权重标准差过小（权重退化）")
            
            if latest["max"] > 100:
                issues.append(f"{name}: 权重最大值过大（{latest['max']:.1f}）")
        
        return issues
```

---

## 分布式训练调试

### NCCL 调试

```bash
# 启用 NCCL 调试日志
export NCCL_DEBUG=INFO          # INFO 级别日志
export NCCL_DEBUG=WARN          # 仅警告和错误
export NCCL_DEBUG_SUBSYS=ALL    # 所有子系统

# NCCL 调试环境变量
export NCCL_IB_DISABLE=0        # 启用 InfiniBand
export NCCL_SOCKET_IFNAME=eth0  # 指定网络接口
export NCCL_P2P_DISABLE=0       # 启用 P2P
export NCCL_SHM_DISABLE=0       # 启用共享内存

# NCCL 超时设置（防止 hang）
export NCCL_TIMEOUT=1800         # 30 分钟超时
export TORCH_NCCL_BLOCKING_WAIT=1
```

### 常见分布式训练错误

```
分布式训练常见错误及解决

1. NCCL Timeout
   错误: "NCCL operation timed out"
   原因: 某个节点卡住、网络问题、负载不均衡
   排查:
     ├── 检查所有节点是否正常运行
     ├── 检查网络连通性（ping/ib_write_bw）
     ├── 检查是否有节点 GPU 故障
     └── 增大 NCCL_TIMEOUT

2. 梯度不一致
   错误: 不同 Rank 的 loss 差异很大
   原因: 数据分片不一致、模型初始化不同步、随机种子不一致
   排查:
     ├── 检查 DataLoader 的 sampler
     ├── 检查模型权重是否一致（broadcast）
     └── 设置相同的随机种子

3. 显存不均衡
   错误: 某些 GPU OOM，其他正常
   原因: 数据长度不均匀、模型并行分配不均
   排查:
     ├── 检查各 GPU 的显存使用 (nvidia-smi)
     ├── 使用 padding 统一序列长度
     └── 检查模型并行的分层策略

4. Hang（卡住不动）
   错误: 训练停止响应
   原因: 死锁、某个 Rank 崩溃但未被检测到
   排查:
     ├── torch.distributed.monitored_barrier()
     ├── 检查每个 Rank 的进程状态
     └── 使用 py-spy 或 gdb attach 到卡住的进程
```

### 分布式调试工具

```python
import torch.distributed as dist

def distributed_health_check():
    """分布式训练健康检查"""
    rank = dist.get_rank()
    world_size = dist.get_world_size()
    
    # 1. 检查所有 Rank 是否就绪
    dist.barrier()
    print(f"Rank {rank}: barrier 通过")
    
    # 2. 检查通信
    tensor = torch.tensor([rank], dtype=torch.float32).cuda()
    gathered = [torch.zeros(1).cuda() for _ in range(world_size)]
    dist.all_gather(gathered, tensor)
    
    expected = list(range(world_size))
    actual = [int(t.item()) for t in gathered]
    assert actual == expected, f"AllGather 不一致: {actual} != {expected}"
    print(f"Rank {rank}: AllGather 正确")
    
    # 3. 检查模型参数一致性
    model_params = list(model.parameters())
    for i, param in enumerate(model_params[:5]):
        param_sum = param.data.sum().item()
        sum_tensor = torch.tensor([param_sum]).cuda()
        all_sums = [torch.zeros(1).cuda() for _ in range(world_size)]
        dist.all_gather(all_sums, sum_tensor)
        
        sums = [t.item() for t in all_sums]
        if max(sums) - min(sums) > 1e-4:
            print(f"⚠️  参数 {i} 不一致: {sums}")
    
    print(f"Rank {rank}: 健康检查完成 ✅")
```

---

## 常见训练问题排查

### 问题速查表

| 问题 | 症状 | 排查方向 | 解决方案 |
|------|------|---------|---------|
| Loss NaN | Loss 变成 NaN | detect_anomaly | BF16, 梯度裁剪, 检查数据 |
| Loss 不降 | 训练无进展 | 检查 LR, 数据, 梯度 | 增大 LR, 检查数据管线 |
| Loss spike | 突然飙升后恢复 | 检查数据质量 | 梯度裁剪, 降低 LR |
| OOM | CUDA out of memory | 显存分析 | 梯度检查点, 减小 batch |
| 训练变慢 | 速度逐渐下降 | 检查 DataLoader | 内存泄漏, GC, 数据缓存 |
| 精度差 | 指标不达标 | 检查评估方法 | 数据质量, 超参数, 模型大小 |

### 调试检查清单

```
训练问题排查检查清单

□ 数据
  □ 数据加载是否正确？（打印前几个 batch 检查）
  □ 标签是否正确？
  □ 数据是否有 NaN/Inf？
  □ tokenizer 和模型是否匹配？
  □ Chat Template 是否正确？

□ 模型
  □ 模型加载是否正确？
  □ 所有参数的 requires_grad 是否正确？
  □ 混合精度是否配置正确？
  □ 梯度检查点是否正常工作？

□ 训练配置
  □ 学习率是否合理？
  □ 学习率调度器是否正确？
  □ 梯度裁剪是否启用？
  □ 权重衰减是否合理？

□ 分布式
  □ 所有节点是否正常？
  □ 网络连通性是否正常？
  □ NCCL 配置是否正确？
  □ 数据分片是否均匀？
```

---

## 延伸阅读

- [PyTorch Debugging Guide](https://pytorch.org/docs/stable/notes/faq.html)
- [NCCL Debugging Tips](https://docs.nvidia.com/deeplearning/nccl/user-guide/docs/troubleshooting.html)
- [Common Training Pitfalls](https://karpathy.github.io/2019/04/25/recipe/)
- [A Recipe for Training Neural Networks](https://karpathy.github.io/2019/04/25/recipe/) - Andrej Karpathy
- [Debugging Deep Learning Models](https://fullstackdeeplearning.com/course/2022/lecture-7-troubleshooting-testing/)
- [PyTorch Distributed Debugging](https://pytorch.org/tutorials/intermediate/dist_tuto.html)

---

*上一篇：[04-profiling-tools.md](04-profiling-tools.md)* | *下一篇：[06-production-observability.md](06-production-observability.md)*

[返回目录](README.md) | [返回主页](../README.md)
