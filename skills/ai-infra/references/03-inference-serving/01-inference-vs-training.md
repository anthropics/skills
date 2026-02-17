# 推理与训练的差异

> 理解推理与训练的本质区别，找到优化空间。

## 关键差异对比

| 维度 | 训练 | 推理 |
|------|------|------|
| **计算流程** | 前向 + 反向 | 仅前向 |
| **优化目标** | 高吞吐量 | 低延迟 |
| **Batch Size** | 大 (数百-数千) | 小/动态 |
| **精度** | FP16/BF16 | INT8/INT4/FP8 |
| **显存占用** | 模型+梯度+优化器+激活 | 模型+KV Cache |
| **容错性** | 允许重试 | 实时响应 |
| **硬件利用** | 算力优先 | 带宽优先 |

## 推理优化空间

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        推理优化方向                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   1. 模型压缩                                                            │
│      ├── 量化: FP16 → INT8/INT4                                        │
│      ├── 剪枝: 移除冗余权重                                              │
│      └── 蒸馏: 训练小模型                                                │
│                                                                         │
│   2. 计算优化                                                            │
│      ├── 算子融合: 减少内存访问                                          │
│      ├── KV Cache: 避免重复计算                                         │
│      └── FlashAttention: 优化 Attention                                │
│                                                                         │
│   3. 服务优化                                                            │
│      ├── Continuous Batching: 动态批处理                                │
│      ├── PagedAttention: 显存管理                                       │
│      └── Speculative Decoding: 加速生成                                 │
│                                                                         │
│   4. 系统优化                                                            │
│      ├── 推理引擎: TensorRT/ONNX Runtime                                │
│      ├── 服务框架: vLLM/TGI/Triton                                      │
│      └── 部署架构: 负载均衡/弹性伸缩                                      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## LLM 推理的特殊挑战

### 自回归生成

```
生成过程: 逐 token 生成，每次只产出一个 token

Step 1: "What" → 计算 → "is"
Step 2: "What is" → 计算 → "the"  
Step 3: "What is the" → 计算 → "capital"
...

问题: 
- 每步都要重新计算 Attention
- GPU 利用率低 (小 batch)
- 延迟累积
```

### Memory Bound

```python
# LLM 推理是 Memory Bound 的
# 计算强度 ≈ 1 FLOP/Byte (远低于 GPU 峰值)

def analyze_arithmetic_intensity():
    """LLM 推理计算强度分析"""
    # 每生成一个 token
    # 需要读取全部模型权重
    # 但只做一次矩阵向量乘
    
    params = 7e9  # 7B 模型
    bytes_per_param = 2  # FP16
    
    # 读取数据量
    read_bytes = params * bytes_per_param
    
    # 计算量 ≈ 2 × params (矩阵向量乘)
    flops = 2 * params
    
    intensity = flops / read_bytes  # ≈ 1
    
    print(f"计算强度: {intensity:.2f} FLOP/Byte")
    print("结论: Memory Bound，带宽是瓶颈")
```

---

*下一篇：[02-quantization.md](02-quantization.md) - 量化技术详解*
