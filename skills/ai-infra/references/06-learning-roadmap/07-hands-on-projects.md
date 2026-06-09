# 动手项目建议

> 通过项目实践巩固 AI Infra 知识，从入门到高级。

## 目录

- [入门级项目](#入门级项目)
- [中级项目](#中级项目)
- [高级项目](#高级项目)
- [项目执行建议](#项目执行建议)

---

## 入门级项目

| 项目 | 难度 | 时间 | 技能点 |
|------|------|------|--------|
| GPU 性能测试工具 | ⭐ | 1周 | CUDA 基础、性能分析 |
| 简单分布式训练 | ⭐⭐ | 1周 | DDP、多卡训练 |
| LLM 推理服务 | ⭐⭐ | 1周 | vLLM、API 开发 |

### 项目 1: GPU 性能测试工具

```python
# gpu_benchmark.py
import torch
import time

def benchmark_matmul(size=4096, iterations=100):
    a = torch.randn(size, size, device='cuda')
    b = torch.randn(size, size, device='cuda')
    
    # 预热
    for _ in range(10):
        c = torch.matmul(a, b)
    torch.cuda.synchronize()
    
    # 计时
    start = time.time()
    for _ in range(iterations):
        c = torch.matmul(a, b)
    torch.cuda.synchronize()
    elapsed = time.time() - start
    
    flops = 2 * size ** 3 * iterations
    tflops = flops / elapsed / 1e12
    return {'time_ms': elapsed/iterations*1000, 'tflops': tflops}

if __name__ == "__main__":
    print(f"设备: {torch.cuda.get_device_name(0)}")
    result = benchmark_matmul()
    print(f"MatMul: {result['tflops']:.2f} TFLOPS")
```

### 项目 2: 简单分布式训练

```python
# ddp_train.py
import torch
import torch.distributed as dist
from torch.nn.parallel import DistributedDataParallel as DDP
import os

def setup(rank, world_size):
    os.environ['MASTER_ADDR'] = 'localhost'
    os.environ['MASTER_PORT'] = '12355'
    dist.init_process_group("nccl", rank=rank, world_size=world_size)

def train(rank, world_size):
    setup(rank, world_size)
    model = DDP(torch.nn.Linear(100, 10).to(rank), device_ids=[rank])
    optimizer = torch.optim.SGD(model.parameters(), lr=0.01)
    
    for epoch in range(10):
        x = torch.randn(32, 100).to(rank)
        loss = torch.nn.MSELoss()(model(x), torch.randn(32, 10).to(rank))
        loss.backward()
        optimizer.step()
        optimizer.zero_grad()
        if rank == 0:
            print(f"Epoch {epoch}, Loss: {loss.item():.4f}")
    
    dist.destroy_process_group()

if __name__ == "__main__":
    torch.multiprocessing.spawn(train, args=(2,), nprocs=2)
```

### 项目 3: LLM 推理服务

```python
# llm_server.py
from fastapi import FastAPI
from vllm import LLM, SamplingParams

app = FastAPI()
llm = LLM(model="facebook/opt-125m")

@app.post("/generate")
async def generate(prompt: str, max_tokens: int = 100):
    outputs = llm.generate([prompt], SamplingParams(max_tokens=max_tokens))
    return {"generated_text": outputs[0].outputs[0].text}
```

---

## 中级项目

| 项目 | 难度 | 时间 | 技能点 |
|------|------|------|--------|
| LLM 微调 + 部署 | ⭐⭐⭐ | 2-3周 | LoRA、量化、部署 |
| 分布式训练监控 | ⭐⭐⭐ | 2周 | Prometheus、监控 |
| ML Pipeline | ⭐⭐⭐ | 2周 | MLflow、Kubeflow |

### 项目 4: LLM 微调 + 部署

**完整流程**:

```
阶段 1: 数据准备 (2天)
├── 选择数据集 (Alpaca/ShareGPT)
└── 数据格式化

阶段 2: LoRA 微调 (3天)
├── 配置 LoRA 参数
└── DeepSpeed 训练

阶段 3: 量化部署 (3天)
├── GPTQ/AWQ 量化
└── vLLM 服务部署

阶段 4: 生产化 (3天)
├── Docker 打包
├── K8s 部署
└── 监控告警
```

**LoRA 微调代码**:

```python
from peft import LoraConfig, get_peft_model
from transformers import AutoModelForCausalLM

model = AutoModelForCausalLM.from_pretrained("meta-llama/Llama-2-7b-hf")
lora_config = LoraConfig(r=16, lora_alpha=32, target_modules=["q_proj", "v_proj"])
model = get_peft_model(model, lora_config)
```

---

## 高级项目

| 项目 | 难度 | 时间 | 技能点 |
|------|------|------|--------|
| 简化版 DeepSpeed | ⭐⭐⭐⭐ | 4-6周 | ZeRO 原理 |
| LLM 推理优化 | ⭐⭐⭐⭐ | 4-6周 | KV Cache |
| GPU 集群调度器 | ⭐⭐⭐⭐⭐ | 6-8周 | K8s 调度 |

### 项目 5: 简化版 ZeRO-1

```python
# simple_zero.py
import torch.distributed as dist

class ZeRO1Optimizer:
    def __init__(self, params, optimizer_class, **kwargs):
        self.world_size = dist.get_world_size()
        self.rank = dist.get_rank()
        self.params = list(params)
        
        # 参数分片
        self.param_groups = [[] for _ in range(self.world_size)]
        for i, p in enumerate(self.params):
            self.param_groups[i % self.world_size].append(p)
        
        # 只为本地参数创建优化器状态
        self.optimizer = optimizer_class(self.param_groups[self.rank], **kwargs)
    
    def step(self):
        # AllReduce 梯度
        for p in self.params:
            if p.grad is not None:
                dist.all_reduce(p.grad)
                p.grad /= self.world_size
        
        # 本地更新
        self.optimizer.step()
        
        # Broadcast 参数
        for rank, group in enumerate(self.param_groups):
            for p in group:
                dist.broadcast(p.data, src=rank)
```

### 项目 6: 简化版 KV Cache

```python
# simple_kv_cache.py
import torch

class KVCache:
    def __init__(self, max_len, num_layers, num_heads, head_dim, device):
        self.cache = {}
        for l in range(num_layers):
            self.cache[l] = {
                'k': torch.zeros(1, num_heads, max_len, head_dim, device=device),
                'v': torch.zeros(1, num_heads, max_len, head_dim, device=device)
            }
        self.length = 0
    
    def update(self, layer, new_k, new_v):
        seq_len = new_k.shape[2]
        self.cache[layer]['k'][:,:,self.length:self.length+seq_len] = new_k
        self.cache[layer]['v'][:,:,self.length:self.length+seq_len] = new_v
        self.length += seq_len
    
    def get(self, layer):
        return self.cache[layer]['k'][:,:,:self.length], self.cache[layer]['v'][:,:,:self.length]
```

---

## 项目执行建议

### 最佳实践

1. **先跑通再优化**: 先实现最简版本
2. **版本控制**: Git 管理，记录修改
3. **文档记录**: README + 关键决策
4. **性能基准**: 量化优化效果

### 项目展示

- 清晰的 README
- 运行说明
- 性能对比数据
- 写博客总结

---

## 延伸阅读

- [面试准备指南](./08-interview-preparation.md)
- [核心技能清单](./05-core-skills.md)
- [推荐资源汇总](./06-recommended-resources.md)

---

*返回章节：[学习路线图](./README.md)*

---

## 参考资料与引用

1. **Karpathy, A.** *nanoGPT.* — 从零构建 GPT  
   https://github.com/karpathy/nanoGPT

2. **Karpathy, A.** *micrograd.* — 从零构建自动微分引擎  
   https://github.com/karpathy/micrograd

3. **LangChain.** *Build LLM Applications.*  
   https://docs.langchain.com/

4. **Kaggle.** *Machine Learning Competitions.*  
   https://www.kaggle.com/
