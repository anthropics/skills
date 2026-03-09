# 多模态推理

> 文本之外的 AI 世界——图像、视频、音频模型的推理有着独特的基础设施挑战。

## 目录

- [多模态推理的特殊性](#多模态推理的特殊性)
- [视觉语言模型推理](#视觉语言模型推理)
- [扩散模型推理](#扩散模型推理)
- [语音模型推理](#语音模型推理)
- [多模态服务架构](#多模态服务架构)
- [性能优化](#性能优化)

---

## 多模态推理的特殊性

### 与纯文本推理的区别

```
┌─────────────────────────────────────────────────────────────┐
│            多模态 vs 纯文本推理差异                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  纯文本 LLM:                                                │
│    输入: token IDs → Embedding → Transformer → 输出 token   │
│    瓶颈: KV Cache 显存 + 自回归解码延迟                      │
│                                                             │
│  视觉语言模型 (VLM):                                        │
│    输入: 图像 → Vision Encoder → 投影层 → LLM Backbone       │
│          + 文本 token                                        │
│    瓶颈: 图像编码 + 大量视觉 token 的 KV Cache               │
│    特殊: 一张图片 = 576-2880 个 token！                      │
│                                                             │
│  扩散模型 (Stable Diffusion / Flux):                         │
│    输入: 文本 → Text Encoder → UNet/DiT 去噪 → 图像         │
│    瓶颈: 迭代去噪 (20-50 步)，每步都是完整前向传播           │
│    特殊: 无自回归，是迭代过程                                 │
│                                                             │
│  语音模型 (Whisper / TTS):                                   │
│    输入: 音频波形 → Mel 频谱 → Encoder → Decoder             │
│    瓶颈: 实时性要求 (流式处理)                               │
│    特殊: 需要流式输入/输出                                   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 视觉语言模型推理

### VLM 架构

```
┌─────────────────────────────────────────────────────────────┐
│              VLM 推理流程 (以 LLaVA 为例)                     │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  输入图像 (224×224)                                          │
│       │                                                     │
│  ┌────▼────────────────────┐                                │
│  │   Vision Encoder        │  ← CLIP ViT-L/14              │
│  │   (ViT, 固定/可训练)    │     ~300M 参数                  │
│  └────┬────────────────────┘                                │
│       │ 576 个视觉 token                                    │
│  ┌────▼────────────────────┐                                │
│  │   Projection Layer      │  ← MLP 投影                    │
│  │   (Visual → Text space) │                                │
│  └────┬────────────────────┘                                │
│       │                                                     │
│  ┌────▼────────────────────┐                                │
│  │   LLM Backbone          │  ← Llama-3-8B/70B 等          │
│  │   [vision tokens]       │                                │
│  │   [text tokens]         │                                │
│  │   → 生成回复            │                                │
│  └─────────────────────────┘                                │
│                                                             │
│  显存占用:                                                   │
│    Vision Encoder: ~1.2 GB                                  │
│    LLM: 8B FP16 = ~16 GB                                    │
│    KV Cache (含 576 视觉 token): 比纯文本大 30-50%          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### VLM 推理优化

```
VLM 特有的优化方向:

1. 视觉 Token 压缩
   576 个视觉 token 太多 → 降低分辨率 / Token 合并
   LLaVA-NeXT: 动态分辨率，只在需要时用高分辨率
   FastV: 在 LLM 层中逐步丢弃不重要的视觉 token

2. 图像缓存
   同一图像多次查询时，Vision Encoder 结果可缓存
   类似 Prefix Caching，但在视觉特征层面

3. 视觉编码器量化
   Vision Encoder 对量化不太敏感
   INT8 量化几乎无精度损失

4. 批处理策略
   图像大小不同 → 需要 padding 或动态 batch
   视觉编码和文本生成可以流水线化
```

### vLLM 中使用 VLM

```python
from vllm import LLM, SamplingParams
from vllm.multimodal.utils import fetch_image

# vLLM 原生支持 VLM
llm = LLM(
    model="llava-hf/llava-v1.6-mistral-7b-hf",
    max_model_len=4096,
)

# 带图像的推理
image = fetch_image("https://example.com/cat.jpg")
prompt = "<image>\nDescribe this image in detail."

output = llm.generate({
    "prompt": prompt,
    "multi_modal_data": {"image": image},
}, SamplingParams(max_tokens=256))
```

---

## 扩散模型推理

### 扩散模型推理流程

```
┌─────────────────────────────────────────────────────────────┐
│            扩散模型推理流程 (Stable Diffusion XL)              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  "A cat sitting on a mat, oil painting style"               │
│       │                                                     │
│  ┌────▼────────────┐                                        │
│  │ Text Encoder    │  CLIP + T5 (编码文本描述)               │
│  │ (~1GB)          │                                        │
│  └────┬────────────┘                                        │
│       │ text embeddings                                     │
│  ┌────▼────────────┐                                        │
│  │ Noise           │  随机噪声 (latent space)                │
│  │ z_T             │  64×64×4 (latent)                       │
│  └────┬────────────┘                                        │
│       │                                                     │
│  ┌────▼────────────┐                                        │
│  │ UNet/DiT        │  ← 核心: 迭代去噪                      │
│  │ (~3-6GB)        │     20-50 步，每步完整前向传播           │
│  │ Step 1→2→...→50 │     条件: text embeddings               │
│  └────┬────────────┘                                        │
│       │ z_0 (去噪后的 latent)                                │
│  ┌────▼────────────┐                                        │
│  │ VAE Decoder     │  latent → 像素图像                      │
│  │ (~0.3GB)        │  64×64×4 → 1024×1024×3                 │
│  └────┬────────────┘                                        │
│       │                                                     │
│  最终图像 (1024×1024)                                        │
│                                                             │
│  耗时分布:                                                   │
│    Text Encoder: ~50ms (5%)                                  │
│    UNet 迭代:    ~900ms (90%)  ← 瓶颈                       │
│    VAE Decode:   ~50ms (5%)                                  │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 扩散模型优化技术

| 技术 | 加速比 | 原理 |
|------|--------|------|
| **减少步数** (DDIM/DPM++) | 2-5× | 50 步 → 10-20 步 |
| **Latent Consistency Model** | 10-50× | 1-4 步生成 |
| **TensorRT 加速** | 1.5-2× | 算子融合、FP16 |
| **Batch 处理** | N× | 多请求并行生成 |
| **Flash Attention** | 1.2-1.5× | 注意力计算优化 |
| **Token Merging (ToMe)** | 1.3-2× | 合并相似 token |
| **模型蒸馏** | 2-10× | SDXL Turbo / LCM |

```python
# 使用 diffusers + TensorRT 优化
from diffusers import StableDiffusionXLPipeline
import torch

# 基础使用
pipe = StableDiffusionXLPipeline.from_pretrained(
    "stabilityai/stable-diffusion-xl-base-1.0",
    torch_dtype=torch.float16,
    variant="fp16",
).to("cuda")

# 启用优化
pipe.enable_xformers_memory_efficient_attention()  # 内存高效注意力

# 使用更少步数的调度器
from diffusers import DPMSolverMultistepScheduler
pipe.scheduler = DPMSolverMultistepScheduler.from_config(
    pipe.scheduler.config
)

image = pipe(
    "A cat sitting on a mat, oil painting",
    num_inference_steps=20,  # 减少到 20 步
    guidance_scale=7.5,
).images[0]
```

---

## 语音模型推理

### 语音模型类型

```
语音 AI 推理场景:

  ASR (语音识别): 语音 → 文本
    代表: Whisper, Conformer
    特点: 实时性要求高 (流式)，计算量中等

  TTS (语音合成): 文本 → 语音
    代表: VITS, ChatTTS, F5-TTS
    特点: 生成质量要求高，延迟敏感

  语音对话: 语音 → 语音
    代表: GPT-4o Voice, Moshi
    特点: 端到端，超低延迟 (<500ms)

推理优化重点:
  - 流式处理: 边接收边处理，降低端到端延迟
  - 实时性: 处理速度 > 1× 实时
  - 量化: Whisper INT8 几乎无精度损失
```

---

## 多模态服务架构

```
┌─────────────────────────────────────────────────────────────┐
│              多模态推理服务架构                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  方案 1: 统一模型服务 (VLM/多模态 LLM)                       │
│    客户端 → API Gateway → vLLM (VLM) → 响应                 │
│    优点: 简单，端到端                                        │
│    适用: LLaVA, Qwen-VL 等 VLM                              │
│                                                             │
│  方案 2: 管线式服务 (Pipeline)                               │
│    客户端 → 图像预处理服务 → CLIP 编码服务 → LLM 服务        │
│    优点: 各组件独立扩缩容，灵活                               │
│    缺点: 延迟增加，架构复杂                                   │
│    适用: 复杂多模态应用                                       │
│                                                             │
│  方案 3: 异构推理 (Triton)                                   │
│    ┌─────────────────────────────┐                          │
│    │        Triton Server         │                          │
│    │  ┌──────┐ ┌──────┐ ┌──────┐ │                          │
│    │  │CLIP  │→│Project│→│ LLM  │ │                          │
│    │  │(GPU) │ │(GPU)  │ │(GPU) │ │                          │
│    │  └──────┘ └──────┘ └──────┘ │                          │
│    │     Ensemble Pipeline       │                          │
│    └─────────────────────────────┘                          │
│    优点: 统一管理，高效调度                                   │
│    适用: 企业级多模态部署                                     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 性能优化

### 多模态推理优化清单

```
1. 图像/视频预处理
   □ 图像 resize 在 CPU/GPU 上加速
   □ 视频解码使用硬件加速 (NVDEC)
   □ 批量处理同尺寸图像

2. Vision Encoder
   □ INT8 量化 (精度损失小)
   □ 输出缓存 (相同图像复用)
   □ Flash Attention

3. LLM 部分
   □ 与纯文本 LLM 相同的优化
   □ 注意视觉 token 对 KV Cache 的额外开销

4. 扩散模型
   □ 减少推理步数 (DPM++ / LCM)
   □ TensorRT 加速 UNet
   □ 半精度 (FP16) 运算
   □ Classifier-Free Guidance 优化
```

---

## 小结

```
多模态推理核心要点:

1. 每种模态有独特的推理特性
   VLM: 视觉 token 膨胀 KV Cache
   扩散模型: 迭代去噪是瓶颈
   语音: 流式处理和实时性

2. VLM 推理 ≈ 文本 LLM + 视觉编码器
   主要瓶颈仍在 LLM 部分
   vLLM 已原生支持多种 VLM

3. 扩散模型优化空间大
   减少步数 + TensorRT + 蒸馏
   可以从 10s 优化到 <1s

4. 架构选择看复杂度
   简单: 端到端 VLM 服务
   复杂: Pipeline / Triton Ensemble
```

---

*返回：[README.md](README.md) - 章节索引*
