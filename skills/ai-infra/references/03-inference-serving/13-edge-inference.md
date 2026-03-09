# 端侧与边缘推理

> 不是所有推理都要在云端——手机、PC、IoT 上运行 AI 模型有着完全不同的技术栈。

## 目录

- [为什么需要端侧推理](#为什么需要端侧推理)
- [端侧硬件加速器](#端侧硬件加速器)
- [llama.cpp 生态](#llamacpp-生态)
- [MLC-LLM](#mlc-llm)
- [Ollama](#ollama)
- [ONNX Runtime Mobile](#onnx-runtime-mobile)
- [模型格式与转换](#模型格式与转换)
- [端侧 vs 云端决策](#端侧-vs-云端决策)

---

## 为什么需要端侧推理

```
┌─────────────────────────────────────────────────────────────┐
│              端侧推理的驱动力                                  │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  1. 隐私保护                                                 │
│     数据不出设备 → 医疗、金融、个人助手                       │
│     不需要网络连接 → 离线场景                                 │
│                                                             │
│  2. 延迟                                                     │
│     无网络往返延迟 → 实时响应                                 │
│     本地推理: ~10ms vs 云端: ~100-500ms                      │
│                                                             │
│  3. 成本                                                     │
│     无需 GPU 云服务 → 边际成本接近 0                          │
│     大规模用户场景 → 云端成本不可承受                          │
│                                                             │
│  4. 可用性                                                   │
│     无网络也能用 → 飞机、偏远地区                             │
│     不依赖服务器 → 去中心化                                  │
│                                                             │
│  典型场景:                                                   │
│  - Apple Intelligence (iPhone 上运行 3B 模型)                │
│  - Windows Copilot (NPU 加速本地推理)                       │
│  - 智能家居 (离线语音助手)                                   │
│  - 自动驾驶 (实时决策不能依赖网络)                           │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 端侧硬件加速器

```
┌─────────────────────────────────────────────────────────────┐
│              端侧 AI 芯片生态                                  │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  手机平台:                                                   │
│  ┌────────────┬──────────────┬────────────────┐             │
│  │ 厂商       │ AI 加速器     │ 算力 (TOPS)    │             │
│  ├────────────┼──────────────┼────────────────┤             │
│  │ Apple      │ Neural Engine│ ~35 TOPS (A17) │             │
│  │ Qualcomm   │ Hexagon NPU  │ ~45 TOPS (8Gen3)│            │
│  │ MediaTek   │ APU          │ ~35 TOPS       │             │
│  │ Google     │ Tensor TPU   │ ~10 TOPS       │             │
│  └────────────┴──────────────┴────────────────┘             │
│                                                             │
│  PC 平台:                                                    │
│  ┌────────────┬──────────────┬────────────────┐             │
│  │ Intel      │ NPU (Meteor L)│ ~34 TOPS      │             │
│  │ Qualcomm   │ Hexagon NPU  │ ~45 TOPS (X E) │             │
│  │ AMD        │ XDNA NPU     │ ~39 TOPS       │             │
│  │ Apple      │ Neural Engine│ ~38 TOPS (M4)  │             │
│  │ NVIDIA     │ RTX GPU      │ ~200+ TOPS     │             │
│  └────────────┴──────────────┴────────────────┘             │
│                                                             │
│  嵌入式/IoT:                                                 │
│  ┌────────────┬──────────────┬────────────────┐             │
│  │ NVIDIA     │ Jetson Orin  │ 275 TOPS       │             │
│  │ Google     │ Coral TPU    │ 4 TOPS         │             │
│  │ Intel      │ Movidius     │ 1 TOPS         │             │
│  │ RPi        │ Hailo-8     │ 26 TOPS        │             │
│  └────────────┴──────────────┴────────────────┘             │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## llama.cpp 生态

### 概述

```
llama.cpp: C/C++ 实现的 LLM 推理引擎
  创始人: Georgi Gerganov
  目标: 在消费级硬件上高效运行 LLM
  
  核心特性:
  ✅ 纯 C/C++，无 Python 依赖
  ✅ CPU 推理 (AVX2/ARM NEON)
  ✅ Metal GPU (Mac)
  ✅ CUDA GPU
  ✅ Vulkan GPU (跨平台)
  ✅ GGUF 模型格式 (紧凑高效)
  ✅ 2-8 bit 量化 (Q2_K 到 Q8_0)
  ✅ Android/iOS 移动端
  
  生态:
  - llama.cpp: 核心引擎
  - GGUF: 模型格式
  - llama-server: HTTP API 服务
  - Ollama: 基于 llama.cpp 的用户友好工具
  - LM Studio: GUI 客户端
  - Jan: 开源 AI 桌面应用
```

### GGUF 量化格式

| 量化类型 | 位宽 | 7B 模型大小 | 质量损失 | 推荐场景 |
|---------|------|-----------|---------|---------|
| F16 | 16-bit | 13.5 GB | 无 | 基准参考 |
| Q8_0 | 8-bit | 7.2 GB | 极小 | 有足够内存时 |
| Q6_K | 6-bit | 5.5 GB | 很小 | 质量优先 |
| Q5_K_M | 5-bit | 4.8 GB | 小 | 推荐平衡 |
| Q4_K_M | 4-bit | 4.1 GB | 较小 | 最常用 |
| Q3_K_M | 3-bit | 3.3 GB | 中等 | 内存紧张 |
| Q2_K | 2-bit | 2.7 GB | 明显 | 极端场景 |

```bash
# llama.cpp 使用示例

# 编译
git clone https://github.com/ggerganov/llama.cpp
cd llama.cpp
make -j$(nproc) GGML_CUDA=1  # CUDA GPU 支持
# make GGML_METAL=1  # Mac Metal 支持

# 下载 GGUF 模型
# 从 HuggingFace 下载量化版本
# https://huggingface.co/TheBloke/Llama-2-7B-GGUF

# 推理
./llama-cli \
    -m models/llama-3-8b-q4_k_m.gguf \
    -p "Explain quantum computing in simple terms:" \
    -n 256 \
    --temp 0.7 \
    -ngl 35  # GPU 层数 (全部放 GPU)

# 启动 API 服务
./llama-server \
    -m models/llama-3-8b-q4_k_m.gguf \
    --host 0.0.0.0 \
    --port 8080 \
    -ngl 35 \
    -c 4096  # 上下文长度

# 量化模型
./llama-quantize \
    models/llama-3-8b-f16.gguf \
    models/llama-3-8b-q4_k_m.gguf \
    Q4_K_M
```

### 各平台性能参考

```
Llama-3-8B Q4_K_M 推理性能 (tokens/s):

  GPU 推理:
    RTX 4090 (24GB)    : ~120 tok/s
    RTX 4060 (8GB)     : ~45 tok/s
    Mac M3 Max (40GB)  : ~35 tok/s
    Mac M2 Pro (16GB)  : ~20 tok/s

  CPU 推理:
    Ryzen 9 7950X      : ~15 tok/s
    Apple M3           : ~12 tok/s
    Intel i7-13700     : ~10 tok/s

  移动端:
    iPhone 15 Pro      : ~8 tok/s (ANE)
    Snapdragon 8 Gen 3 : ~6 tok/s

  注意: 实际性能取决于量化类型、上下文长度、batch size
```

---

## MLC-LLM

```
MLC-LLM: Machine Learning Compilation for LLMs
  来自 TVM 社区 (陈天奇团队)
  
  核心思想: 通过编译器优化，让 LLM 在任意硬件上高效运行
  
  支持的后端:
  - CUDA (NVIDIA GPU)
  - Metal (Apple GPU)  
  - Vulkan (跨平台 GPU)
  - OpenCL (移动 GPU)
  - WebGPU (浏览器！)
  
  vs llama.cpp:
  ┌─────────────┬──────────────┬──────────────┐
  │             │ llama.cpp    │ MLC-LLM      │
  ├─────────────┼──────────────┼──────────────┤
  │ 语言        │ C/C++        │ Python/C++   │
  │ 优化方式    │ 手写算子     │ 编译器自动优化│
  │ 模型支持    │ GGUF 格式    │ 多种格式     │
  │ 浏览器运行  │ WASM (慢)    │ WebGPU (快)  │
  │ 生态成熟度  │ ★★★★★       │ ★★★☆☆       │
  │ 性能        │ 非常好       │ 优秀         │
  └─────────────┴──────────────┴──────────────┘
```

---

## Ollama

```
Ollama: 最简单的本地 LLM 运行工具
  
  一行命令运行任何模型:
    $ ollama run llama3:8b
    $ ollama run qwen2:7b
    $ ollama run phi3:mini
  
  特性:
  - 基于 llama.cpp 构建
  - Docker 风格的模型管理 (pull/run/list)
  - 内置 REST API (兼容 OpenAI)
  - 自动选择最优量化版本
  - 支持 macOS / Linux / Windows
  - GPU 自动检测和加速
  
  架构:
    Ollama CLI → Ollama Server → llama.cpp → GPU/CPU
                      │
                  Model Registry (ollama.com)
```

```bash
# Ollama 使用示例

# 安装
curl -fsSL https://ollama.com/install.sh | sh

# 运行模型
ollama run llama3:8b  # 自动下载 + 运行

# 对话
>>> What is machine learning?
Machine learning is a subset of artificial intelligence...

# API 调用 (兼容 OpenAI)
curl http://localhost:11434/v1/chat/completions \
  -H "Content-Type: application/json" \
  -d '{
    "model": "llama3:8b",
    "messages": [{"role": "user", "content": "Hello"}]
  }'

# 查看已下载模型
ollama list

# 自定义模型 (Modelfile)
cat << 'EOF' > Modelfile
FROM llama3:8b
SYSTEM "You are a helpful coding assistant."
PARAMETER temperature 0.3
PARAMETER num_ctx 4096
EOF
ollama create my-coder -f Modelfile
ollama run my-coder
```

---

## ONNX Runtime Mobile

```
ONNX Runtime: 微软的跨平台推理引擎

  桌面/服务器版本:
    支持所有 ONNX 模型
    CPU/CUDA/TensorRT/DirectML/OpenVINO
    
  Mobile 版本 (ONNX Runtime Mobile):
    针对移动端优化的轻量版本
    支持 Android (ARM/x86) 和 iOS
    ONNX → ORT 格式 (更小更快)
    NNAPI (Android) / CoreML (iOS) 硬件加速
    
  适用场景:
    - 非 LLM 模型 (分类、检测、分割)
    - 小型语言模型 (< 1B 参数)
    - 需要跨平台部署的应用
    
  LLM 场景:
    ONNX Runtime GenAI 扩展支持 LLM
    支持量化 (INT4/INT8)
    支持 DirectML (Windows GPU)
```

---

## 模型格式与转换

```
┌─────────────────────────────────────────────────────────────┐
│              端侧模型格式选择                                  │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  格式        引擎           适用平台      量化支持            │
│  ──────     ──────         ──────────   ────────            │
│  GGUF       llama.cpp      全平台       Q2-Q8, FP16        │
│  ONNX       ONNX Runtime   全平台       INT4/INT8/FP16     │
│  MLC        MLC-LLM        全平台+Web   多种量化             │
│  TFLite     TensorFlow     Android/iOS  INT8/FP16          │
│  CoreML     Core ML        Apple only   INT4-FP16          │
│  TensorRT   TensorRT       NVIDIA GPU   INT4-FP16          │
│                                                             │
│  转换工具:                                                   │
│  HuggingFace → GGUF:  llama.cpp/convert_hf_to_gguf.py     │
│  HuggingFace → ONNX:  optimum-cli export onnx             │
│  ONNX → TensorRT:     trtexec --onnx=model.onnx            │
│  HuggingFace → CoreML: coremltools                         │
│                                                             │
│  推荐:                                                       │
│  LLM 通用 → GGUF (生态最好)                                 │
│  非 LLM → ONNX (兼容性最好)                                 │
│  浏览器 → MLC-LLM WebGPU                                    │
│  Apple 设备 → CoreML                                        │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 端侧 vs 云端决策

```
端侧推理 vs 云端推理 决策树:

├── 模型大小
│   ├── > 30B 参数 → 云端 (端侧内存不够)
│   ├── 7B-30B    → 看设备 (高端 PC/Mac 可跑)
│   └── < 7B      → 端侧可行
│
├── 隐私要求
│   ├── 数据不能出设备 → 端侧
│   └── 数据可以上云   → 取决于其他因素
│
├── 延迟要求
│   ├── < 50ms → 端侧 (无网络延迟)
│   └── > 100ms 可接受 → 云端也行
│
├── 并发量
│   ├── 百万用户 → 混合 (端侧为主，降低成本)
│   └── 少量用户 → 云端 (性价比更高)
│
├── 质量要求
│   ├── 需要最强模型 → 云端 (跑 405B)
│   └── 够用就好 → 端侧 (7B 已经很好)
│
└── 混合方案
    小任务 → 端侧小模型 (快速响应)
    复杂任务 → 路由到云端大模型
    离线 → 端侧兜底
```

---

## 小结

```
端侧推理核心要点:

1. llama.cpp + GGUF 是端侧 LLM 的事实标准
   跨平台、高效、量化灵活
   Ollama/LM Studio 让使用门槛极低

2. 量化是端侧的核心技术
   Q4_K_M 是最常用的平衡点
   7B Q4 ≈ 4GB，大多数设备可运行

3. 端侧性能在快速提升
   NPU 算力每代翻倍
   iPhone/Mac 已能流畅运行 7B 模型

4. 端侧和云端不是非此即彼
   混合方案: 端侧处理简单请求
   复杂任务路由到云端
   → 最佳用户体验 + 最低成本
```

---

*返回：[README.md](README.md) - 章节索引*
