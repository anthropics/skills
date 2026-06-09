# 激活函数深入讲解：从 ReLU 到现代变体

> 激活函数是神经网络的"开关"。本文从 ReLU 出发，深入讲解各类激活函数的原理、数学、优缺点和实际选型，帮你建立扎实的理解。

## 目录

- [为什么需要激活函数（快速回顾）](#为什么需要激活函数快速回顾)
- [Sigmoid 和 Tanh：早期的选择](#sigmoid-和-tanh早期的选择)
- [ReLU：一场革命](#relu一场革命)
- [ReLU 的致命缺陷：Dead Neuron 问题](#relu-的致命缺陷dead-neuron-问题)
- [ReLU 变体家族](#relu-变体家族)
- [GELU 和 SiLU/Swish：现代 LLM 的标配](#gelu-和-siluswish现代-llm-的标配)
- [SwiGLU：LLaMA 的秘密武器](#swiglu-llama-的秘密武器)
- [激活函数的梯度对比](#激活函数的梯度对比)
- [实际选型指南](#实际选型指南)
- [PyTorch 代码实战](#pytorch-代码实战)
- [总结](#总结)

---

## 为什么需要激活函数（快速回顾）

> 详细讲解见 [02-什么是神经网络](02-neural-network-basics.md) 的"激活函数"章节。

### 一句话回顾

**没有激活函数，100 层网络 = 1 层网络。激活函数引入非线性，让网络能拟合任意复杂函数。**

```
没有激活函数:
    第1层: h₁ = W₁x + b₁
    第2层: h₂ = W₂h₁ + b₂ = W₂(W₁x + b₁) + b₂ = W₂W₁x + (W₂b₁ + b₂) = W'x + b'
    → 等价于一层！无论叠多少层都是线性变换

有激活函数:
    第1层: h₁ = f(W₁x + b₁)      ← 非线性折叠
    第2层: h₂ = f(W₂h₁ + b₂)     ← 再次折叠
    → 每层都引入"弯折"，网络能表达任意复杂的曲面
```

### 直觉类比

```
类比: 折纸

    线性变换 = 只能拉伸和旋转纸张
    → 纸还是平的，无论怎么拉都无法做成纸飞机

    激活函数 = 可以折叠纸张
    → 一次折叠 = 一层激活
    → 多次折叠 = 深层网络
    → 足够多的折叠可以折出任何形状（飞机、鹤、玫瑰...）

    这就是为什么"深度"学习需要激活函数——
    每一层的激活函数就是一次"折叠"
```

---

## Sigmoid 和 Tanh：早期的选择

### Sigmoid

```
Sigmoid(x) = 1 / (1 + e⁻ˣ)

输出范围: (0, 1)

图形:
     1.0 ─────────────────────────╱─────
                                ╱
     0.5 ─ ─ ─ ─ ─ ─ ─ ─ ─ ─╱─ ─ ─ ─
                            ╱
     0.0 ─────────────────╱──────────────
                        ↑
                   x=0 时输出 0.5

导数:
    σ'(x) = σ(x) × (1 - σ(x))
    最大值在 x=0: σ'(0) = 0.25      ← 注意！最大才 0.25！

特点:
    ✓ 输出在 (0,1)，适合表示概率
    ✗ 导数最大只有 0.25 → 反向传播时梯度越乘越小 → 梯度消失！
    ✗ 输出不是零中心的 → 梯度更新方向受限
    ✗ 指数运算 e⁻ˣ 计算量相对大
```

### Tanh

```
Tanh(x) = (eˣ - e⁻ˣ) / (eˣ + e⁻ˣ)

输出范围: (-1, 1)      ← 比 Sigmoid 好！零中心

图形:
     1.0 ─────────────────────────╱─────
                                ╱
     0.0 ─ ─ ─ ─ ─ ─ ─ ─ ─ ╱─ ─ ─ ─
                          ╱
    -1.0 ───────────────╱──────────────

导数:
    tanh'(x) = 1 - tanh²(x)
    最大值在 x=0: tanh'(0) = 1.0    ← 比 Sigmoid 好

特点:
    ✓ 输出零中心 → 梯度更新更对称
    ✓ 导数最大为 1 → 比 Sigmoid 更不容易梯度消失
    ✗ 两端仍然饱和（x 很大或很小时导数趋近 0）
    ✗ 仍然有梯度消失问题，只是比 Sigmoid 轻一些
```

### 为什么 Sigmoid/Tanh 被淘汰了？

```
核心问题: 梯度消失 (Vanishing Gradient)

    Sigmoid 导数最大 0.25，假设一个 10 层网络:
    梯度要经过 10 层传播:
    0.25 × 0.25 × ... × 0.25 (10次)
    = 0.25¹⁰
    ≈ 0.00000095

    → 第一层的梯度几乎为 0 → 学不动了！

类比: 传话游戏
    "苹果" → 第1人: "苹果" → 第2人: "苹..果" → ... → 第10人: "？？？"
    每传一次信息衰减一点，最终信号消失

    Sigmoid 就像一个"衰减器"，每层都把信号缩小到原来的 1/4 以下
    层数越深，前面的层越收不到有效的反馈

    → 2010年代之前，深度网络很难训练
    → ReLU 的出现彻底改变了这个局面
```

---

## ReLU：一场革命

### 定义与直觉

```
ReLU(x) = max(0, x)

    x < 0 → 输出 0
    x ≥ 0 → 输出 x（原样传递）

就这么简单。没有指数运算，没有除法，只有一个 max 比较。
```

### 图形

```
输出
  │         ╱
  │        ╱
  │       ╱   斜率 = 1（正区域，梯度恒为1）
  │      ╱
  │     ╱
  │    ╱
  │   ╱
──┼──╱────────── 输入
  │(全是0)
  │  斜率 = 0（负区域，梯度为0）
  │
```

### 导数

```
ReLU'(x) = { 1,  if x > 0
           { 0,  if x < 0
           { 未定义, if x = 0  (实践中取 0)

对比 Sigmoid:
    Sigmoid'(x) 最大 = 0.25   → 每层梯度缩小到 1/4
    ReLU'(x)    最大 = 1.0    → 正区域梯度完整传递！

    10 层网络:
    Sigmoid: 0.25¹⁰ ≈ 0.00000095 → 梯度消失
    ReLU:    1.0¹⁰  = 1.0         → 梯度完整保留！
```

### 为什么 ReLU 是一场革命

```
时间线:

    2010年之前: 大家用 Sigmoid/Tanh，深度网络很难训练
    
    2010年: Nair & Hinton 论文首次在 RBM 中使用 ReLU
    
    2012年: AlexNet 使用 ReLU → ImageNet 比赛碾压对手
            → 训练速度比 Tanh 快 6 倍！
            → 深度学习的"大爆炸"开始了
    
    此后: ReLU 成为默认选择，开启了深度学习黄金十年

ReLU 的三大优势:

┌─────────────────────────────────────────────────────────────┐
│                                                              │
│  1. 缓解梯度消失                                             │
│     正区域导数恒为 1 → 梯度可以无损传递到很深的层             │
│     → 使得 100+ 层的深度网络成为可能                         │
│                                                              │
│  2. 计算极其简单                                             │
│     max(0, x) → 一次比较操作                                 │
│     对比 Sigmoid: e⁻ˣ 需要指数运算 → 慢得多                 │
│     GPU 上: ReLU 比 Sigmoid 快约 6 倍                        │
│                                                              │
│  3. 稀疏激活                                                 │
│     大约 50% 的神经元输出为 0（没有激活）                    │
│     → 稀疏表示 → 更高效、更不容易过拟合                     │
│     类比: 不是所有专家都需要对每个问题发言                    │
│           只有相关的专家才"激活"                              │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### ReLU 的数值计算示例

```
完整的前向+反向传播中 ReLU 的角色:

前向传播:
    线性变换: z = W × x + b
    激活:     h = ReLU(z)

    假设 z = [2.5, -1.3, 0.8, -0.4, 3.1]

    h = ReLU(z) = [2.5, 0.0, 0.8, 0.0, 3.1]
                        ↑         ↑
                    负数变0     负数变0

    → 2个神经元"死了"（没激活），3个"活着"

反向传播:
    假设 ∂L/∂h = [0.3, -0.5, 0.1, 0.7, -0.2]   ← 上游传来的梯度

    ∂L/∂z = ∂L/∂h × ReLU'(z)
           = [0.3, -0.5, 0.1, 0.7, -0.2] × [1, 0, 1, 0, 1]
           = [0.3, 0.0, 0.1, 0.0, -0.2]
                   ↑         ↑
              梯度被阻断   梯度被阻断

    → 没激活的神经元：梯度直接为 0，权重不更新
    → 激活的神经元：梯度完整传递，权重正常更新

    这就是 ReLU 的"开关"特性: 要么全通(梯度=1)，要么全断(梯度=0)
```

---

## ReLU 的致命缺陷：Dead Neuron 问题

### 什么是 Dead Neuron

```
问题: 如果一个神经元的输入 z 始终 < 0，它就永远输出 0

    ReLU(z) = 0   for all z < 0
    ReLU'(z) = 0  for all z < 0

    → 输出是 0 → 梯度也是 0 → 权重无法更新 → 永远输出 0
    → 这个神经元"死了"，永远不会再复活！

类比: 被解雇的员工
    一个员工犯了个错（权重更新到了不好的值），被开除了（永远输出0）
    但公司没有"复职"机制 → 这个位置永远空着
    如果太多员工被开除 → 公司运转不了了！
```

### Dead Neuron 是怎么发生的

```
场景 1: 学习率太大

    权重更新: w_new = w_old - lr × gradient
    
    如果 lr 太大，某次更新把权重甩到很负的值:
    
    更新前: w = 0.5   → z = wx + b 可能为正 → ReLU 激活
    更新后: w = -10.0  → z = wx + b 几乎永远为负 → ReLU 输出 0
    
    → 梯度 = 0 → w 再也不更新 → 神经元永远死亡

场景 2: 偏置初始化不当

    如果 b 被初始化为很大的负数:
    z = Wx + b
    → 即使 Wx 为正，加上很负的 b 后，z 仍然为负
    → ReLU 从一开始就不激活 → 神经元从未活过

场景 3: 异常数据/梯度

    某个异常大的梯度导致权重剧烈变化
    → 神经元突然"翻转"到负区域 → 永远死亡
```

### Dead Neuron 的严重程度

```
实验观察:

    典型深度网络训练中:
    ├── 训练初期: ~10-20% 的 ReLU 神经元可能死亡
    ├── 训练中期: 死亡率可能上升到 30-50%
    └── 极端情况: 某些层 90%+ 的神经元死亡 → 网络几乎失效

    影响:
    ├── 网络有效容量下降（参数在那里，但不起作用）
    ├── 模型表达能力变弱
    └── 梯度信息丢失，训练变慢甚至停滞

检测方法:
    在训练过程中监控每层的激活值:
    如果某个神经元在所有样本上输出都为 0 → 它死了

    dead_ratio = (activations == 0).all(dim=0).float().mean()
    如果 dead_ratio > 0.3 → 需要注意了！
```

### 缓解 Dead Neuron 的方法

```
┌──────────────────────────────────────────────────────────────┐
│  缓解 ReLU Dead Neuron 的五种方法                              │
│                                                               │
│  1. 降低学习率                                                │
│     避免权重被一次更新甩到负区域                              │
│     但学习率太小 → 训练太慢 → 需要权衡                       │
│                                                               │
│  2. 合理的权重初始化                                          │
│     He 初始化 (专门为 ReLU 设计):                             │
│     W ~ N(0, √(2/n_in))                                      │
│     保证初始状态下约 50% 神经元激活                           │
│                                                               │
│  3. 使用 Batch Normalization                                  │
│     在 ReLU 之前对输入做归一化                                │
│     让 z 的分布在 0 附近 → 约一半正一半负 → 减少死亡概率     │
│                                                               │
│  4. 使用 ReLU 变体 (Leaky ReLU, PReLU, ELU)                  │
│     负区域不完全为 0 → 根本上消除 Dead Neuron 问题            │
│     → 详见下一节                                              │
│                                                               │
│  5. 使用 GELU/SiLU                                            │
│     现代激活函数，负区域有微小输出 → 不会完全死亡             │
│     → 详见后续章节                                             │
│                                                               │
└──────────────────────────────────────────────────────────────┘
```

---

## ReLU 变体家族

### Leaky ReLU

```
Leaky ReLU(x) = { x,       if x ≥ 0
                { αx,      if x < 0      (α 通常 = 0.01)

图形:
输出
  │         ╱
  │        ╱
  │       ╱  斜率 = 1
  │      ╱
  │     ╱
  │    ╱
  │   ╱
──┼──╱────────── 输入
  │╱  斜率 = 0.01（不是0！有微小斜率）
  ╱
 ╱│

导数:
    Leaky ReLU'(x) = { 1,   if x > 0
                     { α,   if x < 0

核心改进:
    ✓ 负区域斜率 = 0.01（不是 0）→ 梯度不为 0 → 神经元不会死！
    ✓ 计算同样简单
    ✗ α = 0.01 是人为设定的，不一定最优

数值示例:
    z = [2.5, -1.3, 0.8, -0.4, 3.1]

    ReLU:        [2.5, 0.0,    0.8, 0.0,    3.1]   ← 两个信号完全丢失
    Leaky ReLU:  [2.5, -0.013, 0.8, -0.004, 3.1]   ← 负信号保留了微弱痕迹
```

### PReLU (Parametric ReLU)

```
PReLU(x) = { x,       if x ≥ 0
           { αx,      if x < 0      (α 是可学习的参数！)

与 Leaky ReLU 的唯一区别:
    Leaky ReLU: α = 0.01 (固定)
    PReLU:      α 是参数，通过反向传播学习最优值

    → 网络自己决定负区域的斜率应该是多少
    → 不同层、不同通道可以有不同的 α

    代价: 多了一点点参数（每个通道一个 α）
          7B 模型可能多 ~几十万个参数 → 忽略不计

论文: He et al., 2015 "Delving Deep into Rectifiers"
    → 同一篇论文还提出了 He 初始化（Kaiming Init）
    → 在 ImageNet 上首次超越人类水平
```

### ELU (Exponential Linear Unit)

```
ELU(x) = { x,              if x ≥ 0
         { α(eˣ - 1),      if x < 0      (α 通常 = 1.0)

图形:
输出
  │         ╱
  │        ╱
  │       ╱  斜率 = 1
  │      ╱
  │     ╱
  │    ╱
  │   ╱
──┼──╱────────── 输入
  │╱  平滑的曲线（不是直线！）
  ╱
-α ─────          渐近线: 输出最小值为 -α

特点:
    ✓ 负区域输出趋向 -α（不是 0）→ 不会死
    ✓ 在 x=0 处连续且光滑（导数连续）
    ✓ 负区域均值更接近 0 → 加速收敛
    ✗ 指数运算 eˣ → 计算比 ReLU/Leaky ReLU 慢
    ✗ 实际性能提升不够大，性价比不高
```

### SELU (Scaled ELU)

```
SELU(x) = λ × { x,              if x ≥ 0
              { α(eˣ - 1),      if x < 0

    λ ≈ 1.0507,  α ≈ 1.6733  (精确计算得出)

特殊能力:
    "自归一化" (Self-Normalizing)
    在特定条件下，输出的均值和方差会自动收敛到 (0, 1)
    → 理论上不需要 Batch Normalization

条件 (很苛刻):
    - 全连接网络（不适用于 CNN、Transformer）
    - 使用特定的 LeCun 正态初始化
    - 不能用 Dropout（要用 Alpha Dropout）

现实: 条件太苛刻，实际使用很少，主要是理论上有意思
```

### ReLU 变体对比

```
┌─────────────────────────────────────────────────────────────────┐
│                    ReLU 变体一览                                  │
│                                                                  │
│  函数          │ 负区域       │ 能否死亡 │ 计算复杂度 │ 额外参数 │
│  ──────────────┼──────────────┼──────────┼────────────┼──────── │
│  ReLU          │ 0            │ 会死     │ ★☆☆☆      │ 无       │
│  Leaky ReLU    │ 0.01x        │ 不会死   │ ★☆☆☆      │ 无       │
│  PReLU         │ αx (可学习)  │ 不会死   │ ★☆☆☆      │ 有(少)   │
│  ELU           │ α(eˣ-1)     │ 不会死   │ ★★☆☆      │ 无       │
│  SELU          │ λα(eˣ-1)    │ 不会死   │ ★★☆☆      │ 无       │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## GELU 和 SiLU/Swish：现代 LLM 的标配

### 为什么需要新一代激活函数

```
ReLU 的根本问题:

    在 x=0 处不可导（有个"尖角"）
    负区域输出完全为 0（信息彻底丢失）
    
    → 对于简单的 CNN 来说够用了
    → 对于 Transformer 这样的深层大模型，需要更平滑、更精细的激活函数

目标:
    保留 ReLU 的优势（简单、正区域梯度好）
    同时让负区域有微小输出（不完全丢弃信息）
    并且在 x=0 附近更平滑（梯度更连续）
```

### GELU (Gaussian Error Linear Unit)

```
GELU(x) = x × Φ(x)

    Φ(x) = 正态分布的累积分布函数 (CDF)
    
    直觉: "根据这个值有多'正常'，决定让多少信号通过"
    
    Φ(x) 的含义:
        x = -3: Φ(-3) ≈ 0.001  → 几乎完全阻断
        x = -1: Φ(-1) ≈ 0.159  → 阻断大部分，保留一点
        x =  0: Φ(0)  = 0.5    → 通过一半
        x =  1: Φ(1)  ≈ 0.841  → 通过大部分
        x =  3: Φ(3)  ≈ 0.999  → 几乎完全通过

    GELU(x) = x × Φ(x):
        x = -3: -3 × 0.001  = -0.003   ← 微弱的负信号
        x = -1: -1 × 0.159  = -0.159   ← 保留一些负面信息
        x =  0:  0 × 0.5    =  0       ← 中点
        x =  1:  1 × 0.841  =  0.841   ← 大部分通过
        x =  3:  3 × 0.999  =  2.997   ← 几乎完整通过

图形:
输出
  │           ╱
  │          ╱
  │         ╱
  │        ╱
  │       ╱
  │      ╱
  │     ╱
──┼───╲╱──────── 输入
  │ (有个小凹陷！负区域不完全是0)
  │

近似公式 (实际计算用):
    GELU(x) ≈ 0.5x × (1 + tanh[√(2/π) × (x + 0.044715x³)])

    → 用 tanh 近似，避免直接计算正态分布 CDF
    → PyTorch/TensorFlow 都用这个近似

使用它的模型:
    BERT, GPT-2, GPT-3, GPT-4, Claude 等
```

### SiLU / Swish

```
SiLU(x) = x × σ(x)

    σ(x) = Sigmoid(x) = 1/(1+e⁻ˣ)
    
    直觉: "用 Sigmoid 作为门控，决定让多少 x 通过"

    Swish(x) = x × σ(βx)
    → 当 β = 1 时，Swish = SiLU
    → β 可以是固定值或可学习参数

    SiLU(x):
        x = -3: -3 × σ(-3)  = -3 × 0.047   = -0.142
        x = -1: -1 × σ(-1)  = -1 × 0.269   = -0.269  ← 最小值点
        x =  0:  0 × σ(0)   =  0 × 0.5     =  0
        x =  1:  1 × σ(1)   =  1 × 0.731   =  0.731
        x =  3:  3 × σ(3)   =  3 × 0.953   =  2.858

图形 (和 GELU 非常像):
输出
  │            ╱
  │           ╱
  │          ╱
  │         ╱
  │        ╱
  │       ╱
  │      ╱
──┼────╲╱──────── 输入
  │  (小凹陷，负区域最小值约 -0.28)
  │

使用它的模型:
    LLaMA 1/2/3, Mistral, Gemma 等
    （通常以 SwiGLU 的形式使用，见下一节）
```

### GELU vs SiLU 对比

```
┌──────────────────────────────────────────────────────────────┐
│              GELU vs SiLU                                     │
│                                                               │
│  相似点:                                                      │
│    - 形状几乎一样（差异很小）                                │
│    - 都是平滑的、非单调的                                    │
│    - 负区域都有微小输出                                      │
│    - 都不会产生 Dead Neuron                                   │
│                                                               │
│  区别:                                                        │
│    GELU = x × Φ(x)   → 基于正态分布 CDF                     │
│    SiLU = x × σ(x)   → 基于 Sigmoid                         │
│                                                               │
│    GELU 在极负区域衰减更快（更接近 0）                       │
│    SiLU 在极负区域保留略多的负值                              │
│                                                               │
│  实际性能差异: 极小，选谁都行                                │
│                                                               │
│  选择依据:                                                    │
│    BERT/GPT 系列 → GELU（历史传统）                          │
│    LLaMA/Mistral 系列 → SiLU + GLU = SwiGLU                  │
│                                                               │
└──────────────────────────────────────────────────────────────┘
```

---

## SwiGLU：LLaMA 的秘密武器

### GLU 机制

```
GLU (Gated Linear Unit) 的核心思想:

    普通 FFN:
        output = activation(xW₁) × W₂
        → 一个线性变换 + 激活 + 一个线性变换

    GLU FFN:
        gate   = σ(xW_gate)          ← "门"：决定什么信息通过
        value  = xW_up               ← "值"：准备好的信息
        output = (gate × value) × W_down
        
        → 多了一个"门控"机制，用一个分支决定另一个分支的哪些信息通过

类比: 安检门
    普通方式: 所有人进来 → 过安检机 → 出去
    GLU 方式:  所有人进来 → 一组人负责检查（gate）
                          → 一组人等待通过（value）
                          → 检查组决定让谁通过 → 出去
    → 更精细的信息筛选
```

### SwiGLU = SiLU + GLU

```
SwiGLU(x) = SiLU(xW_gate) × (xW_up)

    展开:
    gate = SiLU(x × W_gate) = (x × W_gate) × σ(x × W_gate)
    up   = x × W_up
    output = gate × up
    → 然后再通过 W_down 降维

完整的 SwiGLU FFN:
    gate   = SiLU(x @ W_gate)     [batch, seq, 4096] × [4096, 11008] → [batch, seq, 11008]
    up     = x @ W_up             [batch, seq, 4096] × [4096, 11008] → [batch, seq, 11008]
    hidden = gate × up            [batch, seq, 11008]（逐元素相乘）
    output = hidden @ W_down      [batch, seq, 11008] × [11008, 4096] → [batch, seq, 4096]

注意: SwiGLU 需要 3 个权重矩阵 (W_gate, W_up, W_down)，比标准 FFN (2个) 多 50% 参数
      所以 LLaMA 把隐藏维度从 4×4096=16384 调成了 2.7×4096≈11008
      → 总参数量和标准 FFN 差不多，但效果更好

┌──────────────────────────────────────────────────────────────┐
│  标准 FFN (GPT):                                              │
│      x → W_up(4096→16384) → GELU → W_down(16384→4096)       │
│      参数: 4096×16384 + 16384×4096 = 1.34 亿                │
│                                                               │
│  SwiGLU FFN (LLaMA):                                         │
│      x → W_gate(4096→11008) → SiLU ─┐                       │
│      x → W_up(4096→11008) ──────────→ × → W_down(11008→4096)│
│      参数: 4096×11008 × 3 = 1.35 亿                         │
│                                                               │
│  参数量差不多，但 SwiGLU 效果更好！                           │
│  → PaLM 论文: SwiGLU 比 GELU FFN 准确率高 ~0.5-1%           │
└──────────────────────────────────────────────────────────────┘
```

---

## 激活函数的梯度对比

### 梯度流对比图

```
假设 10 层网络，每层激活函数对梯度的影响:

Sigmoid (最差):
    Layer 10 → 9 → 8 → 7 → 6 → 5 → 4 → 3 → 2 → 1
    梯度:  1   0.25 0.06 0.016 0.004 0.001 ... → ≈ 0
    ████████   ██████  ████   ███   ██   █   ·   ·
    → 前面的层几乎收不到梯度

Tanh (稍好):
    Layer 10 → 9 → 8 → 7 → 6 → 5 → 4 → 3 → 2 → 1
    梯度:  1   0.5  0.25 0.13 0.06 0.03 0.016 ... → ≈ 0
    ████████   ████   ███   ██   █   ·   ·   ·
    → 比 Sigmoid 好，但仍然衰减

ReLU (正区域完美):
    Layer 10 → 9 → 8 → 7 → 6 → 5 → 4 → 3 → 2 → 1
    梯度:  1   1    1    1    1    1    1    1    1    1
    ████████  ████████  ████████  ████████  ████████
    → 正区域：梯度完美传递！
    → 但如果某层 ReLU 输出 0 → 梯度被切断

GELU/SiLU (最佳):
    Layer 10 → 9 → 8 → 7 → 6 → 5 → 4 → 3 → 2 → 1
    梯度:  1   ~1   ~1   ~1   ~1   ~1   ~1   ~1   ~1
    ████████  ███████  ███████  ███████  ███████
    → 接近 ReLU 的正区域表现
    → 负区域也有微小梯度 → 不会完全切断
    → 平滑过渡 → 优化景观更平滑 → 训练更稳定
```

### 导数曲线对比

```
                  导数值
        1.0 ─────────────────────────────────
            ╲         ╱──── ReLU (阶跃: 0→1)
            ╲       ╱
            ╲     ╱──── GELU/SiLU (平滑过渡)
            ╲   ╱
        0.5  ╲╱──── Tanh
              ╱╲
             ╱  ╲
        0.25 ╱───╲──── Sigmoid (最大只有 0.25)
           ╱      ╲
        0.0 ─────────────────────────────────
                   0          输入 x

关键观察:
    Sigmoid: 导数最大 0.25 → 每层梯度缩小 4 倍
    Tanh:    导数最大 1.0，但两端快速衰减
    ReLU:    导数要么 0 要么 1 → 二值的，不连续
    GELU/SiLU: 导数从负无穷平滑过渡到 1+ → 最佳
```

---

## 实际选型指南

### 不同场景的推荐

```
┌──────────────────────────────────────────────────────────────────┐
│                    激活函数选型指南                                │
│                                                                   │
│  场景                    │ 推荐             │ 原因               │
│  ────────────────────────┼──────────────────┼──────────────────  │
│  快速原型验证            │ ReLU             │ 最简单，够用       │
│  CNN (图像分类)          │ ReLU 或 Leaky ReLU│ 经典且高效        │
│  Transformer / LLM      │ GELU 或 SwiGLU   │ 平滑梯度，效果好  │
│  BERT / GPT 系列        │ GELU             │ 社区标准           │
│  LLaMA / Mistral 系列   │ SwiGLU           │ 门控更强           │
│  二分类输出层           │ Sigmoid          │ 输出概率 (0,1)     │
│  多分类输出层           │ Softmax          │ 输出概率分布       │
│  生成模型 (GAN)          │ Leaky ReLU       │ 避免 Dead Neuron   │
│  RNN / LSTM              │ Tanh + Sigmoid   │ 门控机制需要       │
│                                                                   │
│  默认选择:                                                        │
│    2024+ 年的新项目 → GELU 或 SwiGLU                             │
│    不确定用什么 → 先用 ReLU，不行再换 GELU                       │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

### 性能与计算开销

```
计算开销排序 (从低到高):

    ReLU      ★☆☆☆☆   max(0, x)          → 一次比较
    Leaky ReLU ★☆☆☆☆   类似 ReLU           → 一次比较 + 一次乘法
    SiLU      ★★★☆☆   x × σ(x)           → 一次 Sigmoid + 一次乘法
    GELU      ★★★☆☆   tanh 近似           → 几次乘法 + tanh
    SwiGLU    ★★★★☆   三个线性层 + SiLU   → 多 50% 的矩阵乘法
    ELU       ★★★☆☆   指数运算            → eˣ

实际影响:
    在现代 GPU 上，激活函数的计算开销相比矩阵乘法可以忽略不计
    矩阵乘法占 99% 以上的计算量
    → 激活函数的选择主要看效果，不看速度

    SwiGLU 多 50% 参数 → 需要更多显存和计算
    但效果提升 → 性价比值得（LLaMA 通过缩减维度来抵消）
```

---

## PyTorch 代码实战

### 所有激活函数的对比

```python
import torch
import torch.nn as nn
import torch.nn.functional as F

# 输入数据
x = torch.linspace(-3, 3, 100)

# 各种激活函数
activations = {
    'ReLU':       nn.ReLU(),
    'LeakyReLU':  nn.LeakyReLU(0.01),
    'PReLU':      nn.PReLU(),            # α 可学习
    'ELU':        nn.ELU(alpha=1.0),
    'GELU':       nn.GELU(),
    'SiLU':       nn.SiLU(),             # 也叫 Swish
    'Sigmoid':    nn.Sigmoid(),
    'Tanh':       nn.Tanh(),
}

for name, fn in activations.items():
    y = fn(x)
    print(f"{name:12s}: min={y.min():.3f}, max={y.max():.3f}")

# 输出:
# ReLU        : min=0.000, max=3.000
# LeakyReLU   : min=-0.030, max=3.000
# PReLU       : min=-0.750, max=3.000
# ELU         : min=-0.950, max=3.000
# GELU        : min=-0.170, max=3.000
# SiLU        : min=-0.278, max=2.858
# Sigmoid     : min=0.047, max=0.953
# Tanh        : min=-0.995, max=0.995
```

### 监控 Dead Neuron

```python
import torch
import torch.nn as nn

class NetworkWithMonitoring(nn.Module):
    def __init__(self, input_dim, hidden_dim, output_dim):
        super().__init__()
        self.fc1 = nn.Linear(input_dim, hidden_dim)
        self.relu = nn.ReLU()
        self.fc2 = nn.Linear(hidden_dim, output_dim)
        
        # 用于统计 Dead Neuron
        self.activation_count = None
    
    def forward(self, x):
        z = self.fc1(x)
        h = self.relu(z)
        
        # 监控: 统计每个神经元被激活的比例
        with torch.no_grad():
            active = (h > 0).float().mean(dim=0)  # 每个神经元在 batch 中的激活率
            if self.activation_count is None:
                self.activation_count = active
            else:
                self.activation_count = 0.9 * self.activation_count + 0.1 * active
        
        return self.fc2(h)
    
    def get_dead_neuron_ratio(self, threshold=0.01):
        """返回"死亡"神经元的比例"""
        if self.activation_count is None:
            return 0.0
        dead = (self.activation_count < threshold).float().mean().item()
        return dead

# 使用
model = NetworkWithMonitoring(784, 256, 10)

# 训练若干步后...
for _ in range(100):
    x = torch.randn(32, 784)
    y = model(x)

print(f"Dead neuron ratio: {model.get_dead_neuron_ratio():.2%}")
# 如果 > 30%，建议换成 Leaky ReLU 或 GELU
```

### SwiGLU FFN 实现

```python
import torch
import torch.nn as nn
import torch.nn.functional as F

class SwiGLU_FFN(nn.Module):
    """LLaMA 中使用的 SwiGLU FFN"""
    def __init__(self, hidden_dim=4096, intermediate_dim=11008):
        super().__init__()
        self.w_gate = nn.Linear(hidden_dim, intermediate_dim, bias=False)
        self.w_up   = nn.Linear(hidden_dim, intermediate_dim, bias=False)
        self.w_down = nn.Linear(intermediate_dim, hidden_dim, bias=False)
    
    def forward(self, x):
        gate = F.silu(self.w_gate(x))    # SiLU 门控
        up = self.w_up(x)                 # 值分支
        return self.w_down(gate * up)     # 逐元素相乘后降维

class Standard_FFN(nn.Module):
    """标准 GELU FFN (GPT 风格)"""
    def __init__(self, hidden_dim=4096, intermediate_dim=16384):
        super().__init__()
        self.w_up   = nn.Linear(hidden_dim, intermediate_dim)
        self.w_down = nn.Linear(intermediate_dim, hidden_dim)
    
    def forward(self, x):
        return self.w_down(F.gelu(self.w_up(x)))

# 对比参数量
swiglu = SwiGLU_FFN()
standard = Standard_FFN()

swiglu_params = sum(p.numel() for p in swiglu.parameters())
standard_params = sum(p.numel() for p in standard.parameters())

print(f"SwiGLU FFN:   {swiglu_params:>12,} params")   # ~135M
print(f"Standard FFN: {standard_params:>12,} params")  # ~134M
# → 参数量接近，但 SwiGLU 效果更好
```

---

## 总结

### 激活函数演化时间线

```
1990s           2010            2012            2016            2017-2020       2020+
Sigmoid/Tanh → ReLU 提出 → AlexNet 用 ReLU → GELU 提出 → SiLU/Swish → SwiGLU
(梯度消失)    (革命性突破)  (深度学习爆发)   (Transformer)  (Google Brain)   (LLaMA)
                                                                               
主要问题:      解决方案:     验证有效:        更平滑:        门控:           SOTA:
梯度每层×0.25  正区域梯度=1  训练速度×6       负区域不归零   精细信息筛选     全面最优
```

### 核心知识点

```
┌──────────────────────────────────────────────────────────────────┐
│                    激活函数核心要点                                │
│                                                                   │
│  为什么需要:                                                      │
│    没有激活函数 → 100层=1层 → 网络无法学习复杂规律              │
│                                                                   │
│  ReLU 的革命:                                                     │
│    max(0,x) → 缓解梯度消失、计算极简、稀疏激活                  │
│    缺陷: Dead Neuron（负区域永远为0）                             │
│                                                                   │
│  现代选择 (GELU / SiLU / SwiGLU):                                │
│    平滑、负区域有微小输出、梯度更连续                            │
│    几乎所有现代 LLM 都使用                                       │
│                                                                   │
│  选型原则:                                                        │
│    新项目 → GELU 或 SwiGLU                                       │
│    快速原型 → ReLU                                                │
│    Dead Neuron 问题 → Leaky ReLU 或 GELU                         │
│    输出概率 → Sigmoid (二分类) / Softmax (多分类)                │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

| 激活函数 | 一句话 | 典型使用场景 |
|----------|--------|-------------|
| Sigmoid | 输出概率 (0,1) | 二分类输出层、门控 |
| Tanh | 输出 (-1,1)，零中心 | RNN/LSTM 的门控 |
| ReLU | 正数通过，负数归零 | CNN、快速原型 |
| Leaky ReLU | 负数保留微小斜率 | GAN、避免 Dead Neuron |
| PReLU | 斜率可学习的 Leaky ReLU | 图像分类 |
| GELU | 平滑版 ReLU | BERT、GPT 系列 |
| SiLU | x × Sigmoid(x) | LLaMA (配合 GLU) |
| SwiGLU | SiLU + 门控线性单元 | LLaMA、Mistral、现代 LLM |

---

- **上一篇**：[13-梯度累积与评估指标](13-gradient-accumulation.md)
- **相关章节**：[02-什么是神经网络](02-neural-network-basics.md) — 激活函数初步
- **相关章节**：[05-反向传播详解](05-backpropagation.md) — 梯度如何通过激活函数传播
- **相关章节**：[10-Transformer 架构深入讲解](10-transformer-architecture.md) — GELU/SwiGLU 在 Transformer 中的应用

---

## 参考资料与引用

1. **Nair, V., & Hinton, G. E. (2010).** *Rectified Linear Units Improve Restricted Boltzmann Machines.* ICML 2010. — ReLU 原论文  
   https://www.cs.toronto.edu/~fritz/absps/reluICML.pdf

2. **Hendrycks, D., & Gimpel, K. (2016).** *Gaussian Error Linear Units (GELUs).* — GELU 激活函数  
   https://arxiv.org/abs/1606.08415

3. **Ramachandran, P., Zoph, B., & Le, Q. V. (2017).** *Searching for Activation Functions.* — Swish/SiLU 激活函数  
   https://arxiv.org/abs/1710.05941

4. **Shazeer, N. (2020).** *GLU Variants Improve Transformer.* — SwiGLU 及其他 GLU 变体  
   https://arxiv.org/abs/2002.05202

5. **Dauphin, Y., et al. (2017).** *Language Modeling with Gated Convolutional Networks.* ICML 2017. — 门控线性单元 (GLU) 原论文  
   https://arxiv.org/abs/1612.08083

6. **He, K., et al. (2015).** *Delving Deep into Rectifiers: Surpassing Human-Level Performance on ImageNet Classification.* — PReLU  
   https://arxiv.org/abs/1502.01852
