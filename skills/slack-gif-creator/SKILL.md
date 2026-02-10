---
name: slack-gif-creator
description: 用于创建为 Slack 优化的动画 GIF 的知识和实用程序。提供约束、验证工具和动画概念。当用户请求为 Slack 制作动画 GIF（如"为 Slack 制作一个关于 X 做 Y 的 GIF"）时使用。
license: 完整条款见 LICENSE.txt
---

# Slack GIF 创建器

一个工具包，提供用于创建为 Slack 优化的动画 GIF 的实用程序和知识。

## Slack 要求

**尺寸：**
- 表情符号 GIF：128x128（推荐）
- 消息 GIF：480x480

**参数：**
- FPS：10-30（越低文件大小越小）
- 颜色：48-128（越少文件大小越小）
- 持续时间：表情符号 GIF 保持在 3 秒以下

## 核心工作流程

```python
from core.gif_builder import GIFBuilder
from PIL import Image, ImageDraw

# 1. 创建构建器
builder = GIFBuilder(width=128, height=128, fps=10)

# 2. 生成帧
for i in range(12):
    frame = Image.new('RGB', (128, 128), (240, 248, 255))
    draw = ImageDraw.Draw(frame)

    # 使用 PIL 图元绘制动画
    #（圆形、多边形、线条等）

    builder.add_frame(frame)

# 3. 保存并优化
builder.save('output.gif', num_colors=48, optimize_for_emoji=True)
```

## 绘制图形

### 使用用户上传的图像
如果用户上传图像，请考虑他们是否想要：
- **直接使用**（例如，"制作这个的动画"，"将其拆分为帧"）
- **作为灵感**（例如，"制作类似这样的东西"）

使用 PIL 加载和处理图像：
```python
from PIL import Image

uploaded = Image.open('file.png')
# 直接使用，或仅作为颜色/样式的参考
```

### 从头开始绘制
从头开始绘制图形时，使用 PIL ImageDraw 图元：

```python
from PIL import ImageDraw

draw = ImageDraw.Draw(frame)

# 圆形/椭圆
draw.ellipse([x1, y1, x2, y2], fill=(r, g, b), outline=(r, g, b), width=3)

# 星形、三角形、任何多边形
points = [(x1, y1), (x2, y2), (x3, y3), ...]
draw.polygon(points, fill=(r, g, b), outline=(r, g, b), width=3)

# 线条
draw.line([(x1, y1), (x2, y2)], fill=(r, g, b), width=5)

# 矩形
draw.rectangle([x1, y1, x2, y2], fill=(r, g, b), outline=(r, g, b), width=3)
```

**不要使用：** 表情符号字体（跨平台不可靠）或假设此技能中存在预打包的图形。

### 使图形看起来美观

图形应该看起来精致且有创意，而不是基本。方法如下：

**使用较粗的线条** - 始终为轮廓和线条设置 `width=2` 或更高。细线条（width=1）看起来参差不齐且不专业。

**增加视觉深度：**
- 使用渐变作为背景（`create_gradient_background`）
- 分层多个形状以增加复杂性（例如，带有内部较小星星的星星）

**使形状更有趣：**
- 不要只画一个普通的圆形 - 添加高光、环或图案
- 星星可以有发光（在后面绘制较大的半透明版本）
- 组合多个形状（星星 + 闪光，圆形 + 环）

**注意颜色：**
- 使用鲜艳、互补的颜色
- 增加对比度（浅色形状上的深色轮廓，深色形状上的浅色轮廓）
- 考虑整体构图

**对于复杂的形状**（心形、雪花等）：
- 使用多边形和椭圆的组合
- 仔细计算点以获得对称性
- 添加细节（心形可以有高光曲线，雪花有复杂的分支）

要有创意和细节！一个好的 Slack GIF 应该看起来精致，而不是像占位符图形。

## 可用的实用程序

### GIFBuilder (`core.gif_builder`)
组装帧并为 Slack 优化：
```python
builder = GIFBuilder(width=128, height=128, fps=10)
builder.add_frame(frame)  # 添加 PIL 图像
builder.add_frames(frames)  # 添加帧列表
builder.save('out.gif', num_colors=48, optimize_for_emoji=True, remove_duplicates=True)
```

### 验证器 (`core.validators`)
检查 GIF 是否符合 Slack 要求：
```python
from core.validators import validate_gif, is_slack_ready

# 详细验证
passes, info = validate_gif('my.gif', is_emoji=True, verbose=True)

# 快速检查
if is_slack_ready('my.gif'):
    print("准备好了！")
```

### 缓动函数 (`core.easing`)
平滑运动而不是线性：
```python
from core.easing import interpolate

# 进度从 0.0 到 1.0
t = i / (num_frames - 1)

# 应用缓动
y = interpolate(start=0, end=400, t=t, easing='ease_out')

# 可用：linear、ease_in、ease_out、ease_in_out、
#       bounce_out、elastic_out、back_out
```

### 帧助手 (`core.frame_composer`)
用于常见需求的便利函数：
```python
from core.frame_composer import (
    create_blank_frame,         # 纯色背景
    create_gradient_background,  # 垂直渐变
    draw_circle,                # 圆形助手
    draw_text,                  # 简单文本渲染
    draw_star                   # 五角星
)
```

## 动画概念

### 摇动/振动
使用振荡偏移对象位置：
- 使用带有帧索引的 `math.sin()` 或 `math.cos()`
- 添加小的随机变化以获得自然感觉
- 应用于 x 和/或 y 位置

### 脉冲/心跳
有节奏地缩放对象大小：
- 使用 `math.sin(t * frequency * 2 * math.pi)` 进行平滑脉冲
- 对于心跳：两次快速脉冲然后暂停（调整正弦波）
- 在基础大小的 0.8 到 1.2 倍之间缩放

### 弹跳
对象掉落并弹跳：
- 使用带有 `easing='bounce_out'` 的 `interpolate()` 进行着陆
- 使用 `easing='ease_in'` 进行掉落（加速）
- 通过每帧增加 y 速度来应用重力

### 旋转/自转
围绕中心旋转对象：
- PIL：`image.rotate(angle, resample=Image.BICUBIC)`
- 对于摇摆：对角度使用正弦波而不是线性

### 淡入/淡出
逐渐出现或消失：
- 创建 RGBA 图像，调整 alpha 通道
- 或使用 `Image.blend(image1, image2, alpha)`
- 淡入：alpha 从 0 到 1
- 淡出：alpha 从 1 到 0

### 滑动
将对象从屏幕外移动到位置：
- 起始位置：框架边界之外
- 结束位置：目标位置
- 使用带有 `easing='ease_out'` 的 `interpolate()` 进行平滑停止
- 对于过冲：使用 `easing='back_out'`

### 缩放
缩放和定位以获得缩放效果：
- 放大：从 0.1 缩放到 2.0，裁剪中心
- 缩小：从 2.0 缩放到 1.0
- 可以添加运动模糊以增加戏剧性（PIL 滤镜）

### 爆炸/粒子爆发
创建向外辐射的粒子：
- 生成具有随机角度和速度的粒子
- 更新每个粒子：`x += vx`，`y += vy`
- 添加重力：`vy += gravity_constant`
- 随着时间淡出粒子（减少 alpha）

## 优化策略

仅当被要求使文件大小更小时，实施以下几种方法：

1. **更少的帧** - 更低的 FPS（10 而不是 20）或更短的持续时间
2. **更少的颜色** - `num_colors=48` 而不是 128
3. **更小的尺寸** - 128x128 而不是 480x480
4. **删除重复项** - 在 save() 中设置 `remove_duplicates=True`
5. **表情符号模式** - `optimize_for_emoji=True` 自动优化

```python
# 表情符号的最大优化
builder.save(
    'emoji.gif',
    num_colors=48,
    optimize_for_emoji=True,
    remove_duplicates=True
)
```

## 理念

此技能提供：
- **知识**：Slack 的要求和动画概念
- **实用程序**：GIFBuilder、验证器、缓动函数
- **灵活性**：使用 PIL 图元创建动画逻辑

它不提供：
- 僵化的动画模板或预制函数
- 表情符号字体渲染（跨平台不可靠）
- 内置于技能中的预打包图形库

**关于用户上传的说明**：此技能不包括预构建的图形，但如果用户上传图像，请使用 PIL 加载和处理它 - 根据他们的请求解释他们是想要直接使用它还是仅作为灵感。

要有创意！结合概念（弹跳 + 旋转，脉冲 + 滑动等）并使用 PIL 的全部功能。

## 依赖项

```bash
pip install pillow imageio numpy
```
