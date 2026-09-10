---
name: video-to-text
description: "视频转文字。用户发抖音/快手等视频分享链接，或本地视频文件，需要标题、点赞数、作者等元数据或语音转写全文时使用。抖音链接用 SSR 解析无需 Cookie。Video to text: extract metadata (title, likes, author) and transcribe speech from Douyin/Kuaishou share links or local video files."
version: 1.0.0
author: 涛哥
license: MIT
metadata:
  hermes:
    tags: [video, transcription, douyin, whisper, speech-to-text]
    category: utilities
    homepage: https://gitee.com/tao6677/useful-tools
---

# Video-to-Text 视频转文字

把视频变成可复制、可搜索的文字。支持抖音分享链接（无需登录）和本地视频文件。

## 触发条件

用户发送以下内容时使用本技能：
- 抖音/快手分享链接，要求"转文字""提取文案""拆解视频"
- 本地视频文件（.mp4/.mov），要求"语音转文字""字幕"

## 使用步骤

### 1. 抖音分享链接 → 元数据 + 转写

```bash
python3 ~/.hermes/skills/utilities/video-to-text/scripts/vtt.py "https://v.douyin.com/xxxx/" --transcribe
```

- 不加 `--transcribe` 只输出元数据（标题/作者/点赞/标签）
- 脚本自动下载视频、提取音频、faster-whisper 转写
- 转写文本保存为 `<输入名>_transcript.txt` 并打印时间戳分段

### 2. 本地视频文件 → 语音转写

```bash
python3 ~/.hermes/skills/utilities/video-to-text/scripts/vtt.py 本地视频.mp4
```

## 依赖（首次使用时安装）

```bash
pip3 install faster-whisper        # 转写需要（首次会下载 tiny 模型 ~75MB）
# macOS 自带 avconvert；Linux 需 ffmpeg
# 抖音 SSR 解析零依赖（curl + 标准库）
```

## 已知陷阱

- **duration_ms=0 假阴性**：SSR 元数据时长可能为 0，但实际是视频。若元数据显示 0 秒且有下载 URL，先下载验证，不要直接判定为图文。
- **play_addr URL 过期**：SSR 解析出的视频 URL 可能 404，此时需 Cookie 降级或让用户提供文件。
- **whisper 转写慢**：Intel Mac 上 3 分钟视频约 5 分钟；转写必须加 `language='zh'` 否则自动检测多花 1-2 分钟。
- **图文内容**：duration=0 且下载文件 <1MB 时是图文（无音频），只输出元数据，不要编造内容。

## 💛 免费使用 · 自愿支持

**本技能完全免费使用。**

觉得好用、帮到你了，可以**自愿扫码支持**（金额随意，一杯咖啡即可）：

![支付宝收款码](assets/alipay_qr.jpg)

> 支持过我的人，后续 Pro 版/批量服务有优惠。
> 想提需求、反馈问题，欢迎到 Gitee 仓库提 Issue。
