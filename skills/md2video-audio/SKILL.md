---
name: md2video-audio
description: 将指定的 Markdown (MD) 文件一键转换为带免费真人配音（Edge-TTS 晓晓音色）和讲解画面的 MP4 视频。完全零成本、无第三方 API 费用。当用户要求把 markdown 转成视频、制作口播视频或音视频合成时自动触发。
---

# Markdown 免费口播视频生成技能 (md2video-audio)

- 用途：将本地的 Markdown 文件自动转化为包含画面与免费语音的 MP4 视频。

## 执行步骤与规范

当触发本技能时，请严格按以下步骤在沙箱中执行：

### 1. 环境依赖检查与安装

首先检查是否具备相关依赖，若缺失则自动执行安装：
```bash
pip install edge-tts moviepy markdown 
npm install -g @marp-team/marp-cli
```

(注：若系统提示缺少 ffmpeg，需引导或自动通过 `apt-get install -y ffmpeg` 进行安装)

### 2. markdown文件预处理

- **语义审阅+内容优化**：检查该文件是否利用markdown文件结构化符号按逻辑分段，每段长度适中。如果不满足，则进行**逻辑分段与排版优化**，注意不要在原输入md文件上修改，而是保存成`new-原名前缀-时间戳`的新md文件

  - 检查并补全文章的层级标题（确保有 `#` 和 `##` 作为自然的视觉分镜切换点）。


  - 规范代码块格式，并在代码块上方或前后由 AI 自动补充自然的过渡引导语。

- 将上个步骤得到的md文件拆分为口播稿和展示稿。为保证画面和声音严丝合缝、不会错位，你在编写这两个 Markdown 文件时，**两边的 `---` 分隔符数量必须保持一致**，作为每页的间隔。
  - 转换为逻辑自然的口播稿，保存成`speaking-原名前缀-时间戳`的新md文件
  - 转换为 Marp 格式，用于后续脚本中生成PPT，保存成`show-原名前缀-时间戳`的新md文件
    1. Markdown 文件最顶部加上几行配置
    2. 根据语义逻辑、md段落结构，用 `---` 来分隔每一页 PPT，如

```markdown
---
marp: true
theme: gaia
_class: default
paginate: true
---

# 核心架构解析
### 零代码排版，享受高级 PPT 质感

---

## 章节一：背景介绍
- 现代化大模型应用落地
- 向量检索与索引平衡
  - HNSW 索引平衡速度和精度
  - IVF_PQ 算法加速

---

## 章节二：核心代码示例
```python
# 这里会自动获得精美的高亮排版
def hello():
    print("Hello Marp!")
```

- 这两个保存好的**规范的中间文件名**作为后续调用脚本的参数

### 3. 用Python 脚本一键打包成视频

- 用上述过程中生成的2个中间结果md文件，分别是口播稿和展示稿作为输入，调用执行本skill目录下名为`ai-2md2marp2av.py`，`python ai-2md2marp2av.py 展示稿.md 口播稿.md`

  脚本逻辑为用 Marp 生成的高颜值 PPT 图片后，把图片和 Edge-TTS 生成的语音按对应页数拼起来即可。

### 4. 降级方案

- 如果上述步骤都生成视频失败，则调用降级方案：执行本skill目录下名为`md2marp2av.py`脚本。如果还是没正确生成视频，则执行本skill目录下名为`md2video.py`脚本