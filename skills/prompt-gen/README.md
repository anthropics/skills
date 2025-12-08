# Prompt-Gen 技能

这个技能帮助用户基于关键词生成多样化的AI图像提示词，并可直接调用ModelScope API生成对应的图像。

## 功能特点

- **双模式支持**:
  - 仅生成提示词模式（传统模式）
  - 直接图像生成模式（新功能）
- 基于用户提供的关键词生成4-6个不同风格的提示词
- 覆盖多种艺术风格、构图方式、光照条件和氛围
- 适用于主流AI图像生成工具（Midjourney、DALL-E、Stable Diffusion等）
- **API集成**: 直接调用ModelScope API生成高质量图像
- **限流处理**: 自动处理API限流，顺序生成多张图像
- 提供具体的使用建议和技术参数

## 环境配置

使用图像生成功能前，需要配置API密钥。支持两种方式：

### 方式1: 使用 .env 文件（推荐）
1. 复制示例文件：`cp .env.example .env`
2. 编辑 `.env` 文件，填入您的实际API密钥：
```env
MODELSCOPE_API_KEY=your-actual-api-key-here
```

### 方式2: 设置系统环境变量
```bash
export MODELSCOPE_API_KEY="your-api-key-here"
```

> **注意**: 如果使用 `.env` 文件，请确保安装了 `python-dotenv` 包：
> ```bash
> pip install python-dotenv
> ```

## 使用示例

### 仅提示词生成
**输入**: "海洋、鲸鱼、星空"
**输出**: 多个不同风格的AI图像提示词

### 直接图像生成
**输入**: "用'森林、鹿、晨雾'生成几张不同的图片"
**输出**: 生成的提示词列表 + 实际图像文件（**必须指定绝对路径**作为输出目录）