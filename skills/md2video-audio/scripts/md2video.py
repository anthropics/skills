import asyncio
import os
import re
from datetime import datetime
import edge_tts
from moviepy import TextClip, AudioFileClip, CompositeVideoClip, ColorClip, concatenate_videoclips

VOICE = "zh-CN-XiaoxiaoNeural"  
WIDTH, HEIGHT = 1280, 720
FPS = 24

def sanitize_text_for_display(text):
    """
    清洗文本：
    1. 将 <br> / <br/> 转换为真实的换行符 \n
    2. 移除其他 HTML 标签（如 <b>, </span> 等）
    3. 过滤掉会导致中文字体渲染出方块叉的 Emoji 及特殊符号（已修正原始字符串与十六进制范围）
    """
    if not text:
        return ""
    
    # 1. 智能转换 HTML 换行标签为真实换行
    text = re.sub(r'<br\s*/?>', '\n', text, flags=re.IGNORECASE)
    
    # 2. 移除其他常见的 HTML 标签
    text = re.sub(r'</?[a-zA-Z]+[^>]*>', '', text)
    
    # 3. 过滤 Emoji 和特殊符号区块（注意前面加了 r 变成原始字符串，防止转义报错）
    emoji_pattern = re.compile(
        r"["
        r"\U0001f000-\U0001faf9"  
        r"\U0001f300-\U0001f5ff"
        r"\U0001f600-\U0001f64f"
        r"\U0001f680-\U0001f6ff"
        r"\U0001f900-\U0001f9ff"
        r"\u2600-\u26ff"          
        r"\u2700-\u27bf"          
        r"]+", flags=re.UNICODE
    )
    cleaned = emoji_pattern.sub('', text)
    
    # 清理多余的水平空格，但保留换行符 \n
    cleaned = re.sub(r'[ \t]+', ' ', cleaned)
    return cleaned.strip()

def parse_markdown_by_chapters(md_file_path):
    """
    按 Markdown 章节结构（以 # 或 ## 标题分割）聚合内容。
    """
    if not os.path.exists(md_file_path):
        raise FileNotFoundError(f"找不到文件: {md_file_path}")
    
    with open(md_file_path, "r", encoding="utf-8") as f:
        content = f.read()

    chapters_raw = re.split(r'(?m)^(#+\s+.+)', content)
    
    sections = []
    current_title = "开场简介"
    current_body = []

    for part in chapters_raw:
        part = part.strip()
        if not part:
            continue
        if part.startswith('#'):
            if current_body:
                sections.append((current_title, "\n".join(current_body)))
                current_body = []
            current_title = re.sub(r'#+\s*', '', part).strip()
        else:
            current_body.append(part)
            
    if current_body or current_title:
        sections.append((current_title, "\n".join(current_body)))

    if not sections and content.strip():
        sections.append(("全文概览", content.strip()))

    formatted_sections = []
    for title, body in sections:
        # 口播用的文本（去掉 markdown 和 html 标签，保持语气自然）
        speech_clean = re.sub(r'#+|\*\*|\*|`|```[\s\S]*?```|<[^>]+>', '', body)
        speech_clean = f"接下来我们讲解：{title}。{speech_clean}".strip()
        
        # 画面展示文本：清洗 HTML 标签、Emoji 及特殊符号
        safe_title = sanitize_text_for_display(title)
        safe_body = sanitize_text_for_display(body)
        
        if speech_clean:
            formatted_sections.append((speech_clean, safe_title, safe_body))
            
    return formatted_sections

async def generate_audio_with_retry(text, output_audio_path, retries=3):
    for attempt in range(retries):
        try:
            communicate = edge_tts.Communicate(text, VOICE)
            await communicate.save(output_audio_path)
            if os.path.exists(output_audio_path) and os.path.getsize(output_audio_path) > 0:
                return True
        except Exception as e:
            print(f"  [重试 {attempt+1}/{retries}] 语音生成遇到波动: {e}")
            await asyncio.sleep(2)
        await asyncio.sleep(0.5)
    return False

def create_video_from_md(md_file_path):
    dir_name = os.path.dirname(md_file_path)
    base_name = os.path.splitext(os.path.basename(md_file_path))[0]
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_mp4 = os.path.join(dir_name, f"{base_name}_{timestamp}.mp4") if dir_name else f"{base_name}_{timestamp}.mp4"

    print("正在按极简 PPT 规范解析并清洗 Markdown（已适配 <br> 标签转换）...")
    sections = parse_markdown_by_chapters(md_file_path)
    
    if not sections:
        print("未提取到有效内容！")
        return

    clip_list = []
    print(f"共划分为 {len(sections)} 个 PPT 页面，开始高质量渲染...")

    for i, (speech_text, title_text, body_text) in enumerate(sections):
        print(f"正在处理第 {i+1}/{len(sections)} 页 PPT...")
        temp_audio = f"temp_sec_{i}.mp3"
        
        success = asyncio.run(generate_audio_with_retry(speech_text, temp_audio))
        if not success:
            print(f"警告: 第 {i+1} 页语音生成失败，跳过。")
            continue
            
        audio_clip = AudioFileClip(temp_audio)
        duration = max(audio_clip.duration, 2.5) 
        
        # 现代极简微乳白/浅灰色底板 (Slate-50: RGB 248, 250, 252)
        background = ColorClip(size=(WIDTH, HEIGHT), color=(248, 250, 252), duration=duration)
        
        clips_on_page = [background]

        try:
            # 顶部区域：增加左右边距，防止左右截断（两侧各留白 120px，总宽度 1280 - 240 = 1040）
            title_clip = TextClip(
                text=title_text if title_text else "核心内容",
                font="Hiragino Sans GB",
                font_size=34,
                color='#1E3A8A',
                size=(WIDTH - 240, 80),
                method='caption',
            ).with_duration(duration).with_position((120, 70))
            clips_on_page.append(title_clip)

            # 下方区域：同步调整宽度与左边距，确保正文两侧安全
            body_fontsize = 22 if len(body_text) > 250 else 26
            body_clip = TextClip(
                text=body_text if body_text else "（本章节暂无正文内容）",
                font="Hiragino Sans GB",
                font_size=body_fontsize,
                color='#334155',
                size=(WIDTH - 240, HEIGHT - 220),
                method='caption',
            ).with_duration(duration).with_position((120, 165))
            clips_on_page.append(body_clip)

        except Exception as e:
            print(f"警告: 页面文字排版失败，降级处理。错误: {e}")

        sub_video = CompositeVideoClip(clips_on_page)
        sub_video = sub_video.with_audio(audio_clip)
        clip_list.append(sub_video)
        
        import time
        time.sleep(0.3)

    if not clip_list:
        print("错误: 没有成功生成任何有效的视频页面！")
        return

    print("正在合成最终的极简 PPT 风格视频...")
    final_video = concatenate_videoclips(clip_list)
    
    print(f"正在导出最终视频到 {output_mp4}...")
    final_video.write_videofile(output_mp4, fps=FPS, codec="libx264", audio_codec="aac")
    
    for i in range(len(sections)):
        tmp = f"temp_sec_{i}.mp3"
        if os.path.exists(tmp):
            os.remove(tmp)
            
    print(f"🎉 极简 PPT 风格口播视频生成成功！已保存至: {output_mp4}")

if __name__ == "__main__":
    import sys
    target_md = sys.argv[1] if len(sys.argv) > 1 else "processed_input.md"
    create_video_from_md(target_md)