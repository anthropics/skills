import os
import asyncio
import re
from datetime import datetime
import edge_tts
from moviepy import ImageClip, AudioFileClip, concatenate_videoclips

VOICE = "zh-CN-XiaoxiaoNeural"
FPS = 24

async def generate_audio(text, output_path):
    communicate = edge_tts.Communicate(text, VOICE)
    await communicate.save(output_path)

def build_video_from_marp_images(md_file_path):
    if not os.path.exists(md_file_path):
        raise FileNotFoundError(f"找不到文件: {md_file_path}")
    
    # 获取输入 md 的绝对或相对路径信息
    dir_name = os.path.dirname(md_file_path)
    base_name = os.path.splitext(os.path.basename(md_file_path))[0]
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_mp4 = os.path.join(dir_name, f"{base_name}_{timestamp}.mp4") if dir_name else f"{base_name}_{timestamp}.mp4"

    print("1. 正在调用 Marp 将 Markdown 渲染为 PPT 高清图片...")
    # --images png 会把每一页切成独立的高清 PNG 图片
    exit_code = os.system(f"marp '{md_file_path}' --images png")
    if exit_code != 0:
        print("错误: Marp 渲染失败，请检查是否安装了 marp-cli 及谷歌浏览器内核。")
        return
    
    # 去 md 所在的目录下精准搜寻生成的 .png 图片
    target_dir = dir_name if dir_name else "."
    all_files = os.listdir(target_dir)
    
    # 筛选出以该 markdown 文件名为前缀且以 .png 结尾的图片
    slide_images = sorted([
        os.path.join(target_dir, f) for f in all_files 
        if f.startswith(base_name) and f.endswith(".png")
    ])

    if not slide_images:
        print(f"错误: 在目录 '{target_dir}' 下未找到 Marp 生成的幻灯片图片！")
        return      

    print(f"成功生成 {len(slide_images)} 页幻灯片画面。")

    # 简单提取每一页的文字用于生成对应语音（这里读取 md 按 --- 分割）
    with open(md_file_path, "r", encoding="utf-8") as f:
        content = f.read()
    
    # 过滤掉 frontmatter
    content_body = re.sub(r'^---[\s\S]*?---', '', content)
    slides_text = [s.strip() for s in content_body.split("---") if s.strip()]

    clip_list = []
    temp_audio_files = []

    print("2. 正在为每一页生成对应的 AI 口播语音并对齐画面...")
    for i, img_file in enumerate(slide_images):
        page_num = i + 1
        print(f"正在处理第 {page_num}/{len(slide_images)} 页...")

        # 获取当前页对应的文本，如果没有配对文字则用默认提示
        raw_text = slides_text[i] if i < len(slides_text) else f"这是第 {page_num} 页"
        speech_clean = re.sub(r'#+|\*\*|\*|`|```[\s\S]*?```|<[^>]+>', '', raw_text)
        speech_text = f"接下来我们看第 {page_num} 部分。{speech_clean}".strip()

        audio_path = f"temp_audio_{page_num}.mp3"
        temp_audio_files.append(audio_path)
        
        asyncio.run(generate_audio(speech_text, audio_path))

        audio_clip = AudioFileClip(audio_path)
        duration = max(audio_clip.duration, 2.5) # 每页至少停留 2.5 秒

        # 用标准高颜值图片生成视频片段
        image_clip = ImageClip(img_file).with_duration(duration)
        image_clip = image_clip.with_audio(audio_clip)
        clip_list.append(image_clip)

    print("3. 正在无缝拼接最终视频...")
    final_video = concatenate_videoclips(clip_list)
    final_video.write_videofile(output_mp4, fps=FPS, codec="libx264", audio_codec="aac")

    # 清理临时文件（音频及图片）
    for f in temp_audio_files:
        if os.path.exists(f): os.remove(f)
    for f in slide_images:
        if os.path.exists(f): os.remove(f)

    print(f"🎉 完美！高级 PPT 风格视频已生成: {output_mp4}")

if __name__ == "__main__":
    import sys
    target_md = sys.argv[1] if len(sys.argv) > 1 else "processed_input.md"
    build_video_from_marp_images(target_md)