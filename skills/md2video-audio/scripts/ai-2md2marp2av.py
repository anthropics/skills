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

def build_video_from_files(slide_md_path, script_md_path):
    if not os.path.exists(slide_md_path):
        raise FileNotFoundError(f"找不到画面 Markdown 文件: {slide_md_path}")
    if not os.path.exists(script_md_path):
        raise FileNotFoundError(f"找不到口播稿文件: {script_md_path}")
    
    # 获取输出路径（基于画面 md 所在的目录和名称）
    dir_name = os.path.dirname(slide_md_path)
    base_name = os.path.splitext(os.path.basename(slide_md_path))[0]
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_mp4 = os.path.join(dir_name, f"{base_name}_{timestamp}.mp4") if dir_name else f"{base_name}_{timestamp}.mp4"

    print(f"1. 正在调用 Marp 将画面 Markdown [{slide_md_path}] 渲染为 PPT 高清图片...")
    # 核心：让 Marp 针对画面 md 生成图片
    exit_code = os.system(f"marp '{slide_md_path}' --images png")
    if exit_code != 0:
        print("错误: Marp 渲染失败，请检查是否安装了 marp-cli 及谷歌浏览器内核。")
        return
    
    # 去画面 md 所在的目录下精准搜寻生成的 .png 图片
    target_dir = dir_name if dir_name else "."
    all_files = os.listdir(target_dir)
    
    slide_images = sorted([
        os.path.join(target_dir, f) for f in all_files 
        if f.startswith(base_name) and f.endswith(".png")
    ])

    if not slide_images:
        print(f"错误: 在目录 '{target_dir}' 下未找到 Marp 生成的幻灯片图片！")
        return      

    print(f"成功生成 {len(slide_images)} 页幻灯片画面。")

    # 2. 读取独立的【AI口播稿文件】
    with open(script_md_path, "r", encoding="utf-8") as f:
        script_content = f.read()
    
    # 假设口播稿也是按 --- 分割成对应的页数段落
    script_content_body = re.sub(r'^---[\s\S]*?---', '', script_content)
    speech_sections = [s.strip() for s in script_content_body.split("---") if s.strip()]

    clip_list = []
    temp_audio_files = []

    print("3. 正在读取独立口播稿，为每一页生成对应的 AI 语音并对齐画面...")
    # 按页数进行 zip 匹配（有多少张 PPT 图片就处理多少段口播）
    for i, img_file in enumerate(slide_images):
        page_num = i + 1
        print(f"正在处理第 {page_num}/{len(slide_images)} 页...")

        # 优先使用口播稿中对应的段落，如果口播稿段落不够则用默认提示
        if i < len(speech_sections):
            raw_speech = speech_sections[i]
        else:
            raw_speech = f"这是第 {page_num} 部分的内容。"

        # 清理口播稿中的 markdown 标记，让朗读更自然
        speech_clean = re.sub(r'#+|\*\*|\*|`|```[\s\S]*?```|<[^>]+>', '', raw_speech).strip()
        if not speech_clean:
            speech_clean = f"请看屏幕上的第 {page_num} 页展示。"

        audio_path = os.path.join(target_dir, f"temp_audio_{base_name}_{page_num}.mp3")
        temp_audio_files.append(audio_path)
        
        asyncio.run(generate_audio(speech_clean, audio_path))

        audio_clip = AudioFileClip(audio_path)
        duration = max(audio_clip.duration, 2.5) # 每页至少停留 2.5 秒

        # 用标准高颜值图片生成视频片段
        image_clip = ImageClip(img_file).with_duration(duration)
        image_clip = image_clip.with_audio(audio_clip)
        clip_list.append(image_clip)

    print("4. 正在无缝拼接最终视频...")
    final_video = concatenate_videoclips(clip_list)
    final_video.write_videofile(output_mp4, fps=FPS, codec="libx264", audio_codec="aac")

    # 清理临时文件（音频及图片）
    print("正在清理临时文件...")
    for f in temp_audio_files:
        if os.path.exists(f): os.remove(f)
    for f in slide_images:
        if os.path.exists(f): os.remove(f)

    print(f"🎉 完美！使用独立画面与独立口播稿合成的视频已生成: {output_mp4}")

if __name__ == "__main__":
    import sys
    # 接收两个参数：第一个是画面 md，第二个是口播稿 md
    # 例如：python marp_to_video.py slide.md script.md
    slide_file = sys.argv[1] if len(sys.argv) > 1 else "slide.md"
    script_file = sys.argv[2] if len(sys.argv) > 2 else "script.md"
    
    build_video_from_files(slide_file, script_file)