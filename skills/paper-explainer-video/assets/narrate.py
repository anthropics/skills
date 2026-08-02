#!/usr/bin/env python3
"""
通用配音脚本(edge-tts 中文 TTS)。读 narration_data + pipeline_config。
每个场景旁白合成 media/vo/sceneN.mp3, 句间插停顿, 并打印各段时长便于核对。

用法:  ~/llm_mc_venv/bin/python narrate.py
       ~/llm_mc_venv/bin/python narrate.py --voice zh-CN-YunyangNeural --pitch +0Hz
"""
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from narration_data import NARRATION, SCENE_RATES
import pipeline_config as cfg

ROOT = Path(__file__).parent
VO_DIR = ROOT / "media" / "vo"
PAUSE = "[[slnc 300]]"  # 句间停顿(edge-tts 不识别, 仅占位; 实际停顿靠标点)


def probe(path):
    return float(subprocess.check_output(
        ["ffprobe", "-v", "error", "-show_entries", "format=duration",
         "-of", "csv=p=0", str(path)]).strip())


def synth(i, sentences, voice, rate, pitch):
    """合成一段配音(供并行调用)。返回 (序号, 文本)。"""
    text = "".join(sentences)
    out = VO_DIR / f"scene{i}.mp3"
    scene_rate = SCENE_RATES.get(i, rate)
    subprocess.run(
        [sys.executable, "-m", "edge_tts", "--voice", voice,
         "--rate", scene_rate, "--pitch", pitch,
         "--text", text, "--write-media", str(out)], check=True)
    return i, text


def main(voice, rate, pitch):
    VO_DIR.mkdir(parents=True, exist_ok=True)
    print(f"嗓音 {voice}  语速 {rate}  音高 {pitch}  (并行合成)\n")
    jobs = [(i, s) for i, s in enumerate(NARRATION) if s]   # 跳过静音场景
    # 各段相互独立, 并行调 edge-tts 省网络往返
    with ThreadPoolExecutor(max_workers=min(6, len(jobs))) as ex:
        list(ex.map(lambda a: synth(a[0], a[1], voice, rate, pitch), jobs))
    total = 0.0
    for i, sentences in jobs:
        d = probe(VO_DIR / f"scene{i}.mp3"); total += d
        tag = f"  (语速 {SCENE_RATES[i]})" if i in SCENE_RATES else ""
        print(f"scene{i}  {d:5.1f}s   {len(''.join(sentences))}字{tag}")
    print(f"\n配音总长 {total:.1f}s → {VO_DIR}/")
    print("⚠️ 核对: 每段配音必须 ≤ 对应场景画面时长, 否则结尾被切(超了就加进 SCENE_RATES)。")


if __name__ == "__main__":
    voice = cfg.VOICE
    pitch = cfg.PITCH
    rate = "+0%"
    a = sys.argv
    if "--voice" in a: voice = a[a.index("--voice") + 1]
    if "--rate" in a:  rate = a[a.index("--rate") + 1]
    if "--pitch" in a: pitch = a[a.index("--pitch") + 1]
    main(voice, rate, pitch)
