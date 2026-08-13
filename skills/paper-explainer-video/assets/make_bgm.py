#!/usr/bin/env python3
"""
生成一段免版权的环境/电影感背景音乐(纯合成, 自己造的, 可商用)。

风格: 缓慢的 Am - F - C - G 和弦铺底(pad), 轻微失谐加宽 + Schroeder 混响,
适合沉思/略带忧虑的科普片。确定性输出, 每次一样。

用法:
    python make_bgm.py [时长秒] [输出路径]
    例:  ~/llm_mc_venv/bin/python make_bgm.py 210 media/bgm.wav
"""
import sys
import numpy as np
from scipy.signal import lfilter
from scipy.io import wavfile

SR = 44100


def note(freq, dur, sr=SR):
    """一个柔和的 pad 音: 基频 + 泛音 + 轻微失谐合唱, 带缓入缓出包络。"""
    n = int(dur * sr)
    t = np.arange(n) / sr
    wave = np.zeros(n)
    # 基频 + 2、3 泛音(递减), 每个都做 ±0.3% 失谐两副本(合唱变厚)
    for harm, amp in [(1, 1.0), (2, 0.45), (3, 0.22), (4, 0.1)]:
        for detune in (0.997, 1.0, 1.003):
            wave += amp * np.sin(2 * np.pi * freq * harm * detune * t)
    wave /= 3 * 1.77
    # 慢起慢落包络(像拉弦/吹奏的 pad)
    atk = int(0.9 * sr)
    rel = int(1.4 * sr)
    env = np.ones(n)
    env[:atk] = np.linspace(0, 1, atk) ** 1.5
    env[-rel:] = np.linspace(1, 0, rel) ** 1.5
    return wave * env


def chord(freqs, dur):
    sig = np.zeros(int(dur * SR))
    for f in freqs:
        sig += note(f, dur)
    # 加一个低八度根音垫底, 更温暖
    sig += 0.5 * note(freqs[0] / 2, dur)
    return sig / (len(freqs) + 0.5)


def comb(x, delay_ms, g):
    D = int(delay_ms / 1000 * SR)
    a = np.zeros(D + 1); a[0] = 1; a[D] = -g
    return lfilter([1.0], a, x)


def allpass(x, delay_ms, g):
    D = int(delay_ms / 1000 * SR)
    b = np.zeros(D + 1); b[0] = -g; b[D] = 1.0
    a = np.zeros(D + 1); a[0] = 1.0; a[D] = -g
    return lfilter(b, a, x)


def reverb(x, wet=0.25):
    """简易 Schroeder 混响: 4 并联梳状 + 2 串联全通。"""
    combs = sum(comb(x, d, g) for d, g in
                [(29.7, 0.78), (37.1, 0.74), (41.1, 0.72), (43.7, 0.70)]) / 4
    ap = allpass(combs, 5.0, 0.7)
    ap = allpass(ap, 1.7, 0.7)
    return (1 - wet) * x + wet * ap


def one_pole_lowpass(x, cutoff=2200):
    a = np.exp(-2 * np.pi * cutoff / SR)
    return lfilter([1 - a], [1, -a], x)


def build(total_dur, out_path):
    # Am - F - C - G  (A小调里很常见、情绪饱满的进行)
    progression = [
        [220.00, 261.63, 329.63],            # Am: A C E
        [174.61, 220.00, 261.63],            # F:  F A C
        [261.63, 329.63, 392.00],            # C:  C E G
        [196.00, 246.94, 293.66],            # G:  G B D
    ]
    chord_dur = 7.0
    xfade = 2.0  # 和弦之间交叠, 平滑过渡
    step = chord_dur - xfade

    # 先拼出一段循环, 再循环到目标时长
    loop = np.zeros(int((len(progression) * step + xfade) * SR))
    pos = 0
    for freqs in progression:
        c = chord(freqs, chord_dur)
        end = pos + len(c)
        if end > len(loop):
            loop = np.concatenate([loop, np.zeros(end - len(loop))])
        loop[pos:end] += c
        pos += int(step * SR)
    loop = loop[: int(len(progression) * step * SR)]  # 去掉尾巴, 便于无缝循环

    need = int(total_dur * SR)
    reps = int(np.ceil(need / len(loop)))
    music = np.tile(loop, reps)[:need]

    music = one_pole_lowpass(music, 2200)   # 变暖
    music = reverb(music, wet=0.28)          # 空间感
    # 整体淡入淡出
    fi = int(3 * SR); fo = int(4 * SR)
    music[:fi] *= np.linspace(0, 1, fi)
    music[-fo:] *= np.linspace(1, 0, fo)
    # 归一到 -1.5 dBFS
    peak = np.max(np.abs(music)) + 1e-9
    music = music / peak * 10 ** (-1.5 / 20)

    # 立体声: 左右各加一点点延迟差, 增加宽度
    d = int(0.012 * SR)
    left = music
    right = np.concatenate([np.zeros(d), music])[: len(music)]
    stereo = np.stack([left, right], axis=1)
    wavfile.write(out_path, SR, (stereo * 32767).astype(np.int16))
    print(f"✅ BGM: {out_path}  {total_dur:.0f}s  (Am-F-C-G ambient pad)")


if __name__ == "__main__":
    dur = float(sys.argv[1]) if len(sys.argv) > 1 else 210
    out = sys.argv[2] if len(sys.argv) > 2 else "media/bgm.wav"
    build(dur, out)
