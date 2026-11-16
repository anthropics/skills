"""
FFprobe 封装 — 视频元信息提取
- 分辨率 / 帧率 / 时长 / 编码格式
- 关键帧提取（用于 AI 打标）
- 缩略图生成
"""

import json
import os
import subprocess
from pathlib import Path
from dataclasses import dataclass

from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd, get_ffprobe_cmd


@dataclass
class VideoInfo:
    """视频元信息"""
    file_path: str = ""
    duration_ms: int = 0
    duration_sec: float = 0.0
    fps: float = 30.0
    width: int = 1080
    height: int = 1920
    video_codec: str = ""
    audio_codec: str = ""
    has_audio: bool = False
    file_size_bytes: int = 0
    bitrate_kbps: int = 0
    rotation: int = 0           # 0/90/180/270 — 画面旋转角度

    @property
    def needs_rotation(self) -> bool:
        """是否需要旋转回正（横拍竖看等）"""
        return self.rotation in (90, 270)


class VideoProbe:
    """FFprobe 封装"""

    @staticmethod
    def probe(file_path: str) -> VideoInfo:
        """提取视频完整信息"""
        info = VideoInfo(file_path=file_path)
        info.file_size_bytes = os.path.getsize(file_path) if os.path.exists(file_path) else 0

        try:
            cmd = [
                get_ffprobe_cmd(), "-v", "quiet", "-print_format", "json",
                "-show_format", "-show_streams", file_path,
            ]
            result = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=30)
            data = json.loads(result.stdout)

            for stream in data.get("streams", []):
                if stream["codec_type"] == "video":
                    info.width = stream.get("width", 1080)
                    info.height = stream.get("height", 1920)
                    info.video_codec = stream.get("codec_name", "")
                    # 帧率可能是 "30000/1001" 这种格式
                    fps_str = stream.get("r_frame_rate", "30/1")
                    try:
                        num, den = fps_str.split("/")
                        info.fps = float(num) / float(den) if int(den) != 0 else 30.0
                    except (ValueError, ZeroDivisionError):
                        info.fps = 30.0
                    # 时长
                    dur = float(stream.get("duration", 0))
                    if dur > 0:
                        info.duration_sec = dur

                elif stream["codec_type"] == "audio":
                    info.audio_codec = stream.get("codec_name", "")
                    info.has_audio = True

                # 旋转角度（stream级别: side_data_list + tags）
                if info.rotation == 0:
                    for sd in stream.get("side_data_list", []) or []:
                        if sd.get("rotation") is not None:
                            info.rotation = int(sd["rotation"])
                            break
                if info.rotation == 0:
                    for tag_key in ("rotate", "rotation"):
                        val = stream.get("tags", {}).get(tag_key, "")
                        if val:
                            try:
                                info.rotation = int(val)
                                break
                            except (ValueError, TypeError):
                                pass

            # 旋转角度（format级别 — 部分设备存在这里）
            if info.rotation == 0:
                for tag_key in ("rotate", "rotation"):
                    val = (data.get("format", {}) or {}).get("tags", {}).get(tag_key, "")
                    if val:
                        try:
                            info.rotation = int(val)
                            break
                        except (ValueError, TypeError):
                            pass

            if fmt := data.get("format"):
                if info.duration_sec == 0:
                    info.duration_sec = float(fmt.get("duration", 0))
                info.bitrate_kbps = int(int(fmt.get("bit_rate", 0)) / 1000)

        except (subprocess.TimeoutExpired, json.JSONDecodeError, FileNotFoundError) as e:
            raise RuntimeError(f"FFprobe 解析失败: {file_path} — {e}") from e

        info.duration_ms = int(info.duration_sec * 1000)
        # ffprobe 的 rotation 是「画面已旋转角度」（display matrix，逆时针为负），
        # 而 detect/editor 的 transpose 用的是「回正角度」= 取反（互为逆变换）。
        # 实测：iPhone 竖拍报 -90 → 回正需顺时针 90°（transpose=1），故取反得 90。
        # 取反后归一化到 {0,90,180,270}，负值不再漏判成「无旋转」。
        info.rotation = (-info.rotation) % 360
        return info

    @staticmethod
    def extract_key_frames(
        file_path: str, output_dir: str, count: int = 5, quality: int = 2
    ) -> list[str]:
        """
        从视频中提取关键帧（用于 AI 视觉打标）
        返回提取的图片路径列表
        """
        os.makedirs(output_dir, exist_ok=True)
        base = Path(file_path).stem

        # 先获取时长
        try:
            info = VideoProbe.probe(file_path)
            duration = max(info.duration_sec, 1)
        except Exception:
            duration = 5  # fallback

        # 均匀间隔提取帧
        interval = max(1, int(duration / count))
        output_pattern = os.path.join(output_dir, f"{base}_frame_%02d.jpg")

        cmd = [
            get_ffmpeg_cmd(), "-y", "-v", "quiet",
            "-i", file_path,
            "-vf", f"fps=1/{interval}",
            "-vframes", str(count),
            "-q:v", str(quality),
            output_pattern,
        ]
        subprocess.run(cmd, capture_output=True, timeout=60)

        # 收集生成的文件
        frames = sorted(
            [os.path.join(output_dir, f) for f in os.listdir(output_dir)
             if f.startswith(f"{base}_frame_") and f.endswith(".jpg")]
        )
        return frames

    @staticmethod
    def generate_thumbnail(file_path: str, output_path: str, time_sec: float = 1.0) -> str:
        """生成视频缩略图（指定时间点的截图）"""
        os.makedirs(os.path.dirname(output_path), exist_ok=True)

        cmd = [
            get_ffmpeg_cmd(), "-y", "-v", "quiet",
            "-ss", str(time_sec),
            "-i", file_path,
            "-vframes", "1",
            "-q:v", "2",
            output_path,
        ]
        subprocess.run(cmd, capture_output=True, timeout=30)
        return output_path if os.path.exists(output_path) else ""
