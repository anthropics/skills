import os
import time
import logging
import tempfile
import textwrap
import numpy as np
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont
from gtts import gTTS
try:
    # moviepy v2
    from moviepy import ImageClip, AudioFileClip, concatenate_videoclips, CompositeVideoClip
except ImportError:
    # moviepy v1 fallback
    from moviepy.editor import ImageClip, AudioFileClip, concatenate_videoclips, CompositeVideoClip

logger = logging.getLogger(__name__)

# Colour palettes per niche
PALETTES = {
    "tech":       {"bg_start": (10, 10, 30),  "bg_end": (25, 30, 80),  "accent": (100, 149, 237), "text": (230, 230, 255)},
    "finance":    {"bg_start": (8,  28, 18),  "bg_end": (18, 58, 38),  "accent": (212, 175, 55),  "text": (230, 255, 230)},
    "motivation": {"bg_start": (38, 18, 8),   "bg_end": (88, 44, 18),  "accent": (255, 140, 0),   "text": (255, 240, 220)},
    "health":     {"bg_start": (8,  30, 24),  "bg_end": (18, 68, 52),  "accent": (0,  200, 150),  "text": (220, 255, 240)},
    "ai":         {"bg_start": (18, 8,  38),  "bg_end": (48, 18, 78),  "accent": (180, 100, 255), "text": (240, 220, 255)},
    "science":    {"bg_start": (8,  18, 38),  "bg_end": (18, 38, 78),  "accent": (100, 200, 255), "text": (220, 235, 255)},
    "history":    {"bg_start": (28, 18, 8),   "bg_end": (68, 48, 22),  "accent": (210, 180, 140), "text": (255, 245, 230)},
    "news":       {"bg_start": (22, 22, 22),  "bg_end": (50, 50, 55),  "accent": (220, 60,  60),  "text": (240, 240, 240)},
    "default":    {"bg_start": (20, 20, 20),  "bg_end": (50, 50, 50),  "accent": (200, 200, 200), "text": (240, 240, 240)},
}

# YouTube: 16:9  |  TikTok: 9:16
SIZES = {
    "youtube": (1920, 1080),
    "tiktok":  (1080, 1920),
}


class VideoCreator:
    def __init__(self, config):
        self.config = config
        self.font_path = self._find_font()
        os.makedirs(config.OUTPUT_DIR, exist_ok=True)

    # ── Public ────────────────────────────────────────────────────────────────

    def create_video(self, script_data: dict, niche_name: str, platform: str = "youtube") -> str | None:
        size = SIZES.get(platform, SIZES["youtube"])
        slides = script_data.get("slides", [])
        narration = script_data.get("narration", "")
        title = script_data.get("title", "Video")
        palette = PALETTES.get(niche_name, PALETTES["default"])

        if not slides or not narration:
            logger.error("No slides or narration in script data")
            return None

        # 1. TTS audio
        logger.info("Generating TTS audio …")
        audio_path = self._tts(narration)
        if not audio_path:
            return None

        audio_clip = AudioFileClip(audio_path)
        total_dur = audio_clip.duration
        slide_dur = total_dur / len(slides)

        # 2. Build image clips
        logger.info("Rendering %d slides …", len(slides))
        clips = []
        for i, slide in enumerate(slides):
            img_arr = self._render_slide(
                slide_title=slide.get("title", title),
                slide_content=slide.get("content", ""),
                palette=palette,
                size=size,
                slide_num=i + 1,
                total=len(slides),
                platform=platform,
            )
            clips.append(ImageClip(img_arr, duration=slide_dur))

        # 3. Concatenate + audio
        try:
            video = concatenate_videoclips(clips, method="compose")
        except TypeError:
            video = concatenate_videoclips(clips)

        try:
            video = video.with_audio(audio_clip)   # moviepy v2
        except AttributeError:
            video = video.set_audio(audio_clip)    # moviepy v1

        # 4. Export
        ts = int(time.time())
        out_file = os.path.join(self.config.OUTPUT_DIR, f"{niche_name}_{platform}_{ts}.mp4")
        logger.info("Exporting → %s", out_file)
        write_kwargs = dict(fps=24, codec="libx264", audio_codec="aac", logger=None)
        try:
            video.write_videofile(out_file, **write_kwargs)
        except TypeError:
            write_kwargs.pop("logger", None)
            video.write_videofile(out_file, **write_kwargs)

        # Cleanup
        try:
            os.unlink(audio_path)
        except OSError:
            pass

        return out_file

    # ── Slide rendering ───────────────────────────────────────────────────────

    def _render_slide(
        self,
        slide_title: str,
        slide_content: str,
        palette: dict,
        size: tuple[int, int],
        slide_num: int,
        total: int,
        platform: str,
    ) -> np.ndarray:
        w, h = size
        img = self._gradient(size, palette["bg_start"], palette["bg_end"])
        draw = ImageDraw.Draw(img)
        accent = palette["accent"]
        text_color = palette["text"]

        # Top accent bar
        draw.rectangle([0, 0, w, max(6, h // 120)], fill=accent)

        if platform == "youtube":
            self._draw_youtube_layout(draw, slide_title, slide_content, text_color, accent, w, h)
        else:
            self._draw_tiktok_layout(draw, slide_title, slide_content, text_color, accent, w, h)

        # Progress bar
        bar_h = max(4, h // 200)
        bar_y = h - bar_h - max(8, h // 80)
        progress_w = int(w * slide_num / total)
        draw.rectangle([0, bar_y, w, bar_y + bar_h], fill=(60, 60, 60))
        draw.rectangle([0, bar_y, progress_w, bar_y + bar_h], fill=accent)

        return np.array(img)

    def _draw_youtube_layout(self, draw, title, content, text_color, accent, w, h):
        # Title centered at 15% height
        t_font = self._font(int(h * 0.052))
        c_font = self._font(int(h * 0.033))
        self._draw_centered_wrapped(draw, title, w // 2, int(h * 0.14), t_font, text_color, int(w * 0.88))
        # Accent divider
        dy = int(h * 0.30)
        draw.rectangle([int(w * 0.15), dy, int(w * 0.85), dy + 3], fill=accent)
        # Content
        self._draw_centered_wrapped(draw, content, w // 2, int(h * 0.55), c_font, text_color, int(w * 0.82))

    def _draw_tiktok_layout(self, draw, title, content, text_color, accent, w, h):
        t_font = self._font(int(h * 0.038))
        c_font = self._font(int(h * 0.026))
        self._draw_centered_wrapped(draw, title, w // 2, int(h * 0.12), t_font, text_color, int(w * 0.90))
        dy = int(h * 0.24)
        draw.rectangle([int(w * 0.10), dy, int(w * 0.90), dy + 3], fill=accent)
        self._draw_centered_wrapped(draw, content, w // 2, int(h * 0.50), c_font, text_color, int(w * 0.86))

    # ── Helpers ───────────────────────────────────────────────────────────────

    def _gradient(self, size: tuple[int, int], start: tuple, end: tuple) -> Image.Image:
        w, h = size
        img = Image.new("RGB", size)
        draw = ImageDraw.Draw(img)
        for y in range(h):
            ratio = y / h
            r = int(start[0] + (end[0] - start[0]) * ratio)
            g = int(start[1] + (end[1] - start[1]) * ratio)
            b = int(start[2] + (end[2] - start[2]) * ratio)
            draw.line([(0, y), (w, y)], fill=(r, g, b))
        return img

    def _font(self, size: int) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
        if self.font_path:
            try:
                return ImageFont.truetype(self.font_path, size)
            except Exception:
                pass
        return ImageFont.load_default()

    def _draw_centered_wrapped(
        self,
        draw: ImageDraw.ImageDraw,
        text: str,
        cx: int,
        cy: int,
        font,
        color: tuple,
        max_w: int,
    ):
        """Wrap text to max_w pixels and draw it centered around (cx, cy)."""
        words = text.split()
        lines: list[str] = []
        current: list[str] = []

        for word in words:
            test = " ".join(current + [word])
            try:
                bbox = draw.textbbox((0, 0), test, font=font)
                tw = bbox[2] - bbox[0]
            except AttributeError:
                tw = len(test) * 9

            if tw <= max_w:
                current.append(word)
            else:
                if current:
                    lines.append(" ".join(current))
                current = [word]
        if current:
            lines.append(" ".join(current))

        try:
            bbox = draw.textbbox((0, 0), "Ag", font=font)
            line_h = int((bbox[3] - bbox[1]) * 1.5)
        except AttributeError:
            line_h = 28

        total_h = len(lines) * line_h
        y0 = cy - total_h // 2

        for i, line in enumerate(lines):
            try:
                bbox = draw.textbbox((0, 0), line, font=font)
                tw = bbox[2] - bbox[0]
            except AttributeError:
                tw = len(line) * 9
            x = cx - tw // 2
            draw.text((x, y0 + i * line_h), line, font=font, fill=color)

    def _tts(self, text: str) -> str | None:
        # Try gTTS (online) first
        try:
            tts = gTTS(text=text, lang=self.config.TTS_LANGUAGE, slow=False)
            path = tempfile.mktemp(suffix=".mp3")
            tts.save(path)
            return path
        except Exception as exc:
            logger.warning("gTTS failed (%s) — trying offline TTS …", exc)

        # Fall back to pyttsx3 (offline, requires espeak-ng)
        try:
            import pyttsx3
            engine = pyttsx3.init()
            path = tempfile.mktemp(suffix=".wav")
            engine.save_to_file(text, path)
            engine.runAndWait()
            engine.stop()
            if os.path.exists(path) and os.path.getsize(path) > 0:
                return path
        except Exception as exc:
            logger.warning("pyttsx3 failed (%s) — generating silent audio …", exc)

        # Last resort: generate silence so video still renders
        return self._silent_audio(len(text.split()) * 0.4)  # ~0.4s per word

    def _silent_audio(self, duration_seconds: float) -> str:
        """Create a silent WAV file of the given duration."""
        import wave, struct, math
        path = tempfile.mktemp(suffix=".wav")
        sample_rate = 22050
        n_samples = int(sample_rate * duration_seconds)
        with wave.open(path, "w") as wf:
            wf.setnchannels(1)
            wf.setsampwidth(2)
            wf.setframerate(sample_rate)
            wf.writeframes(struct.pack("<" + "h" * n_samples, *([0] * n_samples)))
        return path

    def _find_font(self) -> str | None:
        candidates = [
            "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
            "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
            "/usr/share/fonts/truetype/freefont/FreeSansBold.ttf",
            "/usr/share/fonts/truetype/ubuntu/Ubuntu-B.ttf",
            "/System/Library/Fonts/Helvetica.ttc",
            os.path.join(os.path.dirname(__file__), "../../assets/fonts/Roboto-Bold.ttf"),
        ]
        for p in candidates:
            if os.path.exists(p):
                logger.debug("Using font: %s", p)
                return p
        logger.warning("No TTF font found; using PIL default font (text may look small)")
        return None
