#!/usr/bin/env python3
"""
GIF Builder - Core module for assembling frames into GIFs optimized for Slack.

This module provides the main interface for creating GIFs from programmatically
generated frames, with automatic optimization for Slack's requirements.
"""

from pathlib import Path
from typing import Optional

import imageio.v3 as imageio
import numpy as np
from PIL import Image


class GIFBuilder:
    """Builder for creating optimized GIFs from frames."""

    def __init__(self, width: int = 480, height: int = 480, fps: int = 15):
        """
        Initialize GIF builder.

        Args:
            width: Frame width in pixels
            height: Frame height in pixels
            fps: Frames per second
        """
        self.width = width
        self.height = height
        self.fps = fps
        self.frames: list[np.ndarray] = []

    def add_frame(self, frame: np.ndarray | Image.Image):
        """
        Add a frame to the GIF.

        Args:
            frame: Frame as numpy array or PIL Image (will be converted to RGB)
        """
        if isinstance(frame, Image.Image):
            frame = np.array(frame.convert("RGB"))

        # Ensure frame is correct size
        if frame.shape[:2] != (self.height, self.width):
            pil_frame = Image.fromarray(frame)
            pil_frame = pil_frame.resize(
                (self.width, self.height), Image.Resampling.LANCZOS
            )
            frame = np.array(pil_frame)

        self.frames.append(frame)

    def add_frames(self, frames: list[np.ndarray | Image.Image]):
        """Add multiple frames at once."""
        for frame in frames:
            self.add_frame(frame)

    def optimize_colors(
        self,
        num_colors: int = 128,
        use_global_palette: bool = True,
        frames: Optional[list[np.ndarray]] = None,
    ) -> list[np.ndarray]:
        """
        Reduce colors in all frames using quantization.

        Args:
            num_colors: Target number of colors (8-256)
            use_global_palette: Use a single palette for all frames (better compression)
            frames: Frames to optimize (defaults to the builder's frames)

        Returns:
            List of color-optimized frames
        """
        frames = self.frames if frames is None else frames
        optimized = []

        if use_global_palette and len(frames) > 1:
            # Create a global palette from all frames
            # Sample frames to build palette
            sample_size = min(5, len(frames))
            sample_indices = [
                int(i * len(frames) / sample_size) for i in range(sample_size)
            ]
            sample_frames = [frames[i] for i in sample_indices]

            # Combine sample frames into a single image for palette generation
            # Flatten each frame to get all pixels, then stack them
            all_pixels = np.vstack(
                [f.reshape(-1, 3) for f in sample_frames]
            )  # (total_pixels, 3)

            # Create a properly-shaped RGB image from the pixel data
            # We'll make a roughly square image from all the pixels
            total_pixels = len(all_pixels)
            width = min(512, int(np.sqrt(total_pixels)))  # Reasonable width, max 512
            height = (total_pixels + width - 1) // width  # Ceiling division

            # Pad if necessary to fill the rectangle
            pixels_needed = width * height
            if pixels_needed > total_pixels:
                padding = np.zeros((pixels_needed - total_pixels, 3), dtype=np.uint8)
                all_pixels = np.vstack([all_pixels, padding])

            # Reshape to proper RGB image format (H, W, 3)
            img_array = (
                all_pixels[:pixels_needed].reshape(height, width, 3).astype(np.uint8)
            )
            combined_img = Image.fromarray(img_array, mode="RGB")

            # Generate global palette
            global_palette = combined_img.quantize(colors=num_colors, method=2)

            # Apply global palette to all frames
            for frame in frames:
                pil_frame = Image.fromarray(frame)
                quantized = pil_frame.quantize(palette=global_palette, dither=1)
                optimized.append(np.array(quantized.convert("RGB")))
        else:
            # Use per-frame quantization
            for frame in frames:
                pil_frame = Image.fromarray(frame)
                quantized = pil_frame.quantize(colors=num_colors, method=2, dither=1)
                optimized.append(np.array(quantized.convert("RGB")))

        return optimized

    @staticmethod
    def _deduplicate_frames(
        frames: list[np.ndarray], threshold: float = 0.9995
    ) -> tuple[list[np.ndarray], int]:
        """
        Remove duplicate or near-duplicate consecutive frames.

        Pure helper: returns the deduplicated frames and the number removed
        without mutating the input list.
        """
        if len(frames) < 2:
            return list(frames), 0

        deduplicated = [frames[0]]
        removed_count = 0

        for i in range(1, len(frames)):
            # Compare with previous frame
            prev_frame = np.array(deduplicated[-1], dtype=np.float32)
            curr_frame = np.array(frames[i], dtype=np.float32)

            # Calculate similarity (normalized)
            diff = np.abs(prev_frame - curr_frame)
            similarity = 1.0 - (np.mean(diff) / 255.0)

            # Keep frame if sufficiently different
            # High threshold (0.9995+) means only remove nearly identical frames
            if similarity < threshold:
                deduplicated.append(frames[i])
            else:
                removed_count += 1

        return deduplicated, removed_count

    def deduplicate_frames(self, threshold: float = 0.9995) -> int:
        """
        Remove duplicate or near-duplicate consecutive frames.

        Args:
            threshold: Similarity threshold (0.0-1.0). Higher = more strict (0.9995 = nearly identical).
                      Use 0.9995+ to preserve subtle animations, 0.98 for aggressive removal.

        Returns:
            Number of frames removed
        """
        self.frames, removed_count = self._deduplicate_frames(self.frames, threshold)
        return removed_count

    def save(
        self,
        output_path: str | Path,
        num_colors: int = 128,
        optimize_for_emoji: bool = False,
        remove_duplicates: bool = False,
    ) -> dict:
        """
        Save frames as optimized GIF for Slack.

        Args:
            output_path: Where to save the GIF
            num_colors: Number of colors to use (fewer = smaller file)
            optimize_for_emoji: If True, optimize for emoji size (128x128, fewer colors)
            remove_duplicates: If True, remove duplicate consecutive frames (opt-in)

        Returns:
            Dictionary with file info (path, size, dimensions, frame_count)
        """
        if not self.frames:
            raise ValueError("No frames to save. Add frames with add_frame() first.")

        output_path = Path(output_path)

        # Work on copies: saving must never change the builder's frames or
        # dimensions, so the same builder can be saved again with different
        # settings and produce the same output.
        frames = list(self.frames)
        width = self.width
        height = self.height

        # Remove duplicate frames to reduce file size
        if remove_duplicates:
            frames, removed = self._deduplicate_frames(frames, threshold=0.9995)
            if removed > 0:
                print(
                    f"  Removed {removed} nearly identical frames (preserved subtle animations)"
                )

        # Optimize for emoji if requested
        if optimize_for_emoji:
            if width > 128 or height > 128:
                print(f"  Resizing from {width}x{height} to 128x128 for emoji")
                width = 128
                height = 128
                # Resize all frames
                resized_frames = []
                for frame in frames:
                    pil_frame = Image.fromarray(frame)
                    pil_frame = pil_frame.resize((128, 128), Image.Resampling.LANCZOS)
                    resized_frames.append(np.array(pil_frame))
                frames = resized_frames
            num_colors = min(num_colors, 48)  # More aggressive color limit for emoji

            # More aggressive FPS reduction for emoji
            if len(frames) > 12:
                print(f"  Reducing frames from {len(frames)} to ~12 for emoji size")
                # Keep every nth frame to get close to 12 frames
                keep_every = max(1, len(frames) // 12)
                frames = [frames[i] for i in range(0, len(frames), keep_every)]

        # Optimize colors with global palette
        optimized_frames = self.optimize_colors(
            num_colors, use_global_palette=True, frames=frames
        )

        # Calculate frame duration in milliseconds
        frame_duration = 1000 / self.fps

        # Save GIF
        imageio.imwrite(
            output_path,
            optimized_frames,
            duration=frame_duration,
            loop=0,  # Infinite loop
        )

        # Get file info
        file_size_kb = output_path.stat().st_size / 1024
        file_size_mb = file_size_kb / 1024

        info = {
            "path": str(output_path),
            "size_kb": file_size_kb,
            "size_mb": file_size_mb,
            "dimensions": f"{width}x{height}",
            "frame_count": len(optimized_frames),
            "fps": self.fps,
            "duration_seconds": len(optimized_frames) / self.fps,
            "colors": num_colors,
        }

        # Print info
        print(f"\n✓ GIF created successfully!")
        print(f"  Path: {output_path}")
        print(f"  Size: {file_size_kb:.1f} KB ({file_size_mb:.2f} MB)")
        print(f"  Dimensions: {width}x{height}")
        print(f"  Frames: {len(optimized_frames)} @ {self.fps} fps")
        print(f"  Duration: {info['duration_seconds']:.1f}s")
        print(f"  Colors: {num_colors}")

        # Size info
        if optimize_for_emoji:
            print(f"  Optimized for emoji (128x128, reduced colors)")
        if file_size_mb > 1.0:
            print(f"\n  Note: Large file size ({file_size_kb:.1f} KB)")
            print("  Consider: fewer frames, smaller dimensions, or fewer colors")

        return info

    def clear(self):
        """Clear all frames (useful for creating multiple GIFs)."""
        self.frames = []
