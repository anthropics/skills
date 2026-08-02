"""
Per-paper config. build_video.py / render_avatar.py / narrate.py all read it.
(The values below are for the "model collapse" example; change them per paper.)
"""

# Scene class names; order = video order. Must match the classes in scenes.py
# and narration_data.NARRATION one-to-one.
SCENES = [
    "IntroScene",
    "HookScene",
    "GaussianCollapse",
    "TailCutoff",
    "GMMMerge",
    "LLMTextScene",
    "ConclusionScene",
    "ReferencesScene",
]

OUTPUT_BASENAME = "ModelCollapse_Explainer"  # final-file name prefix
QUALITY = "1080p60"
XFADE = 0.6                            # cross-fade seconds between scenes

# Voiceover (edge-tts en-US voice). See SKILL.md for the full list.
VOICE = "en-US-AriaNeural"            # clear, professional female; others: JennyNeural / GuyNeural / en-GB-SoniaNeural
PITCH = "+0Hz"                        # natural; nudge a few Hz to taste

# Video encode tiers (speed vs quality). Set env MC_FAST=1 to use the preview tier.
#   preview: h264_videotoolbox = M-series hardware encode, 5-10x faster than libx264 (slightly lower quality, fine for iteration)
#   final:   libx264 crf18 medium = high quality
ENCODE_FINAL = ["-c:v", "libx264", "-preset", "medium", "-pix_fmt", "yuv420p", "-crf", "18"]
ENCODE_PREVIEW = ["-c:v", "h264_videotoolbox", "-b:v", "8M", "-pix_fmt", "yuv420p"]

# Live2D virtual host
USE_AVATAR = True       # FAST preview can set False, saves 3-5 min (skips render_avatar; final = base_video)
L2D_MODEL = "/tmp/live2dpy/Resources/v3/llny/llny.model3.json"
AVATAR = dict(
    # Render canvas: slightly larger than display (~1.3x) for anti-alias oversampling; don't go too
    # big (GPU->CPU readback is expensive).
    # ⚠️ If you change W/H, keep the aspect ratio ≈ original (380/388 ≈ 0.979), or scale/offset framing breaks.
    W=380, H=388,        # display ~300 wide, this is ~1.27x oversample
    scale=1.55,          # camera zoom
    offset_x=-0.3,       # center the face horizontally (model defaults to the right — must adjust)
    offset_y=-1.55,      # vertical (show the whole face + top of head)
    fps=30,
    sway=4.0,            # head-sway amplitude (degrees); not too large or it sways out of frame
    crop=0.62,           # keep top fraction (crops the chest watermark)
    disp_w=300,          # corner display width (px)
    margin_x=200,        # distance from the right edge (larger = further left)
    margin_y=10,         # distance from the bottom edge
)
