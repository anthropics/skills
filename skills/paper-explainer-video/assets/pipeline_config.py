"""
每篇论文要改的配置。build_video.py / render_avatar.py / narrate.py 都读它。
(下面的值是"模型崩溃"那篇的，换论文时按需改。)
"""

# 场景类名，顺序 = 视频顺序，必须和 scenes.py 里的类、narration_data.NARRATION 一一对应
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

OUTPUT_BASENAME = "模型崩溃_科普视频"  # 成片文件名前缀
QUALITY = "1080p60"
XFADE = 0.6                            # 场景间交叉转场秒数

# 配音(edge-tts zh-CN 嗓音)
VOICE = "zh-CN-XiaoyiNeural"           # 卡通/活泼(萝莉感); 其它见 SKILL.md
PITCH = "+20Hz"                        # 调高更萌; "+0Hz" 不变

# 视频编码档(性能↔质量)。脚本里设环境变量 MC_FAST=1 走预览快档。
#   预览: h264_videotoolbox = M 系列硬编, 比 libx264 快 5-10x(画质略低, 迭代足够)
#   成片: libx264 crf18 medium = 高质量
ENCODE_FINAL = ["-c:v", "libx264", "-preset", "medium", "-pix_fmt", "yuv420p", "-crf", "18"]
ENCODE_PREVIEW = ["-c:v", "h264_videotoolbox", "-b:v", "8M", "-pix_fmt", "yuv420p"]

# Live2D 虚拟主播
USE_AVATAR = True       # FAST 预览可设 False, 省 3-5 分钟(跳过 render_avatar, 成片用 base_video)
L2D_MODEL = "/tmp/live2dpy/Resources/v3/llny/llny.model3.json"
AVATAR = dict(
    # 渲染画框: 比显示尺寸略大(~1.3x)留点过采样抗锯齿即可, 别太大(回读GPU→CPU很贵)。
    # ⚠️ 改 W/H 必须保持宽高比≈原值(460/470≈0.979), 否则 scale/offset 构图全乱。
    W=312, H=319,        # 显示 300 宽, ~1.04x 过采样(角落小图肉眼无锯齿差, 回读像素再省~32%)
    scale=1.55,          # 摄像机缩放
    offset_x=-0.3,       # 水平居中脸(模型默认偏右，务必调)
    offset_y=-1.55,      # 垂直(露出整张脸+头顶)
    fps=15,              # 主播帧率: 二次元本就"一拍二"(12fps), 15fps 更有动画感且回读减半(口型包络自动跟随)
    sway=4.0,            # 摆头幅度(度)，别太大否则摆出框
    crop=0.62,           # 取上百分比(裁掉胸口水印)
    crop_left=0.35,      # 裁掉左侧百分比: llny 脸左侧另有材质水印(实测占 10.7%-29.3%,
                         # 脸从 40.3% 才开始) → 裁 35% 去干净且不碰脸; 换模型需重测
    disp_w=300,          # 角落显示宽度(px)
    margin_x=200,        # 距右边(越大越靠左)
    margin_y=10,         # 距底边
)
