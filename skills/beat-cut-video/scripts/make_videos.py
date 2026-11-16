# -*- coding: utf-8 -*-
"""AdFlow 无头出片 — 文案进，成片出（不经图形界面，不调任何大模型 API）。

用法示例:
    python make_videos.py --text-file 文案.txt --product-name 保温杯 --count 3
    python make_videos.py --text "第一句钩子。第二句卖点。" --platform douyin
    python make_videos.py --text-file 文案.txt --voice zh-CN-YunxiNeural --rate 1.1

常用参数:
    --text-file / --text  文案（二选一，必填）
    --product-name  产品名（默认「我的产品」，只用于内部记录和命名）
    --category      产品类目（如 美妆/家居/食品，影响自动时长）
    --count         出几条（默认 3，同一文案不同配音和画面组合）
    --platform      douyin/xiaohongshu/kuaishou/shipinhao/ocean_engine
    --voice         指定音色（空=自动男女交替；edge 音色见 references/tts-setup.md）
    --rate          语速倍率如 0.9 / 1.1（0=默认）
    --aspect        portrait 竖屏（默认）/ landscape 横屏
    --duration      目标时长秒（0=引擎自动定）
    --prefix        视频文件名前缀
    --bgm           指定背景音乐文件（空=自动轮换 bgm_library；没有就不配乐）
"""
import argparse
import os
import sys
import traceback

sys.stdout.reconfigure(errors="replace")

SKILL_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENGINE = os.path.join(SKILL_ROOT, "engine")
sys.path.insert(0, ENGINE)


def read_text(args) -> str:
    if args.text_file:
        if not os.path.isfile(args.text_file):
            print("[X] 找不到文案文件: %s" % args.text_file)
            sys.exit(1)
        with open(args.text_file, encoding="utf-8") as f:
            return f.read().strip()
    if args.text:
        return args.text.strip()
    print("[X] 没给文案：用 --text-file 文件 或 --text \"文案\" 传入")
    sys.exit(1)


def main():
    ap = argparse.ArgumentParser(description="AdFlow 无头出片")
    ap.add_argument("--text-file", default="")
    ap.add_argument("--text", default="")
    ap.add_argument("--product-name", default="我的产品")
    ap.add_argument("--category", default="")
    ap.add_argument("--count", type=int, default=3)
    ap.add_argument("--platform", default="ocean_engine",
                    choices=["douyin", "xiaohongshu", "kuaishou",
                             "shipinhao", "ocean_engine"])
    ap.add_argument("--voice", default="")
    ap.add_argument("--rate", type=float, default=0.0)
    ap.add_argument("--aspect", default="portrait",
                    choices=["portrait", "landscape"])
    ap.add_argument("--duration", type=int, default=0, help="目标时长秒，0=自动")
    ap.add_argument("--prefix", default="")
    ap.add_argument("--bgm", default="")
    args = ap.parse_args()

    text = read_text(args)
    if len(text) < 5:
        print("[X] 文案太短（至少一两句完整的话）")
        sys.exit(1)

    try:
        from adflow.agents.pipeline import AdPipeline
        from adflow.models import ProductProfile
        from adflow.db.material_repo import MaterialRepo
        from adflow.config_loader import config
    except Exception as e:
        print("[X] 引擎依赖没装好（%s）" % e)
        print("先跑: python setup_env.py --all ，再 python check_env.py 复查")
        sys.exit(1)

    # 前置检查：素材库必须有货
    repo = MaterialRepo()
    n_total = repo.count()
    if n_total == 0:
        print("[X] 素材库是空的，没法剪片")
        print("先跑: python import_materials.py --dir \"你的视频素材文件夹\"")
        sys.exit(1)
    print("素材库: %d 条素材" % n_total)

    product = ProductProfile(
        name=args.product_name,
        category=args.category,
        key_selling_points="[]",
        target_audience="",
        pain_points="[]",
        brand_tone="亲切口语",
    )

    pipeline = AdPipeline()

    def on_progress(msg):
        print("  | " + str(msg))

    print("开始出片（%d 条，平台 %s）...\n" % (args.count, args.platform))
    try:
        result = pipeline.run(
            product=product,
            platform=args.platform,
            target_duration_ms=args.duration * 1000 if args.duration > 0 else 0,
            variant_count=max(1, args.count),
            custom_text=text,
            name_prefix=args.prefix,
            aspect_ratio=args.aspect,
            voice_override=args.voice,
            speech_rate_override=args.rate,
            bgm_file_override=args.bgm,
            progress_callback=on_progress,
        )
    except KeyboardInterrupt:
        print("\n已手动停止")
        sys.exit(130)
    except Exception:
        print("\n[X] 出片失败，完整报错如下:\n")
        traceback.print_exc()
        print("\n常见原因对照（references/engine-reference.md 有详细版）:")
        print("  * 没找到 ffmpeg      -> python setup_env.py --ffmpeg")
        print("  * 配音超时/报网络错   -> Edge 免费配音要联网；换网络或稍后重试")
        print("  * No module named xx -> python setup_env.py --deps")
        sys.exit(1)

    if getattr(result, "cancelled", False):
        print("任务已取消")
        sys.exit(0)

    print("\n" + "=" * 46)
    print("出片完成")
    print("=" * 46)
    ok_count = 0
    for i, v in enumerate(result.variants, 1):
        path = v.output_file or "(没生成)"
        passed = getattr(v, "compliance_check_passed", 0)
        flag = "合规检查通过" if passed else "合规检查未过(见日志)"
        if passed:
            ok_count += 1
        print("[%d] %s\n     %s" % (i, path, flag))
    print("\n成片文件夹: " + config.output_dir)
    print("共 %d 条" % len(result.variants))
    if not result.variants:
        print("[X] 一条都没出来 — 把上面的日志发给 Claude 排查")
        sys.exit(1)


if __name__ == "__main__":
    main()
