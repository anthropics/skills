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
    --force         已出的成品也全部重出（默认同参数重跑沿用已验过的成片只补缺）

断点续跑:
    重跑同一条命令，上次已出且体检过的成片直接沿用（STATUS=SKIP），只补缺的
    条目（含上次没过体检的）。账本在 engine/output/.make_videos_ledger.json，
    按参数指纹识别同组任务；改参数自动视为新任务全量出。

退出码:
    0    出片 + 成片体检全过
    1    出片失败（看 FAILED_STAGE 和日志排查）
    2    出片了，但有成片没过体检（看 FAIL_REASONS，不能算完成）
    130  手动停止
"""
import argparse
import json
import os
import sys
import time
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
    ap.add_argument("--force", action="store_true",
                    help="已出的成品也全部重出（默认同参数重跑只补缺）")
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

    last_progress = [""]  # 闭包可变：记最后一条进度消息，失败时当 FAILED_STAGE 报

    def on_progress(msg):
        last_progress[0] = str(msg)
        print("  | " + str(msg))

    def deliver(kept, new_files):
        """打印成片清单标记块 + 体检硬门禁 + 退出。
        kept=沿用旧成片，new_files=本次新出，条目都是 {path, compliance}"""
        print("\n" + "=" * 46)
        print("出片完成" if new_files else "全部沿用已验过的成片（一条没重出）")
        print("=" * 46)
        # 成片清单标记块（机器可读，agent 直接解析这两行一等）
        print("===VIDEOS_START===")
        files = []
        for item, status in ([(i, "SKIP") for i in kept]
                             + [(i, "OK") for i in new_files]):
            files.append(item["path"])
            print("FILE=%s" % item["path"])
            print("STATUS=%s" % status)
            print("COMPLIANCE=%s" % ("PASS" if item.get("compliance") else "FAIL"))
        print("===VIDEOS_END===")
        print("\n成片文件夹: " + config.output_dir)
        print("共 %d 条（沿用 %d + 新出 %d）" % (len(files), len(kept), len(new_files)))
        if not files:
            print("[X] 一条都没出来 — 把上面的日志发给 Claude 排查")
            sys.exit(1)

        # ── 成片体检（硬门禁）：全过才算完成 ──
        import verify_output
        print("\n" + "=" * 46)
        print("成片体检（时长/画面/声音硬门禁）")
        print("=" * 46)
        all_ok, _ = verify_output.verify_and_report(
            files, expect_orientation=args.aspect)
        if not all_ok:
            print("\n[X] 有成片没过体检 — 按上面 FAIL_REASONS 处理，这批不能算完成")
            print("    重跑同一条命令会沿用验过的、只补没过的；要全部重出加 --force")
            sys.exit(2)
        sys.exit(0)

    # ── 断点续跑：同参数重跑时，账本里体检过的旧成片直接沿用，只补缺 ──
    ledger_path = os.path.join(config.output_dir, ".make_videos_ledger.json")
    import hashlib
    # 指纹不含 --count：条数是「总共要几条」不是任务身份，加量重跑=只补增量
    raw = "|".join(["v1", text, args.product_name, args.category,
                    args.platform, args.aspect, str(args.duration),
                    args.prefix, args.voice, "%.2f" % args.rate,
                    os.path.abspath(args.bgm) if args.bgm else ""])
    sig = hashlib.sha256(raw.encode("utf-8")).hexdigest()[:16]

    def load_ledger():
        try:
            with open(ledger_path, encoding="utf-8") as f:
                data = json.load(f)
            return data if isinstance(data, dict) else {}
        except (OSError, ValueError):
            return {}

    kept = []
    if not args.force:
        entry = load_ledger().get(sig)
        if entry:
            import verify_output
            for item in entry.get("files", []):
                p = item.get("path", "")
                if not (p and os.path.isfile(p) and os.path.getsize(p) > 0):
                    continue
                if verify_output.verify_one(p, expect_orientation=args.aspect)["PASS"]:
                    kept.append(item)
                else:
                    print("[!] 旧成片体检不过，不算数（这次重出）: %s" % p)
            if kept:
                print("断点续跑：这组参数已验过 %d 条成片，直接沿用" % len(kept))

    kept = kept[:args.count]
    if len(kept) >= args.count:
        deliver(kept, [])
        return
    need = args.count - len(kept)

    print("开始出片（%s%d 条，平台 %s）...\n"
          % ("补" if kept else "", need, args.platform))
    try:
        result = pipeline.run(
            product=product,
            platform=args.platform,
            target_duration_ms=args.duration * 1000 if args.duration > 0 else 0,
            variant_count=max(1, need),
            custom_text=text,
            name_prefix=args.prefix,
            aspect_ratio=args.aspect,
            voice_override=args.voice,
            speech_rate_override=args.rate,
            bgm_file_override=args.bgm,
            progress_callback=on_progress,
        )
    except KeyboardInterrupt:
        print("\n已手动停止（重跑同一条命令会沿用已验过的成片，只补缺的）")
        sys.exit(130)
    except Exception:
        print("\n[X] 出片失败（FAILED_STAGE=%s），完整报错如下:\n"
              % last_progress[0])
        traceback.print_exc()
        print("\n常见原因对照（references/engine-reference.md 有详细版）:")
        print("  * 没找到 ffmpeg      -> python setup_env.py --ffmpeg")
        print("  * 配音超时/报网络错   -> Edge 免费配音要联网；换网络或稍后重试")
        print("  * No module named xx -> python setup_env.py --deps")
        print("===VIDEOS_START===")
        print("FAILED_STAGE=%s" % last_progress[0])
        print("===VIDEOS_END===")
        sys.exit(1)

    if getattr(result, "cancelled", False):
        print("任务已取消")
        sys.exit(130)

    new_files = []
    for v in result.variants:
        path = v.output_file or ""
        if path and os.path.isfile(path):
            new_files.append({
                "path": os.path.abspath(path),
                "compliance": 1 if getattr(v, "compliance_check_passed", 0) else 0,
            })

    # 账本在体检前就落盘：渲染成果别等体检完才记，体检挂了下次重跑也能沿用
    ledger = load_ledger()
    ledger[sig] = {"files": kept + new_files, "ts": int(time.time())}
    try:
        with open(ledger_path, "w", encoding="utf-8") as f:
            json.dump(ledger, f, ensure_ascii=False, indent=1)
    except OSError as e:
        print("[!] 续跑账本写入失败（不影响本次出片）: %s" % e)

    deliver(kept, new_files)


if __name__ == "__main__":
    main()
