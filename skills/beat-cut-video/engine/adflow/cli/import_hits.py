# -*- coding: utf-8 -*-
"""
爆款库批量导入工具 — CSV → HitLibrary

用法:
  python -m adflow.cli.import_hits --csv hits.csv
  python -m adflow.cli.import_hits --csv hits.csv --dry-run    # 预览不导入

CSV 格式:
  source,text,category,platform,ctr,cvr,tags,notes
  本地,我其实是一个挺爱吃零食的人...,零食,短视频,0.035,0.04,达人安利;零食;第一人称,
  视频1.mp4,,零食,短视频,,,,
"""

import argparse
import csv
import logging
import os
import sys

logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")
logger = logging.getLogger("adflow.import_hits")


def import_from_csv(csv_path: str, dry_run: bool = False) -> dict:
    """从 CSV 文件批量导入爆款到 HitLibrary

    Args:
        csv_path: CSV 文件路径
        dry_run: True=只预览不实际导入

    Returns:
        {"total": int, "imported": int, "skipped": int, "errors": [str]}
    """
    from adflow.analytics.hit_library import hit_library

    stats = {"total": 0, "imported": 0, "skipped": 0, "errors": []}

    with open(csv_path, "r", encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)
        required = {"text"}
        missing = required - set(reader.fieldnames or [])
        if missing:
            # 允许 text 列缺失（视频导入不需要 text）
            pass

        for row_num, row in enumerate(reader, 1):
            stats["total"] += 1
            source = (row.get("source") or "CSV导入").strip()
            text = (row.get("text") or "").strip()
            category = (row.get("category") or "").strip()
            platform = (row.get("platform") or "").strip()
            tags_str = (row.get("tags") or "").strip()
            notes = (row.get("notes") or "").strip()

            # 解析 tags
            tags = [t.strip() for t in tags_str.replace(";", ",").split(",") if t.strip()]

            # CTR/CVR
            try:
                ctr = float(row.get("ctr", 0) or 0)
            except (ValueError, TypeError):
                ctr = 0.0
            try:
                cvr = float(row.get("cvr", 0) or 0)
            except (ValueError, TypeError):
                cvr = 0.0

            logger.info("第%d行: %s... (%s)", row_num, text[:30] if text else source, category)

            if dry_run:
                logger.info("  [预览] 跳过实际导入")
                stats["imported"] += 1
                continue

            try:
                if source.endswith((".mp4", ".mov", ".avi", ".webm")):
                    # 视频文件导入
                    if os.path.exists(source):
                        hit_id = hit_library.import_video(
                            video_path=source,
                            tags=tags,
                            notes=notes,
                        )
                        logger.info("  导入视频: %s", hit_id)
                        stats["imported"] += 1
                    else:
                        logger.warning("  视频文件不存在: %s", source)
                        stats["skipped"] += 1
                elif text:
                    # 文本导入
                    hit_id = hit_library.import_text_only(
                        text=text,
                        product_name=row.get("source", "")[:50] if source else "",
                        category=category,
                        tags=tags,
                        notes=notes,
                    )
                    logger.info("  导入文本: %s", hit_id)
                    stats["imported"] += 1
                else:
                    logger.warning("  第%d行既无文本也无视频路径，跳过", row_num)
                    stats["skipped"] += 1
            except Exception as e:
                msg = f"第{row_num}行导入失败: {e}"
                logger.error("  %s", msg)
                stats["errors"].append(msg)
                stats["skipped"] += 1

    return stats


def main():
    parser = argparse.ArgumentParser(
        description="AdFlow 爆款库批量导入工具",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  python -m adflow.cli.import_hits --csv hits.csv
  python -m adflow.cli.import_hits --csv hits.csv --dry-run
  python -m adflow.cli.import_hits --csv hits.csv --verbose

CSV 列说明:
  source   : 来源标识（本地文本填任意名，视频填文件路径）
  text     : 爆款文案全文（文本导入必填）
  category : 品类（坚果/零食/护肤/美妆/数码等）
  platform : 平台（douyin/kuaishou/xiaohongshu/shipinhao）
  ctr      : 点击率（如 0.035 表示 3.5%）
  cvr      : 转化率（如 0.04 表示 4%）
  tags     : 标签，分号或逗号分隔（如 "达人安利;零食;第一人称"）
  notes    : 备注
        """,
    )
    parser.add_argument("--csv", required=True, help="CSV 文件路径")
    parser.add_argument("--dry-run", action="store_true", help="只预览，不实际导入")
    parser.add_argument("--verbose", "-v", action="store_true", help="详细输出")
    args = parser.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    # 确保 config 已加载
    try:
        from adflow.config_loader import config
        if not hasattr(config, '_data') or not config._data:
            config_path = os.path.join(os.path.dirname(__file__), "..", "..", "config.yaml")
            config.load(os.path.abspath(config_path))
    except Exception:
        pass

    csv_path = args.csv
    if not os.path.isabs(csv_path):
        csv_path = os.path.abspath(csv_path)

    if not os.path.exists(csv_path):
        logger.error("CSV 文件不存在: %s", csv_path)
        sys.exit(1)

    logger.info("开始导入: %s", csv_path)
    stats = import_from_csv(csv_path, dry_run=args.dry_run)

    print()
    print("=" * 50)
    print(f"导入完成: 总计 {stats['total']} 条")
    print(f"  成功: {stats['imported']}")
    print(f"  跳过: {stats['skipped']}")
    print(f"  错误: {len(stats['errors'])}")
    if stats["errors"]:
        for e in stats["errors"]:
            print(f"    - {e}")
    print("=" * 50)

    if args.dry_run:
        print("(预览模式，未实际导入)")


if __name__ == "__main__":
    main()
