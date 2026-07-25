#!/usr/bin/env python3
"""doc-init 文档覆盖度闸门。

用途：当项目已存在 `## 领域地图（doc-init）` 段时，**用脚本（而非模型自陈）**判定旧地图是否仍覆盖
当前代码。把当前代码的功能入口（Controller / Service / Handler / Job / 子模块等）与地图里登记的
入口锚点做前缀匹配，算出覆盖率和"没有任何地图行覆盖、却有成片代码"的功能区；再用地图段里嵌入的
源码指纹基线戳，算出地图生成后代码涨了多少。最后给出 COMPLETE / STALE / NEEDS_INIT 判定和退出码。

设计边界（遵循 doc-init「脚本收集事实、模型判断业务」原则）：
- 脚本只做机械覆盖匹配和阈值防呆，**不判定某个未覆盖目录是不是真实业务域**（可能是死代码、vendor、
  测试目录）——这一步仍交模型按产品北极星过滤。
- 脚本给的是"必须继续复核"的硬闸门：verdict 非 COMPLETE 时，模型不得直接收工。

输入：project_inventory.py 产出的 JSON + 项目根（读 AGENTS.md 的领域地图段）。
退出码：0=COMPLETE，2=STALE（需续写/复核），3=NEEDS_INIT（无地图段），1=用法/读取错误。
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import date
from pathlib import Path
from typing import Any

MAP_HEADING_RE = re.compile(r"^\s*##\s+领域地图（doc-init）\s*$")
NEXT_HEADING_RE = re.compile(r"^\s*##\s+")
STAMP_RE = re.compile(r"<!--\s*覆盖度复核基线：(?P<body>.*?)-->", re.S)
PATH_TOKEN_RE = re.compile(r"[A-Za-z0-9_.\-/]+/[A-Za-z0-9_.\-/]*")
INT_RE = re.compile(r"(\d+)")


def find_agents_file(root: Path) -> Path | None:
    for name in ("AGENTS.md", "agents.md"):
        candidate = root / name
        if candidate.is_file():
            return candidate
    return None


def extract_map_section(text: str) -> str | None:
    """抽出 `## 领域地图（doc-init）` 段正文（到下一个 ## 标题前）。无则返回 None。"""
    lines = text.splitlines()
    start = None
    for i, line in enumerate(lines):
        if MAP_HEADING_RE.match(line):
            start = i + 1
            break
    if start is None:
        return None
    end = len(lines)
    for j in range(start, len(lines)):
        if NEXT_HEADING_RE.match(lines[j]):
            end = j
            break
    return "\n".join(lines[start:end])


def parse_stamp(section: str) -> dict[str, Any] | None:
    """解析基线戳：覆盖度复核基线：DATE · 源码指纹 扫描 N 文件 ... / M 子模块 · 基线提交 HASH。"""
    m = STAMP_RE.search(section)
    if not m:
        return None
    body = m.group("body")
    stamp: dict[str, Any] = {"raw": m.group(0).strip()}
    date_m = re.search(r"(\d{4}-\d{2}-\d{2})", body)
    stamp["date"] = date_m.group(1) if date_m else None
    files_m = re.search(r"扫描\s*(\d+)\s*文件", body)
    stamp["scanned_files"] = int(files_m.group(1)) if files_m else None
    mods_m = re.search(r"(\d+)\s*子模块", body)
    stamp["submodules"] = int(mods_m.group(1)) if mods_m else None
    commit_m = re.search(r"基线提交\s*([0-9a-fA-F]{6,40})", body)
    stamp["commit"] = commit_m.group(1) if commit_m else None
    return stamp


def parse_map_anchors(section: str, root: Path) -> tuple[list[dict[str, str]], list[str]]:
    """从领域地图表格里抽每行的领域名 + 入口锚点路径。

    锚点单元格可能是 `src/channels/` 或 `src/channels/ · ChannelHandler`，取其中像路径的 token，
    优先保留文件系统里真实存在的路径。返回 (域行列表, 去重后的锚点前缀列表)。
    """
    rows: list[dict[str, str]] = []
    anchors: list[str] = []
    seen: set[str] = set()
    for line in section.splitlines():
        if not line.strip().startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 2:
            continue
        # 跳过表头与分隔行
        joined = "".join(cells)
        if set(joined) <= set("-: ") or "领域" in cells[0] or "入口锚点" in joined or "状态" in joined and "入口" in joined:
            # 表头/分隔行启发式：含"领域/入口锚点/状态"列名或全是 ---
            if set(joined) <= set("-: ") or ("领域" in cells[0] and "锚点" in joined):
                continue
        domain = cells[0]
        anchor_cell = cells[1]
        if set(anchor_cell) <= set("-: ") or not domain or set(domain) <= set("-: "):
            continue
        tokens = PATH_TOKEN_RE.findall(anchor_cell)
        row_anchors: list[str] = []
        for tok in tokens:
            norm = tok.strip().rstrip("/")
            if not norm:
                continue
            row_anchors.append(norm)
            if norm not in seen:
                seen.add(norm)
                anchors.append(norm)
        status = cells[2].strip() if len(cells) >= 3 else ""
        rows.append({"domain": domain, "anchor_cell": anchor_cell, "anchors": ",".join(row_anchors), "status": status})
    # 锚点排序：真实存在的优先，长的优先（更精确）
    anchors.sort(key=lambda a: ((root / a).exists(), len(a)), reverse=True)
    return rows, anchors


def collect_code_units(inventory: dict[str, Any]) -> list[str]:
    """当前代码的功能入口集合：entry_candidates 文件 + 子模块目录，去重。"""
    units: set[str] = set()
    for paths in (inventory.get("entry_candidates") or {}).values():
        for p in paths:
            if isinstance(p, str):
                units.add(p)
    for mod in inventory.get("submodules") or []:
        path = mod.get("path") if isinstance(mod, dict) else None
        if path:
            units.add(str(path).rstrip("/"))
    return sorted(units)


def is_covered(unit: str, anchors: list[str]) -> bool:
    for anchor in anchors:
        if unit == anchor or unit.startswith(anchor + "/") or anchor.startswith(unit + "/"):
            return True
    return False


def entries_under(anchors_csv: str, units: list[str]) -> list[str]:
    """列出落在该域锚点目录之内的当前代码入口（仅 unit 在 anchor 内，不含反向包含）。

    供漂移点检：把"去抽查已生成域是否漂移"从散文变成"这是该域当前 N 个入口，逐个核对 KB 是否仍匹配"。
    """
    row_anchors = [a for a in anchors_csv.split(",") if a]
    hits: set[str] = set()
    for u in units:
        for a in row_anchors:
            if u == a or u.startswith(a + "/"):
                hits.add(u)
                break
    return sorted(hits)


def group_dir(unit: str, depth: int) -> str:
    parts = [p for p in unit.split("/") if p]
    if len(parts) <= 1:
        return parts[0] if parts else unit
    return "/".join(parts[: min(depth, len(parts) - 1)])


def git_short_commit(root: Path) -> str | None:
    try:
        out = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, timeout=10,
        )
        if out.returncode == 0:
            return out.stdout.strip() or None
    except Exception:
        return None
    return None


def build_fingerprint(inventory: dict[str, Any], root: Path) -> dict[str, Any]:
    langs = {item["language"]: item["file_count"] for item in inventory.get("languages") or []}
    return {
        "scanned_files": (inventory.get("scan") or {}).get("scanned_files"),
        "submodules": len(inventory.get("submodules") or []),
        "languages": langs,
        "commit": git_short_commit(root),
    }


def make_stamp_line(fp: dict[str, Any]) -> str:
    langs = fp.get("languages") or {}
    top = sorted(langs.items(), key=lambda kv: kv[1], reverse=True)[:3]
    lang_str = " · ".join(f"{k} {v}" for k, v in top) if top else "无识别语言"
    commit = fp.get("commit")
    commit_str = f" · 基线提交 {commit}" if commit else ""
    return (
        f"<!-- 覆盖度复核基线：{date.today().isoformat()} · 源码指纹 "
        f"扫描 {fp.get('scanned_files')} 文件 / {lang_str} / {fp.get('submodules')} 子模块{commit_str} -->"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="doc-init 文档覆盖度闸门：判定旧领域地图是否仍覆盖当前代码")
    parser.add_argument("--root", default=".", help="项目根目录")
    parser.add_argument("--inventory", default=".doc-init-project-inventory.json", help="project_inventory.py 产出的 JSON 路径")
    parser.add_argument("--min-coverage", type=float, default=0.85, help="入口覆盖率低于此值判 STALE")
    parser.add_argument("--max-uncovered-area-entries", type=int, default=3, help="任一未覆盖目录入口数 >= 此值判 STALE（疑似未登记领域）")
    parser.add_argument("--max-growth-pct", type=float, default=0.25, help="相对基线扫描文件数增长超过此比例判 STALE")
    parser.add_argument("--group-depth", type=int, default=2, help="未覆盖功能区按前几级目录聚合")
    parser.add_argument("--allow-missing-baseline", action="store_true", help="无基线戳时不强制判 STALE")
    parser.add_argument("--json", action="store_true", help="输出 JSON（默认输出人类可读摘要）")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    inv_path = Path(args.inventory)
    if not inv_path.is_absolute():
        inv_path = root / inv_path
    if not inv_path.is_file():
        print(f"[错误] 找不到 inventory：{inv_path}，请先运行 project_inventory.py --output {inv_path.name}", file=sys.stderr)
        return 1
    try:
        inventory = json.loads(inv_path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001
        print(f"[错误] inventory JSON 解析失败：{exc}", file=sys.stderr)
        return 1

    agents = find_agents_file(root)
    fingerprint = build_fingerprint(inventory, root)
    result: dict[str, Any] = {
        "root": str(root),
        "current_fingerprint": fingerprint,
        "suggested_stamp": make_stamp_line(fingerprint),
    }

    if agents is None:
        result.update({"verdict": "NEEDS_INIT", "map_present": False,
                       "reasons": ["根目录无 AGENTS.md"]})
        emit(result, args.json)
        return 3
    section = extract_map_section(agents.read_text(encoding="utf-8"))
    if section is None:
        result.update({"verdict": "NEEDS_INIT", "map_present": False,
                       "reasons": ["AGENTS.md 无 `## 领域地图（doc-init）` 段——视为初始化未完成"]})
        emit(result, args.json)
        return 3

    rows, anchors = parse_map_anchors(section, root)
    stamp = parse_stamp(section)

    units = collect_code_units(inventory)
    covered = [u for u in units if is_covered(u, anchors)]
    uncovered = [u for u in units if not is_covered(u, anchors)]
    total = len(units)
    coverage_pct = (len(covered) / total) if total else None

    # 未覆盖功能区聚合
    area_counter: dict[str, list[str]] = {}
    for u in uncovered:
        area_counter.setdefault(group_dir(u, args.group_depth), []).append(u)
    uncovered_areas = sorted(
        ({"dir": d, "entry_count": len(v), "sample": sorted(v)[:5]} for d, v in area_counter.items()),
        key=lambda a: a["entry_count"], reverse=True,
    )

    # 代码量增长
    growth = None
    if stamp and stamp.get("scanned_files") and fingerprint.get("scanned_files"):
        base = stamp["scanned_files"]
        cur = fingerprint["scanned_files"]
        growth = {
            "baseline_scanned_files": base,
            "current_scanned_files": cur,
            "delta": cur - base,
            "pct": round((cur - base) / base, 4) if base else None,
            "baseline_submodules": stamp.get("submodules"),
            "current_submodules": fingerprint.get("submodules"),
        }

    reasons: list[str] = []
    verdict = "COMPLETE"

    if total == 0:
        verdict = "STALE"
        reasons.append("inventory 未识别出任何功能入口（entry_candidates/submodules 为空），无法机械确认覆盖度，需人工复核")
    if not anchors:
        verdict = "STALE"
        reasons.append("领域地图段未解析出任何入口锚点路径，地图可能损坏或锚点写法不规范")
    if coverage_pct is not None and coverage_pct < args.min_coverage:
        verdict = "STALE"
        reasons.append(f"入口覆盖率 {coverage_pct:.0%} < 阈值 {args.min_coverage:.0%}（{len(uncovered)}/{total} 个功能入口无地图行覆盖）")
    big_areas = [a for a in uncovered_areas if a["entry_count"] >= args.max_uncovered_area_entries]
    if big_areas:
        verdict = "STALE"
        reasons.append(
            "存在未登记的成片功能区（疑似地图生成后新增或当年漏掉的领域）："
            + "；".join(f"{a['dir']}（{a['entry_count']} 入口）" for a in big_areas[:8])
        )
    if stamp is None and not args.allow_missing_baseline:
        verdict = "STALE"
        reasons.append("领域地图段无『覆盖度复核基线』戳，无法判断代码涨了多少，按可能严重过期处理")
    if growth and growth.get("pct") is not None and growth["pct"] > args.max_growth_pct:
        verdict = "STALE"
        reasons.append(f"代码量较基线增长 {growth['pct']:.0%}（{growth['baseline_scanned_files']}→{growth['current_scanned_files']} 文件）> 阈值 {args.max_growth_pct:.0%}，需逐域漂移点检")

    if verdict == "COMPLETE":
        reasons.append("地图入口锚点覆盖当前代码功能区、且代码量未明显增长，可判定真正完成")

    # 漂移点检清单：对「已生成（复用现有）」域给出当前锚点目录下的入口，供模型逐域核对 KB 是否仍准。
    reuse_domains: list[dict[str, Any]] = []
    for row in rows:
        if "已生成" not in row.get("status", ""):
            continue
        ents = entries_under(row["anchors"], units)
        reuse_domains.append({
            "domain": row["domain"],
            "anchors": row["anchors"],
            "status": row["status"],
            "entry_count": len(ents),
            "entries_sample": ents[:8],
        })

    result.update({
        "verdict": verdict,
        "map_present": True,
        "mapped_domains": len(rows),
        "map_anchors": anchors,
        "baseline_stamp": stamp,
        "growth": growth,
        "coverage": {
            "total_entry_points": total,
            "covered": len(covered),
            "uncovered": len(uncovered),
            "coverage_pct": round(coverage_pct, 4) if coverage_pct is not None else None,
            "uncovered_areas": uncovered_areas,
        },
        "reuse_domains_for_drift_check": reuse_domains,
        "reasons": reasons,
    })
    emit(result, args.json)
    return 0 if verdict == "COMPLETE" else 2


def emit(result: dict[str, Any], as_json: bool) -> None:
    if as_json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return
    v = result["verdict"]
    badge = {"COMPLETE": "✅ COMPLETE", "STALE": "⚠️  STALE（需续写/复核）", "NEEDS_INIT": "🆕 NEEDS_INIT"}[v]
    print(f"覆盖度闸门判定：{badge}")
    if result.get("map_present"):
        cov = result["coverage"]
        print(f"  地图登记领域：{result['mapped_domains']} 个 · 解析锚点 {len(result['map_anchors'])} 条")
        pct = cov["coverage_pct"]
        print(f"  功能入口覆盖：{cov['covered']}/{cov['total_entry_points']}"
              + (f"（{pct:.0%}）" if pct is not None else ""))
        if result.get("growth"):
            g = result["growth"]
            pctg = g.get("pct")
            print(f"  代码量基线对比：{g['baseline_scanned_files']}→{g['current_scanned_files']} 文件"
                  + (f"（+{pctg:.0%}）" if pctg is not None else ""))
        elif result.get("baseline_stamp") is None:
            print("  代码量基线对比：无基线戳，无法对比")
        if cov["uncovered_areas"]:
            print("  未覆盖功能区（按入口数降序，模型据此判断是否真实新领域）：")
            for a in cov["uncovered_areas"][:10]:
                print(f"    - {a['dir']}：{a['entry_count']} 入口，例 {', '.join(a['sample'][:3])}")
        rd = result.get("reuse_domains_for_drift_check") or []
        if rd:
            print("  漂移点检清单（『已生成（复用现有）』域当前入口；逐域核对 KB 标注入口是否仍落得到实处、有无成片新增未登记入口）：")
            for d in rd:
                line = f"    - {d['domain']}（{d['anchors'] or '无锚点'}）：当前 {d['entry_count']} 入口"
                if d["entries_sample"]:
                    line += f"，例 {', '.join(d['entries_sample'][:3])}"
                print(line)
    print("判定理由：")
    for r in result["reasons"]:
        print(f"  - {r}")
    print(f"建议写回地图段的基线戳：\n  {result['suggested_stamp']}")


if __name__ == "__main__":
    sys.exit(main())
