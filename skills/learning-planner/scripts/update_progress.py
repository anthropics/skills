#!/usr/bin/env python3
"""
Update progress on a learning-plan.json file.

Usage:
    python3 update_progress.py <plan.json> \\
        [--complete id1,id2,...] \\
        [--in-progress id1,id2,...] \\
        [--reset id1,id2,...] \\
        [--output <path>]

What this does:
  1. Applies any requested status changes:
       --complete     -> sets status to 'completed'
       --in-progress  -> sets status to 'in-progress'
       --reset        -> clears a manual status so it gets recomputed below
                          (use this to undo an accidental --complete/--in-progress)
  2. Recomputes 'locked' vs 'available' for every module that is not currently
     'in-progress' or 'completed', based on whether all of its prerequisites
     have status 'completed'. This is the only place availability is computed --
     it should not be hand-edited elsewhere.
  3. Recomputes overall and per-category (core/optional/advanced) progress
     percentages, and a status breakdown.
  4. Updates meta.last_updated to today's date.
  5. Writes the result back to the same file (or --output if given), and
     prints a summary of what changed, including newly-unblocked modules.

This script assumes the input has already passed scripts/validate_plan.py --
it does not re-validate schema structure.
"""
import argparse
import datetime
import json
import sys


def load_json(path):
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def save_json(path, data):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
        f.write("\n")


def parse_id_list(value):
    if not value:
        return []
    return [v.strip() for v in value.split(",") if v.strip()]


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("plan", help="Path to learning-plan.json")
    parser.add_argument("--complete", default="", help="Comma-separated module IDs to mark as completed")
    parser.add_argument("--in-progress", default="", help="Comma-separated module IDs to mark as in-progress")
    parser.add_argument("--reset", default="", help="Comma-separated module IDs to reset to a recomputed status")
    parser.add_argument("--output", default=None, help="Write to a different file instead of overwriting in place")
    args = parser.parse_args()

    data = load_json(args.plan)
    modules = data.get("modules", [])
    by_id = {m["id"]: m for m in modules if "id" in m}

    complete_ids = parse_id_list(args.complete)
    in_progress_ids = parse_id_list(args.in_progress)
    reset_ids = parse_id_list(args.reset)

    unknown = [i for i in complete_ids + in_progress_ids + reset_ids if i not in by_id]
    if unknown:
        print(f"ERROR: unknown module id(s): {', '.join(unknown)}")
        sys.exit(1)

    changes = []

    for mid in reset_ids:
        old = by_id[mid]["status"]
        by_id[mid]["status"] = "locked"  # placeholder; recomputed below
        changes.append((mid, old, "reset (recomputed below)"))

    for mid in complete_ids:
        old = by_id[mid]["status"]
        if old != "completed":
            unmet = [
                p for p in (by_id[mid].get("prerequisites") or [])
                if by_id.get(p, {}).get("status") != "completed"
            ]
            if unmet:
                print(f"WARNING: marking '{mid}' completed even though prerequisite(s) not completed: {', '.join(unmet)}")
            by_id[mid]["status"] = "completed"
            changes.append((mid, old, "completed"))

    for mid in in_progress_ids:
        old = by_id[mid]["status"]
        if old == "completed":
            print(f"WARNING: '{mid}' is already completed; not changing to in-progress")
            continue
        if old != "in-progress":
            by_id[mid]["status"] = "in-progress"
            changes.append((mid, old, "in-progress"))

    # Recompute locked/available for every module not manually tracked as
    # in-progress/completed. One pass is sufficient: availability depends only
    # on prerequisites' 'completed' status, which is now final for this run.
    newly_available = []
    newly_locked = []
    for m in modules:
        if m.get("status") in ("in-progress", "completed"):
            continue
        prereqs = m.get("prerequisites") or []
        all_done = all(by_id.get(p, {}).get("status") == "completed" for p in prereqs)
        new_status = "available" if all_done else "locked"
        if m["status"] != new_status:
            (newly_available if new_status == "available" else newly_locked).append(m["id"])
            m["status"] = new_status

    # Consistency check: an in-progress/completed module whose prerequisites
    # are no longer all completed (e.g. after a --reset) is left as-is, but
    # flagged so the user can decide what to do.
    inconsistent = []
    for m in modules:
        if m.get("status") in ("in-progress", "completed"):
            prereqs = m.get("prerequisites") or []
            unmet = [p for p in prereqs if by_id.get(p, {}).get("status") != "completed"]
            if unmet:
                inconsistent.append((m["id"], unmet))

    # Progress stats
    total = len(modules)
    completed = sum(1 for m in modules if m.get("status") == "completed")
    overall_pct = round(100 * completed / total, 1) if total else 0.0

    by_category = {}
    for cat in ("core", "optional", "advanced"):
        cat_modules = [m for m in modules if m.get("category") == cat]
        if cat_modules:
            cat_completed = sum(1 for m in cat_modules if m.get("status") == "completed")
            by_category[cat] = {
                "completed": cat_completed,
                "total": len(cat_modules),
                "percent": round(100 * cat_completed / len(cat_modules), 1),
            }

    status_counts = {}
    for m in modules:
        s = m.get("status", "unknown")
        status_counts[s] = status_counts.get(s, 0) + 1

    data.setdefault("meta", {})["last_updated"] = datetime.date.today().isoformat()

    output_path = args.output or args.plan
    save_json(output_path, data)

    # Report
    print(f"Updated {output_path}\n")

    if changes:
        print("Status changes:")
        for mid, old, new in changes:
            print(f"  - {mid}: {old} -> {new}")
        print()

    if newly_available:
        print("Newly available (prerequisites now satisfied):")
        for mid in newly_available:
            print(f"  - {mid}: {by_id[mid].get('title', '')}")
        print()

    if newly_locked:
        print("Newly locked (re-evaluated as blocked):")
        for mid in newly_locked:
            print(f"  - {mid}: {by_id[mid].get('title', '')}")
        print()

    if inconsistent:
        print("WARNING: the following modules are in-progress/completed but have")
        print("incomplete prerequisites (left unchanged -- review manually):")
        for mid, unmet in inconsistent:
            print(f"  - {mid}: incomplete prerequisite(s) {', '.join(unmet)}")
        print()

    print(f"Overall progress: {completed}/{total} modules completed ({overall_pct}%)")
    for cat, stats in by_category.items():
        print(f"  {cat}: {stats['completed']}/{stats['total']} ({stats['percent']}%)")
    print()
    print("Status breakdown: " + ", ".join(f"{k}={v}" for k, v in status_counts.items()))


if __name__ == "__main__":
    main()
