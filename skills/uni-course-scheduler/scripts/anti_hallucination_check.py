#!/usr/bin/env python3
"""
反幻觉检测器 (anti_hallucination_check) — 云端输出自动复核工具
版本: v2.0 | 日期: 2026-08-05
配套文档: 反幻觉约束提示词_v1.1.md

用途: 对 LoomLoom 云端管道每个步骤的输出执行反幻觉自检，
     对照「提交给云端的目录文本」(事实边界) 检查：
       1. 输出中的课程代码是否都在输入中出现（防编造）
       2. 编造代码是否属于已知跨校污染（COMP1000/MATH1001/PHYS1100 等）
       3. decision 步骤 why_rejected 是否引用输入之外的课程（无候选池应为 []）
       4. schedule 步骤课时段是否精确匹配 TIMETABLE 段（防"真实课程+假时段"）
       5. default_timetable 声明是否缺失

用法:
    python3 anti_hallucination_check.py <output_json> <input_catalog.txt> [--context decision|schedule|catalog|recommend]
    python3 anti_hallucination_check.py --self-test   # 运行 8 场景回归测试

返回码: 0 = 通过(无 violation)，1 = 检出幻觉
"""
import json, re, sys

KNOWN_CROSS_UNIVERSITY = {
    "COMP1000": "Macquarie University (MQ) - 跨校污染",
    "MATH1001": "UQ College pre-university only (not UG)",
    "PHYS1100": "not a UQ course",
}

def extract_codes(text):
    """提取形如 ABC1234 (4位) 或 COMP90038 (5位) 的课程代码"""
    return set(re.findall(r'\b([A-Z]{3,4}\d{4,5})\b', text.upper()))

def parse_timetable_block(input_catalog_text):
    """解析 TIMETABLE 段为记录列表 [(code, type, day, start, end)]"""
    block = re.search(r'TIMETABLE:\s*(.*?)(?:\n\n|\Z)', input_catalog_text, re.DOTALL)
    if not block:
        return []
    records = []
    for line in block.group(1).splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        m = re.match(
            r'([A-Z]{3,4}\d{4,5})\s*\|\s*(\w+)\s*\|\s*(Monday|Tuesday|Wednesday|Thursday|Friday|Saturday|Sunday)\s*\|\s*(\d{2}:\d{2})-(\d{2}:\d{2})',
            line, re.IGNORECASE)
        if m:
            records.append((m.group(1).upper(), m.group(2), m.group(3), m.group(4), m.group(5)))
    return records

def anti_hallucination_check(output_json, input_catalog_text, context="decision"):
    """
    反幻觉自检。
    output_json: 云端步骤输出 (dict)
    input_catalog_text: 提交给云端的目录文本
    context: catalog / recommend / schedule / decision
    返回 {"passed": bool, "violations": [...], "warnings": [...]}
    """
    violations, warnings = [], []
    input_codes = extract_codes(input_catalog_text)
    output_codes = extract_codes(json.dumps(output_json, ensure_ascii=False))
    phantom = set(output_codes) - set(input_codes)

    # 检查1: 课程代码必须全部来自输入
    for c in sorted(phantom):
        origin = KNOWN_CROSS_UNIVERSITY.get(c)
        note = f" [{origin}]" if origin else ""
        violations.append(f"编造课程代码 {c}{note} — 输入目录中不存在")

    # 检查2: 编造代码出现在字段值中
    def walk(obj, path=""):
        if isinstance(obj, dict):
            for k, v in obj.items():
                walk(v, f"{path}.{k}" if path else k)
        elif isinstance(obj, list):
            for i, v in enumerate(obj):
                walk(v, f"{path}[{i}]")
        elif isinstance(obj, str):
            if re.match(r'^[A-Z]{3,4}\d{4,5}$', obj.strip()) and obj.strip().upper() in phantom:
                violations.append(f"{path}: 编造课程代码出现在字段值中")
    walk(output_json)

    # 检查3: decision 步骤 why_rejected
    if context == "decision":
        why = output_json.get("report", {}).get("selection_reasoning", {}).get("why_rejected")
        if why is None:
            warnings.append("why_rejected 字段缺失（应显式输出 [] 或候选列表）")
        elif isinstance(why, list) and len(why) > 0:
            bad = [i.get("course_code", "").upper() for i in why
                   if isinstance(i, dict) and i.get("course_code", "").upper() not in input_codes]
            if bad:
                violations.append(f"why_rejected 引用输入之外的课程: {bad}（无候选池时应输出 []）")
        elif isinstance(why, list) and len(why) == 0:
            warnings.append("why_rejected=[] 正确（输入无候选池）")

    # 检查4: schedule 课时段必须精确匹配 TIMETABLE 段
    if context == "schedule":
        tt_records = parse_timetable_block(input_catalog_text)
        tt_flat = {(r[0], r[2], r[3], r[4]) for r in tt_records}
        has_default = output_json.get("default_timetable") is True
        for s in output_json.get("schedule", []):
            code = str(s.get("course_code", "")).upper()
            day = s.get("day", "")
            st, et = s.get("start_time", ""), s.get("end_time", "")
            if has_default:
                continue
            key = (code, day, st, et)
            if key not in tt_flat:
                relaxed = any(r[0] == code and r[2] == day and r[3] == st for r in tt_records)
                if not relaxed:
                    violations.append(
                        f"schedule: {code} {day} {st}-{et} 不在输入 TIMETABLE 段且未声明 default_timetable=true")
                else:
                    warnings.append(
                        f"schedule: {code} {day} {st}-{et} 起始匹配但结束时间与 TIMETABLE 段不一致（可能四舍五入，建议核对）")
        if has_default:
            warnings.append("default_timetable=true 已声明（默认课表，需核实）")

    return {"passed": len(violations) == 0, "violations": violations, "warnings": warnings}


def self_test():
    """8 场景回归测试"""
    input_catalog = """UQ Bachelor of Biomedical Science (2546). Each course = 2 units. Year 1 Semester 1 (starts 2027-02-22): BIOM1001 Fund Bio Sci I (compulsory); CHEM1100 Chemistry 1 (compulsory); SCIE1000 Theory & Practice (compulsory); BIOL1020 Genes Cells & Evolution (compulsory). 2027 S1: starts 2027-02-22, 13 teaching weeks, ends 2027-05-28.

TIMETABLE:
BIOM1001 | Lecture | Monday | 09:00-10:00 | weeks 1-13
BIOM1001 | Tutorial | Tuesday | 14:00-15:00 | weeks 1-13
CHEM1100 | Lecture | Monday | 14:00-15:00 | weeks 1-13
CHEM1100 | Lecture | Tuesday | 09:00-10:00 | weeks 1-13
SCIE1000 | Lecture | Monday | 11:00-12:00 | weeks 1-13
SCIE1000 | Workshop | Tuesday | 10:00-12:00 | weeks 1-13
BIOL1020 | Lecture | Monday | 10:00-11:00 | weeks 1-13
BIOL1020 | Tutorial | Wednesday | 10:00-11:00 | weeks 1-13
BIOL1020 | Practical | Friday | 09:00-12:00 | weeks 1-12
"""
    cases = [
        ("T1 决策报告-真实幻觉", "decision",
         {"report": {"selection_reasoning": {"why_rejected": [
             {"course_code": "MATH1001", "reasoning": "数学"},
             {"course_code": "PHYS1100", "reasoning": "物理"},
             {"course_code": "COMP1000", "reasoning": "计算机"}]}}}, "拦截"),
        ("T2 决策报告-守约束", "decision",
         {"report": {"selection_reasoning": {"why_rejected": []}}}, "通过"),
        ("T3 候选池合规", "decision",
         {"report": {"selection_reasoning": {"why_rejected": [
             {"course_code": "SCIE1000", "reasoning": "匹配度低"}]}}}, "通过"),
        ("T4 排课-编造时段(周六7点)", "schedule",
         {"schedule": [{"course_code": "BIOL1020", "session_type": "Practical",
                        "day": "Saturday", "start_time": "07:00", "end_time": "10:00"}]}, "拦截"),
        ("T5 排课-声明默认", "schedule",
         {"default_timetable": True, "schedule": [{"course_code": "BIOM1001",
          "session_type": "Lecture", "day": "Monday", "start_time": "09:00", "end_time": "10:00"}]}, "通过"),
        ("T6 排课-精确匹配真实时段", "schedule",
         {"schedule": [{"course_code": "BIOL1020", "session_type": "Practical",
                        "day": "Friday", "start_time": "09:00", "end_time": "12:00"}]}, "通过"),
        ("T7 排课-起始匹配结束不符", "schedule",
         {"schedule": [{"course_code": "BIOL1020", "session_type": "Practical",
                        "day": "Friday", "start_time": "09:00", "end_time": "11:00"}]}, "警告放行"),
        ("T8 目录-编造课程", "catalog",
         {"courses": [{"course_code": "BIOM1001"}, {"course_code": "MATH1001"}]}, "拦截"),
    ]
    print("反幻觉检测器 v2 回归测试（8 场景）")
    print("=" * 72)
    all_ok = True
    for name, ctx, out, expect in cases:
        r = anti_hallucination_check(out, input_catalog, ctx)
        behaves = "通过" if r["passed"] else "拦截"
        match = (behaves == expect) or (expect == "警告放行" and r["passed"] and len(r["warnings"]) > 0)
        all_ok = all_ok and match
        print(f"\n─── {name} | 预期: {expect} | 实际: {behaves} {'OK' if match else 'MISMATCH'}")
        for v in r["violations"]:
            print(f"   [拦截] {v}")
        for w in r["warnings"]:
            print(f"   [提示] {w}")
    print(f"\n{'全部通过 OK' if all_ok else '存在不符合项 MISMATCH'}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(2)
    out = json.load(open(sys.argv[1], encoding="utf-8"))
    catalog = open(sys.argv[2], encoding="utf-8").read()
    ctx = "decision"
    if "--context" in sys.argv:
        ctx = sys.argv[sys.argv.index("--context") + 1]
    r = anti_hallucination_check(out, catalog, ctx)
    print(json.dumps(r, ensure_ascii=False, indent=2))
    sys.exit(0 if r["passed"] else 1)
