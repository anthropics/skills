#!/usr/bin/env python3
"""需求分析产物自检脚本。

用法：
    python3 check_artifacts.py <产物目录> [--stage G1|G2|G3]

检查项：
  G1 闸门   —— 目录里只允许《需求澄清问题清单》与《访谈记录与假设登记册》，
                且这两份文件里不得含任何分析结论（内容级闸门，不只是文件数）
  编号闭合   —— 所有被引用的编号都有定义，无悬空引用
  前缀撞号   —— 同一前缀被复用于两类不同事物（错误）；同一族系内措辞不一（提示）
  溯源完整   —— 需求类条目必须带 A-xx 或 S-xx 标注
  S-xx 合规  —— S-xx 不得包含结构化分析结论；登记表两列须存在且非空

判定思路（为什么不能只比文字）：
    「同一编号出现在多份产物里」本身不是问题——SRS 摘录、优先级评估索引、
    变更分析表都会复述上游编号，那是**引用**。真正的问题只有一类：
    **同一个前缀被拿去指代了两类不同的东西**。
    判据是**族系**：一份产物里共用同一批前缀的那组编号属于一个族系。
    同一前缀出现在**族系不相交**的两处 → 它被复用了（错误）；
    出现在族系相同的两处 → 只是措辞不同（提示，或按摘要关系豁免）。

    族系不能靠"同一张表里出现了哪些前缀"来算——那对表格切分方式过度敏感
    （同一份真实撞号，把支撑流程单独列一张表就会从"报错"退化成"静默"）。
    所以族系按**语义角色**判定：一个编号的定义点处在什么栏目下，
    决定它在这个族系里的角色。角色不同 = 两套不相干的族系。

退出码：0 = 通过，1 = 发现问题，2 = 用法/目录错误
"""

import argparse
import difflib
import os
import re
import sys
from collections import defaultdict

# ---------------------------------------------------------------- 基础常量

# G1 阶段允许的文件名 —— 精确白名单，不接受"名字里带这几个词就行"
# 允许 "<系统名>_需求澄清问题清单.md" 与 "<系统名>_访谈记录与假设登记册.md"
# 英文版对应 "<系统>_clarification-questions.md" 与 "<系统>_interview-assumption-register.md"
G1_ALLOWED_BASENAMES = (
    "需求澄清问题清单.md", "访谈记录与假设登记册.md",
    "clarification-questions.md", "interview-assumption-register.md",
)

# 疑问句豁免只在"问题清单"这类文件里生效（登记册里不该有疑问句）
G1_QUESTION_LIST_BASENAMES = ("需求澄清问题清单.md", "clarification-questions.md")

# S-xx 登记册（S-xx 唯一定义处）的文件名特征
G1_REGISTER_BASENAMES = ("访谈记录与假设登记册.md", "interview-assumption-register.md")

# S-xx 登记表的列名识别 —— 中英双语
SXX_VERIFICATION_COLUMNS = (
    "验证方式", "如何验证", "验证方法", "验证手段",
    "verification method", "how to verify", "verification", "validate how",
)
SXX_CONSEQUENCE_COLUMNS = (
    "验证不成立的后果", "不成立的后果", "后果",
    "consequence if", "consequences if", "consequence", "impact if", "if it fails",
)


def _row_has_verification_and_consequence(row):
    """这一行里是否同时出现"验证方式"与"不成立的后果"的说明（双语）。"""
    low = row.lower()
    has_verify = any(k in row for k in SXX_VERIFICATION_COLUMNS) or any(
        k in low for k in ("verif", "validat", "confirm")
    )
    has_consequence = any(k in row for k in SXX_CONSEQUENCE_COLUMNS) or any(
        k in low for k in ("consequence", "impact if", "if it fails", "fails")
    )
    return has_verify and has_consequence

# G1 阶段允许出现的编号前缀 —— 只有访谈族系的四类
G1_ALLOWED_PREFIXES = ("Q", "A", "S", "T")

# G1 阶段：标题里出现这些词 = 这份文件在讲分析产物（越界）
G1_HEADING_MARKERS = (
    "功能清单", "功能需求", "非功能需求", "领域模型", "领域类", "业务流程",
    "业务场景", "场景分析", "问题卡片", "干系人", "管控点", "质量场景",
    "业务规则", "需求规格说明书", "状态机", "类图", "实体关系", "流程图",
    "表结构", "业务数据", "业务报表", "价值评估", "优先级评估", "追溯矩阵",
    "验收标准", "维护需求", "业务规则描述",
    # 英文
    "feature list", "feature requirement", "functional requirement",
    "non-functional requirement", "nonfunctional requirement",
    "domain model", "business process", "process flow", "workflow",
    "business scenario", "scenario analysis", "problem card",
    "stakeholder", "control point", "quality scenario",
    "business rule", "requirements specification", "state machine",
    "class diagram", "entity relationship", "flowchart", "flow chart",
    "data model", "business report", "value assessment",
    "priority assessment", "traceability matrix", "acceptance criteri",
    "maintenance requirement",
)

# G1 阶段的表格：表头出现这些词 = 这张表是分析结论表
# 只扫表头，不扫正文 —— 正文里"现有业务流程是…"是合法的 A-xx 事实。
G1_TABLE_HEADER_MARKERS = (
    "业务流程", "流程步骤", "流程说明", "流程名称", "触发条件", "责任人",
    "业务场景", "场景", "领域模型", "领域类", "功能需求", "功能清单",
    "干系人", "问题卡片", "管控点", "验收标准", "质量场景", "业务规则",
    "需求规格说明书", "报表", "状态机", "类图", "实体关系", "流程图",
    "表结构", "字段包括", "模块", "子系统", "步骤", "动作",
    # 英文
    "business process", "process step", "process name", "trigger condition",
    "owner", "responsible", "business scenario", "scenario",
    "domain model", "domain class", "functional requirement", "feature list",
    "stakeholder", "problem card", "control point", "acceptance criteri",
    "quality scenario", "business rule", "requirements specification",
    "report", "state machine", "class diagram", "entity relationship",
    "flowchart", "flow chart", "table structure", "fields include",
    "module", "subsystem", "step", "action",
)

# G1 阶段：正文出现这些强断言 = 分析结论（不是问题，是结论）
G1_ASSERTION_PATTERNS = (
    re.compile(r"系统应当"),
    re.compile(r"系统应该"),
    re.compile(r"系统必须"),
    re.compile(r"系统将"),
    re.compile(r"系统应(?!需求)"),
    re.compile(r"系统需(?!求)"),
    re.compile(r"应(?:当)?(?:包含|包括|提供|支持|具备|实现|覆盖|分为|设计|设定)"),
    re.compile(r"需(?:要)?(?:包含|包括|提供|支持|具备|实现)"),
    re.compile(r"必须(?:包含|包括|提供|支持|具备|实现)"),
    re.compile(r"(?:该|本)系统(?:包含|分为|由)"),
    re.compile(r"包含以下"),
    re.compile(r"分为以下"),
    re.compile(r"设计为"),
    # 英文
    re.compile(r"\b(?:the|this)\s+system\s+(?:shall|must|should|will|needs? to)\b", re.IGNORECASE),
    re.compile(r"\b(?:the|this)\s+system\s+(?:includes?|contains?|consists? of|is composed of|is divided)\b", re.IGNORECASE),
    re.compile(r"\bshall\s+(?:include|provide|support|contain|cover|be divided|be designed)\b", re.IGNORECASE),
    re.compile(r"\bmust\s+(?:include|provide|support|contain|cover)\b", re.IGNORECASE),
    re.compile(r"\bshould\s+(?:include|provide|support|contain)\b", re.IGNORECASE),
    re.compile(r"\bincludes?\s+the\s+following\b", re.IGNORECASE),
    re.compile(r"\bdivided\s+into\s+the\s+following\b", re.IGNORECASE),
    re.compile(r"\bdesigned\s+as\s+(?:a|an|the)\b", re.IGNORECASE),
)

# G1 阶段：代码块里画流程图 = 分析结论
G1_DIAGRAM_PATTERNS = (
    re.compile(r"```\s*mermaid", re.IGNORECASE),
    re.compile(r"^\s*(?:flowchart|graph|sequenceDiagram|stateDiagram|classDiagram|erDiagram|stateDiagram-v2)\b", re.MULTILINE),
)

# G1 阶段：无编号的"功能清单"式列表
#
# 标题里写"功能清单"很容易被 G1_HEADING_MARKERS 抓到，但换个中性标题
# （"附：本次要做的"）就能绕过。判据落在**列表项本身的形态**上：
# 功能/能力清单的每一项都是"纯中文短名词短语"（散客体检预约登记、
# 团体体检批量导入、报告推送），既没有句子标点，也不需要编号。
#
# 排除项：
#   · 含 ASCII 字母/数字 —— "追加 A-xx"、"转 S-01" 这类带编号的操作说明
#   · 含中文标点 —— 是完整句子，不是清单项
#   · 长度 > 20 —— 是解释性文字，不是清单项
G1_NOMINAL_ITEM_MAX = 20
# 英文一个单词约 5–8 字符，长度上限需单独放宽，否则英文清单项全部漏判
G1_NOMINAL_ITEM_MAX_EN = 60
G1_NOMINAL_RUN = 3

# 术语/口径类章节里的名词速查列表是合法的，不算"功能清单"
G1_NOMINAL_EXEMPT_HEADING = (
    "术语", "口径", "名词", "缩写", "简称", "解释", "对照", "速查",
    # 英文
    "glossary", "terminology", "term", "definition", "abbreviation",
    "acronym", "quick reference", "cheat sheet", "reference table",
)

# 汇总型产物：其编号是"复述上游"的引用，不参与族系冲突判定
# 判定按文件名**结尾**匹配，不做子串包含 —— 否则改个名就能豁免
SUMMARY_ARTIFACT_KEYWORDS = (
    "需求规格说明书", "需求优先级评估", "变更分析表",
    # 英文
    "requirements-specification", "requirements specification",
    "priority-assessment", "priority assessment",
    "change-log", "change log", "change-analysis",
)

# 出现在 S-xx 描述里说明混入了分析结论的特征词
STRUCTURE_MARKERS = (
    "状态机", "流程图", "领域模型", "类图", "实体关系", "状态流转",
    "字段包括", "表结构", "分为以下", "包含以下模块",
    # 英文
    "state machine", "flowchart", "flow chart", "domain model",
    "class diagram", "entity relationship", "state transition",
    "fields include", "table structure", "divided into", "consists of the following",
)

# 编号后面不能再跟字母数字（避免 BR-19b 被误读成 BR-19）
# 不用 \b —— 中文字符也算 \w，会导致"依据A-01"匹配不上
ID_RE = re.compile(r"(?<![A-Za-z0-9])([A-Z]{1,4})-(\d{1,4})(?![0-9A-Za-z])")
# 溯源标记必须匹配完整编号，避免 "NDA-01" 里的 "A-0" 与 "US-01" 里的 "S-0" 蒙混过关
AS_RE = re.compile(r"(?<![A-Za-z0-9])([AS])-(\d{1,4})(?![0-9A-Za-z])")
HEADING_RE = re.compile(r"^#{1,6}\s+(.*)$")
BULLET_RE = re.compile(r"^([-*+]|\d+[.)])\s+(.*)$")
SEP_ROW_RE = re.compile(r"^\s*\|[\s:|-]*-{2,}[\s:|-]*\|\s*$")

# 悬空引用只对这些前缀报错
KNOWN_PREFIXES = {
    "Q", "A", "S", "T", "PC", "SD", "SP", "RN", "CP", "FP", "US",
    "BR", "DC", "QS", "MR", "C", "F", "NFR", "AC", "CF", "N", "R", "G", "V", "M",
}

# 需求条目 —— 这些必须能溯源到 A-xx / S-xx
#
# 只覆盖"需求条目"（功能/非功能/验收/维护），不覆盖分析产物
# （BR 业务规则 / US 业务场景 / PC 问题卡片 / CP 管控点 / QS 质量场景）。
# 那些产物引用上游事实或分析结论即可 —— 要求它们直达 A-xx 会把
# "经分析结论推出的业务规则"错判成溯源缺失。
TRACEABLE_PREFIXES = ("F", "NFR", "AC", "MR")

# 表示"属于某条目的某个子部分"的后缀 —— 这类行是引用而非定义
# 只认 "的/之" 和 "前后中内 + 的/之"：
# "前台/后台/中间/内部" 是 B 端场景里极常见的描述开头，不能当引用
PARTICULAR_RE = re.compile(r"^(?:的|之)|^([前后中内])(?:的|之)")

# 表头里代表"这条记录叫什么"的列 —— 优先取这类单元格做描述
NAME_HEADER_RE = re.compile(
    r"名称|标题|内容|描述|说明|规则内容|需求|问题|假设内容|摘要"
    r"|name|title|description|detail|content|summary|assumption|requirement",
    re.IGNORECASE,
)

# 语义角色：表头/标题里的关键词 → 这个族系在讲什么
# 顺序即优先级（先匹配到的赢）
#
# 关键：角色必须由**所属栏目/章节**决定，不能由条目自身文本决定。
# 「### Q-05（频率与场景规律）」里的"场景"是这条问题的**名字**，
# 不是栏目 —— 用它定角色会把问题误判成场景族。
ROLE_KEYWORDS = (
    ("假设", "假设"),
    ("术语", "术语"),
    ("事实", "事实"),
    ("卡片", "问题"),
    ("问题", "问题"),
    ("规则", "规则"),
    ("约束", "约束"),
    ("管控", "管控"),
    ("报表", "报表"),
    ("质量", "质量"),
    ("领域", "领域"),
    ("干系人", "干系人"),
    ("流程", "流程"),
    ("场景", "场景"),
    ("需求", "需求"),
    ("功能", "需求"),
    ("数据", "数据"),
    ("优先级", "优先级"),
    ("追溯", "追溯"),
    ("覆盖", "追溯"),
    ("结论", "结论"),
    ("步骤", "流程"),
    ("动作", "流程"),
    # 英文
    ("assumption", "假设"),
    ("glossary", "术语"),
    ("terminology", "术语"),
    ("term ", "术语"),
    ("fact", "事实"),
    ("confirmed", "事实"),
    ("problem card", "问题"),
    ("issue", "问题"),
    ("question", "问题"),
    ("rule", "规则"),
    ("constraint", "约束"),
    ("control point", "管控"),
    ("report", "报表"),
    ("quality", "质量"),
    ("domain", "领域"),
    ("stakeholder", "干系人"),
    ("process", "流程"),
    ("workflow", "流程"),
    ("step", "流程"),
    ("scenario", "场景"),
    ("requirement", "需求"),
    ("feature", "需求"),
    ("data", "数据"),
    ("priority", "优先级"),
    ("traceab", "追溯"),
    ("coverage", "追溯"),
    ("conclusion", "结论"),
)

# 角色判定时忽略的"通用"栏目词 —— 它们不携带族系信息
ROLE_IGNORE = (
    "编号", "名称", "标题", "说明", "描述", "备注", "内容", "摘要",
    "id", "no.", "no", "name", "title", "note", "remark", "comment",
    "description", "detail", "content", "summary",
)

# 族系相似度阈值：低于此值即认为两个族系不相交（同一前缀被复用）
COHORT_JACCARD_MIN = 0.6

# 摘要豁免：短文本长度不足长文本的这个比例时，视为"摘录/简写"而非"另一件事"，
# 不报措辞不一致（错判率优先于召回率——提示是给人看的，不能刷屏）
SUMMARY_LENGTH_RATIO = 0.8


# ---------------------------------------------------------------- 工具函数

def collect_files(root):
    out = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if not d.startswith(".")]
        for fn in filenames:
            if fn.endswith((".md", ".txt")):
                out.append(os.path.join(dirpath, fn))
    return sorted(out)


def read_all(files):
    docs = {}
    for f in files:
        try:
            docs[f] = open(f, encoding="utf-8", errors="replace").read()
        except OSError:
            pass
    return docs


def split_table_row(line):
    s = line.strip()
    if s.startswith("|"):
        s = s[1:]
    if s.endswith("|"):
        s = s[:-1]
    return [c.strip() for c in s.split("|")]


def is_pure_reflist(cell):
    """单元格是否只是编号列表或指针（无实质内容）。"""
    c = cell.strip()
    if not c or c in {"—", "-", "–", "/", "同上", "N/A", "n/a", "无"}:
        return True
    if re.fullmatch(r"(见|参见|详见|同上|同前|参考)", c):
        return True
    if re.fullmatch(r"(?i)(see|refer to|as above|same as|ref:|reference)", c):
        return True
    if re.fullmatch(r"[A-Z]{1,4}-\d{1,4}(\s*[、,，/；;]\s*[A-Z]{1,4}-\d{1,4})*", c):
        return True
    return False


def has_prose(cell):
    """单元格是否是实质内容。"""
    c = cell.strip()
    if is_pure_reflist(c):
        return False
    residue = re.sub(r"[A-Z]{1,4}-\d{1,4}", "", c)
    residue = re.sub(r"[\s、,，/；;()（）\[\]【】*_`]", "", residue)
    return len(residue) >= 2


def subject_of(text):
    """取条目的描述文本 —— 用于判断同一编号在不同处是否指同一事物。"""
    t = text.strip()
    t = re.sub(r"^[\s·•\-—–:：|/\\]+", "", t)
    t = re.sub(r"[\s*_`]+", "", t)
    return t


def same_thing(a, b):
    """两段描述是否指同一事物（同义改写或互为缩写）。"""
    if a == b:
        return True
    ca = set(re.sub(r"[^\w一-鿿]", "", a))
    cb = set(re.sub(r"[^\w一-鿿]", "", b))
    if ca and cb and (ca <= cb or cb <= ca):
        return True
    return difflib.SequenceMatcher(None, a, b).ratio() >= 0.5


def is_summary_artifact(path):
    """是否是汇总型产物（其编号是复述上游的引用）。

    按文件名**结尾**匹配，不做子串包含 —— 子串包含会让
    "需求规格说明书_业务流程附录.md" 这种改名的文件整体豁免。
    """
    stem = os.path.splitext(os.path.basename(path))[0]
    return any(stem.endswith(k) for k in SUMMARY_ARTIFACT_KEYWORDS)


def map_role(text):
    """从表头/标题文字里提取语义角色。"""
    if not text:
        return None
    low = text.lower()
    for kw, role in ROLE_KEYWORDS:
        # 英文关键词大小写不敏感；中文关键词原样匹配
        hit = kw.lower() in low if re.search(r"[A-Za-z]", kw) else kw in text
        if not hit:
            continue
        # 命中的是通用栏目词时不算 —— "编号|说明" 说明不了任何族系
        if kw in ROLE_IGNORE or kw.lower() in ROLE_IGNORE:
            continue
        return role
    return None


def role_of(*candidates):
    """依次尝试多个上下文，取第一个能定出角色的。"""
    for c in candidates:
        r = map_role(c)
        if r:
            return r
    return None


def table_role(header, name_col_idx):
    """判定表格里一条记录的族系角色。

    取「名称列」的表头 —— 那是这条记录**所属的栏目**。
    名称列取不到时退而用整行表头。
    """
    if not header:
        return None
    if name_col_idx is not None and 0 <= name_col_idx < len(header):
        r = map_role(header[name_col_idx])
        if r:
            return r
    return role_of(" ".join(header))


# ---------------------------------------------------------------- 文档切块

def split_blocks(text):
    """把文档切成块：表格块 / 标题块 / 列表块 / 普通文本块。

    块的划分只用于定位"这条记录长什么样"，不用于算族系 ——
    族系按语义角色算，见 role_of。
    """
    lines = text.splitlines()
    blocks = []
    i = 0
    n = len(lines)
    while i < n:
        s = lines[i].strip()
        if s.startswith("|"):
            rows = []
            while i < n and lines[i].strip().startswith("|"):
                rows.append(lines[i])
                i += 1
            header = None
            body = rows
            if len(rows) >= 2 and SEP_ROW_RE.match(rows[1].strip()):
                header = split_table_row(rows[0])
                body = rows[2:]
            blocks.append({"type": "table", "header": header, "rows": body})
            continue
        if HEADING_RE.match(s):
            blocks.append({"type": "heading", "header": None, "rows": [lines[i]]})
            i += 1
            continue
        if BULLET_RE.match(s):
            rows = []
            while i < n and BULLET_RE.match(lines[i].strip()):
                rows.append(lines[i])
                i += 1
            blocks.append({"type": "bullet", "header": None, "rows": rows})
            continue
        blocks.append({"type": "text", "header": None, "rows": [lines[i]]})
        i += 1
    return blocks


def row_definition(cells, header):
    """从一行表格单元格里解析出 (定义编号, 描述文本, 名称列索引, 行内全部编号)。

    描述文本的取法：首格自带名称 → 用首格尾部；否则按表头挑"名称"列；
    都没有就用第二格。

    同时返回**名称列的索引** —— 判族系角色时要看这条记录属于哪个栏目，
    而不是它自己叫什么。
    """
    all_ids = [(p, int(n)) for p, n in ID_RE.findall(" ".join(cells))]
    if not cells:
        return None, None, None, all_ids

    m = re.match(
        r"^\**\s*`?([A-Z]{1,4})-(\d{1,4})(?![0-9A-Za-z])`?\s*\**[：:]?\s*(.*)$",
        cells[0],
    )
    if not m:
        return None, None, None, all_ids
    p, n = m.group(1), int(m.group(2))
    trailing = m.group(3).strip()

    # 首格含多个编号（"M-01 / M-02 的xx步骤"）→ 合并引用行
    if len(ID_RE.findall(cells[0])) > 1:
        return None, None, None, all_ids
    # 名称以"的/之"开头 → 指向某条目的子部分，属引用
    if trailing and PARTICULAR_RE.match(trailing):
        return None, None, None, all_ids

    if has_prose(trailing):
        # 描述就在首格里 → 所属栏目也是首格对应的表头
        return (p, n), subject_of(trailing), 0, all_ids

    # 首格只有编号 → 按表头找"名称"列
    if header:
        for idx, h in enumerate(header):
            if idx == 0 or not h:
                continue
            if NAME_HEADER_RE.search(h) and idx < len(cells):
                # 名称列里装的是**另一个编号** → 这是追溯表，本行只当引用
                if re.match(r"^\**\s*`?[A-Z]{1,4}-\d{1,4}", cells[idx]):
                    return None, None, None, all_ids
                # 名称列的**邻列**装的是**另一个**编号 → 这一行是引用关系
                # （追溯表：| 场景 | 来源流程 | 解决的问题卡片 | 主要干系人 |
                #   "解决的问题卡片" 匹配名称列正则，但这一行整行都是引用）
                # 注意排除首格 —— 首格就是本行自己的编号，不算"另一个"
                for nb in (idx - 1, idx + 1):
                    if nb <= 0 or nb >= len(cells):
                        continue
                    if re.match(r"^\**\s*`?[A-Z]{1,4}-\d{1,4}", cells[nb]):
                        return None, None, None, all_ids
                if has_prose(cells[idx]):
                    return (p, n), subject_of(cells[idx]), idx, all_ids
                break

    if len(cells) > 1:
        second = cells[1].strip()
        # 次格以编号开头 → 追溯表，本行只当引用
        if re.match(r"^\**\s*`?[A-Z]{1,4}-\d{1,4}", second):
            return None, None, None, all_ids
        if has_prose(second):
            return (p, n), subject_of(second), 1, all_ids
    return None, None, None, all_ids


def heading_definition(text):
    """从标题行里解析 (定义编号, 描述文本, 标题层级, 全部编号)。

    描述文本的取法：编号后的正文；若正文在括号里（如"## Q-01（谁提的）"），
    则取括号内的说明——那是这条记录的名字。
    """
    m = HEADING_RE.match(text.strip())
    if not m:
        return None, None, None, []
    body = m.group(1)
    all_ids = [(p, int(n)) for p, n in ID_RE.findall(body)]
    head = re.split(r"[（(【\[]", body)[0]
    ids = ID_RE.findall(head)
    if not ids:
        return None, None, None, all_ids
    p, n = ids[0]
    n = int(n)
    token = f"{p}-{n:02d}"
    if token not in head:
        return None, None, None, all_ids
    rest = head.split(token, 1)[1] if token in head else head
    level = len(text.strip()) - len(text.strip().lstrip("#"))
    if not subject_of(rest):
        # 编号后紧跟括号 → 括号里就是这条记录的名字
        m2 = re.search(r"[（(【\[]([^）)】\]]+)[）)】\]]", body)
        if m2:
            return (p, n), subject_of(m2.group(1)), level, all_ids
        # 编号后没有正文也没有括号 → 标题本身就是这条记录的全部
        # （如"### Q-01"，问题正文在标题下面的段落里）
        # 描述取编号本身，保证它仍被登记为一个定义点
        return (p, n), token, level, all_ids
    return (p, n), subject_of(rest), level, all_ids


def bullet_definition(text):
    """从列表项里解析 (定义编号, 描述文本, 列表项原文, 全部编号)。"""
    m = BULLET_RE.match(text.strip())
    if not m:
        return None, None, None, []
    body = m.group(2).strip()
    m2 = re.match(
        r"^\**\s*`?([A-Z]{1,4})-(\d{1,4})(?![0-9A-Za-z])`?\s*\**[：:]?\s*(.*)$", body
    )
    if not m2:
        return None, None, None, []
    # 行首列了多个编号（"- N-01/N-02/N-03 同为…"）→ 引用，非定义
    head_token = body.split()[0] if body.split() else ""
    if len(ID_RE.findall(head_token)) > 1:
        return None, None, None, []
    p, n = m2.group(1), int(m2.group(2))
    rest = m2.group(3).strip()
    if rest and PARTICULAR_RE.match(rest):
        return None, None, None, []
    if not subject_of(rest):
        return None, None, None, []
    return (p, n), subject_of(rest), body, []


def extract_row(blk, row):
    if blk["type"] == "table":
        return row_definition(split_table_row(row), blk["header"])
    if blk["type"] == "heading":
        return heading_definition(row)
    if blk["type"] == "bullet":
        return bullet_definition(row)
    return None, None, "", []


# ---------------------------------------------------------------- 族系

def extract_sites(docs):
    """抽出所有编号的"定义点"，并计算每个定义点所属的族系。

    返回 sites: {(前缀, 序号): [(文件, 描述, 族系角色, 族系前缀集合), ...]}

    族系角色由**所属栏目**决定，而不是条目自己叫什么：
      · 表格里的记录 → 看它落在哪一栏（表头那一列的语义）
      · 标题里的记录 → 看它属于哪个章节（最近的上级章节的语义）
      · 列表里的记录 → 同上

    角色不同 = 两套不相干的族系 → 同一前缀被复用（真撞号）。
    """
    per_file_sites = {}
    for f, text in docs.items():
        blocks = split_blocks(text)
        file_prefixes = set()

        # 第一遍：这份文件里定义了哪些前缀（族系前缀集合的兜底）
        for blk in blocks:
            for row in blk["rows"]:
                d, _, _, _ = extract_row(blk, row)
                if d:
                    file_prefixes.add(d[0])

        # 章节栈：[(层级, 标题文本)]
        stack = []

        for blk in blocks:
            if blk["type"] == "table":
                table_prefixes = set()
                for row in blk["rows"]:
                    d, _, _, _ = row_definition(split_table_row(row), blk["header"])
                    if d:
                        table_prefixes.add(d[0])
                cohort = table_prefixes or file_prefixes
            else:
                cohort = file_prefixes

            for row in blk["rows"]:
                d, subj, ctx, _ = extract_row(blk, row)
                if not (d and subj):
                    continue
                if blk["type"] == "table":
                    role = table_role(blk["header"], ctx)
                else:
                    # 标题/列表定义 → 角色取自**所属章节**，
                    # 而不是条目自身文字（那是这条记录的名字）
                    role = role_of(section_context(stack))
                per_file_sites.setdefault(d, []).append((f, subj, role, cohort))

            if blk["type"] == "heading":
                m = HEADING_RE.match(blk["rows"][0].strip())
                body = m.group(1) if m else ""
                level = len(blk["rows"][0]) - len(blk["rows"][0].lstrip("#"))
                while stack and stack[-1][0] >= level:
                    stack.pop()
                stack.append((level, body))
    return per_file_sites


def section_context(stack):
    """取最近的**上级章节**文本。

    注意不能直接取栈顶 —— 栈顶可能是同级的上一个标题
    （"### Q-05" 的下一个是 "### Q-06"，栈顶是 Q-05，不是它们所属的章节）。
    """
    for level, text in reversed(stack):
        if level <= 2:
            return text
    return stack[-1][1] if stack else ""


# ---------------------------------------------------------------- 检查项

def check_g1_gate(root, files, docs):
    """G1 闸门：只允许两份文件，且这两份文件里不得含分析结论。

    闸门管的是**内容**，不是文件数量 —— 所以除了文件名白名单，还要查内容：
      · 标题/表头出现分析产物特征词 → 这份文件在讲分析产物
      · 出现 Q/A/S/T 之外的前缀编号 → 分析结论编号
      · 正文出现"该系统应包含…"这类强断言 → 分析结论
      · 代码块里画流程图 → 分析结论
    """
    problems = []
    seen = defaultdict(int)

    for f in files:
        name = os.path.basename(f)
        if not name.endswith(G1_ALLOWED_BASENAMES):
            problems.append(
                f"G1 闸门：不允许存在额外文件 —— {os.path.relpath(f, root)}"
            )
            continue
        seen[name] += 1
        problems += check_g1_content(f, docs.get(f, ""))

    for suffix, n in seen.items():
        if n > 1:
            problems.append(
                f"G1 闸门：同一份产物出现 {n} 次 —— {suffix}"
                f"（G1 只允许《需求澄清问题清单》与《访谈记录与假设登记册》各一份）"
            )
    return problems


def _match_marker(markers, text):
    """在文本里找第一个命中的特征词（英文大小写不敏感）。"""
    if not text:
        return None
    low = text.lower()
    for m in markers:
        if re.search(r"[A-Za-z]", m):
            if m.lower() in low:
                return m
        elif m in text:
            return m
    return None


def check_g1_content(path, text):
    """检查 G1 允许的两份文件里是否混进了分析结论。"""
    problems = []
    name = os.path.basename(path)
    lines = text.splitlines()

    for blk in split_blocks(text):
        # 1) 标题里出现分析产物名
        if blk["type"] == "heading":
            text_head = blk["rows"][0]
            hit = _match_marker(G1_HEADING_MARKERS, text_head)
            if hit:
                problems.append(
                    f"G1 闸门：{name} 的标题出现分析产物『{hit}』"
                    f"（G1 只允许问题、答复、编号化假设、术语定义）"
                )
            continue

        # 2) 表格表头出现分析结论特征词
        if blk["type"] == "table":
            header = blk["header"]
            if header:
                for cell in header:
                    hit = _match_marker(G1_TABLE_HEADER_MARKERS, cell)
                    if hit:
                        problems.append(
                            f"G1 闸门：{name} 的表格表头出现分析结论特征词"
                            f"『{hit}』（闸门管内容不管文件数量）"
                        )
                        break

        # 3) 出现 Q/A/S/T 之外的前缀编号（定义或引用都算）
        for row in blk["rows"]:
            d, _, _, _ = extract_row(blk, row)
            ids = [d] if d else []
            if not ids:
                ids = [(p, int(n)) for p, n in ID_RE.findall(row)]
            for p, n in ids:
                if p not in G1_ALLOWED_PREFIXES:
                    problems.append(
                        f"G1 闸门：{name} 出现分析结论编号 {p}-{n:02d}"
                        f"（G1 阶段只允许 {'/'.join(G1_ALLOWED_PREFIXES)} 四类编号）"
                    )
                    break

    # 4) 正文强断言（表格行与标题行已由上面的规则覆盖）
    for i, line in enumerate(lines, 1):
        s = line.strip()
        if not s or s.startswith("|"):
            continue
        body = re.sub(r"^#{1,6}\s+", "", s)
        body = re.sub(r"^([-*+]|\d+[.)])\s+", "", body)
        if not body:
            continue
        # 整句是疑问 → 放过（问句本身不是结论）
        # 但只在"问题清单"这类文件里放过 —— 登记册里不该有疑问句
        if name.endswith(G1_QUESTION_LIST_BASENAMES) and re.search(r"[？?]\s*$", body):
            continue
        # 按句读切分：只对"陈述句"判断断言
        for seg in re.split(r"[。！？；]", body):
            seg = seg.strip()
            if not seg:
                continue
            hit = next(
                (p.pattern for p in G1_ASSERTION_PATTERNS if p.search(seg)), None
            )
            if hit:
                problems.append(
                    f"G1 闸门：{name} 出现分析结论断言『{hit}』"
                    f"（G1 只允许问题、答复、编号化假设、术语定义）"
                )
                break

    # 5) 流程图代码块
    for pat in G1_DIAGRAM_PATTERNS:
        if pat.search(text):
            problems.append(
                f"G1 闸门：{name} 出现流程图代码块（闸门管内容不管文件数量）"
            )
            break

    # 6) 无编号的"功能清单"式列表
    problems += check_g1_nominal_list(name, text)

    return problems


def is_nominal_item(s):
    """这一行是不是"清单项"—— 短名词短语（中文或英文）。

    用来识别没编号的功能/能力清单：
      中文：
      · 必须是纯中文（可含空格与全角标点）—— 含 ASCII 字母数字的是编号说明
      · 不能有中文句读 —— 有句读的是解释性句子
      · 长度不超过上限 —— 长的都是解释性文字
      英文：
      · 必须是 1–5 个单词构成的名词短语
      · 不能含动词性/句子性结构（含 is/are/will/should/must、句末标点等）
      · 长度不超过上限
    """
    s = s.strip()
    if not s:
        return False

    # 英文清单项：1–5 个单词，无句法标记
    if re.search(r"[A-Za-z]", s):
        if len(s) > G1_NOMINAL_ITEM_MAX_EN:
            return False
        if re.search(r"[，。；：？！、（）「」《》“”‘’]", s):
            return False
        if re.search(r"[.;:!?()\[\]{}\"'`,]", s):
            return False
        # 含系动词/情态动词 → 是句子不是清单项
        if re.search(
            r"\b(?:is|are|was|were|be|been|will|shall|should|must|can|could|"
            r"would|may|might|has|have|had|does|do|did|that|which|when|"
            r"if|because|so|then|than)\b",
            s,
            re.IGNORECASE,
        ):
            return False
        words = re.findall(r"[A-Za-z][A-Za-z'\-]*", s)
        if not (1 <= len(words) <= 5):
            return False
        return True

    # 中文清单项
    if len(s) > G1_NOMINAL_ITEM_MAX:
        return False
    if re.search(r"[A-Za-z0-9]", s):
        return False
    if re.search(r"[，。；：？！、（）「」《》“”‘’]", s):
        return False
    # 至少要有两个汉字，纯符号不算
    return len(re.findall(r"[一-鿿]", s)) >= 2


def check_g1_nominal_list(name, text):
    """抓"用中性标题掩盖的无编号功能清单"。

    标题写"功能清单"会被 G1_HEADING_MARKERS 抓到，换成"附：本次要做的"
    就能绕过。判据落在**列表项形态**上：连续若干条纯中文短名词短语。

    例外：术语/口径类章节里的名词速查列表是合法的（术语本身就要短），
    按所在章节标题排除。
    """
    problems = []
    current_heading = ""
    for blk in split_blocks(text):
        if blk["type"] == "heading":
            m = HEADING_RE.match(blk["rows"][0].strip())
            current_heading = m.group(1) if m else ""
            continue
        if blk["type"] != "bullet":
            continue
        if any(k in current_heading for k in G1_NOMINAL_EXEMPT_HEADING):
            continue
        run = []
        for row in blk["rows"]:
            m = BULLET_RE.match(row.strip())
            item = m.group(2).strip() if m else row.strip()
            if is_nominal_item(item):
                run.append(item)
                continue
            if len(run) >= G1_NOMINAL_RUN:
                break
            run = []
        if len(run) >= G1_NOMINAL_RUN:
            problems.append(
                f"G1 闸门：{name} 出现无编号的清单式条目"
                f"（如『{run[0]}』『{run[1]}』）"
                f"（G1 只允许问题、答复、编号化假设、术语定义；"
                f"功能/能力清单属于分析结论）"
            )
    return problems


def analyze(docs):
    definitions = {}
    referenced = defaultdict(list)
    for f, text in docs.items():
        for line in text.splitlines():
            all_ids = [(p, int(n)) for p, n in ID_RE.findall(line)]
            for key in all_ids:
                referenced[key].append(f)
    for f, text in docs.items():
        blocks = split_blocks(text)
        for blk in blocks:
            for row in blk["rows"]:
                d, subj, _, all_ids = extract_row(blk, row)
                if d:
                    if d not in definitions:
                        definitions[d] = {"file": f, "subject": subj}
                    elif subj and not definitions[d].get("subject"):
                        definitions[d]["subject"] = subj
                for p, n in all_ids:
                    referenced[(p, n)].append(f)
    return definitions, referenced


def check_closed(definitions, referenced):
    problems = []
    for (p, n), files in sorted(referenced.items()):
        if (p, n) in definitions:
            continue
        if p not in KNOWN_PREFIXES:
            continue
        problems.append(
            f"悬空引用：{p}-{n:02d} 被引用但无定义 —— {os.path.basename(files[0])}"
        )
    return problems


def jaccard(a, b):
    if not a and not b:
        return 1.0
    if not a or not b:
        return 0.0
    return len(a & b) / len(a | b)


def check_prefix_collision(sites):
    """检测"同一前缀被复用于两类事物"。

    - 语义角色不同 → 错误（真撞号）
    - 角色相同但措辞不一致 → 提示（同一事物两种叫法）
    - 角色判不出来 → 退回前缀集合相似度判定
    """
    errors = []
    warnings = []

    for key in sorted(sites):
        entries = sites[key]
        # 同一份产物内部不比对（那是本产物自己的表内差异）
        by_file = defaultdict(list)
        for f, subj, role, cohort in entries:
            by_file[f].append((subj, role, cohort))

        files = sorted(by_file)
        conflict_pairs = []   # (文件A, 描述A, 角色A, 文件B, 描述B, 角色B)
        wording_pairs = []
        for i in range(len(files)):
            for j in range(i + 1, len(files)):
                fa, fb = files[i], files[j]
                for subj_a, role_a, cohort_a in by_file[fa]:
                    for subj_b, role_b, cohort_b in by_file[fb]:
                        if same_thing(subj_a, subj_b):
                            continue
                        # 汇总型产物复述上游编号 → 引用关系，不参与判定
                        if is_summary_artifact(fa) or is_summary_artifact(fb):
                            continue
                        short, long = sorted((subj_a, subj_b), key=len)
                        excerpt = len(short) < SUMMARY_LENGTH_RATIO * len(long)

                        # 角色判定优先：角色不同 = 两套不相干的族系
                        if role_a and role_b:
                            if role_a != role_b:
                                conflict_pairs.append(
                                    (fa, subj_a, role_a, fb, subj_b, role_b)
                                )
                                continue
                            if not excerpt:
                                wording_pairs.append((fa, subj_a, fb, subj_b))
                            continue

                        # 角色判不出来 → 退回前缀集合相似度
                        disjoint = jaccard(cohort_a, cohort_b) < COHORT_JACCARD_MIN
                        if disjoint:
                            conflict_pairs.append(
                                (fa, subj_a, role_a or "—", fb, subj_b, role_b or "—")
                            )
                        elif not excerpt:
                            wording_pairs.append((fa, subj_a, fb, subj_b))

        if conflict_pairs:
            lines = [
                f"编号撞号：{key[0]}-{key[1]:02d} 在两套互不相干的编号族系里"
                f"指代了不同事物"
            ]
            for fa, subj_a, role_a, fb, subj_b, role_b in conflict_pairs:
                lines.append(
                    f"      『{subj_a[:40]}』 —— {os.path.basename(fa)}"
                    f"（{role_a}族）  ≠  『{subj_b[:40]}』 —— {os.path.basename(fb)}"
                    f"（{role_b}族）"
                )
            errors.append("\n".join(lines))

        for fa, subj_a, fb, subj_b in wording_pairs:
            warnings.append(
                f"措辞不一致：{key[0]}-{key[1]:02d} 在两份产物里指同一件事，但名称不同\n"
                f"      『{subj_a[:40]}』 —— {os.path.basename(fa)}\n"
                f"      『{subj_b[:40]}』 —— {os.path.basename(fb)}"
            )
    return errors, warnings


def check_traceability(docs):
    """需求类条目必须能溯源到 A-xx 或 S-xx。

    判定以**定义点**为准（这条记录是在这里被定义的），不是"哪里提到过它"——
    变更分析表、需求优先级评估里复述 F-xx 是引用，不要求它们带 A/S 标注。
    """
    problems = []
    for f, text in docs.items():
        if is_summary_artifact(f):
            continue
        for blk in split_blocks(text):
            for row in blk["rows"]:
                d, _, _, all_ids = extract_row(blk, row)
                if not d or d[0] not in TRACEABLE_PREFIXES:
                    continue
                if not AS_RE.search(row):
                    problems.append(
                        f"溯源缺失：{d[0]}-{d[1]:02d} 无 A-xx / S-xx 标注 —— "
                        f"{os.path.basename(f)}"
                    )
    return problems


def check_sxx_purity(docs):
    """S-xx 只能记"相信什么、怎么验证、不成立会怎样"，不得写成结构化分析结论。

    只检查 **S-xx 的定义行**（定义行 = 该行以 S-xx 开头并给出描述）。
    下游文档里引用 S-15 的句子，即使恰好出现"领域模型"等词，也不是违规。
    """
    problems = []
    for f, text in docs.items():
        for blk in split_blocks(text):
            for row in blk["rows"]:
                d, subj, _, _ = extract_row(blk, row)
                if not d or d[0] != "S" or not subj:
                    continue
                for marker in STRUCTURE_MARKERS:
                    if re.search(r"[A-Za-z]", marker):
                        matched = marker.lower() in subj.lower()
                    else:
                        matched = marker in subj
                    if matched:
                        problems.append(
                            f"S-xx 混入分析结论：{os.path.basename(f)} 的 "
                            f"S-{d[1]:02d} 出现结构特征词『{marker}』"
                        )
                        break
    return problems


def check_sxx_columns(docs):
    """S-xx 登记表必须同时写明「验证方式」与「验证不成立的后果」，且不得留空。

    文档承诺是"必须同时写明验证方式、不成立的后果"——但光有这两列还不够，
    每一条 S-xx 都要真的填上内容，否则"必须"就只是一句口号。

    适用范围：S-xx 的**唯一定义处**——《访谈记录与假设登记册》。
    别的产物里出现 S- 前缀属于前缀复用，由「编号撞号」负责报错。
    """
    problems = []
    for f, text in docs.items():
        name = os.path.basename(f)
        is_register = name.endswith(G1_REGISTER_BASENAMES) or any(
            k in name for k in ("假设", "访谈")
        ) or any(k in name.lower() for k in ("assumption", "interview", "register"))
        for blk in split_blocks(text):
            if blk["type"] != "table":
                # S-xx 写成列表项/标题 → 无法按列校验，
                # 但仍要求同一行里能看到"验证"与"后果"的说明
                for row in blk["rows"]:
                    d, subj, _, _ = extract_row(blk, row)
                    if not d or d[0] != "S" or not subj:
                        continue
                    if not (is_register or "假设" in name or "访谈" in name):
                        continue
                    if _row_has_verification_and_consequence(row):
                        continue
                    problems.append(
                        f"S-xx 未写验证方式与不成立的后果：{name} 的 S-{d[1]:02d}"
                    )
                continue

            header = blk["header"]
            s_rows = []
            for row in blk["rows"]:
                cells = split_table_row(row)
                d, _, _, _ = row_definition(cells, header)
                if d and d[0] == "S":
                    s_rows.append(cells)
            if not s_rows:
                continue
            # 只有登记册、或表头自称"假设内容"的表，才按假设登记表对待
            looks_like_register = bool(
                header and any(
                    ("假设内容" in h) or ("assumption" in h.lower())
                    for h in header
                )
            )
            if not (is_register or looks_like_register):
                continue

            if not header:
                if len(s_rows) >= 2:
                    problems.append(
                        f"S-xx 登记表缺表头：{name} 里的 S-xx 表格"
                        f"没有表头，无法确认「验证方式」与「验证不成立的后果」两列"
                    )
                continue

            v_idx = find_column(header, SXX_VERIFICATION_COLUMNS)
            c_idx = find_column(header, SXX_CONSEQUENCE_COLUMNS)
            st_idx = find_column(header, ("状态", "status"))
            if v_idx is None:
                problems.append(
                    f"S-xx 登记表缺列：{name} 的 S-xx 表格"
                    f"没有「验证方式」列"
                )
            if c_idx is None:
                problems.append(
                    f"S-xx 登记表缺列：{name} 的 S-xx 表格"
                    f"没有「验证不成立的后果」列"
                )

            for cells in s_rows:
                label = cells[0] if cells else "S-xx"
                if v_idx is not None and v_idx < len(cells) and is_empty_cell(cells[v_idx]):
                    problems.append(
                        f"S-xx 验证方式为空：{name} 的 {label}"
                    )
                if c_idx is None or c_idx >= len(cells):
                    continue
                if not is_empty_cell(cells[c_idx]):
                    continue
                status = cells[st_idx] if st_idx is not None and st_idx < len(cells) else ""
                if not re.search(
                    r"已关闭|作废|已验证|不适用|无需验证|closed|void|verified|n/a|not applicable",
                    status,
                    re.IGNORECASE,
                ):
                    problems.append(
                        f"S-xx 未写不成立的后果：{name} 的 {label}"
                    )
    return problems


def find_column(header, keywords):
    """在表头里找出与任一关键词匹配的列号。

    英文表头大小写混合（"Verification Method"），故对 ASCII 关键词
    做大小写不敏感匹配；中文关键词原样匹配。
    """
    for idx, h in enumerate(header):
        if not h:
            continue
        h_low = h.lower()
        for kw in keywords:
            if kw in h:
                return idx
            if re.search(r"[A-Za-z]", kw) and kw.lower() in h_low:
                return idx
    return None


def is_empty_cell(cell):
    """单元格是否等于"没写"。"""
    c = cell.strip()
    if not c:
        return True
    if c in {"—", "-", "–", "/", "同上", "N/A", "n/a", "无", "待补", "待定", "TBD", "？", "?"}:
        return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("directory")
    ap.add_argument("--stage", choices=["G1", "G2", "G3"], default="G3")
    args = ap.parse_args()

    root = os.path.abspath(args.directory)
    if not os.path.isdir(root):
        print(f"目录不存在：{root}")
        return 2

    files = collect_files(root)
    docs = read_all(files)
    if not docs:
        print(f"目录下没有 .md 文件：{root}")
        return 2

    errors = []
    warnings = []
    if args.stage == "G1":
        errors += check_g1_gate(root, files, docs)

    definitions, referenced = analyze(docs)
    errors += check_closed(definitions, referenced)
    if args.stage in ("G2", "G3"):
        sites = extract_sites(docs)
        collide, wording = check_prefix_collision(sites)
        errors += collide
        warnings += wording
    if args.stage in ("G2", "G3"):
        errors += check_traceability(docs)
    errors += check_sxx_purity(docs)
    errors += check_sxx_columns(docs)

    print(f"检查目录：{root}")
    print(
        f"阶段：{args.stage}    文件数：{len(files)}    "
        f"已定义编号：{len(definitions)}"
    )
    print("-" * 62)

    if errors:
        print(f"发现 {len(errors)} 个错误：")
        for p in errors:
            print(f"  ✗ {p}")
    if warnings:
        print(f"另有 {len(warnings)} 处提示（不判错）：")
        for p in warnings:
            print(f"  ⚠ {p}")
    if not errors and not warnings:
        print("✓ 全部检查通过")

    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
