"""
Validator for tracked changes in Word documents.

Detects untracked edits in a Word document: text that differs from the
original without a <w:ins>/<w:del> wrapper recording it. The tracked changes
that are new relative to the original are undone, and the result is compared
against the original; whatever text still differs was edited without being
tracked.

The body (word/document.xml) is compared, and so is each header, footer,
footnotes and endnotes part, against the original's part of the same name.
Other parts, comments among them, are not checked. A page-number field
whose cached result is a plain number counts as its name in braces
("{PAGE}"), not as that number, which any application that repaginates the
document rewrites.
"""

import re
import tempfile
import zipfile
from difflib import SequenceMatcher
from pathlib import Path

import defusedxml.ElementTree as ET
from defusedxml.common import DefusedXmlException

from helpers import rendered_text, safe_extract


XML_ERRORS = (ET.ParseError, DefusedXmlException, LookupError, ValueError)


class _WorkSpent(Exception):

    pass


class _Matcher(SequenceMatcher):

    def __init__(self, a, b, allowance):
        self.allowance = allowance  
        super().__init__(None, a, b, autojunk=False)

    def find_longest_match(self, alo=0, ahi=None, blo=0, bhi=None):
        items = self.a[alo:ahi]
        self.allowance[0] -= len(items) + sum(len(self.b2j.get(x, ())) for x in items)
        if self.allowance[0] < 0:
            raise _WorkSpent
        return super().find_longest_match(alo, ahi, blo, bhi)


class RedliningValidator:

    def __init__(self, unpacked_dir, original_docx, verbose=False):
        self.unpacked_dir = Path(unpacked_dir)
        self.original_docx = Path(original_docx)
        self.verbose = verbose
        self._work_left = [self.WORK_ALLOWED]
        self.namespaces = {
            "w": "http://schemas.openxmlformats.org/wordprocessingml/2006/main"
        }

    def repair(self) -> int:
        return 0

    def validate(self):
        modified_file = self.unpacked_dir / "word" / "document.xml"
        if not modified_file.exists():
            print(f"FAILED - Modified document.xml not found at {modified_file}")
            return False

        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)

            try:
                with zipfile.ZipFile(self.original_docx, "r") as zip_ref:
                    safe_extract(zip_ref, temp_path)
            except Exception as e:
                print(f"FAILED - Error unpacking original docx: {e}")
                return False

            original_file = temp_path / "word" / "document.xml"
            if not original_file.exists():
                print(
                    f"FAILED - Original document.xml not found in {self.original_docx}"
                )
                return False

            sides = (("original", temp_path), ("modified", self.unpacked_dir))
            change_count, failures, differences = 0, [], []
            for part in self._parts_to_compare(temp_path, self.unpacked_dir):
                roots = []
                for side, unpacked in sides:
                    try:
                        roots.append(self._parse_part(unpacked / part))
                    except XML_ERRORS as e:
                        failures.append(
                            f"FAILED - Error parsing {part} of the {side} document: {e}"
                        )
                if len(roots) < len(sides):
                    continue  
                new_changes, original_text, modified_text = self._compare_part(*roots)
                change_count += len(new_changes)
                if modified_text != original_text:
                    differences.append((part, original_text, modified_text))

            if differences:
                failures.append(self._generate_detailed_diff(differences))
            if failures:
                print("\n".join(failures))
                return False

            if self.verbose:
                print(
                    f"PASSED - All {change_count} change(s) against the original "
                    "are properly tracked"
                )
            return True

    OTHER_PARTS = (
        "word/header*.xml",
        "word/footer*.xml",
        "word/footnotes.xml",
        "word/endnotes.xml",
    )

    def _parts_to_compare(self, original_dir, modified_dir):
        others = set()
        for unpacked in (Path(original_dir), Path(modified_dir)):
            for pattern in self.OTHER_PARTS:
                others.update(
                    path.relative_to(unpacked).as_posix()
                    for path in unpacked.glob(pattern)
                )
        return ["word/document.xml", *sorted(others)]

    def _compare_part(self, original_root, modified_root):
        for root in (original_root, modified_root):
            self._flatten_text_elements(root)
        new_changes = self._new_tracked_changes(original_root, modified_root)
        self._remove_tracked_changes(modified_root, new_changes)
        return (
            new_changes,
            self._extract_text_content(original_root),
            self._extract_text_content(modified_root),
        )

    def _parse_part(self, path):
        if not path.is_file():
            return ET.fromstring("<absent/>")
        return ET.parse(path).getroot()

    def _flatten_text_elements(self, root):
        for elem in self._text_elements(root):
            if len(elem):
                elem.text = "".join(elem.itertext())
                for child in list(elem):
                    elem.remove(child)

    def _tracked_change_elements(self, root):
        w = self.namespaces["w"]
        tags = (f"{{{w}}}ins", f"{{{w}}}del", f"{{{w}}}moveFrom", f"{{{w}}}moveTo")
        return [elem for elem in root.iter() if elem.tag in tags]

    def _rendered_text(self, elem):
        preserve = elem.get("{http://www.w3.org/XML/1998/namespace}space") == "preserve"
        return rendered_text(elem.text or "", preserve)

    def _text_elements(self, elem):
        w = self.namespaces["w"]
        return [
            node
            for node in elem.iter()
            if node.tag in (f"{{{w}}}t", f"{{{w}}}delText")
        ]

    def _tracked_change_key(self, elem):
        w = self.namespaces["w"]
        text = "".join(self._rendered_text(node) for node in self._text_elements(elem))
        return (elem.tag, elem.get(f"{{{w}}}author"), elem.get(f"{{{w}}}date"), text)

    def _new_tracked_changes(self, original_root, modified_root):
        original = self._tracked_change_elements(original_root)
        modified = self._tracked_change_elements(modified_root)

        pool = {}
        for elem in original:
            pool.setdefault(self._tracked_change_key(elem), []).append(elem)

        matched, leftover = set(), []
        for elem in modified:
            bucket = pool.get(self._tracked_change_key(elem))
            if bucket:
                matched.add(bucket.pop())
            else:
                leftover.append(elem)

        def group(elem):
            return self._tracked_change_key(elem)[:3]

        def text_of(elems):
            return "".join(self._tracked_change_key(e)[3] for e in elems)

        unmatched_original = {}
        for elem in original:
            if elem not in matched:
                unmatched_original.setdefault(group(elem), []).append(elem)

        by_group = {}
        for elem in leftover:
            by_group.setdefault(group(elem), []).append(elem)

        new = set()
        for key, elems in by_group.items():
            rebuilt = text_of(elems)
            if rebuilt and rebuilt == text_of(unmatched_original.get(key, [])):
                continue  
            new.update(elems)
        return new

    def _generate_detailed_diff(self, differences):
        self._work_left = [self.WORK_ALLOWED]
        error_parts = [
            "FAILED - Document text doesn't match after removing the tracked changes",
            "",
            "Likely causes:",
            "  1. Modified text inside another author's <w:ins> or <w:del> tags",
            "  2. Made edits without proper tracked changes",
            "  3. Didn't nest <w:del> inside <w:ins> when deleting another's insertion",
            "  4. Rewrote another author's <w:ins>/<w:del> and changed its text on",
            "     the way. A tracked change from the original is recognised by its",
            "     author, date and text; anything that doesn't reproduce one exactly",
            "     reads as new, and the text it carried is reported missing.",
            "",
            "For pre-redlined documents, use correct patterns:",
            "  - To reject another's INSERTION: Nest <w:del> inside their <w:ins>",
            "  - To reject PART of one: nest <w:del> around only the runs you reject.",
            "    Their <w:ins> may be split around it, so long as the pieces keep",
            "    their author and date and still spell out the same text.",
            "  - To restore another's DELETION: Add new <w:ins> AFTER their <w:del>",
            "",
        ]

        explain_page_fields = False
        for part, original_text, modified_text in differences:
            body = part == "word/document.xml"
            heading = "Differences:" if body else f"Differences in {part}:"
            if error_parts[-1]:
                error_parts.append("")  
            word_diff = self._word_diff(original_text, modified_text)
            error_parts.extend([heading, "=" * len(heading), word_diff])
            if original_text.replace("\n", "") == modified_text.replace("\n", ""):
                error_parts.append("Only paragraph breaks differ here.")
            if re.search(r"\{(%s)\}" % "|".join(self.PAGE_FIELDS), word_diff):
                explain_page_fields = True
        if explain_page_fields:
            error_parts.extend(["", self.PAGE_FIELD_NOTE])
        if self._work_left[0] < 0:
            error_parts.extend(["", self.WORK_SPENT_NOTE])

        return "\n".join(error_parts)

    def _word_diff(self, original_text, modified_text):
        out = []
        steps = self._steps(original_text.split("\n"), modified_text.split("\n"))
        for tag, was, now in steps:
            if tag == "replace" and len(was) == len(now):
                out.extend(self._mark_changes(x, y) for x, y in zip(was, now) if x != y)
            elif tag != "equal":
                out.append(self._mark_changes("\n".join(was), "\n".join(now)))
        return "\n".join(out)

    def _mark_changes(self, old, new, by_character=False, trim=True):

        def mark(text, opening, closing):
            marked = re.sub(r"[^\n]+", lambda m: opening + m[0] + closing, text)
            return marked if marked.strip("\n") or opening == "{+" else ""

        pattern = "(?s)." if by_character else r"\S+\s*|\s+"
        out = []
        steps = self._steps(re.findall(pattern, old), re.findall(pattern, new), trim)
        for tag, was, now in steps:
            lone_word = len(was) == len(now) == 1
            was, now = "".join(was), "".join(now)
            if tag == "equal":
                out.append(now)
            elif tag == "replace" and not by_character:
                long_word = lone_word and min(len(was), len(now)) > self.LONG_WORD
                marked = self._mark_changes(was, now, by_character=True, trim=long_word)
                out.append(marked)
            else:
                out.append(mark(was, "[-", "-]") + mark(now, "{+", "+}"))
        return "".join(out)

    WORK_ALLOWED = 10_000_000
    LONG_WORD = 200

    def _steps(self, a, b, trim=True):

        def shared_start(x, y):
            return next(
                (i for i, (p, q) in enumerate(zip(x, y)) if p != q), min(len(x), len(y))
            )

        head = shared_start(a, b) if trim else 0
        tail = shared_start(a[head:][::-1], b[head:][::-1]) if trim else 0
        a_mid, b_mid = a[head : len(a) - tail], b[head : len(b) - tail]
        try:
            if self._work_left[0] < len(a_mid):
                self._work_left[0] = -1
                raise _WorkSpent
            numbers = {}
            numbered = [
                [numbers.setdefault(x, len(numbers)) for x in s] for s in (a_mid, b_mid)
            ]
            opcodes = _Matcher(*numbered, self._work_left).get_opcodes()
            steps = [(tag, a_mid[i:j], b_mid[m:n]) for tag, i, j, m, n in opcodes]
        except _WorkSpent:
            steps = [("replace", a_mid, b_mid)]
        return [
            ("equal", a[:head], b[:head]),
            *steps,
            ("equal", a[len(a) - tail :], b[len(b) - tail :]),
        ]

    def _remove_tracked_changes(self, root, targets):
        w = self.namespaces["w"]
        ins_tag = f"{{{w}}}ins"
        del_tag = f"{{{w}}}del"
        move_from_tag = f"{{{w}}}moveFrom"
        move_to_tag = f"{{{w}}}moveTo"

        self._merge_split_paragraphs(root, targets)

        for parent in root.iter():
            to_remove = []
            for child in parent:
                if child.tag in (ins_tag, move_to_tag) and child in targets:
                    to_remove.append(child)
            for elem in to_remove:
                parent.remove(elem)

        renamed = {
            f"{{{w}}}delText": f"{{{w}}}t",
            f"{{{w}}}delInstrText": f"{{{w}}}instrText",
        }

        for parent in root.iter():
            to_process = []
            for child in parent:
                if child.tag in (del_tag, move_from_tag) and child in targets:
                    to_process.append((child, list(parent).index(child)))

            for del_elem, del_index in reversed(to_process):
                for elem in del_elem.iter():
                    elem.tag = renamed.get(elem.tag, elem.tag)

                for child in reversed(list(del_elem)):
                    parent.insert(del_index, child)
                parent.remove(del_elem)

        range_tags = (
            f"{{{w}}}moveFromRangeStart",
            f"{{{w}}}moveFromRangeEnd",
            f"{{{w}}}moveToRangeStart",
            f"{{{w}}}moveToRangeEnd",
        )
        for parent in root.iter():
            to_remove = [
                c
                for c in parent
                if c.tag in range_tags and len(c) == 0 and not (c.text or "").strip()
            ]
            for elem in to_remove:
                parent.remove(elem)

    def _merge_split_paragraphs(self, root, targets):
        w = self.namespaces["w"]
        p_tag = f"{{{w}}}p"
        ppr_tag = f"{{{w}}}pPr"
        marker_path = f"{ppr_tag}/{{{w}}}rPr/{{{w}}}ins"

        for parent in list(root.iter()):
            for para in reversed([child for child in parent if child.tag == p_tag]):
                if not any(m in targets for m in para.findall(marker_path)):
                    continue
                siblings = list(parent)
                index = siblings.index(para)
                following = siblings[index + 1] if index + 1 < len(siblings) else None
                if following is None or following.tag != p_tag:
                    continue
                if any(self._text_elements(c) for c in para if c.tag == ppr_tag):
                    continue
                insert_at = 1 if len(following) and following[0].tag == ppr_tag else 0
                for child in reversed([c for c in para if c.tag != ppr_tag]):
                    following.insert(insert_at, child)
                parent.remove(para)

    def _extract_text_content(self, root):
        p_tag = f"{{{self.namespaces['w']}}}p"

        paragraphs = []
        for p_elem in root.findall(f".//{p_tag}"):
            paragraph_text = self._paragraph_text(p_elem)
            if paragraph_text:
                paragraphs.append(paragraph_text)

        return "\n".join(paragraphs)

    PAGE_FIELDS = {"PAGE", "NUMPAGES", "SECTIONPAGES"}
    PAGE_NUMBER = re.compile(r"-? ?[0-9]{1,6} ?-?|[ivxlcdm]{1,8}|[a-z]{1,2}|", re.I)
    PAGE_FIELD_NOTE = (
        "Note: {PAGE}, {NUMPAGES} or {SECTIONPAGES} above stands for a page-number\n"
        "field. Word recomputes the number it displays, so the number stored in\n"
        "the file is not compared, but adding or removing the field still counts."
    )

    WORK_SPENT_NOTE = (
        "Note: the texts were too long or repetitive to compare closely all the\n"
        "way through, so a passage shown whole, as removed and then added, may\n"
        "differ in only a few characters. Compare such a passage with the\n"
        "original directly to find the edit."
    )

    def _paragraph_text(self, p_elem):
        w = self.namespaces["w"]
        t_tag, instr_tag = f"{{{w}}}t", f"{{{w}}}instrText"
        fld_char, fld_simple = f"{{{w}}}fldChar", f"{{{w}}}fldSimple"

        def page_field(instruction, field):
            words = instruction.split()
            locked = field.get(f"{{{w}}}fldLock") in ("1", "true", "on")
            if words and words[0].upper() in self.PAGE_FIELDS and not locked:
                return words[0].upper()

        def shown(name, result):
            return "{%s}" % name if self.PAGE_NUMBER.fullmatch(result) else result

        parts, fields = [], []
        skipped = set()  

        def sink():
            for *_, result in reversed(fields):
                if result is not None:
                    return result
            return parts

        for elem in p_elem.iter():
            if elem.tag == fld_simple:
                name = page_field(elem.get(f"{{{w}}}instr", ""), elem)
                if name:
                    texts = [self._rendered_text(t) for t in elem.iter(t_tag)]
                    sink().append(shown(name, "".join(texts).strip()))
                    skipped.update(elem.iter(t_tag))
            elif elem.tag == fld_char:
                kind = elem.get(f"{{{w}}}fldCharType")
                if kind == "begin":
                    fields.append([elem, "", False, None])
                elif kind == "separate" and fields and not fields[-1][2]:
                    fields[-1][2] = True
                    if page_field(fields[-1][1], fields[-1][0]):
                        fields[-1][3] = []
                elif kind == "end" and fields:
                    begin, instruction, _, result = fields.pop()
                    name = page_field(instruction, begin)
                    if name:
                        sink().append(shown(name, "".join(result or []).strip()))
            elif elem.tag == instr_tag and fields and not fields[-1][2]:
                fields[-1][1] += elem.text or ""
            elif elem.tag == t_tag and elem not in skipped:
                sink().append(self._rendered_text(elem))
        for *_, result in fields:
            parts.extend(result or [])
        return "".join(parts)


if __name__ == "__main__":
    raise RuntimeError("This module should not be run directly.")
