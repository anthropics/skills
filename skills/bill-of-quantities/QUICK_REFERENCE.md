# Bill of Quantities Skill - Quick Reference

## 📍 Location

```
/Users/user/Documents/GitHub/skills/skills/bill-of-quantities/
```

## 📚 What You Have

| File | Purpose |
|------|---------|
| `SKILL.md` | Complete skill definition & methodology |
| `DEVELOPMENT.md` | Setup guide & evaluation workflow |
| `references/standards.md` | BoQ standards, units, examples |
| `evals/evals.json` | 3 test cases for evaluation |
| `scripts/generate_sample_boq.py` | Generate sample outputs |

## 🚀 Quick Commands

### View Skill Definition

```bash
cat /Users/user/Documents/GitHub/skills/skills/bill-of-quantities/SKILL.md | head -100
```

### Generate Sample Outputs

```bash
cd /Users/user/Documents/GitHub/skills/skills/bill-of-quantities
python scripts/generate_sample_boq.py
cat sample_outputs/sample_boq.md
```

### View Test Cases

```bash
cat /Users/user/Documents/GitHub/skills/skills/bill-of-quantities/evals/evals.json | python -m json.tool | head -50
```

### Read Reference Standards

```bash
cat /Users/user/Documents/GitHub/skills/skills/bill-of-quantities/references/standards.md | head -80
```

## 🎯 What the Skill Does

**Input**: Construction specs, drawings, project details  
**Process**: Extract quantities → Organize sections → Validate assumptions → Generate outputs  
**Output**: CSV/Excel, Markdown table, Analysis report

## 📊 BoQ Section Structure

```
A. Preliminaries      → Site setup, insurance, supervision
B. Groundwork         → Excavation, foundations, drainage  
C. Structures         → Concrete, masonry, structural work
D. Finishes           → Paint, flooring, doors, windows
E. Services           → Electrical, plumbing, HVAC
F. External Works     → Paving, landscaping, drainage
G. Contingency        → Risk allowance, provisional sums
```

## 🧪 Test Cases

| Eval | Complexity | Focus | Expected Items |
|------|-----------|-------|-----------------|
| 1 | Low-Med | Simple single-storey building | 20+ |
| 2 | Med-High | Multi-storey residential | 40+ |
| 3 | High | Incomplete specs + estimation | 15-25 + assumptions |

## 💾 Output Example

**CSV Format** (5 columns):

```
Section | Code | Item Description | Qty | Unit
A | A.1 | Site Mobilization | 1 | Item
B | B.1 | Excavation | 1000 | m³
C | C.1 | Concrete Walls | 2700 | m²
D | D.1 | Plastering | 2700 | m²
E | E.1 | Electrical Distribution | 1 | Item
F | F.1 | External Paving | 200 | m²
```

**Markdown Format** (Table):

```
| Section | Item | Qty | Unit |
|---------|------|-----|------|
| A | Site Mobilization | 1 | Item |
| B | Excavation | 1000 | m³ |
| C | Concrete Walls | 2700 | m² |
```

## ✅ Quality Criteria

When evaluating outputs:

- ✓ Complete (all items extracted)
- ✓ Accurate (quantities calculated correctly)
- ✓ Organized (proper sections)
- ✓ Clear (descriptions detailed enough for pricing)
- ✓ Documented (assumptions listed)
- ✓ Formatted (CSV/Markdown/report provided)

## 🔄 Evaluation Workflow

1. **Run with-skill version** (uses this skill to generate BoQ)
2. **Run baseline version** (no skill, compare results)
3. **Review qualitative outputs** - BoQ completeness, clarity, organization
4. **Check quantitative metrics** - Items count, section breakdown, accuracy
5. **Gather feedback** - What worked, what needs improvement
6. **Iterate** - Refine SKILL.md based on findings

## 🎓 Development Cycle

```
Create ✅ → Test ✅ → Evaluate ⏳ → Iterate ⏳ → Refine ⏳ → Deploy ⏳
```

## 📖 Documentation

- **SKILL.md**: 400+ lines of comprehensive extraction guidance
- **DEVELOPMENT.md**: Setup, evaluation, iteration workflow
- **references/standards.md**: RICS standards, units, calculations, examples
- **Sample outputs**: CSV, Markdown, report templates

## 💡 Key Concepts

### RICS Standard Sections

Industry-standard organization for construction items (A-G framework)

### Assumptions Documentation

Every inference noted with confidence level (High/Medium/Low)

### Output Formats

Multiple formats for different use cases:

- CSV for import into estimating software
- Markdown for documentation & sharing  
- Report for analysis & recommendations

### Quantity Validation

Extracted quantities cross-referenced against building dimensions

## 🚦 Status

| Task | Status |
|------|--------|
| Skill definition written | ✅ Complete |
| Test cases created | ✅ Complete |
| Reference materials | ✅ Complete |
| Helper scripts | ✅ Complete |
| Ready for evaluation | ✅ Ready |

---

**Next**: Run evaluations with skill-creator framework to test and iterate

For more details: See `DEVELOPMENT.md`
