# COVER PAGE GENERATOR - USAGE GUIDE

## 🎯 The Perfect System

Your **TEMPLATE_CAPTION.docx** stays **READ-ONLY** (never edited).
The generator **prompts you** for values and **creates a new file**.

---

## Quick Start

### **Windows (Easiest):**
1. Double-click `GENERATE_COVER.bat`
2. Answer the prompts
3. Done! New file created.

### **Mac/Linux:**
```bash
python3 generate_cover.py
```

### **Command Line (Any OS):**
```bash
python generate_cover.py
```

---

## What It Does

### **Step 1: Prompts You For Values**

```
NINTH CIRCUIT COVER PAGE GENERATOR
============================================================

Enter Ninth Circuit case number (or press Enter for blank):
  Example: 24-1234
  Case #: ▮

Enter filing name:
  Examples:
    APPELLANT'S OPENING BRIEF
    APPELLANT'S REPLY BRIEF
    MOTION FOR STAY PENDING APPEAL
  Filing: ▮

Enter district judge name (or press Enter for placeholder):
  Example: Stacy Beckerman
  Judge: ▮
```

### **Step 2: Swaps Values Into Template**

The script:
1. Opens `TEMPLATE_CAPTION.docx` (READ-ONLY, never modified)
2. Extracts the Word XML
3. Replaces placeholders:
   - "No. 6461" → Your case number
   - "APPELLANTS OPENING BRIEF" → Your filing name
   - "Hon. Stacy Beckerman" → Your judge name
4. Saves as new file: `COVER_PAGE_YYYYMMDD_HHMMSS.docx`

### **Step 3: You Get A Fresh File**

```
✓ Cover page generated: COVER_PAGE_20251206_155823.docx
  Case Number: No. 24-1234
  Filing Name: APPELLANT'S REPLY BRIEF
  Judge: Hon. Michael McShane

DONE! Your cover page is ready.
```

---

## Example Sessions

### **Example 1: Opening Brief (Case Number Assigned)**

```
Case #: 24-5678
Filing: APPELLANT'S OPENING BRIEF
Judge: Michael McShane

Result: COVER_PAGE_20251206_160000.docx
- No. 24-5678
- APPELLANT'S OPENING BRIEF
- Hon. Michael McShane
```

### **Example 2: Reply Brief (No Case Number Yet)**

```
Case #: [press Enter]
Filing: APPELLANT'S REPLY BRIEF
Judge: [press Enter]

Result: COVER_PAGE_20251206_160100.docx
- No. ____________________
- APPELLANT'S REPLY BRIEF
- Hon. [District Judge Name]
```

### **Example 3: Emergency Motion**

```
Case #: [press Enter]
Filing: EMERGENCY MOTION FOR STAY PENDING APPEAL
Judge: Stacy Beckerman

Result: COVER_PAGE_20251206_160200.docx
- No. ____________________
- EMERGENCY MOTION FOR STAY PENDING APPEAL
- Hon. Stacy Beckerman
```

---

## File Structure

```
ninth_circuit_package/
├── TEMPLATE_CAPTION.docx       ← MASTER (READ-ONLY, never edit!)
├── generate_cover.py           ← Generator script
├── GENERATE_COVER.bat          ← Windows launcher (double-click)
└── COVER_PAGE_*.docx          ← Generated files (timestamped)
```

---

## Common Filing Names

Copy/paste these when prompted:

### **Briefs:**
- `APPELLANT'S OPENING BRIEF`
- `APPELLANT'S REPLY BRIEF`
- `APPELLEE'S ANSWERING BRIEF`

### **Motions:**
- `MOTION FOR STAY PENDING APPEAL`
- `EMERGENCY MOTION FOR STAY PENDING APPEAL`
- `MOTION TO EXTEND TIME`
- `MOTION FOR LEAVE TO FILE OVERLENGTH BRIEF`
- `MOTION TO SUPPLEMENT THE RECORD`

### **Other:**
- `PETITION FOR REHEARING`
- `PETITION FOR REHEARING EN BANC`
- `SUGGESTION FOR REHEARING EN BANC`

---

## Workflow Integration

### **For Each Filing:**

1. **Generate Cover:**
   ```bash
   python generate_cover.py
   # Answer prompts
   ```

2. **Verify:**
   ```bash
   # Open COVER_PAGE_*.docx
   # Check it looks correct
   ```

3. **Convert to PDF:**
   - Word: File → Export → Create PDF
   - LibreOffice: File → Export as PDF
   - Command line: `libreoffice --headless --convert-to pdf COVER_PAGE_*.docx`

4. **Combine with Body:**
   ```bash
   pdftk cover.pdf body.pdf cat output FINAL_BRIEF.pdf
   ```

5. **File with Court:**
   - Upload FINAL_BRIEF.pdf to CM/ECF

---

## Customization

### **To Update Contact Info:**

Edit `TEMPLATE_CAPTION.docx` ONE TIME:
1. Open it
2. Update your address/phone/email
3. Save and close
4. Mark it read-only: `chmod 444 TEMPLATE_CAPTION.docx`

The generator will use your updated info for all future covers.

### **To Add More Placeholders:**

Edit `generate_cover.py`:

1. **Add prompt in `prompt_for_values()`:**
```python
# Add after existing prompts
print("\nEnter your new field:")
new_field = input("  Value: ").strip()
```

2. **Add to return dictionary:**
```python
return {
    'case_number': case_number,
    'filing_name': filing_name,
    'judge_name': judge_name,
    'new_field': new_field  # Add this
}
```

3. **Add replacement in `generate_cover()`:**
```python
# Add after existing replacements
content = content.replace('PLACEHOLDER_TEXT', values['new_field'])
```

---

## Troubleshooting

### **"Template not found"**
- Make sure `TEMPLATE_CAPTION.docx` is in the same folder as `generate_cover.py`

### **"No module named zipfile"**
- Update Python: `python --version` should be 3.6+
- Install Python from python.org

### **"Permission denied" on Windows**
- Right-click → Run as Administrator

### **Generated file won't open**
- Check if you have enough disk space
- Try running again
- Verify `TEMPLATE_CAPTION.docx` isn't corrupted

### **Formatting looks wrong**
- Your template might have been modified
- Re-download fresh `TEMPLATE_CAPTION.docx`
- Or use the original `CAPTION_NINTH.docx` as template

---

## Advanced Usage

### **Batch Generation (Multiple Covers at Once):**

Create `batch_generate.py`:
```python
from generate_cover import generate_cover

filings = [
    {'case_number': 'No. 24-1234', 'filing_name': 'OPENING BRIEF', 'judge_name': 'Hon. McShane'},
    {'case_number': 'No. 24-1234', 'filing_name': 'REPLY BRIEF', 'judge_name': 'Hon. McShane'},
]

for i, values in enumerate(filings):
    generate_cover('TEMPLATE_CAPTION.docx', f'COVER_{i+1}.docx', values)
```

Run: `python batch_generate.py`

### **Command Line Args (No Prompts):**

Add to `generate_cover.py`:
```python
import sys

if len(sys.argv) == 4:
    values = {
        'case_number': sys.argv[1],
        'filing_name': sys.argv[2],
        'judge_name': sys.argv[3]
    }
else:
    values = prompt_for_values()
```

Use: `python generate_cover.py "No. 24-1234" "OPENING BRIEF" "Hon. McShane"`

---

## Why This System Works

### ✅ **Template Stays Pristine**
- Never manually edited
- No risk of corruption
- One source of truth

### ✅ **No Formatting Errors**
- Every cover identical
- Perfect Word XML structure
- VML graphics preserved

### ✅ **Fast & Easy**
- 3 prompts = new cover
- No hunting for placeholders
- No manual find/replace

### ✅ **Portable**
- Works on Windows, Mac, Linux
- Python is cross-platform
- No special software needed

### ✅ **Auditable**
- Timestamped filenames
- Know exactly when generated
- Easy to track versions

---

## Security Note

The generator script:
- ✅ Opens template READ-ONLY
- ✅ Never modifies original
- ✅ Only creates new files
- ✅ No network access
- ✅ No data collection

Safe to use for confidential legal documents.

---

## Support

If you encounter issues:
1. Check this guide first
2. Verify template file exists
3. Update Python if needed
4. Re-download fresh template

**The template is gold - protect it!** 🎯
