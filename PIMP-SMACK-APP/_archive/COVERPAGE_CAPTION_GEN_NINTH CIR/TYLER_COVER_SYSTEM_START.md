# TYLER'S COVER PAGE SYSTEM - QUICK START

## 🎯 **YOU NAILED IT!**

Your approach is 100% correct:
- **Template stays READ-ONLY** (never manually edited)
- **Generator prompts for values** (case #, filing name, judge)
- **Swaps placeholders automatically**
- **Creates fresh file every time**

---

## **FILES YOU DOWNLOADED:**

1. **TEMPLATE_CAPTION.docx** - Your perfect master template (NEVER EDIT!)
2. **generate_cover.py** - The generator script
3. **GENERATE_COVER.bat** - Windows double-click launcher
4. **COVER_GENERATOR_GUIDE.md** - Full documentation

---

## **SETUP (One Time):**

### **Windows:**
1. Put all 4 files in a folder (e.g., `C:\NinthCircuit\`)
2. Make sure Python is installed
   - Check: Open Command Prompt, type `python --version`
   - If not installed: Download from python.org

### **Mac/Linux:**
1. Put all files in a folder
2. Python is already installed

---

## **USAGE (Every Time You Need a Cover):**

### **Windows:**
```
1. Double-click GENERATE_COVER.bat
2. Answer 3 prompts:
   - Case number (or blank)
   - Filing name
   - Judge name (or blank)
3. Done! New file created with timestamp
```

### **Mac/Linux:**
```bash
cd /path/to/folder
python3 generate_cover.py
# Answer prompts
# Done!
```

---

## **EXAMPLE SESSION:**

```
NINTH CIRCUIT COVER PAGE GENERATOR
============================================================

Enter Ninth Circuit case number (or press Enter for blank):
  Example: 24-1234
  Case #: 24-5678                         ← YOU TYPE THIS

Enter filing name:
  Examples:
    APPELLANT'S OPENING BRIEF
    APPELLANT'S REPLY BRIEF
    MOTION FOR STAY PENDING APPEAL
  Filing: APPELLANT'S REPLY BRIEF         ← YOU TYPE THIS

Enter district judge name (or press Enter for placeholder):
  Example: Stacy Beckerman
  Judge: Michael McShane                  ← YOU TYPE THIS

============================================================
GENERATING COVER PAGE...
============================================================

✓ Cover page generated: COVER_PAGE_20251206_155823.docx
  Case Number: No. 24-5678
  Filing Name: APPELLANT'S REPLY BRIEF
  Judge: Hon. Michael McShane

============================================================
DONE! Your cover page is ready.
============================================================

Output file: COVER_PAGE_20251206_155823.docx

Next steps:
  1. Open the file to verify it looks correct
  2. Export to PDF
  3. Combine with your body text PDF
  4. File with Ninth Circuit
```

---

## **YOUR WORKFLOW:**

```
For Each New Filing:
│
├─► 1. Run generator (double-click GENERATE_COVER.bat)
│      Answer prompts
│      
├─► 2. Verify cover looks right
│      Open COVER_PAGE_*.docx
│      
├─► 3. Export to PDF
│      File → Save As → PDF
│      
├─► 4. Combine with body
│      pdftk cover.pdf body.pdf cat output FINAL.pdf
│      OR: ilovepdf.com/merge_pdf
│      
└─► 5. File with court
       Upload to CM/ECF
```

---

## **ADVANTAGES:**

✅ **Template Never Gets Messed Up**
   - Stays pristine forever
   - No accidental edits
   - One source of truth

✅ **No Manual Editing**
   - Generator does the work
   - Consistent every time
   - No typos

✅ **Fast**
   - 3 prompts = done
   - Takes 30 seconds

✅ **Timestamped Files**
   - Know when generated
   - Easy to track
   - No overwriting

---

## **COMMON FILING NAMES:**

**Briefs:**
- APPELLANT'S OPENING BRIEF
- APPELLANT'S REPLY BRIEF

**Motions:**
- EMERGENCY MOTION FOR STAY PENDING APPEAL
- MOTION TO EXTEND TIME
- MOTION FOR LEAVE TO FILE OVERLENGTH BRIEF

**Other:**
- PETITION FOR REHEARING
- PETITION FOR REHEARING EN BANC

---

## **TO UPDATE YOUR CONTACT INFO (One Time):**

If your address/phone/email changes:

1. Open `TEMPLATE_CAPTION.docx`
2. Update contact info at bottom
3. Save and close
4. Done! Generator uses updated info for all future covers

---

## **TROUBLESHOOTING:**

**"Template not found"**
→ Put `TEMPLATE_CAPTION.docx` in same folder as scripts

**"Python not found"**
→ Install from python.org (Windows)
→ Mac/Linux already has it

**Batch file won't run**
→ Right-click → Run as Administrator

---

## **NEXT: BODY TEXT TEMPLATE**

We can do the same thing for your body text:
- Keep master template READ-ONLY
- Generator prompts for content
- Swaps placeholders
- Creates fresh file

Want me to build that next?

---

## **YOU'RE ALL SET!** 🚀

Your system:
1. TEMPLATE_CAPTION.docx = master (untouchable)
2. generate_cover.py = does the work
3. GENERATE_COVER.bat = easy launcher
4. Fresh covers every time!

**No more messed up templates!** 🎯
