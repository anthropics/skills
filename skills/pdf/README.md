# PDF Processing

A production-ready skill for working with PDF documents — read, extract, transform, and generate PDFs programmatically.

## Quick Start

**Use this skill when:**
- You need to read/extract content from PDF files
- You want to generate PDFs programmatically
- You're processing PDF forms or structured documents
- You need to transform or manipulate PDF content
- You're working with legacy documents that are PDF-only

## What This Skill Covers

### PDF Reading & Extraction
- Extract text, metadata, and structure from existing PDFs
- Handle different PDF formats and encodings
- Parse forms and form fields
- Extract images and attachments

### PDF Generation
- Create PDFs from scratch programmatically
- Add text, images, tables, headers/footers
- Apply styling (fonts, colors, layouts)
- Generate multi-page documents

### PDF Transformation
- Merge, split, or reorder pages
- Compress or optimize PDFs
- Apply security (encryption, permissions)
- Add annotations and comments

### Form Handling
- Read form fields and values
- Fill PDF forms programmatically
- Submit forms as structured data
- Validate form data before processing

## Supported Use Cases

### Content Extraction
```python
# Read a PDF and extract all text
pdf_content = extract_text('invoice.pdf')
```

### Report Generation
```python
# Generate a PDF report from data
create_pdf_report(
    title='Monthly Report',
    sections=[...],
    output='report.pdf'
)
```

### Form Processing
```python
# Read form fields from a template
form_fields = read_form('application.pdf')
fill_form('application.pdf', form_fields, 'completed.pdf')
```

### Document Transformation
```python
# Merge multiple PDFs into one
merge_pdfs(['page1.pdf', 'page2.pdf'], 'merged.pdf')
```

## How to Use This Skill

1. **Read SKILL.md** for comprehensive guidance
2. **Check references/**:
   - `reference.md` — detailed API and patterns
   - `forms.md` — working with PDF forms
3. **Use language-specific examples** (if available in scripts/)
4. **Test with sample PDFs** before production use

## Quick Reference

### Key Concepts

- **PDFs as data**: Treat PDFs as structured data you can read, manipulate, and generate
- **Cross-platform**: PDF processing works consistently across operating systems
- **Character encoding**: Pay attention to encoding for international text
- **Binary format**: PDFs are binary; use appropriate libraries and tools

### Common Patterns

| Task | Pattern | Reference |
|---|---|---|
| Extract text | Use PDF reader library | `reference.md` |
| Generate PDF | Use PDF writer library | `reference.md` |
| Work with forms | Read/write form fields | `forms.md` |
| Merge PDFs | Concatenate page streams | `reference.md` |
| Handle metadata | Read/write PDF properties | `reference.md` |

### Supported Operations

**Reading:**
- Extract text (all or specific pages)
- Extract metadata (title, author, etc.)
- Read form fields
- Extract images and attachments

**Writing:**
- Create PDFs from text/images
- Add pages to existing PDFs
- Fill form fields
- Add annotations

**Transforming:**
- Merge multiple PDFs
- Split PDFs by page
- Compress for file size
- Encrypt/protect

## Important Notes

### Performance
- Large PDFs (>100MB) may be slow to process
- Consider streaming for very large files
- Test with actual file sizes before production

### File Formats
- Works with standard PDF-1.4 and later
- Some older PDFs may have compatibility issues
- Complex PDFs (scanned images, etc.) may not extract text cleanly

### Dependencies
- Requires PDF processing library for your language
- May need system dependencies (see installation notes)
- Some operations require additional libraries

## Troubleshooting

| Problem | Likely Cause | Solution |
|---|---|---|
| Can't extract text | Scanned PDF (image-based) | Use OCR tool instead |
| Form fields not recognized | Non-standard form format | Try manual field extraction |
| Encoding issues | Character encoding mismatch | Specify encoding explicitly |
| Performance slow | Large file or complex structure | Process in chunks or pages |
| Library conflicts | Multiple PDF libraries | Use only one; check versions |

## Related Skills

- **docx**: For Word document processing
- **pptx**: For PowerPoint presentation processing
- **xlsx**: For Excel spreadsheet processing
- **doc-coauthoring**: For writing documentation about PDFs

## Structure of This Skill

```
pdf/
├── SKILL.md                # Core skill (314 lines)
├── README.md               # This file
├── LICENSE.txt             # Apache 2.0 license
├── reference.md            # Detailed API and patterns
├── forms.md                # PDF forms guide
└── scripts/
    ├── merge_pdfs.py       # Utility to merge PDFs
    ├── extract_text.py     # Text extraction helper
    └── validate.py         # PDF validation tool
```

## Getting Started

### Step 1: Understand Your Task
- Extracting text from PDFs?
- Generating new PDFs?
- Working with forms?
- Transforming existing PDFs?

### Step 2: Read Relevant Section
- General: SKILL.md § Overview
- Extraction: SKILL.md § Reading & Extracting
- Generation: SKILL.md § Creating PDFs
- Forms: `forms.md`
- Details: `reference.md`

### Step 3: Implement
- Find language-specific example in `reference.md`
- Copy pattern and adapt to your use case
- Test with sample file
- Iterate based on results

### Step 4: Troubleshoot
- Check `reference.md` for known issues
- Test with different PDF types
- Verify file format compatibility
- Check system dependencies

## Production Checklist

Before using PDF processing in production:
- [ ] Tested with actual file sizes and types
- [ ] Verified character encoding handling
- [ ] Tested error cases (corrupt files, etc.)
- [ ] Validated output PDFs in readers
- [ ] Checked performance with large batches
- [ ] Have fallback for unsupported formats
- [ ] Documented any limitations

## For Contributors

### Adding New PDF Capabilities
1. Document in `SKILL.md`
2. Add patterns/examples to `reference.md`
3. Update `forms.md` if affects forms
4. Add utility script in `scripts/`
5. Include tests for new functionality

### Updating Existing Capabilities
1. Keep SKILL.md in sync with changes
2. Update relevant reference file
3. Test with multiple PDF types
4. Document breaking changes clearly

---

**Last Updated**: August 2026  
**License**: Apache 2.0  
**Repository**: anthropics/skills

**Production-Ready**: Yes. Used in production by Anthropic.

**Next Steps**: 
1. Read SKILL.md for overview
2. Check `reference.md` for detailed patterns
3. Look at `scripts/` for utility examples
4. Test with your PDFs
