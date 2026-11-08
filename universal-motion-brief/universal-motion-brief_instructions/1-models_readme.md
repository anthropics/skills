1. [Description]
This skill builds motions and appellate briefs by merging structured data (JSON) into a user-supplied DOCX template. It preserves the original template's formatting, styles, and footnotes, making it ideal for generating documents that require strict adherence to a specific layout or style guide without the risk of generative AI hallucinating formatting.

2. [requirements]
- Python 3.x
- `python-docx` library
- A `.docx` template file with `{{PLACEHOLDERS}}`.
- A `.json` data file containing the values for the placeholders.

3. [Cautions]
- Placeholders must match exactly (case-sensitive).
- Do not place placeholders inside footnotes if you need to preserve them (the script may not process them correctly or might break the footnote reference).
- Ensure the JSON structure matches the expected placeholders.
- The script does not re-flow text; it only replaces tokens.

4. [Definitions]
- **Template**: A DOCX file containing static text and `{{TOKEN}}` placeholders.
- **Mapping**: An optional JSON file that maps keys in your data to the tokens in the template (e.g., `{"case_no": "CASE_NUMBER"}`).
- **Render**: The process of replacing placeholders with actual data.

5. [log]
(No run logs available yet. This section will be populated by the system upon successful execution.)

6. [model_readme]
Use the `scripts/render_docx.py` script to generate the document.

Command format:
`python skills/universal-motion-brief/scripts/render_docx.py --template "[PATH_TO_TEMPLATE]" --data "[PATH_TO_DATA]" --output "[PATH_TO_OUTPUT]"`

Options:
- `--mapping [PATH]`: Use if your data keys don't match template tokens.
- `--strict`: Fail if any placeholder is left unfilled.

Example:
`python skills/universal-motion-brief/scripts/render_docx.py --template "templates/motion.docx" --data "data/motion_data.json" --output "OUTBOX/motion.docx"`
