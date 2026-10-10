1. [Description]
This skill generates a Ninth Circuit Court of Appeals compliant cover page. It uses a Python script to populate a DOCX template with case-specific information such as the case number, filing title, and judge's name. It is designed to ensure formatting compliance for appellate briefs and motions.

2. [requirements]
- Python 3.x
- `python-docx` library
- A valid DOCX template (internal to the script or provided path)
- Access to `d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\COVER_GENERATOR_COMPLETE\generate_cover.py` (Note: The script location is external to the skill folder in the current configuration, see SKILL.md).

3. [Cautions]
- Ensure the Case Number is in the correct format (e.g., 25-6461).
- The script path is hardcoded in the SKILL.md examples; verify the path exists before running.
- The output directory `COVER_GENERATOR_COMPLETE/output/` must exist or be writable.
- Verify the judge's name spelling as it appears on the District Court docket.

4. [Definitions]
- **Case Number**: The appellate case number assigned by the Ninth Circuit (not the District Court number).
- **Filing Name**: The exact title of the document being filed (e.g., "APPELLANT'S OPENING BRIEF").
- **Judge Name**: The name of the District Court judge whose decision is being appealed.

5. [log]
(No run logs available yet. This section will be populated by the system upon successful execution.)

6. [model_readme]
To use this skill, execute the python script `generate_cover.py` with the required arguments.
Command format:
`python "d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\COVER_GENERATOR_COMPLETE\generate_cover.py" --case "[CASE_NUMBER]" --filing "[FILING_NAME]" --judge "[JUDGE_NAME]"`

Example:
`python "d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\COVER_GENERATOR_COMPLETE\generate_cover.py" --case "25-6461" --filing "APPELLANT'S OPENING BRIEF" --judge "Stacy Beckerman"`

The output will be a DOCX file in the output directory. Check the terminal output for the exact path.
