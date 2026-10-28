---
name: resume-scorer
description: Evaluate a resume PDF against a job description. Use this skill whenever the user wants to score, evaluate, review, compare, or assess a resume against a job posting, job description, or role requirements. Also use when the user wants to identify gaps in a resume, get improvement suggestions, check keyword alignment, or understand how well a candidate matches a position. Triggers on mentions of resume review, resume scoring, resume analysis, job fit assessment, ATS optimization, or candidate evaluation.
license: Complete terms in LICENSE.txt
---

# Resume Scorer

Evaluate a resume against a job description, producing a structured assessment with per-criterion scores, strengths, gaps, and actionable improvement suggestions.

## Inputs

1. **Resume**: A PDF file path. Extract text using `pdfplumber` (preferred) or `pypdf`.
2. **Job Description**: Either inline text or a file path (`.txt`, `.md`, `.pdf`, or `.docx`). If the user pastes the JD directly in the conversation, use that.

If the user provides only a resume without a JD, ask for the job description before proceeding. If the user provides only a JD, ask for the resume.

## Workflow

### Step 1: Extract Resume Content

```python
import pdfplumber

with pdfplumber.open(resume_path) as pdf:
    text = "\n".join(page.extract_text() or "" for page in pdf.pages)
```

If `pdfplumber` is unavailable, fall back to `pypdf`:

```python
from pypdf import PdfReader

reader = PdfReader(resume_path)
text = "\n".join(page.extract_text() or "" for page in reader.pages)
```

### Step 2: Parse Structured Data from the Resume

Extract and organize the following sections from the raw text. Not every resume will have all sections; extract what is present and note what is missing.

- **Contact Information**: Name, email, phone, LinkedIn, location
- **Summary / Objective**: Professional summary or career objective
- **Experience**: For each role: title, company, dates, duration, bullet points
- **Education**: Degree, institution, graduation date, GPA (if listed)
- **Skills**: Technical skills, tools, languages, frameworks
- **Certifications**: Name, issuing body, date
- **Projects**: Notable projects with descriptions
- **Publications / Awards**: If present

### Step 3: Parse the Job Description

Extract key requirements from the JD:

- **Required Skills**: Hard skills, technologies, tools explicitly required
- **Preferred Skills**: Nice-to-have qualifications
- **Experience Requirements**: Minimum years, specific domain experience
- **Education Requirements**: Degree level, field of study
- **Responsibilities**: Core duties of the role
- **Keywords**: Domain-specific terms, certifications, methodologies

### Step 4: Score Against Criteria

Read the `criteria.json` file bundled with this skill to load the scoring rubric. Each criterion has a name, weight, max score, and scoring guidance.

The default criteria are:

| Criterion | Weight | What to Evaluate |
|-----------|--------|------------------|
| Technical Skills Match | 30% | Overlap between resume skills and JD required/preferred skills |
| Experience Relevance | 25% | Years of experience, relevance of past roles to the target position |
| Education Alignment | 15% | Degree level and field match against JD requirements |
| Keyword Coverage | 15% | Presence of JD-specific terms, tools, methodologies in the resume |
| Certifications & Extras | 10% | Relevant certifications, publications, awards |
| Presentation Quality | 5% | Clarity, structure, quantified achievements, action verbs |

For each criterion, assign a score from 0 to 10 based on the guidance in `criteria.json`, then compute the weighted overall score.

### Step 5: Produce the Evaluation Report

Output the evaluation as structured text (or JSON if the user requests it) with these sections:

```
## Resume Evaluation Report

### Candidate
[Name] | [Current/Most Recent Title]

### Overall Score: [X.X / 10] ([descriptor])

Score descriptors:
- 9.0-10.0: Exceptional match
- 7.5-8.9: Strong match
- 6.0-7.4: Moderate match
- 4.0-5.9: Weak match
- 0.0-3.9: Poor match

### Per-Criterion Breakdown
| Criterion | Score | Weight | Weighted Score | Notes |
|-----------|-------|--------|----------------|-------|
| ...       | X/10  | XX%    | X.XX           | ...   |

### Strengths
- [Specific strength with evidence from the resume]
- ...

### Gaps
- [Specific gap: what the JD requires that the resume lacks]
- ...

### Improvement Suggestions
1. [Actionable suggestion to improve the resume for this role]
2. ...

### Keyword Analysis
- **Present**: [keywords found in both resume and JD]
- **Missing**: [JD keywords not found in resume]
```

## Customization

Users can customize scoring by:

1. **Adjusting weights**: "Weight technical skills at 40% instead of 30%"
2. **Adding criteria**: "Also score for leadership experience"
3. **Changing scale**: "Use a 100-point scale"
4. **Focusing on specific areas**: "Only evaluate the technical skills match"

When the user requests custom criteria, modify the rubric accordingly and note the changes in the report.

## Multiple Resumes

If the user provides multiple resumes to compare against the same JD:

1. Score each independently
2. Produce a comparison summary table ranking candidates
3. Highlight differentiators between top candidates

## Output Formats

- **Default**: Structured markdown report in the conversation
- **JSON**: If requested, output a machine-readable JSON object with all scores and analysis
- **File**: If requested, write the report to a `.md` or `.txt` file

## Guidelines

- Be objective and evidence-based. Every score should be justified by specific content from the resume and JD.
- Do not penalize for information not typically found on resumes (age, photo, etc.).
- Recognize equivalent skills (e.g., "React" matches "React.js", "ReactJS"; "AWS" matches "Amazon Web Services").
- Account for seniority: a senior role JD should weight experience more heavily; an entry-level JD should weight education and projects more.
- When skills are listed in the JD as "preferred" vs "required", weight required skills more heavily in the technical match score.
- Flag potential ATS issues: missing keywords, unusual formatting notes from extraction, etc.
- Keep suggestions constructive and specific rather than generic.
