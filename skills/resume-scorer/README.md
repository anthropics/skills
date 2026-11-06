# Resume Scorer Skill

Evaluate a resume PDF against a job description to produce a structured assessment with per-criterion scores, strengths, gaps, and actionable improvement suggestions.

## Usage

Provide a resume PDF and a job description:

```
Score my resume at ~/Documents/resume.pdf against this job description:

Senior Backend Engineer at Acme Corp
Requirements:
- 5+ years Python experience
- PostgreSQL, Redis, Docker
- Experience with microservices architecture
...
```

Or reference a JD file:

```
Evaluate resume.pdf against the job posting in job-description.txt
```

## What You Get

- **Overall score** (0-10) with a descriptor (Exceptional / Strong / Moderate / Weak / Poor match)
- **Per-criterion breakdown** with individual scores, weights, and notes
- **Strengths**: what the resume does well relative to the role
- **Gaps**: specific JD requirements the resume does not address
- **Improvement suggestions**: concrete, actionable steps to strengthen the resume
- **Keyword analysis**: which JD keywords appear in the resume and which are missing

## Default Scoring Criteria

| Criterion | Weight | Description |
|-----------|--------|-------------|
| Technical Skills Match | 30% | Overlap between resume skills and JD required/preferred skills |
| Experience Relevance | 25% | Years and relevance of past roles to the target position |
| Education Alignment | 15% | Degree level and field vs. JD education requirements |
| Keyword Coverage | 15% | Presence of JD-specific terms and phrases in the resume |
| Certifications & Extras | 10% | Relevant certifications, publications, awards |
| Presentation Quality | 5% | Structure, clarity, quantified achievements |

## Configuration

### Adjusting Weights

Ask for different weights:

```
Score my resume but weight technical skills at 40% and reduce education to 10%
```

### Adding Custom Criteria

```
Also evaluate leadership experience as a criterion with 15% weight
```

### Different Output Formats

```
Give me the evaluation as JSON
```

```
Write the evaluation report to evaluation.md
```

### Comparing Multiple Resumes

```
Compare these three resumes against the same JD:
- candidate_a.pdf
- candidate_b.pdf
- candidate_c.pdf
```

## Files

- `SKILL.md` - Skill definition and instructions
- `criteria.json` - Configurable scoring rubric with weights, scales, and scoring guidance
- `README.md` - This file
- `LICENSE.txt` - Apache 2.0 license
