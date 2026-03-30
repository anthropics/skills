# Example Prompts

## Company brief + JD forensic analysis

```text
Research Myriad Genetics for my interview. Here's the JD:

Corporate Strategy Director -- Myriad Genetics
Salt Lake City, UT (US based remote)

The Director of Strategy will lead the identification, evaluation,
and prioritization of strategic growth opportunities...

[paste full JD text]
```

## Company-only brief (no JD)

```text
Give me a company brief on Moderna. I want to understand their
financial performance, pipeline, leadership team, competitive
position, and any recent news or legal issues.
```

## Private company (graceful degradation)

```text
Research Anthropic for me. They're private so no SEC data,
but I want employee sentiment, hiring signals, leadership,
and competitive landscape.
```

## Diagnostics company

```text
Research Guardant Health. Focus on their MRD/liquid biopsy
pipeline, pharma partnerships, data revenue, and how they
compare to Natera and Foundation Medicine.
```

## With custom output directory

```text
Research Recursion Pharmaceuticals for my interview.
Output to ~/Documents/job-apps/recursion/
```

## Programmatic (Python SDK -- data collector only)

```python
from python_implementation import company_research

# Returns path to company_data.json (structured data, not final report)
json_path = company_research("Moderna", output_dir="/tmp/moderna-research/")
```
