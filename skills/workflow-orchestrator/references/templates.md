# Workflow Templates

Predefined workflow templates for common multi-step patterns. Suggest these when a user's request matches one of the patterns below. Templates are starting points — encourage the user to customize steps, add/remove them, or adjust dependencies.

## Table of Contents
- [Research and Report](#research-and-report)
- [Build, Test, Deploy](#build-test-deploy)
- [Data Pipeline](#data-pipeline)
- [Content Creation](#content-creation)

---

## Research and Report

**Use when**: the user wants to investigate a topic and produce a written deliverable — a report, summary, analysis, or recommendation document.

**Pattern**: gather information from multiple sources, synthesize findings, produce a structured document.

```yaml
template:
  name: research-and-report
  description: "Research a topic from multiple angles and produce a structured report"
  parameters:
    - name: topic
      description: "The subject to research"
      required: true
    - name: output_format
      description: "Desired output format (markdown, docx, pdf)"
      required: false
      default: "markdown"
  workflow:
    name: research-and-report
    steps:
      - id: gather-sources
        skill: "web research or file reading"
        input: "Research {{topic}} thoroughly. Find key facts, data points, and expert opinions. Summarize each source."
        depends_on: []

      - id: analyze-findings
        skill: "analysis and reasoning"
        input: "Analyze the research from {{gather-sources}}. Identify key themes, contradictions, and gaps. Produce a structured analysis with main findings and supporting evidence."
        depends_on: [gather-sources]

      - id: generate-charts
        skill: "data visualization"
        input: "Based on any quantitative data from {{gather-sources}}, create relevant charts or visualizations. If no quantitative data exists, create a conceptual diagram summarizing the topic structure."
        depends_on: [gather-sources]
        on_failure: skip

      - id: write-report
        skill: "document writing"
        input: "Write a comprehensive report on {{topic}} using the analysis from {{analyze-findings}} and visualizations from {{generate-charts}}. Structure: Executive Summary, Background, Key Findings, Analysis, Recommendations, Appendix."
        depends_on: [analyze-findings, generate-charts]
```

**Customization ideas**:
- Add a `peer-review` step after `write-report` that critiques the draft
- Add a `competitive-analysis` step parallel to `gather-sources` for business contexts
- Replace `generate-charts` with domain-specific visualization

---

## Build, Test, Deploy

**Use when**: the user wants to make code changes and push them through a quality pipeline — build, lint, test, and optionally deploy.

**Pattern**: make changes, verify quality at multiple levels, deploy if everything passes.

```yaml
template:
  name: build-test-deploy
  description: "Build, test, and deploy code changes through a quality pipeline"
  parameters:
    - name: change_description
      description: "What code changes to make"
      required: true
    - name: deploy_target
      description: "Where to deploy (staging, production, or none)"
      required: false
      default: "none"
  workflow:
    name: build-test-deploy
    steps:
      - id: implement-changes
        skill: "code writing"
        input: "Implement the following changes: {{change_description}}. Follow existing code conventions and patterns."
        depends_on: []

      - id: run-linter
        tool: "Bash"
        input: "Run the project's linter on the changed files. Fix any lint errors automatically where possible."
        depends_on: [implement-changes]
        retry:
          max_attempts: 2

      - id: run-unit-tests
        tool: "Bash"
        input: "Run the project's unit test suite. Report which tests pass and fail."
        depends_on: [implement-changes]

      - id: run-integration-tests
        tool: "Bash"
        input: "Run integration tests if they exist. Report results."
        depends_on: [run-linter, run-unit-tests]
        on_failure: skip

      - id: create-commit
        skill: "git operations"
        input: "Stage and commit the changes from {{implement-changes}} with a descriptive commit message. Only commit if {{run-linter}} and {{run-unit-tests}} both passed."
        depends_on: [run-linter, run-unit-tests]
        condition: "{{run-linter}}.status == completed and {{run-unit-tests}}.status == completed"

      - id: deploy
        skill: "deployment"
        input: "Deploy to {{deploy_target}} if specified and not 'none'. Push the commit from {{create-commit}}."
        depends_on: [create-commit, run-integration-tests]
        condition: "{{deploy_target}} != 'none'"
        on_failure: ask
```

**Customization ideas**:
- Add a `write-tests` step after `implement-changes` if new test coverage is needed
- Add a `security-scan` step parallel to `run-unit-tests`
- Add a `create-pr` step instead of or after `deploy`

---

## Data Pipeline

**Use when**: the user wants to extract data from sources, transform it, and load it somewhere — classic ETL, data cleaning, or data processing tasks.

**Pattern**: fetch/read data, clean and transform, validate, output to destination.

```yaml
template:
  name: data-pipeline
  description: "Extract, transform, and load data from sources to a destination"
  parameters:
    - name: source_description
      description: "Where the data comes from (file paths, URLs, APIs)"
      required: true
    - name: transformations
      description: "What transformations to apply"
      required: true
    - name: destination
      description: "Where to put the result (file path, format)"
      required: true
  workflow:
    name: data-pipeline
    steps:
      - id: extract-data
        skill: "file reading or data fetching"
        input: "Read and extract data from: {{source_description}}. Report the shape of the data (rows, columns, types) and any immediate issues noticed."
        depends_on: []

      - id: profile-data
        skill: "data analysis"
        input: "Profile the data from {{extract-data}}: check for missing values, outliers, data type issues, duplicate rows, and value distributions. Produce a data quality summary."
        depends_on: [extract-data]

      - id: transform-data
        skill: "data processing"
        input: "Apply these transformations to the data from {{extract-data}}, informed by the quality report from {{profile-data}}: {{transformations}}. Handle edge cases identified in the profile."
        depends_on: [extract-data, profile-data]

      - id: validate-output
        skill: "data validation"
        input: "Validate the transformed data from {{transform-data}}: check row counts, verify transformations were applied correctly, spot-check sample records, ensure no data loss."
        depends_on: [transform-data]

      - id: load-output
        skill: "file writing"
        input: "Write the validated data from {{validate-output}} to: {{destination}}. Confirm the output file exists and report its size."
        depends_on: [validate-output]
```

**Customization ideas**:
- Add parallel `extract-*` steps for multiple data sources, then a `merge-data` step
- Add an `archive-source` step to backup originals before transformation
- Add a `generate-summary` step that produces a human-readable report of what changed

---

## Content Creation

**Use when**: the user wants to produce creative or editorial content — blog posts, documentation, presentations, marketing materials, or multi-format content from a single brief.

**Pattern**: research/outline, draft content, review/edit, produce final artifacts in multiple formats.

```yaml
template:
  name: content-creation
  description: "Create polished content from a brief, with research, drafting, and multi-format output"
  parameters:
    - name: brief
      description: "The content brief — topic, audience, tone, key points to cover"
      required: true
    - name: formats
      description: "Output formats needed (e.g., 'blog post and twitter thread', 'docs page and slides')"
      required: true
  workflow:
    name: content-creation
    steps:
      - id: research-topic
        skill: "research"
        input: "Research background material for this content brief: {{brief}}. Gather facts, examples, quotes, and data points that would strengthen the content."
        depends_on: []

      - id: create-outline
        skill: "writing"
        input: "Create a detailed outline based on the brief ({{brief}}) and research ({{research-topic}}). Structure it for the target audience. Include section headers, key points per section, and where to use examples or data."
        depends_on: [research-topic]

      - id: write-draft
        skill: "writing"
        input: "Write a full draft following the outline from {{create-outline}}. Use the research from {{research-topic}} for supporting material. Match the tone specified in the brief."
        depends_on: [create-outline]

      - id: edit-and-polish
        skill: "writing and editing"
        input: "Edit the draft from {{write-draft}}: improve clarity, fix grammar, tighten prose, verify factual claims against {{research-topic}}, ensure it matches the brief's requirements. Produce the final version."
        depends_on: [write-draft]

      - id: produce-formats
        skill: "document conversion"
        input: "Take the final content from {{edit-and-polish}} and produce it in these formats: {{formats}}. Each format should be optimized for its medium (e.g., shorter for social, more detailed for docs)."
        depends_on: [edit-and-polish]
```

**Customization ideas**:
- Add an `seo-optimization` step between `edit-and-polish` and `produce-formats` for web content
- Add a `create-visuals` step parallel to `write-draft` for presentations
- Split `produce-formats` into parallel steps, one per format, if the formats are very different
