# Internal Comms

## Description
This skill provides structured templates and guidelines for drafting standardized internal organizational communications. It ensures consistency, clarity, and professionalism across various communication types such as 3P updates (Progress, Plans, Problems), company newsletters, FAQs, and general status reports. By leveraging pre-defined Markdown templates, it helps the model generate content that aligns with corporate best practices and specific formatting requirements.

## Requirements
- Access to the `examples/` directory containing the guideline files (`3p-updates.md`, `company-newsletter.md`, etc.).
- Context provided by the user regarding the specific content (e.g., project details, team updates).

## Cautions
- **Tone**: Maintain a professional, objective tone suitable for internal business contexts.
- **Accuracy**: Ensure all generated content accurately reflects the user's input; do not invent metrics or status updates.
- **Formatting**: Strictly follow the structure defined in the selected guideline file (e.g., headers, bullet points).

## Definitions
- **3P Update**: A reporting format focusing on Progress (what was done), Plans (what will be done), and Problems (blockers).
- **Internal Comms**: Communications intended for an audience within the organization, not external clients or public.

## Log
(No run logs available yet. This section will be populated by the system upon successful execution.)

## Model Readme
To use this skill:
1.  **Identify Type**: Determine the type of communication requested (3P, Newsletter, FAQ, or General).
2.  **Read Template**: Read the corresponding file in `skills/internal-comms/examples/`:
    -   `3p-updates.md`
    -   `company-newsletter.md`
    -   `faq-answers.md`
    -   `general-comms.md`
3.  **Generate**: Draft the communication following the structure and instructions found in the template file.
4.  **Review**: Ensure the tone is appropriate and all sections are complete.
