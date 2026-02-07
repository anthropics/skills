# Brand Guidelines

## Description
This skill serves as a reference guide for applying Anthropic's official brand identity to generated artifacts. It defines specific color hex codes (Dark, Light, Mid Gray, Light Gray) and accent colors (Orange, Blue, Green), as well as typography standards (Poppins for headings, Lora for body). This skill does not contain executable scripts but provides the necessary constants and style rules that a model should strictly adhere to when creating designs, documents, or UI elements that require Anthropic branding.

## Requirements
- None (Reference only).
- Access to the color codes and font names defined in `SKILL.md`.

## Cautions
- Do not approximate colors; use the exact hex codes provided.
- If Poppins/Lora are not available in the target environment (e.g., web safe fonts), use the specified fallbacks (Arial for headings, Georgia for body).
- Ensure high contrast between text and background (e.g., Dark text on Light background).

## Definitions
- **Hex Code**: A six-digit alphanumeric code used to represent colors in HTML/CSS.
- **Poppins**: Geometric sans-serif typeface used for headings.
- **Lora**: Contemporary serif typeface used for body text.

## Log
(No run logs - this is a documentation skill with no scripts to execute.)

## Model Readme
Use the values defined in `SKILL.md` when generating content:
- **Primary Text**: #141413
- **Background**: #faf9f5
- **Accents**: #d97757 (Orange), #6a9bcc (Blue), #788c5d (Green).
- **Fonts**: `font-family: 'Poppins', Arial, sans-serif;` for headings; `font-family: 'Lora', Georgia, serif;` for body.

Apply these styles to HTML/CSS artifacts, SVG generation, or when writing Python code that generates visualizations (e.g., matplotlib, p5.js).

