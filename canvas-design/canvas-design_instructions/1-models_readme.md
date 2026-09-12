# Canvas Design

## Description
This skill provides a creative framework for generating high-quality visual art and design documents (.png, .pdf). It operates in two phases: first, by defining a unique "Design Philosophy" (a written aesthetic manifesto), and second, by writing and executing Python code to visually express that philosophy on a digital canvas. It emphasizes original, museum-quality abstract art, minimal text, and sophisticated composition, avoiding "AI slop" or generic templates. It allows the model to act as a high-end graphic designer using code as the medium.

## Requirements
- Python environment with image generation libraries (e.g., `PIL`/`Pillow`, `cairo`, `matplotlib`, or `reportlab`).
- Access to `./canvas-fonts/` for custom typography (if available, otherwise use system fonts).
- Ability to write and execute Python scripts to save .png or .pdf files.

## Cautions
- **Copyright**: Create original designs; do not copy existing artists.
- **Text**: Keep text minimal and visual-first. Ensure no overlaps or truncation.
- **Craftsmanship**: The code should generate high-resolution, polished outputs.
- **Fonts**: Use the provided fonts in `canvas-fonts` if possible to ensure distinctiveness.

## Definitions
- **Design Philosophy**: A 4-6 paragraph Markdown document defining the aesthetic movement, rules, and behaviors of the art.
- **Canvas**: The digital drawing surface (e.g., a PIL Image object or PDF page).
- **Visual Expression**: The translation of abstract philosophical concepts into concrete visual elements (shapes, colors, lines).

## Log
(No run logs available yet. This section will be populated by the system upon successful execution.)

## Model Readme
To use this skill:
1.  **Phase 1: Philosophy**: Generate a Markdown file defining the "Design Philosophy". Name the movement (e.g., "Brutalist Joy") and describe its visual rules (space, form, color).
2.  **Phase 2: Execution**: Write a Python script to generate the artwork based on the philosophy.
    -   Use libraries like `PIL`, `cairo`, or `reportlab`.
    -   Implement the visual rules programmatically (e.g., loops for patterns, specific color palettes).
    -   Save the output as a high-quality .png or .pdf.
3.  **Refine**: If the user requests changes, refine the code to enhance the "craftsmanship" without adding unnecessary clutter.
