# Theme Factory

## Description
This skill acts as a design system manager, providing 10 pre-defined professional visual themes (color palettes and font pairings) that can be applied to various artifacts (slides, documents, HTML pages). It also supports on-the-fly generation of custom themes based on user preferences. Its primary purpose is to ensure visual consistency and aesthetic quality in generated content without requiring the user to be a designer. It bridges the gap between raw content and polished presentation.

## Requirements
- Access to the `themes/` directory containing the 10 pre-set Markdown theme files.
- Access to `theme-showcase.pdf` for visual reference (if supported by the environment).
- Ability to read hex codes and font names from the theme files and apply them to the target artifact (e.g., CSS for HTML, XML for DOCX/PPTX).

## Cautions
- **Consistency**: When applying a theme, ensure all elements (headings, body, backgrounds, accents) use the specified values.
- **Contrast**: Ensure text remains readable against background colors.
- **Fallback**: If a specific font is not available in the target format/environment, select a close alternative (serif vs. sans-serif).

## Definitions
- **Theme**: A cohesive set of design decisions including a color palette (primary, secondary, accent, background) and typography (heading font, body font).
- **Artifact**: The output file or content being styled (e.g., a PowerPoint deck, a React component, a PDF).

## Log
(No run logs available yet. This section will be populated by the system upon successful execution.)

## Model Readme
To use this skill:
1.  **Showcase**: Offer the user a choice of themes. If possible, reference `theme-showcase.pdf` or list the names (Ocean Depths, Sunset Boulevard, etc.).
2.  **Select**: Once a theme is chosen, read the corresponding file in `skills/theme-factory/themes/` (e.g., `ocean-depths.md`).
3.  **Apply**: Extract the hex codes and font names.
    -   For **HTML/CSS**: Create a `:root` variable set or Tailwind config.
    -   For **Python/PPTX**: Use the hex codes to set RGB colors.
4.  **Custom**: If the user wants a custom theme, generate a new palette and font pairing that matches their description, following the structure of the existing theme files.
