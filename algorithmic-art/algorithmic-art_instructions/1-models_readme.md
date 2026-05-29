1. [Description]
This skill enables the creation of algorithmic art using p5.js. It follows a two-step process: first defining an "Algorithmic Philosophy" (a manifesto of the aesthetic movement), and then expressing that philosophy through code (HTML/JS). It emphasizes seeded randomness, emergent behavior, and computational beauty.

2. [requirements]
- Ability to generate Markdown (.md) for the philosophy.
- Ability to generate HTML and JavaScript (.js) for the p5.js sketch.
- p5.js library (usually loaded via CDN in the generated HTML).

3. [Cautions]
- Do not copy existing artists' work; focus on original algorithmic concepts.
- Ensure the generated HTML correctly references the p5.js library.
- The philosophy step is critical; do not skip it to just write code.
- The code should be 90% algorithmic generation and 10% parameters.

4. [Definitions]
- **Algorithmic Philosophy**: A written manifesto defining the aesthetic movement, rules, and behaviors of the art to be created.
- **p5.js**: A JavaScript library for creative coding.
- **Seeded Randomness**: Using a fixed seed to ensure reproducible but random-looking results.

5. [log]
(No run logs available yet. This section will be populated by the system upon successful execution.)

6. [model_readme]
To use this skill:
1. **Phase 1**: Generate an Algorithmic Philosophy based on user input. Output this as a Markdown file.
   - Name the movement.
   - Articulate the philosophy (form, process, behavior).
   - Emphasize craftsmanship.
2. **Phase 2**: Implement the philosophy in p5.js.
   - Create an HTML file that loads p5.js.
   - Create a JS file with the sketch code.
   - Ensure the code reflects the philosophy defined in Phase 1.

**Helper Script**:
You can use `python skills/algorithmic-art/scripts/scaffold_art.py --name "ProjectName"` to create the folder structure and empty files in the OUTBOX.
