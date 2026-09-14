---
name: md2video-audio 
description: Convert a specified Markdown file into an MP4 video with free natural-sounding voice-over and presentation visuals in one click, at zero cost. Automatically trigger this skill when the user asks to convert Markdown into a video, create a narrated video, or combine audio and video.
---

# Free Markdown-to-Narrated-Video Skill (`md2video-audio`)

- Purpose: Automatically convert a local Markdown file into an MP4 video containing presentation visuals and free voice-over narration.

## 1. Global Core Rules

**The following rules must be strictly followed and must never be violated under any circumstances:**

- **Rule 1:** **Do not modify the original document.** Execute all steps sequentially: original document → formatted and optimized document → presentation document → narration script → final video. Each stage must be generated from the output of the preceding stage.
- **Rule 2:** Never install or remove dependencies, delete files, execute scripts, or provide interactive input without authorization. If anything is uncertain, ask the user for confirmation.

## 2. Core Sequential Workflow

- This task follows a strict sequential workflow consisting of the stages below. You must proceed **in the specified order**. Do **not** move to a later stage until the current stage has been completed and passed validation.

### 1. Check and Install Environment Dependencies

See the corresponding reference file: `references/enviroment.md`.

### 2. Generate the Optimized Document

- Do not modify the original file.
- Output: Save the result as a new Markdown file named `new-<original-filename-prefix>-<timestamp>.md`.
- Preserve the original wording, content, and logic. Only perform necessary paragraph and section restructuring, add colors, and insert natural introductory, transitional, and concluding phrases.
- See the corresponding reference file: `references/newscript.md`.

### 3. Generate the Presentation Document

- Output: Save the result as a new Markdown file named `show-<original-filename-prefix>-<timestamp>.md`.
- Split the `new-<original-filename-prefix>-<timestamp>.md` file generated in the previous stage into logically organized presentation slides. Requirements:
  1. Add several configuration lines at the top of the Markdown file. Pause here and ask the user which Marp presentation style they want to use and whether to include `allowHtml: true`. For the default style, see `references/showscript.md`.
  2. Convert HTML (HyperText Markup Language) tags into Markdown syntax whenever possible. For example, convert `<img>` into `![]()` while preserving its original parameters.
  3. Based on the semantic structure and Markdown paragraph organization, use `---` to separate individual PPT (PowerPoint Presentation) slides.
- Check whether each slide complies with the following pagination rules:
  1. Determine whether the content of a slide exceeds the safe page capacity, defined as 85% of the height of a Marp slide. Estimate the height dynamically by counting different types of lines and calculating their occupied height based on the styles defined in the YAML Front Matter at the top of the document. If the content exceeds the safe capacity boundary, divide it into several logically coherent units, with each unit occupying one slide. While ensuring that every slide remains within the safe capacity and has a visually appealing layout, minimize the total number of slides.
  2. Determine whether a single content block exceeds 350 px (pixels) in height. If the block can be divided, such as a table or code block, split it into multiple logically coherent blocks, each approximately 350 px high.
  3. If a line of code is too long, insert line breaks at semantically appropriate positions.
- If validation passes, proceed to the next stage. Otherwise, revise the invalid sections until validation passes. If validation still fails after three revision attempts, ask the user to modify the document manually before continuing.

### 4. Generate the Narration Script

- Output: Save the result as a new Markdown file named `speaking-<original-filename-prefix>-<timestamp>.md`.
- Generate a natural and logically coherent narration script based on the presentation document:
  1. Add `---` as the first line of the narration script, then start the narration for the first slide on the next line.
  2. Remove miscellaneous emoji, decorative icons, and other presentation-only characters that would sound unnatural when read aloud. Preserve slide separators.
- Verify that the narration script and presentation document contain the same number of `---` slide separators. Run the following regular-expression command:

```bash
grep -E '^---[[:space:]]*$' your_file.md | wc -l
```

- If the counts do not match, revise the narration script so that each section aligns with the corresponding slide in the presentation document. In most cases, this requires adding `---` to the beginning of the narration script.
- If validation passes, proceed to the next stage. Otherwise, continue revising the invalid sections until validation passes. If validation still fails after three revision attempts, ask the user to modify the document manually before continuing.

### 5. Package Everything into a Video Using the Python Script

- Use the two intermediate Markdown files generated in the preceding stages—the presentation document and the narration script—as inputs.
- Execute the `ai-2md2marp2av.py` script located in this skill’s directory:

```bash
python ai-2md2marp2av.py presentation.md narration.md
```

- Note that the script requires interactive input. The user must provide this input manually.
- The script uses Marp to generate visually polished PPT slide images. It then uses Edge TTS (Text-to-Speech) to generate narration audio and combines each slide image with its corresponding audio segment to produce the final video.

### 6. Fallback Options

- If video generation fails, use the fallback procedure:
  1. Execute the `md2marp2av.py` script located in this skill’s directory.
  2. If that also fails, execute the `md2video.py` script.