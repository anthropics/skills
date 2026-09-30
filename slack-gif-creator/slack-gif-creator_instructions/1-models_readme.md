1. [Description]
This skill provides a toolkit for creating animated GIFs optimized for Slack. It includes validators for Slack's strict size/dimension constraints and composable primitives for creating animations (shake, bounce, etc.). It is useful for creating custom emoji or reaction GIFs.

2. [requirements]
- Python environment with image processing capabilities (likely PIL/Pillow).
- Access to the validator scripts and animation primitives defined in the skill.
- Source images or text to animate.

3. [Cautions]
- **Strict Limits**: Slack Emoji GIFs must be < 64KB. This is very small.
- **Dimensions**: 128x128 for emojis, 480x480 for message GIFs.
- **Colors**: Limit palette to 32-48 colors for emojis to save space.

4. [Definitions]
- **Emoji GIF**: A small, square animated image used as a custom emoji.
- **Message GIF**: A larger animated image used in chat messages.
- **Validator**: A script that checks if the file meets Slack's technical requirements.

5. [log]
(No run logs available yet. This section will be populated by the system upon successful execution.)

6. [model_readme]
To create a Slack GIF:
1. **Determine Type**: Emoji (<64KB) or Message (~2MB).
2. **Create**: Use animation primitives (code) to generate frames.
3. **Optimize**: Reduce colors, frames, and dimensions.
4. **Validate**: Run the validator script to ensure it meets Slack's limits.
5. **Iterate**: If validation fails, reduce quality/length and try again.

**Helper Script**:
Use `python skills/slack-gif-creator/scripts/create_gif.py --create-sample "output.gif"` to generate a sample or `--validate "output.gif"` to check compliance.
