import os

skills_dir = 'skills'

for root, dirs, files in os.walk(skills_dir):
    if 'SKILL.md' in files:
        filepath = os.path.join(root, 'SKILL.md')
        with open(filepath, 'r') as f:
            content = f.read()

        # Replace .pdf with pdf (or just remove the dot, or remove the word)
        # It's better to just leave it as is if it's text. The rule is about *uploaded files*, not the text in SKILL.md containing the word ".pdf".
        # Oh, wait! The instruction says: "Not supported: Binary & rich media: .pdf, .docx, .doc, .xlsx, .jpg, .png, or any other non-plain-text formats or image types."
        # This applies to the files IN THE ZIP, not the text in SKILL.md.
        pass
