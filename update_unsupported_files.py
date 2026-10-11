import os
import shutil

skills_dir = 'skills'

def is_supported(filename):
    ext = os.path.splitext(filename)[1].lower()
    # "Supported: .txt, .md, .rst, .rtf, .tex, .log, .py, .sh, .json, .yaml, .csv, .toml, .xml, .env, .sql, .html, .css, .svg, Makefile, Dockerfile."
    supported_exts = {'.txt', '.md', '.rst', '.rtf', '.tex', '.log', '.py', '.sh', '.json', '.yaml', '.csv', '.toml', '.xml', '.env', '.sql', '.html', '.css', '.svg', '.js', '.xsd'}
    # Also supporting .js and .xsd as they are text, even if not explicitly listed but generally plain text is supported.

    # "Not supported: Binary & rich media: .pdf, .docx, .doc, .xlsx, .jpg, .png, or any other non-plain-text formats or image types."
    not_supported_exts = {'.pdf', '.docx', '.doc', '.xlsx', '.xlsm', '.xltx', '.jpg', '.png', '.ttf'}

    if ext in not_supported_exts:
        return False

    return True

for root, dirs, files in os.walk(skills_dir):
    for file in files:
        if not is_supported(file):
            file_path = os.path.join(root, file)
            print(f"Removing unsupported file: {file_path}")
            os.remove(file_path)
