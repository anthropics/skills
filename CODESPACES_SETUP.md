# 🚀 ⚡️CodeSpaces Quick Setup

Get the Skills repository running in **6 minutes** with this streamlined workflow.

## Setup Steps

### 1. Navigate to the repository
Go to: https://github.com/allsxxing/skills

### 2. Launch ⚡️CodeSpaces
Click **Code** → **Codespaces** → **Create codespace on main**

### 3. Wait for initialization
Wait ~3 minutes for ⚡️CodeSpaces to spin up

### 4. Copy the setup script
Open [`ULTRA-COMPACT-ONELINER.txt`](ULTRA-COMPACT-ONELINER.txt) and copy the entire command

### 5. Paste into terminal
Paste the command into the ⚡️CodeSpaces terminal

### 6. Press ENTER
The script will install all dependencies in ~3 minutes

### 7. Done! 🎉
Your environment is now ready with all dependencies installed

## What Gets Installed

The setup script installs everything needed for all skills:

### System Packages (apt-get)
- **pandoc** - Document conversion for DOCX text extraction
- **libreoffice** - PDF conversion from Office documents
- **poppler-utils** - PDF manipulation tools (pdftoppm)

### Node.js Packages (npm)
- **docx** - Create new Word documents
- **pptxgenjs** - PowerPoint generation
- **playwright** - Web automation and testing (+ Chromium browser)
- **react-icons, react, react-dom** - Icon support for presentations
- **sharp** - Image processing and SVG rasterization

### Python Packages (pip)
- **defusedxml** - Secure XML parsing for OOXML
- **pillow** - Image manipulation
- **imageio, imageio-ffmpeg** - GIF creation
- **numpy** - Numerical operations
- **anthropic** - Anthropic API client
- **mcp** - Model Context Protocol SDK
- **markitdown[pptx]** - Extract text from presentations

## Verification

After setup completes, verify installations:

```bash
# Check system tools
pandoc --version
libreoffice --version
pdftoppm -v

# Check Node packages
npm list -g docx playwright pptxgenjs

# Check Python packages
pip list | grep -E "defusedxml|pillow|anthropic|mcp"

# Check Playwright browser
playwright --version
```

## Skills Enabled

With this setup, you can now use:

- ✅ **docx** - Create and edit Word documents
- ✅ **pdf** - PDF manipulation and forms
- ✅ **pptx** - Create and edit PowerPoint presentations
- ✅ **xlsx** - Excel spreadsheet operations
- ✅ **webapp-testing** - Automated web testing
- ✅ **slack-gif-creator** - Animated GIF creation
- ✅ **mcp-builder** - MCP server development
- ✅ **web-artifacts-builder** - React artifact creation
- ✅ All other skills in the repository

## Alternative: Manual Setup

If you prefer to install dependencies individually or encounter issues with the oneliner:

```bash
# System packages
sudo apt-get update
sudo apt-get install -y pandoc libreoffice poppler-utils

# Node.js packages
npm install -g docx pptxgenjs playwright react-icons react react-dom sharp

# Python packages
pip install defusedxml pillow imageio imageio-ffmpeg numpy anthropic mcp "markitdown[pptx]"

# Playwright browser
playwright install chromium --with-deps
```

## Troubleshooting

### Permission errors with npm
If you get EACCES errors, try:
```bash
npm config set prefix ~/.npm-global
export PATH=~/.npm-global/bin:$PATH
```

### Python package conflicts
If pip shows conflicts, use:
```bash
pip install --upgrade pip
pip install --force-reinstall <package-name>
```

### Playwright browser issues
If Chromium fails to install:
```bash
playwright install --with-deps chromium
```

## Next Steps

After setup:
1. Browse [skills/](skills/) directory to explore available skills
2. Read [README.md](README.md) for skill usage instructions
3. Check [spec/agent-skills-spec.md](spec/agent-skills-spec.md) for technical details
4. Use [template/SKILL.md](template/SKILL.md) to create your own skills

---

**Time to productivity: 6 minutes** ⏱️
