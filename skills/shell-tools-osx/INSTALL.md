# Installation & Usage

## Install the Skill in Claude

1. **Package the skill:**
   ```bash
   cd /path/to/shell-tools-osx
   zip -r shell-tools-osx.zip . -x "*.git*" -x "*.DS_Store"
   ```

2. **Upload to Claude:**
   - Open Claude Desktop or Web
   - Go to Settings → Capabilities → Skills
   - Upload the `shell-tools-osx.zip` file
   - The skill will be available in all future conversations

3. **Use the skill:**
   - Start a new chat
   - When you mention tasks like "search this codebase" or "find all TypeScript files", Claude will automatically load this skill
   - You can also explicitly invoke it by mentioning specific tools: "use ripgrep to find...", "use ast-grep to refactor..."

## Install the CLI Tools (macOS)

### Essential Tools (16)
```bash
# Core tools
brew install fd ripgrep ast-grep jq yq git-delta httpie \
             gh shellcheck tokei sd

# Automation & quality
brew install mise just pre-commit watchexec

# Performance & analysis
brew install hyperfine difftastic
```

### Optional Tools (4)
```bash
# Interactive & secrets management
brew install fzf direnv sops age
```

**Additional setup:**
```bash
# Authenticate with GitHub (required for gh)
gh auth login

# fzf key bindings (optional - if fzf installed)
"$(brew --prefix)/opt/fzf/install" --key-bindings --completion --no-update-rc

# direnv shell hook (optional - if direnv installed, add to ~/.zshrc or ~/.bashrc)
eval "$(direnv hook zsh)"  # or bash
```

## Skill Structure

```
shell-tools-osx/
├── SKILL.md                          # Main skill instructions (loaded when skill triggers)
├── INSTALL.md                        # This file
├── README.md                         # Design principles & improvements
├── scripts/                          # Helper scripts
│   ├── search-and-preview.sh        # Interactive file search with preview
│   ├── code-search-replace.sh       # Guided AST refactoring workflow
│   ├── project-setup.sh             # Bootstrap project configs
│   └── analyze-codebase.sh          # Quick codebase analysis
├── references/                       # Detailed documentation (loaded as needed)
│   └── commands.md                  # Comprehensive command reference (20 tools)
└── assets/                          # Template config files
    ├── .mise.toml                   # Runtime & task management
    ├── .envrc                       # Environment variables (optional)
    ├── justfile                     # Task runner recipes with new tools
    ├── .pre-commit-config.yaml      # Git hooks with shellcheck
    └── .sops.yaml                   # Secrets encryption (optional)
```

## Quick Start

After installing both the skill and CLI tools:

1. **Test basic tools:**
   ```bash
   fd --version
   rg --version
   sg --version
   yq --version
   gh --version
   tokei --version
   ```

2. **Try a workflow:**
   ```bash
   # Analyze codebase
   tokei .

   # Find TODO comments
   rg -n "TODO"

   # Simple find/replace
   sd 'old' 'new' file.txt -p

   # Make an API call
   http GET httpbin.org/get

   # Check GitHub status
   gh pr status
   ```

3. **Bootstrap a project:**
   ```bash
   cd /path/to/your/project
   /path/to/shell-tools-osx/scripts/project-setup.sh
   ```

## Using with Claude

Example prompts that will trigger this skill:

- "Search this codebase for all instances of `fetchUser`"
- "Find all TypeScript files that import React"
- "Refactor all console.log statements to use logger.debug"
- "Analyze this codebase and give me statistics"
- "Update the docker-compose.yml to use Node 20"
- "Create a GitHub PR for my changes"
- "Help me set up a justfile for this project"
- "Validate all shell scripts in this repo"
- "Benchmark the test suite"

The skill will provide copy-pasteable commands using the installed tools, along with explanations and best practices.

## Updating the Skill

To update the skill after making changes:

1. Make your changes to SKILL.md, scripts, references, or assets
2. Re-package: `zip -r shell-tools-osx.zip . -x "*.git*" -x "*.DS_Store"`
3. Upload the new zip file in Claude Settings → Skills
4. Start a new conversation to use the updated version

## Resources

- [Anthropic Skills Documentation](https://docs.anthropic.com/claude/docs/skills)
- Tool documentation: See `references/commands.md` for detailed command reference
- Example configs: See `assets/` directory for ready-to-use templates
