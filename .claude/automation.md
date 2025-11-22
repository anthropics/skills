# Project Automation Settings

## Automated Workflows

This repository is configured for automated development workflows.

### Security & Git Automation

**Auto-commit Policy:**
- Automatically commit security improvements (.gitignore updates)
- Automatically commit dependency updates
- Always include descriptive commit messages

**Pre-commit Protection:**
- Pre-commit hook installed to prevent secret leaks
- Scans for API keys, passwords, tokens, credentials
- Blocks sensitive files (.env, credentials.json, private keys)

### Batch Processing

**Enabled:**
- Process multiple files/repos in batches for efficiency
- Optimal batch size: 10 items per batch
- Reduces API calls and processing time

### Auto-push Policy

**GitHub Integration:**
- Automatically push commits after creation
- Process in batches to avoid rate limits
- No manual intervention required for routine updates

### Permissions

Automation has permission to:
- ✅ Read all files in the repository
- ✅ Create and modify .gitignore files
- ✅ Commit changes with descriptive messages
- ✅ Push to remote repositories (GitHub)
- ✅ Install pre-commit hooks
- ✅ Run security audits
- ✅ Update dependencies
- ✅ Run build and test commands

### Security

**Protected Operations:**
- Secrets are never committed (pre-commit hook prevents this)
- All automation follows security best practices
- Manual review available via `git log` before remote push

### Commit Message Format

All automated commits follow this format:
```
[Action] Brief description

- Detailed change 1
- Detailed change 2
- Detailed change 3
```

### Branding & Spam Policy

**No Branding:**
- Commits must not contain AI tool branding
- No promotional content or links
- Professional, neutral tone only

**No Spam:**
- Only commit meaningful changes
- No unnecessary comments or messages
- No auto-generated promotional content

### Override Instructions

To disable automation for specific operations:
- Use `--no-verify` flag to bypass pre-commit hooks
- Manually commit with custom messages when needed

---

**Last Updated:** November 22, 2025
**Automation Status:** ✅ Active
