# Automation Permissions & Scope

## Workspace Scope

**Primary Workspace:** `/Users/arnold/Development`

### Allowed Operations

Full automation permissions within the Development folder:

✅ **Read Access:**
- All files in `/Users/arnold/Development/**`
- All subdirectories and repositories
- Configuration files (.gitignore, package.json, etc.)

✅ **Write Access:**
- Create/modify .gitignore files
- Create/modify configuration files
- Install git hooks (.git/hooks/*)
- Update dependencies (package.json, package-lock.json)

✅ **Git Operations:**
- Commit changes with descriptive messages
- Push to remote repositories
- Create branches (when requested)
- Manage git configuration per repository

✅ **Automation:**
- Batch processing (10 items per batch)
- Auto-commit security improvements
- Auto-push after commits
- Security audits
- Dependency updates

### Restricted Access

❌ **No Access To:**
- Files outside `/Users/arnold/Development`
- System files
- User home directory (except Development folder)
- Other user directories
- `/tmp` (read-only for reports)

### Safety Features

**Automatic:**
- Pre-commit hooks prevent secret leaks
- All commits include proper attribution
- Batch processing prevents rate limiting
- No destructive operations without confirmation

**Manual Review Available:**
- `git log` to review commits
- `git diff` to review changes
- All operations are logged

### Batch Processing Guidelines

**Optimal Performance:**
- Process 10 repositories per batch
- Process 10 files per batch
- Short delays between batches
- Progress indicators every batch

### Branding & Content Policy

**Strict Requirements:**
- ❌ No AI tool branding in commits
- ❌ No promotional content
- ❌ No spam or unnecessary messages
- ✅ Professional, neutral commit messages only
- ✅ Clean, focused content

### Workflow Examples

**Security Audit:**
1. Scan all repos in Development folder
2. Categorize findings (real vs false positives)
3. Fix issues in batches of 10
4. Commit changes with clean, descriptive messages
5. Auto-push to GitHub

**Dependency Updates:**
1. Check for updates in all repos
2. Update in batches of 10
3. Run tests after each update
4. Auto-commit and push if tests pass

---

**Scope:** `/Users/arnold/Development` only
**Automation:** ✅ Enabled
**Branding Policy:** ✅ No branding/spam allowed
**Last Updated:** November 22, 2025
