# GitHub Repository Setup Checklist

## Branch Protection Rules

### Main Branch Protection

Navigate to: `Settings → Branches → Add rule`

**Branch name pattern:** `main`

**Required Settings:**

- [x] Require a pull request before merging
  - [x] Require approvals: **1**
  - [x] Dismiss stale pull request approvals when new commits are pushed
  - [x] Require review from Code Owners (if CODEOWNERS file exists)

- [x] Require status checks to pass before merging
  - [x] Require branches to be up to date before merging
  - **Required status checks:**
    - `lint-and-format` (ESLint + Prettier)
    - `type-check` (TypeScript compilation)
    - `test` (Vitest with 70% coverage)
    - `security` (npm audit + console.log check)
    - `accessibility` (WCAG 2.1 compliance)
    - `backend-lint` (Python: flake8, black, mypy)
    - `bundle-size` (< 5MB check)

- [x] Require conversation resolution before merging
- [x] Require linear history (optional, recommended)
- [x] Do not allow bypassing the above settings
- [x] Restrict who can push to matching branches
  - Add: Administrators, Maintainers only

### Develop Branch Protection

Same rules as `main` branch, but with:

- Require approvals: **1** (can be same as main or less strict)
- Required checks: Same as main

---

## Environment Secrets Configuration

Navigate to: `Settings → Secrets and variables → Actions`

### Required Secrets for Deployment

**For Staging:**

- `STAGING_HOST` - Staging server hostname/IP
- `STAGING_USER` - SSH username
- `STAGING_SSH_KEY` - Private SSH key (full content)

**For Production:**

- `PRODUCTION_HOST` - Production server hostname/IP
- `PRODUCTION_USER` - SSH username
- `PRODUCTION_SSH_KEY` - Private SSH key (full content)

**For AWS/Cloud (Optional):**

- `AWS_ACCESS_KEY_ID` - AWS access key
- `AWS_SECRET_ACCESS_KEY` - AWS secret key

**For Monitoring (Optional):**

- `SENTRY_DSN` - Sentry error tracking DSN
- `DATADOG_API_KEY` - DataDog monitoring API key

---

## Dependabot Configuration

### Enable Dependabot Alerts

Navigate to: `Settings → Code security and analysis`

- [x] Enable **Dependency graph**
- [x] Enable **Dependabot alerts**
- [x] Enable **Dependabot security updates**

### Configure Dependabot Version Updates

File already exists: `.github/dependabot.yml`

To customize update schedule, edit:

```yaml
# .github/dependabot.yml
version: 2
updates:
  - package-ecosystem: 'npm'
    directory: '/'
    schedule:
      interval: 'weekly' # or daily/monthly
    open-pull-requests-limit: 5
```

---

## GitHub Copilot Setup (Optional)

### Enable Copilot for Repository

Navigate to: `Settings → Copilot`

- [x] Enable GitHub Copilot
- [x] Allow suggestions matching public code
- [x] Enable Copilot Chat

### Share Instructions with Team

File exists: `.github/copilot-instructions.md`

Team members should:

1. Install GitHub Copilot extension in VS Code
2. Review copilot-instructions.md for project-specific guidelines
3. Use Copilot suggestions while following ESLint/Prettier rules

---

## Verification Checklist

After completing setup:

### Local Verification

```bash
# Verify git hooks are working
git commit --allow-empty -m "test: pre-commit hook"
# Should run ESLint + Prettier

# Verify validation script
npm run validate
# Should pass: lint, format:check, type-check, test

# Test pre-push hook
git push origin <your-branch>
# Should run full validation suite
```

### GitHub Actions Verification

```bash
# Create test PR
git checkout -b test/ci-validation
echo "test" > test.txt
git add test.txt
git commit -m "test: CI validation"
git push -u origin test/ci-validation

# Create PR
gh pr create --title "test: CI validation" --body "Testing workflows"

# Verify all checks pass
gh pr checks
```

### Expected Results

- ✅ All GitHub Actions workflows complete successfully
- ✅ Branch protection prevents direct pushes to main
- ✅ PRs require approval before merge
- ✅ Status checks must pass before merge
- ✅ Pre-commit hooks auto-fix code style
- ✅ Pre-push hooks prevent bad code from being pushed

---

## Team Onboarding

Share with new team members:

1. **CONTRIBUTING.md** - Complete contribution guide
2. **DEPLOYMENT.md** - Deployment procedures
3. **RUNBOOK.md** - Operations manual
4. This setup checklist

### Required Developer Setup

```bash
# Clone repository
git clone https://github.com/criptolandiatv/skills.git
cd skills

# Install dependencies
npm install

# Husky hooks will be automatically installed
# Verify hooks are working
npm run validate

# Install recommended VS Code extensions
code --install-extension dbaeumer.vscode-eslint
code --install-extension esbenp.prettier-vscode
code --install-extension firsttris.vscode-jest-runner
code --install-extension streetsidesoftware.code-spell-checker
```

---

## Monitoring & Metrics

### CI/CD Success Rate

Track in GitHub: `Insights → Actions`

**Target metrics:**

- PR success rate (first attempt): **>80%**
- Average CI/CD runtime: **<5 minutes**
- Workflow failure rate: **<10%**

### Code Quality Metrics

Monitor in pull requests:

- **Test Coverage:** Currently passing with no tests, target **>70%** when tests added
- **ESLint Warnings:** Currently 13, target **<20** maximum
- **Bundle Size:** Target **<5MB** for production build

### Security Metrics

Review monthly:

- **npm audit vulnerabilities:** Currently 34 (mostly in ml5, not production)
- **Target:** 0 high/critical in production dependencies
- **Dependabot PRs:** Review and merge weekly

---

## Support & Escalation

**For setup issues:**

- Review `CONTRIBUTING.md` for detailed guidelines
- Check GitHub Actions logs for workflow failures
- Verify all secrets are correctly configured

**For CI/CD failures:**

- Run `npm run validate` locally to reproduce
- Check `RUNBOOK.md` for troubleshooting
- Review recent commits for breaking changes

**For deployment issues:**

- Follow `DEPLOYMENT.md` procedures
- Check `RUNBOOK.md` emergency procedures
- Verify environment variables are correct

---

**Last Updated:** 2025-10-25
**Version:** 1.0.0
**Owner:** DevOps Team
