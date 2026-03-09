# ScoutQA CLI Reference

AI-powered exploratory testing for web applications using the `scoutqa` CLI.

[ScoutQA](https://scoutqa.ai/) automatically tests your websites for accessibility issues, broken user flows, and usability problems — all from simple English instructions.

## When to Use ScoutQA

Use ScoutQA when:

- User asks to "test this website" or "run exploratory testing"
- You want to proactively verify web features after implementation
- Automated QA testing is needed without writing Playwright scripts

Use Playwright (main SKILL.md) when:

- You need precise control over test steps
- Testing local development servers
- Capturing specific screenshots or console logs

## Installation

1. Install the ScoutQA CLI:

```bash
npm i -g @scoutqa/cli@latest
```

2. Add your [API key][api-key] by logging in:

```bash
scoutqa auth login
```

3. Install the plugin:

```bash
claude plugin marketplace add https://github.com/scoutqa-dot-ai/claude-code
claude plugin i scoutqa-plugin@scoutqa-marketplace
```

## Basic Usage

```bash
scoutqa --url "https://example.com" --prompt "test the login flow"
```

**Important**: Run with Bash tool timeout of 5000ms. After 5 seconds, the tool returns control with a task ID while the test continues in the background.

## Command Options

| Option     | Description                        |
| ---------- | ---------------------------------- |
| `--url`    | Target URL to test                 |
| `--prompt` | Natural language test instructions |

## Workflow

1. **Write specific test prompts** with clear expectations
2. **Run scoutqa command** with 5000ms Bash timeout
3. **Inform user** of execution ID and browser URL
4. **Extract and analyze results** when complete

## Parallel Testing

Run multiple tests simultaneously by making multiple Bash calls in a single message:

```bash
# Test 1: Authentication
scoutqa --url "https://example.com/login" --prompt "test login with valid credentials"

# Test 2: Features
scoutqa --url "https://example.com/dashboard" --prompt "verify dashboard loads correctly"

# Test 3: Accessibility
scoutqa --url "https://example.com" --prompt "check for accessibility issues"
```

## Reporting Results

Present issues with:

- **Severity**: High / Medium / Low
- **Category**: Functional, UI, Performance, Accessibility
- **Impact**: Description of user impact
- **Location**: Page/component where found

## Follow-up Commands

For stuck executions needing clarification or credentials:

```bash
scoutqa send-message --execution-id <id> --message "credentials are user@test.com / password123"
```

## Troubleshooting

| Issue                       | Solution                                                  |
| --------------------------- | --------------------------------------------------------- |
| command not found: scoutqa  | Install CLI: npm i -g @scoutqa/cli@latest                 |
| Auth expired / unauthorized | Run scoutqa auth login                                    |
| Execution hangs             | Use scoutqa send-message --execution-id                   |
| Check test results          | Visit browser URL or scoutqa get-execution --execution-id |
