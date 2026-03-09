---
name: log-analyzer
description: Analyze application logs, error logs, stack traces, and debugging output. Use this when users want to: debug errors from logs, understand what went wrong from error messages, analyze application logs to find issues, parse stack traces, identify error patterns, get debugging suggestions, or make sense of crash reports. Trigger whenever the user shares logs, error messages, stack traces, or asks for help debugging something that failed.
license: Apache-2.0
---

# Log Analyzer & Debugging Assistant

This skill helps analyze logs, errors, and debugging information to identify problems and suggest solutions.

## Core Capabilities

### 1. Log Format Detection
Automatically identify and parse different log formats:
- **Application logs**: Python (logging), Node.js (winston/bunyan), Java (log4j), Go (logrus), Rust (log/env_logger)
- **Server logs**: Nginx, Apache, Caddy
- **Container logs**: Docker, Kubernetes, Docker Compose
- **CI/CD logs**: GitHub Actions, GitLab CI, Jenkins, CircleCI
- **Database logs**: PostgreSQL, MySQL, MongoDB, Redis
- **System logs**: syslog, journalctl, Windows Event Log

### 2. Error Analysis

When analyzing errors, follow this structured approach:

**Step 1: Extract Key Information**
```
- Error type/exception class
- Error message
- File and line number
- Stack trace (full or partial)
- Timestamp and context
- Related warnings or deprecations
```

**Step 2: Categorize the Error**
```
Common error categories:
- Syntax/Type errors (code issues)
- Import/Dependency errors (missing packages)
- Configuration errors (wrong settings)
- Network errors (connection failures)
- Permission errors (access denied)
- Resource errors (out of memory, disk full)
- Race conditions (timing issues)
- Logic errors (bugs in algorithm)
```

**Step 3: Identify Root Cause**
Look for:
- The immediate cause (what directly failed)
- Underlying causes (why it failed)
- Contributing factors (environment, state, timing)
- Cascading failures (errors triggered by other errors)

**Step 4: Provide Actionable Solutions**
For each identified issue:
- Explain what went wrong (in simple terms)
- Suggest specific fixes with code examples when applicable
- Provide debugging steps to verify the fix
- Mention preventive measures

### 3. Stack Trace Analysis

Parse and interpret stack traces from any language:

**Python Stack Traces**
```python
Traceback (most recent call last):
  File "app.py", line 42, in <module>
    result = process_data(data)
  File "app.py", line 38, in process_data
    return json.loads(raw_data)
json.decoder.JSONDecodeError: Expecting value: line 1 column 1 (char 0)
```
Analysis: The error occurs in `process_data()` at line 38 when trying to parse invalid JSON.

**JavaScript Stack Traces**
```javascript
Error: Cannot read property 'map' of undefined
    at processItems (/src/app.js:42:15)
    at main (/src/app.js:28:5)
```
Analysis: `items` is undefined when passed to `processItems()`.

**Java Stack Traces**
```java
Exception in thread "main" java.lang.NullPointerException
    at com.example.Service.process(Service.java:42)
    at com.example.Main.main(Main.java:15)
```
Analysis: A null reference at line 42 in Service.java.

**Go Stack Traces**
```go
panic: runtime error: invalid memory address or nil pointer dereference
[signal SIGSEGV: segmentation violation code=0x1 addr=0x8 pc=0x1234]

goroutine 1 [running]:
main.(*Handler).Process(...)
        /app/handler.go:42 +0x123
main.main()
        /app/main.go:15 +0x456
```
Analysis: Nil pointer dereference in handler.go:42.

**Rust Stack Traces**
```rust
thread 'main' panicked at 'called Option::unwrap() on a None value', src/main.rs:42:15
```
Analysis: Called `unwrap()` on a `None` value.

### 4. Log Pattern Recognition

Identify common patterns that indicate issues:

**Error Cascades**
```
[ERROR] Connection refused: database:5432
[ERROR] Failed to initialize connection pool
[ERROR] Unable to start application
```
Analysis: Root cause is database connection failure, subsequent errors are cascading.

**Memory Issues**
```
Out of memory: Kill process 12345 (node) score 900
JavaScript heap out of memory
FATAL ERROR: Reached heap limit Allocation failed
```
Analysis: Application exceeded memory limits, needs optimization or increased allocation.

**Race Conditions**
```
[ERROR] Transaction aborted: deadlock detected
[ERROR] Concurrent update conflict
[WARN] Retry attempt 1/3
```
Analysis: Concurrent database operations causing conflicts.

**Resource Exhaustion**
```
[ERROR] Too many open files
[ERROR] File descriptor limit reached
[WARN] Connection pool exhausted
```
Analysis: System resource limits exceeded, need to increase limits or fix resource leaks.

### 5. Contextual Analysis

Consider the broader context:
- **Environment**: Development, staging, production
- **Recent changes**: Deployments, configuration changes
- **Load level**: Normal traffic, spike, stress test
- **Dependencies**: Version changes, upstream failures
- **Time patterns**: Intermittent, recurring, time-of-day specific

### 6. Debugging Workflow

Follow this systematic approach when users ask for debugging help:

```
1. GATHER INFORMATION
   - Ask for complete logs (not just errors)
   - Request context about what was happening
   - Get reproduction steps if available
   - Check environment details (OS, runtime version)

2. ANALYZE LOGS
   - Identify the first/earliest error (root cause)
   - Look for error patterns across multiple runs
   - Check for warnings that preceded errors
   - Note any anomalies or unexpected values

3. FORM HYPOTHESIS
   - What is the most likely cause?
   - What evidence supports this?
   - What alternative explanations exist?

4. PROVIDE SOLUTIONS
   - Start with most likely fix
   - Provide debugging steps to verify
   - Suggest preventive measures
   - Offer fallback solutions

5. VALIDATE
   - Ask user to try the solution
   - Adjust based on feedback
   - If solution doesn't work, reconsider hypothesis
```

### 7. Common Issues & Quick Fixes

**Import/Module Errors**
```
Error: Cannot find module 'express'
Fix: npm install express
```

**Permission Errors**
```
Error: EACCES: permission denied
Fix: chmod +x script.sh  or  sudo npm install -g
```

**Port Already in Use**
```
Error: Port 3000 is already in use
Fix: lsof -ti:3000 | xargs kill -9  or  use a different port
```

**Connection Refused**
```
Error: ECONNREFUSED 127.0.0.1:5432
Fix: Ensure the service is running: systemctl start postgresql
```

**Timeout Errors**
```
Error: Request timeout after 30000ms
Fix: Increase timeout or check network connectivity
```

**Out of Memory**
```
Error: JavaScript heap out of memory
Fix: Increase Node.js memory: NODE_OPTIONS=--max_old_space_size=4096
```

## Output Format

When analyzing logs, provide:

1. **Summary** (1-2 sentences)
   - What type of issue was found
   - Severity level (critical, error, warning, info)

2. **Root Cause** (bullet points)
   - The primary issue
   - Any contributing factors

3. **Specific Fixes** (code examples when applicable)
   - Exact steps to fix
   - Code snippets showing before/after
   - Configuration changes needed

4. **Verification Steps**
   - How to confirm the fix works
   - What to check after applying the fix

5. **Prevention Tips**
   - How to avoid this issue in the future
   - Best practices related to this issue

## Examples

### Example 1: Python Error

**User provides:**
```python
Traceback (most recent call last):
  File "app.py", line 10, in <module>
    data = json.loads(request.text)
json.decoder.JSONDecodeError: Expecting value: line 1 column 1 (char 0)
```

**Analysis:**
- **Issue**: Trying to parse invalid JSON (empty string or non-JSON content)
- **Fix**: Add validation and error handling
```python
import json

# Before
data = json.loads(request.text)

# After
if not request.text or not request.text.strip():
    data = {}
else:
    try:
        data = json.loads(request.text)
    except json.JSONDecodeError as e:
        print(f"Invalid JSON: {e}")
        data = {}
```

### Example 2: Node.js Error

**User provides:**
```javascript
Error: connect ENOENT /path/to/config.json
    at Object.openSync (node:fs:588:3)
    at Object.readFileSync (node:fs:456:17)
```

**Analysis:**
- **Issue**: File doesn't exist at the specified path
- **Fix**: Check if file exists before reading, or create default config
```javascript
import fs from 'fs';
import path from 'path';

const configPath = '/path/to/config.json';

// Before (will crash if file doesn't exist)
const config = JSON.parse(fs.readFileSync(configPath));

// After (handles missing file)
let config = {};
if (fs.existsSync(configPath)) {
  config = JSON.parse(fs.readFileSync(configPath));
} else {
  console.warn(`Config file not found at ${configPath}, using defaults`);
}
```

### Example 3: Database Connection Error

**User provides:**
```
Error: connect ECONNREFUSED 127.0.0.1:5432
    at TCPConnectWrap.afterConnect [as oncomplete] (node:net:1195:13)
```

**Analysis:**
- **Issue**: PostgreSQL is not running or wrong port
- **Fix Steps**:
  1. Check if PostgreSQL is running: `pg_isready` or `systemctl status postgresql`
  2. Start if needed: `brew services start postgresql`  or `systemctl start postgresql`
  3. Verify connection string matches actual port (default: 5432)

### Example 4: Kubernetes Pod Crash

**User provides:**
```yaml
Status:       CrashLoopBackOff
Restart Count:  5
Events:
  Warning   BackOff    Back-off restarting failed container
```

**Analysis:**
- **Issue**: Container keeps crashing immediately after start
- **Debug Steps**:
  1. Get pod logs: `kubectl logs <pod-name>`
  2. Check previous crash: `kubectl logs <pod-name> --previous`
  3. Describe pod for events: `kubectl describe pod <pod-name>`
  4. Common causes: missing env vars, failed healthcheck, missing config files

## Best Practices

1. **Always ask for complete logs** - Not just the error, but surrounding context
2. **Look for the first error** - Subsequent errors are often symptoms
3. **Consider the environment** - Dev vs production differences matter
4. **Provide context-aware solutions** - Adjust based on language/framework
5. **Educate while solving** - Explain why the error occurred, not just how to fix it
6. **Verify assumptions** - If uncertain about the cause, suggest debugging steps to confirm
7. **Handle multiple errors** - When logs show multiple issues, prioritize by severity and dependencies

## When to Use This Skill

Trigger this skill when users:
- Share error messages or stack traces
- Paste application logs (any format)
- Ask for help debugging something
- Mention crashes, panics, or failures
- Want to understand why something isn't working
- Need help interpreting CI/CD failure logs
- Have issues with deployments or services

## Integration with Other Skills

This skill works well with:
- **webapp-testing**: When debugging test failures
- **mcp-builder**: When debugging MCP server issues
- **docx/pdf**: When documenting error reports
- **internal-comms**: When writing incident reports
