# Scan Detection Rules — Pattern Reference

Detailed Grep patterns for all 24 detection rules. Use this as reference when executing the `scan` subcommand.

**Markdown files**: For `.md` files, only scan inside fenced code blocks (between ``` markers). Additionally, decode and re-scan base64-encoded payloads found in any file.

## Rule 1: SHELL_EXEC (HIGH)
**Files**: `*.js`, `*.ts`, `*.mjs`, `*.cjs`, `*.py`, `*.md`

| Pattern | Description |
|---------|-------------|
| `require\s*\(\s*['"\x60]child_process` | Node.js child_process require |
| `from\s+['"\x60]child_process` | ES module child_process import |
| `\bexec\s*\(` | exec() call |
| `\bexecSync\s*\(` | execSync() call |
| `\bspawn\s*\(` | spawn() call |
| `\bspawnSync\s*\(` | spawnSync() call |
| `\bexecFile\s*\(` | execFile() call |
| `\bfork\s*\(` | fork() call |
| `\bsubprocess\.` | Python subprocess module |
| `\bos\.system\s*\(` | Python os.system() |
| `\bos\.popen\s*\(` | Python os.popen() |
| `\bos\.exec\w*\s*\(` | Python os.exec*() |
| `\bcommands\.getoutput\s*\(` | Python commands module |
| `\bcommands\.getstatusoutput\s*\(` | Python commands module |

## Rule 2: AUTO_UPDATE (CRITICAL)
**Files**: `*.js`, `*.ts`, `*.py`, `*.sh`, `*.md`

| Pattern | Description |
|---------|-------------|
| `cron\|schedule\|interval.*exec\|setInterval.*exec` (i) | Scheduled execution |
| `auto.?update\|self.?update` (i) | Auto-update mechanism |
| `curl.*\|\s*(bash\|sh)` | curl pipe to shell |
| `wget.*\|\s*(bash\|sh)` | wget pipe to shell |
| `fetch.*then.*eval` | Fetch and eval chain |
| `download.*execute` (i) | Download and execute |

## Rule 3: REMOTE_LOADER (CRITICAL)
**Files**: `*.js`, `*.ts`, `*.mjs`, `*.py`, `*.md`

| Pattern | Description |
|---------|-------------|
| `import\s*\(\s*[^'"\x60\s]` | Dynamic import with variable |
| `require\s*\(\s*[^'"\x60\s]` | Dynamic require with variable |
| `fetch\s*\([^)]*\)\.then\([^)]*\)\s*\.then\([^)]*eval` | Fetch + eval chain |
| `axios\.[^)]*\.then\([^)]*eval` | Axios + eval chain |
| `exec\s*\(\s*requests\.get` | Python exec(requests.get()) |
| `eval\s*\(\s*requests\.get` | Python eval(requests.get()) |
| `exec\s*\(\s*urllib` | Python exec(urllib) |
| `eval\s*\(\s*urllib` | Python eval(urllib) |
| `__import__\s*\(` | Python dynamic import |
| `importlib\.import_module\s*\(` | Python importlib |

## Rule 4: READ_ENV_SECRETS (MEDIUM)
**Files**: `*.js`, `*.ts`, `*.mjs`, `*.py`

| Pattern | Description |
|---------|-------------|
| `process\.env\s*\[` | Node.js env bracket access |
| `process\.env\.` | Node.js env dot access |
| `require\s*\(\s*['"\x60]dotenv` | dotenv require |
| `from\s+['"\x60]dotenv` | dotenv import |
| `os\.environ` | Python os.environ |
| `os\.getenv\s*\(` | Python os.getenv() |
| `dotenv\.load_dotenv` | Python dotenv |
| `from\s+dotenv\s+import` | Python dotenv import |

## Rule 5: READ_SSH_KEYS (CRITICAL)
**Files**: All

| Pattern | Description |
|---------|-------------|
| `~/.ssh` | SSH directory reference |
| `\.ssh/id_rsa` | RSA key |
| `\.ssh/id_ed25519` | Ed25519 key |
| `\.ssh/id_ecdsa` | ECDSA key |
| `\.ssh/id_dsa` | DSA key |
| `\.ssh/known_hosts` | Known hosts |
| `\.ssh/authorized_keys` | Authorized keys |
| `HOME.*\.ssh` | HOME-based SSH path |
| `USERPROFILE.*\.ssh` | Windows SSH path |

## Rule 6: READ_KEYCHAIN (CRITICAL)
**Files**: All

| Pattern | Description |
|---------|-------------|
| `keychain` (i) | Keychain reference |
| `security\s+find-` | macOS security command |
| `Chrome.*Local\s+State` (i) | Chrome local state |
| `Chrome.*Login\s+Data` (i) | Chrome login data |
| `Chrome.*Cookies` (i) | Chrome cookies |
| `Chromium` (i) | Chromium browser |
| `Firefox.*logins\.json` (i) | Firefox logins |
| `Firefox.*cookies\.sqlite` (i) | Firefox cookies |
| `CredRead` | Windows CredRead |
| `Windows.*Credentials` (i) | Windows credentials |
| `credential.*manager` (i) | Credential manager |

## Rule 7: PRIVATE_KEY_PATTERN (CRITICAL)
**Files**: All

| Pattern | Description |
|---------|-------------|
| `['"\x60]0x[a-fA-F0-9]{64}['"\x60]` | Ethereum private key in quotes |
| `private[_\s]?key\s*[:=]\s*['"\x60]0x[a-fA-F0-9]{64}` (i) | Named private key |
| `PRIVATE_KEY\s*[:=]\s*['"\x60][a-fA-F0-9]{64}` (i) | PRIVATE_KEY assignment |

## Rule 8: MNEMONIC_PATTERN (CRITICAL)
**Files**: All

| Pattern | Description |
|---------|-------------|
| Quoted string with 12-24 BIP-39 words starting with: abandon, ability, able, about, above, absent, absorb, abstract, absurd, abuse | Mnemonic phrase |
| `seed[_\s]?phrase\s*[:=]\s*['"\x60]` (i) | Seed phrase assignment |
| `mnemonic\s*[:=]\s*['"\x60]` (i) | Mnemonic assignment |
| `recovery[_\s]?phrase\s*[:=]\s*['"\x60]` (i) | Recovery phrase assignment |

## Rule 9: WALLET_DRAINING (CRITICAL)
**Files**: `*.js`, `*.ts`, `*.sol`

| Pattern | Description |
|---------|-------------|
| `approve\s*\([^,]+,\s*(type\s*\(\s*uint256\s*\)\s*\.max\|0xffffffff\|MaxUint256\|MAX_UINT)` (i) | Approve max uint |
| `transferFrom.*approve\|approve.*transferFrom` (i, multiline) | Approve + transferFrom |
| `permit\s*\(.*deadline` (i, multiline) | Permit with deadline |

## Rule 10: UNLIMITED_APPROVAL (HIGH)
**Files**: `*.js`, `*.ts`, `*.sol`

| Pattern | Description |
|---------|-------------|
| `\.approve\s*\([^,]+,\s*ethers\.constants\.MaxUint256` | ethers MaxUint256 approval |
| `\.approve\s*\([^,]+,\s*2\s*\*\*\s*256\s*-\s*1` | 2**256-1 approval |
| `\.approve\s*\([^,]+,\s*type\(uint256\)\.max` | Solidity type(uint256).max |
| `setApprovalForAll\s*\([^,]+,\s*true\)` | setApprovalForAll(true) |

## Rule 11: DANGEROUS_SELFDESTRUCT (HIGH)
**Files**: `*.sol`

| Pattern | Description |
|---------|-------------|
| `selfdestruct\s*\(` | selfdestruct call |
| `suicide\s*\(` | suicide call (deprecated) |

## Rule 12: HIDDEN_TRANSFER (MEDIUM)
**Files**: `*.sol`

| Pattern | Description |
|---------|-------------|
| `.transfer(` in functions not named `transfer`/`_transfer` | Hidden transfer in non-transfer function |
| `\.call\{value:\s*[^}]+\}\s*\(['"\x60]['"\x60]\)` | Low-level call with value, empty data |

## Rule 13: PROXY_UPGRADE (MEDIUM)
**Files**: `*.sol`, `*.js`, `*.ts`

| Pattern | Description |
|---------|-------------|
| `upgradeTo\s*\(` | upgradeTo call |
| `upgradeToAndCall\s*\(` | upgradeToAndCall |
| `_setImplementation\s*\(` | Internal set implementation |
| `IMPLEMENTATION_SLOT` | Implementation storage slot |

## Rule 14: FLASH_LOAN_RISK (MEDIUM)
**Files**: `*.sol`, `*.js`, `*.ts`

| Pattern | Description |
|---------|-------------|
| `flashLoan\s*\(` (i) | flashLoan call |
| `flash\s*Loan` (i) | flashLoan reference |
| `IFlashLoan` | Flash loan interface |
| `executeOperation\s*\(` | AAVE callback |
| `AAVE.*flash` (i) | AAVE flash reference |

## Rule 15: REENTRANCY_PATTERN (HIGH)
**Files**: `*.sol`

Look for external calls followed by state changes in the same function:
- `.call{` or `.transfer(` followed by a state variable assignment (`variable =`, `variable +=`, etc.)
- This violates the Checks-Effects-Interactions pattern

## Rule 16: SIGNATURE_REPLAY (HIGH)
**Files**: `*.sol`

| Pattern | Description |
|---------|-------------|
| `ecrecover\s*\(` | ecrecover usage |

**Validation**: After finding `ecrecover`, check if the enclosing function also references `nonce`. If no nonce is found, flag as SIGNATURE_REPLAY.

## Rule 17: OBFUSCATION (HIGH)
**Files**: `*.js`, `*.ts`, `*.mjs`, `*.py`, `*.md`

| Pattern | Description |
|---------|-------------|
| `\beval\s*\(` | eval() call |
| `new\s+Function\s*\(` | Function constructor |
| `setTimeout\s*\(\s*['"\x60]` | setTimeout with string |
| `setInterval\s*\(\s*['"\x60]` | setInterval with string |
| `atob\s*\([^)]+\).*eval` | Base64 decode + eval |
| `Buffer\.from\s*\([^,]+,\s*['"\x60]base64['"\x60]\s*\).*eval` | Buffer base64 + eval |
| 10+ consecutive `\\x[0-9a-fA-F]{2}` | Hex escape obfuscation |
| 10+ consecutive `\\u[0-9a-fA-F]{4}` | Unicode escape obfuscation |
| `String\.fromCharCode\s*\(\s*\d+(?:\s*,\s*\d+){10,}` | Large fromCharCode |
| `eval\s*\(\s*function\s*\(\s*p\s*,\s*a\s*,\s*c\s*,\s*k\s*,\s*e` | Packed JS (p,a,c,k,e,r) |

## Rule 18: PROMPT_INJECTION (CRITICAL)
**Files**: All

| Pattern | Description |
|---------|-------------|
| `ignore\s+(previous\|all\|above\|prior)\s+(instructions?\|rules?\|guidelines?)` (i) | Ignore instructions |
| `disregard\s+(previous\|all\|above\|prior)\s+(instructions?\|rules?\|guidelines?)` (i) | Disregard instructions |
| `forget\s+(previous\|all\|above\|prior)\s+(instructions?\|rules?\|guidelines?)` (i) | Forget instructions |
| `you\s+are\s+(now\|a)\s+(?:DAN\|jailbroken\|unrestricted)` (i) | Jailbreak attempt |
| `pretend\s+(?:you\s+are\|to\s+be)\s+(?:a\s+)?(?:different\|new\|unrestricted)` (i) | Role pretend |
| `act\s+as\s+(?:if\s+)?(?:you\s+have\s+)?no\s+(?:restrictions?\|rules?\|limitations?)` (i) | No restrictions |
| `(?:no\|without\|skip)\s+(?:need\s+(?:for\s+)?)?confirm(?:ation)?` (i) | Skip confirmation |
| `bypass\s+(?:security\|safety\|restrictions?\|confirm)` (i) | Bypass security |
| `auto(?:matically)?\s+(?:approve\|confirm\|execute\|run)` (i) | Auto-execute |
| `you\s+must\s+(?:always\s+)?(?:obey\|follow\|execute)` (i) | Force obedience |
| `system\s*:\s*you\s+are` (i) | System prompt injection |
| `\[system\].*\[/system\]` (i, multiline) | System tag injection |
| `忽略(?:之前\|所有\|上面)(?:的)?(?:指令\|规则\|说明)` | Chinese: ignore instructions |
| `无需确认\|自动执行\|跳过验证` | Chinese: skip confirm / auto-exec |

## Rule 19: NET_EXFIL_UNRESTRICTED (HIGH)
**Files**: `*.js`, `*.ts`, `*.mjs`, `*.py`, `*.md`

| Pattern | Description |
|---------|-------------|
| `fetch\s*\([^)]+,\s*\{[^}]*method\s*:\s*['"\x60]POST` | Fetch POST |
| `axios\.post\s*\(` | Axios POST |
| `requests\.post\s*\(` | Python requests POST |
| `http\.request\s*\([^)]*method\s*:\s*['"\x60]POST` | Node http POST |
| `new\s+FormData\s*\(` | FormData creation |
| `enctype\s*[:=]\s*['"\x60]multipart/form-data` | Multipart upload |

## Rule 20: WEBHOOK_EXFIL (CRITICAL)
**Files**: All

| Pattern | Description |
|---------|-------------|
| `discord(?:app)?\.com/api/webhooks` (i) | Discord webhooks |
| `api\.telegram\.org/bot` (i) | Telegram bot API |
| `telegram-bot-api` (i) | Telegram bot lib |
| `hooks\.slack\.com` (i) | Slack webhooks |
| `webhook\s*[:=]\s*['"\x60]https?:` (i) | Generic webhook URL |
| `ngrok\.io` (i) | ngrok tunnel |
| `ngrok-free\.app` (i) | ngrok free |
| `requestbin` (i) | RequestBin |
| `pipedream` (i) | Pipedream |
| `webhook\.site` (i) | Webhook.site |

## Rule 21: TROJAN_DISTRIBUTION (CRITICAL)
**Files**: `*.md`

Detects trojanized binary distribution patterns. Flags when 2+ of the following signals are present:

| Signal | Pattern | Description |
|--------|---------|-------------|
| Download | `https?://.*(?:releases/download\|\.zip\|\.tar\|\.exe\|\.dmg)` (i) | Binary download URL |
| Password | `password\s*[:=]` (i) | Password for archive |
| Execute | `chmod\s+\+x\|\.\/\w+\|run\s+the\|execute` (i) | Execute instruction |

**Validation**: Must match at least 2 of the 3 signals to trigger.

## Rule 22: SUSPICIOUS_PASTE_URL (HIGH)
**Files**: All

| Pattern | Description |
|---------|-------------|
| `glot\.io/snippets/` (i) | Glot.io snippets |
| `pastebin\.com/` (i) | Pastebin |
| `hastebin\.com/` (i) | Hastebin |
| `paste\.ee/` (i) | Paste.ee |
| `dpaste\.org/` (i) | dpaste |
| `rentry\.co/` (i) | Rentry |
| `ghostbin\.com/` (i) | Ghostbin |
| `pastie\.io/` (i) | Pastie |

## Rule 23: SUSPICIOUS_IP (MEDIUM)
**Files**: All

| Pattern | Description |
|---------|-------------|
| `\b(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})\b` | IPv4 address |

**Validation**: Excludes private/reserved ranges:
- `127.x.x.x` (loopback), `0.x.x.x`, `10.x.x.x`, `172.16-31.x.x`, `192.168.x.x`, `169.254.x.x` (link-local)
- Version-like patterns (`x.0.0.0`)
- Values > 255 in any octet

## Rule 24: SOCIAL_ENGINEERING (MEDIUM)
**Files**: `*.md`

| Pattern | Description |
|---------|-------------|
| `CRITICAL\s+REQUIREMENT` (i) | Urgency pressure |
| `WILL\s+NOT\s+WORK\s+WITHOUT` (i) | Fear-based pressure |
| `MANDATORY.*(?:install\|download\|run\|execute)` (i) | Mandatory action |
| `you\s+MUST\s+(?:install\|download\|run\|execute\|paste)` (i) | Forced action |
| `paste\s+(?:this\s+)?into\s+(?:your\s+)?[Tt]erminal` (i) | Terminal paste instruction |
| `IMPORTANT:\s*(?:you\s+)?must` (i) | Importance pressure |

**Validation**: Only triggers if content also contains a command execution pattern (`curl`, `wget`, `bash`, `sh`, `./`, `chmod`, `npm run`, `node`).

Note: `(i)` = case insensitive search, `(multiline)` = enable multiline matching.
