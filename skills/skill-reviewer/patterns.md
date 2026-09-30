# Malicious Pattern Library

Detailed detection rules for security review reference.

## 1. System Destruction Commands

### File Deletion
```regex
rm\s+(-[rRfF]+\s+)*[/~]
rm\s+-rf\s+
rmdir\s+/[sS]
del\s+/[fFsS]
Remove-Item\s+-Recurse
shred\s+-[uvz]
```

### Disk Operations
```regex
format\s+[A-Z]:
fdisk\s+/dev/
mkfs\.[a-z]+\s+
dd\s+if=.*/dev/(zero|random)
parted\s+/dev/
```

### System Control
```regex
shutdown\s+(-[hHrR]|now)
reboot(\s+-f)?
init\s+[0-6]
halt|poweroff
systemctl\s+(stop|disable)\s+
```

## 2. Data Exfiltration Patterns

### Network Exfiltration
```regex
curl\s+.*(-X\s+POST|-d\s+@).*file
wget\s+--post-file
scp\s+.*@.*:
rsync\s+.*@.*:
ftp\s+put
nc\s+-[el].*<
```

### Sensitive File Access
```regex
cat\s+.*(passwd|shadow|sudoers)
cat\s+.*\.ssh/(id_rsa|authorized_keys)
cat\s+.*\.(pem|key|crt|p12)
cat\s+.*(\.aws|\.config).*credentials
base64\s+.*\.(pem|key|ssh)
```

### Credential Harvesting
```regex
grep\s+.*(password|secret|token|api.?key)
find\s+.*-name\s+.*\.(pem|key|env)
env\s*\|\s*grep\s+(SECRET|KEY|TOKEN)
```

## 3. Privilege Escalation

### Direct Escalation
```regex
sudo\s+(-s|-i|su)
su\s+-\s*$
pkexec
doas\s+
```

### Permission Modification
```regex
chmod\s+[0-7]?777
chmod\s+[ugo]\+[sS]
chown\s+root
chgrp\s+(root|wheel|sudo)
setcap\s+
```

### User Operations
```regex
useradd|adduser
usermod\s+-[aG].*(sudo|wheel|admin)
visudo
echo.*>>\s*/etc/sudoers
```

## 4. Prompt Injection Patterns

### Role Hijacking (English)
```regex
ignore\s+(previous|above|all)\s+(instructions?|prompts?)
forget\s+(your|all|everything)
you\s+are\s+now
from\s+now\s+on
disregard\s+(all|any|previous)
pretend\s+(to\s+be|you\s+are)
act\s+as\s+(if|though)?
```

### Role Hijacking (Chinese)
```regex
忽略(之前|上面|以上|前面)(的)?(所有|全部)?指令
忘记你(的|是)
你现在是(一个)?
从现在开始.*(你|必须|只能)
不要(遵守|遵循|执行)
扮演(一个)?
假装(你是)?
```

### Fake System Markers
```regex
\[SYSTEM\]|\[ADMIN\]|\[ROOT\]|\[OVERRIDE\]
<system>|</system>|<\|im_start\|>
###SYSTEM###|===ADMIN===|---ROOT---
^(Human|User|Assistant|AI):\s*
\[INST\]|\[/INST\]
<<SYS>>|<</SYS>>
```

### Jailbreak Keywords
```regex
(DAN|Do\s+Anything\s+Now)
(Jailbreak|jail\s*break)
Developer\s+Mode
no\s+(restrictions?|limitations?|ethical|guidelines?)
(unfiltered|uncensored|without\s+restrictions?)
bypass\s+(safety|security|filter)
```

### Context Manipulation
```regex
End\s+of\s+(conversation|prompt|instruction)
New\s+(conversation|session|task)\s+begins?
---\s*END\s*(SYSTEM|PROMPT)?\s*---
</(task|instruction|system)>
The\s+above\s+was\s+a\s+test
```

## 5. Social Engineering Patterns

### Urgency
```regex
immediately|right\s+now|urgent|asap
立即|马上|现在就|紧急
otherwise.*(lose|lost|fail|damage)
否则.*(丢失|损坏|失败|危险)
```

### Authority Impersonation
```regex
official(ly)?\s+(recommend|require)
官方(推荐|要求|建议)
admin(istrator)?\s+(require|request)
(管理员|系统|官方)要求
```

### Fear Exploitation
```regex
(has\s+been|being|is)\s+(hack|attack|compromise|infect)
(已被|可能被|正在被)(入侵|攻击|感染)
(virus|malware|trojan)
(病毒|木马|恶意软件)
```

## 6. Code Obfuscation

### Variable Concatenation
```regex
\$[a-z]\$[a-z].*\$[a-z]
\$\{[a-z]\}\$\{[a-z]\}
[a-z]=\"[a-z]+\";\s*[a-z]=\"[a-z]+\".*\$[a-z]\$[a-z]
```

### Encoded Execution
```regex
echo\s+.*\|\s*base64\s+-d\s*\|\s*(bash|sh|eval)
python\s+-c\s+.*base64.*decode.*exec
\$\(.*base64.*-d\)
eval\s*\(\s*decode
```

### Dynamic Execution
```regex
eval\s*\(
exec\s*\(
\$\(.*\)
`[^`]+`
Function\s*\(.*\)\s*\(
new\s+Function\s*\(
```

## 7. Supply Chain Risks

### Unsafe Downloads
```regex
curl\s+-[sS]?\s+https?://.*\|\s*(ba)?sh
wget\s+-[qO-]+.*\|\s*(ba)?sh
pip\s+install\s+[^=<>]+$
npm\s+install\s+[^@]+$
go\s+get\s+[^@]+$
```

### Suspicious Sources
```regex
raw\.githubusercontent\.com
pastebin\.com|paste\.ee
bit\.ly|tinyurl|t\.co
gist\.github\.com.*raw
```

## 8. Hidden Content Detection

### HTML Comment Hiding
```regex
<!--[\s\S]*?(SYSTEM|ignore|override|secret)[\s\S]*?-->
```

### Zero-Width Characters
```
\u200B  # Zero-width space
\u200C  # Zero-width non-joiner
\u200D  # Zero-width joiner
\uFEFF  # Zero-width no-break space
```

### Unicode Obfuscation
```regex
[\u0400-\u04FF]  # Cyrillic character disguise
[\uFF00-\uFFEF]  # Full-width characters
```

## Usage Notes

1. These patterns assist detection; they are not absolute standards
2. Pattern matches require contextual judgment
3. Some patterns are legitimate in specific scenarios
4. Continuously update to address new attack vectors
