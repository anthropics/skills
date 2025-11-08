# GPL Licensing Guidelines for ComfyUI Integration

## Overview

This document provides strategies for safely integrating ComfyUI in proprietary applications while maintaining GPL compliance. The key principle is **API-only separation**: your proprietary code uses HTTP to call ComfyUI without directly linking GPL libraries.

## GPL Licensing Basics

### What is GPL?

The GNU General Public License (GPL) is a "copyleft" license that:
- Requires modifications to be released under GPL
- Requires software containing GPL code to be released under GPL
- Does NOT require linking to GPL libraries via network APIs

### ComfyUI Licensing Status

**ComfyUI itself** contains GPL-licensed dependencies but the core architecture supports:
- **API-only access** - HTTP interface does not transmit GPL licensing obligations
- **Separate process** - ComfyUI can run as independent service
- **Clear separation** - Your code and ComfyUI code remain legally distinct

## Licensing Categories

### GPL-Compatible (Can Be Used)

- **MIT License** - Permissive, no copyleft restrictions
- **Apache 2.0** - Permissive with patent grant
- **BSD 2/3-Clause** - Permissive, similar to MIT
- **ISC License** - Permissive, rarely used
- **Public Domain** - No restrictions

### GPL-Incompatible (Use with Caution)

- **GPL v2** - Requires proprietary code to be released
- **GPL v3** - Stronger copyleft, incompatible with some proprietary licenses
- **AGPL** - Network copyleft (worse than GPL)
- **Proprietary** - Generally incompatible with GPL

## API-Only Separation Architecture

### Safe Architecture Pattern

```
Your Proprietary Application (Python/Node.js/Java/etc)
    ↓ (JSON over HTTPS)
ComfyUI Inference Backend (Separate Process)
    ↓ (Process boundary - legal separation)
ComfyUI Core (GPL-Licensed)
    ↓ (Direct linking)
Models & Dependencies (Various Licenses)
```

### What Makes This Safe

1. **No Direct Linking** - Your code doesn't link GPL libraries
2. **Network Boundary** - HTTP requests don't create derivative work
3. **Process Isolation** - ComfyUI runs as separate service
4. **Different Products** - Your app is distinct from ComfyUI
5. **Reverse Engineering** - User cannot extract GPL code from your app

### What Could Make This Risky

1. **Code Mixing** - Importing ComfyUI Python modules directly
2. **Dynamic Linking** - Loading ComfyUI shared libraries
3. **Distribution** - Shipping ComfyUI with your application
4. **Modifications** - Changing GPL code without releasing changes
5. **Unclear Separation** - Making it appear as single product

## Implementation Guidelines

### Safe Pattern 1: Docker Containerization

```dockerfile
# Dockerfile for ComfyUI service (separate from your app)
FROM python:3.10-slim
RUN apt-get update && apt-get install -y git
RUN git clone https://github.com/comfyanonymous/ComfyUI /opt/ComfyUI
WORKDIR /opt/ComfyUI
RUN pip install -r requirements.txt
EXPOSE 8188
CMD ["python", "main.py", "--listen", "0.0.0.0"]
```

Your app connects via HTTP - legally separate.

### Safe Pattern 2: Subprocess with HTTP API

```python
# Your application (proprietary)
import requests
import subprocess
import time

# Start ComfyUI as separate process
comfyui_process = subprocess.Popen(
    ["python", "/path/to/ComfyUI/main.py", "--listen", "0.0.0.0"],
    stdout=subprocess.PIPE
)

time.sleep(5)  # Wait for startup

# Communicate via HTTP only
response = requests.post(
    "http://localhost:8188/api/prompt",
    json={"client_id": "myapp", "prompt": workflow}
)

# No GPL contamination - just HTTP requests
```

### Safe Pattern 3: Separate Deployment

```
Production Environment:
├── Your App Container (Python/Node/Java - Your License)
└── ComfyUI Container (Separate - GPL Notice Required)
```

Document in DEPLOYMENT.md that ComfyUI runs as separate service.

## Unsafe Patterns

### Pattern 1: Direct Python Import (UNSAFE)

```python
# DON'T DO THIS - Creates derivative work
from comfyui.core import inference_engine

# Your code now contains GPL code - must be released under GPL
```

### Pattern 2: Linking Shared Libraries (UNSAFE)

```python
# DON'T DO THIS - Linking creates derivative work
import ctypes
lib = ctypes.CDLL("/path/to/comfyui_core.so")

# Creating combined binary - must be released under GPL
```

### Pattern 3: Distributing Modified ComfyUI (UNSAFE)

```bash
# DON'T DO THIS - Modifying GPL code without releasing changes
cd ComfyUI
# Modify core files
tar -czf comfyui-modified.tar.gz
# Distribute to customers
```

If you modify ComfyUI, release the modifications under GPL.

## Legal Compliance Checklist

### Before Launching

- [ ] Confirm ComfyUI runs as separate process or service
- [ ] Verify no direct Python imports from ComfyUI core
- [ ] Check all custom nodes for GPL licenses
- [ ] Audit transitive dependencies for GPL
- [ ] Document GPL components in THIRD_PARTY_NOTICES.md
- [ ] Specify in documentation that ComfyUI is separate service
- [ ] Add ComfyUI license in distributed materials

### In THIRD_PARTY_NOTICES.md

```markdown
## ComfyUI

ComfyUI is a separate inference service used by this application.

**ComfyUI Repository:** https://github.com/comfyanonymous/ComfyUI
**ComfyUI License:** GPL v3
**Usage:** Accessed via HTTP API only - not linked or distributed

**Important:** Users must install and run ComfyUI separately.
This application does NOT distribute or modify ComfyUI code.
ComfyUI's GPL license applies to ComfyUI only, not to this application.
```

### In Documentation

```markdown
## ComfyUI Backend

This application requires ComfyUI to be installed separately.

### Installation

1. Install ComfyUI from: https://github.com/comfyanonymous/ComfyUI
2. Follow ComfyUI setup instructions
3. Start ComfyUI service: `python main.py --listen 0.0.0.0`
4. Configure this application to connect to ComfyUI API

### Licensing

ComfyUI is licensed under GPL v3. This application is separate
software and does not modify or include ComfyUI source code.
See https://github.com/comfyanonymous/ComfyUI/blob/main/LICENSE
for ComfyUI's full license text.
```

## Custom Node License Audit

### Red Flags for GPL

Check GitHub repo for these warning signs:
- GPL or AGPL in LICENSE file
- "Derived from GPL project"
- "License: GPL-compatible"
- Imports GPL-licensed packages without clear separation
- Unclear license attribution

### Audit Process

```bash
# 1. Check LICENSE file
cat custom_nodes/node_name/LICENSE

# 2. Check requirements.txt for GPL packages
grep -E "gpl|agpl" custom_nodes/node_name/requirements.txt

# 3. Search code for imports of GPL packages
grep -r "import.*gpl" custom_nodes/node_name/

# 4. Check package metadata
pip show package_name | grep License
```

### Automated License Scanning

Use tools to scan dependencies:

```bash
# Install FOSSA CLI
pip install fossa-cli

# Scan ComfyUI directory
fossa analyze

# View license report
fossa report --format csv > licenses.csv
```

## License Compliance Disclaimer

**This is not legal advice.** GPL compliance is complex and fact-dependent. Consider:

1. **Consult Legal Counsel** - Engage a lawyer familiar with GPL
2. **Specific Jurisdiction** - Copyright law varies by country
3. **Your Use Case** - Different situations have different risks
4. **Custom Modifications** - If you modify ComfyUI, the analysis changes

### When to Seek Legal Help

- [ ] Modifying ComfyUI source code
- [ ] Bundling ComfyUI with your application
- [ ] Distributing modified dependencies
- [ ] Significant commercial value of integration
- [ ] Selling to enterprises requiring license compliance verification

## Best Practices Summary

### Dos

1. **Use HTTP API** - Only communicate with ComfyUI via HTTP
2. **Document Separation** - Clear documentation about architecture
3. **Separate Deployment** - Run ComfyUI as distinct service
4. **Audit Nodes** - Verify custom node licenses
5. **Monitor Updates** - Track license changes in updates
6. **Include Notices** - THIRD_PARTY_NOTICES.md with all licenses
7. **Get Legal Review** - Especially for commercial applications

### Don'ts

1. **Don't Import ComfyUI** - No `from comfyui import ...`
2. **Don't Ship Modified ComfyUI** - Release changes under GPL
3. **Don't Use GPL Nodes** - Unless clearly separated
4. **Don't Link GPL Libraries** - Avoid shared library dependencies
5. **Don't Obscure Separation** - Be transparent about architecture
6. **Don't Ignore Updates** - Monitor for license changes

## Resources

### GPL Information

- **Official GPL License:** https://www.gnu.org/licenses/gpl-3.0.en.html
- **GPL FAQ:** https://www.gnu.org/licenses/gpl-faq.html
- **GPL Compatibility:** https://www.apache.org/licenses/GPL-compatibility.html

### License Scanning Tools

- **FOSSA:** https://fossa.com (automatic scanning)
- **Black Duck:** https://blackduck.com (enterprise scanning)
- **REUSE:** https://reuse.software (license compliance)
- **pip-licenses:** https://github.com/raimon49/pip-audit (local Python)

### ComfyUI Resources

- **ComfyUI Repository:** https://github.com/comfyanonymous/ComfyUI
- **ComfyUI License:** https://github.com/comfyanonymous/ComfyUI/blob/main/LICENSE
- **ComfyUI Discussions:** https://github.com/comfyanonymous/ComfyUI/discussions

## Example Compliance Document

```markdown
# License Compliance Statement

## Application License

This application is licensed under [YOUR LICENSE - MIT/Apache/etc].

## ComfyUI Backend

This application uses ComfyUI as a separate inference backend service.
ComfyUI is licensed under GPL v3, accessible only via HTTP API.

### Installation & Usage

Users must install ComfyUI separately from:
https://github.com/comfyanonymous/ComfyUI

This application:
- Does NOT distribute ComfyUI source code
- Does NOT modify ComfyUI code
- Does NOT link against ComfyUI libraries
- Does communicate with ComfyUI via HTTP API only

### Compliance

The API-only architecture ensures that this application's source code
does not contain or derive from GPL-licensed code. ComfyUI's GPL
license applies only to ComfyUI itself, not to this application.

For full details on GPL and ComfyUI licensing, see:
https://github.com/comfyanonymous/ComfyUI/blob/main/LICENSE
```

---

**Last Updated:** 2024
**Status:** Guidance Document (Not Legal Advice)
