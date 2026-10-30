---
name: vastai
description: Vast.ai CLI to manage GPU instances, volumes, serverless endpoints, and billing.
allowed-tools: Bash(vastai:*)
compatibility: Linux, macOS
metadata:
  author: vast-ai
---

# vastai

Manage GPU instances, templates, volumes, serverless endpoints, SSH keys, and billing on Vast.ai.

> Command is `vastai` (lowercase). Always use `--raw` for machine-readable JSON output.

## Install

```bash
# PyPI (recommended)
pip install vastai

# Latest from GitHub
wget https://raw.githubusercontent.com/vast-ai/vast-python/master/vast.py -O vast
chmod +x vast
```

## Quick start

```bash
vastai set api-key <YOUR_API_KEY>                   # Authenticate (one-time); Create API Key in account at https://console.vast.ai/cli
vastai show user                                    # Verify auth + check balance
vastai create ssh-key ~/.ssh/id_ed25519.pub         # Register SSH key (do BEFORE create)
vastai search offers 'gpu_name=RTX_4090 num_gpus=1 verified=true direct_port_count>=1 rentable=true' -o 'dlperf_usd-'
# Note the offer ID from the output
vastai create instance <OFFER_ID> --image pytorch/pytorch:@vastai-automatic-tag --disk 20 --ssh --direct
# Automatically grab appropriate image tag; Response:  {"success": true, "new_contract": <INSTANCE_ID>}
vastai show instance <INSTANCE_ID>                  # Poll until actual_status == "running" (see Instance status values below)
vastai ssh-url <INSTANCE_ID>                        # Get SSH connection string
vastai copy local:./data/ <INSTANCE_ID>:/workspace/ # Upload files
vastai destroy instance <INSTANCE_ID> -y             # Clean up (stops all billing; -y skips confirmation)
```

API key: https://console.vast.ai/cli

## Global flags

Available on every command:

```
--api-key KEY    Override stored API key
--raw            Output machine-readable JSON (agents should always use this)
--full           Print full results (don't page with less)
--explain        Show underlying API calls (useful for debugging)
--curl           Show equivalent curl command
--no-color       Disable colored output
--url URL        Override server REST API URL
--retry RETRY    Set retry limit for API calls
--version        Show CLI version
```

## Query syntax

Search commands accept filter expressions. Operators: `=`, `!=`, `>`, `>=`, `<`, `<=`, `in`, `notin`.

```bash
# Examples
'gpu_name=RTX_4090 num_gpus=1'           # Exact match + numeric
'gpu_ram>=48 reliability>0.95'           # Greater-than filters
'geolocation=EU dph_total<=2.0'          # Region + price cap
```

Common filter fields: `num_gpus`, `gpu_name`, `gpu_ram`, `cpu_ram`, `disk_space`, `reliability`, `compute_cap`, `inet_up`, `inet_down`, `dph_total`, `geolocation`, `direct_port_count`, `verified`, `rentable`

Common sort fields: `score` (default — overall value), `dlperf_usd` (DL perf per dollar), `dph_total` (price), `num_gpus`, `reliability`

## Commands

### Instances

```bash
vastai show instances                                    # List all your instances
vastai show instances-v1                                 # Paginated instances with full filter/sort/cols support
vastai show instances-v1 --status running loading        # Filter by status
vastai show instances-v1 --gpu-name 'RTX 4090'           # Filter by GPU
vastai show instances-v1 --label training                # Filter by label
vastai show instances-v1 --order-by start_date desc      # Sort by column
vastai show instances-v1 --cols id,status,gpu,dph        # Custom columns
vastai show instance <id>                                # Poll single instance (use for status checks)
vastai create instance <offer-id> --image pytorch/pytorch:2.4.0-cuda12.4-cudnn9-runtime --disk 20 --ssh --direct
# Response includes "new_contract": <id> — that is your instance ID
vastai launch instance --gpu-name RTX_4090 --num-gpus 1 --image pytorch/pytorch
vastai start instance <id>                               # Start stopped instance
vastai stop instance <id>                                # Stop (preserves disk, no GPU charges)
vastai reboot instance <id>                              # Stop + start
vastai destroy instance <id> -y                          # Delete permanently (irreversible; -y required for non-interactive use)
vastai destroy instances <id1> <id2> -y                  # Batch delete (-y skips confirmation prompt)
vastai label instance <id> --label "training-run-1"      # Tag instance
vastai update instance <id>                              # Recreate from updated template
vastai prepay instance <id>                              # Deposit credits into reserved instance
vastai recycle instance <id>                             # Destroy + recreate
```

**Recommended Vast.ai images** (use `@vastai-automatic-tag` to get the right tag for the machine automatically; browse pre-configured models at https://vast.ai/model-library):

<!-- Note: @vastai-automatic-tag is resolved server-side — CLI passes it unchanged -->

```bash
vastai/base-image:@vastai-automatic-tag          # Minimal Ubuntu base
vastai/pytorch:@vastai-automatic-tag             # PyTorch + CUDA
vastai/linux-desktop:@vastai-automatic-tag       # Linux desktop (VNC/RDP)

# vLLM — set model via env vars with huggingface model example
vastai create instance <id> --image vastai/vllm:@vastai-automatic-tag --disk 40 --ssh --direct \
  --env '-e MODEL_NAME=Qwen/Qwen2.5-3B-Instruct -e HF_TOKEN=hf_xxx'

# ComfyUI — set model checkpoint via env vars with huggingface model example
vastai create instance <id> --image vastai/comfy:@vastai-automatic-tag --disk 40 --ssh --direct \
  --env '-e CHECKPOINT_MODEL=black-forest-labs/FLUX.1-schnell -e HF_TOKEN=hf_xxx'
```

**create instance flags:**
- `--image IMAGE` — Docker image
- `--disk DISK` — Local disk in GB
- `--ssh` / `--jupyter` — Connection type
- `--direct` — Faster direct connections
- `--label LABEL` — Instance label
- `--env ENV` — Env vars and port mappings, e.g. `'-e TZ=UTC -p 8080:8080'`
- `--onstart FILE` — Path to a startup script file
- `--onstart-cmd CMD` — Startup script as inline string (for longer scripts use `--onstart` or gzip+base64 encode)
- `--bid_price PRICE` — Interruptible (spot) pricing in $/hr
- `--template_hash HASH` — Create from template
- `--create-volume ID` — Attach new volume
- `--link-volume ID` — Attach existing volume
- `--cancel-unavail` — Fail if no machine available (vs. create stopped)

**Instance status values:**

| `actual_status` | Meaning |
|-----------------|---------|
| `null` | Provisioning |
| `created` | Instance created, not yet provisioned |
| `loading` | Image downloading / container starting |
| `running` | Active — GPU charges apply |
| `stopped` | Halted — disk charges only |
| `frozen` | Paused with memory — GPU charges apply |
| `exited` | Container process exited unexpectedly |
| `rebooting` | Restarting (transient) |
| `unknown` | No recent heartbeat from host |
| `offline` | Host disconnected from Vast servers |

> **Poll loop warning:** If `actual_status` becomes `exited`, `unknown`, or `offline` it will never reach `running`. Always add a timeout and error branch — otherwise your script loops forever while disk charges accrue. Destroy and retry with a different offer.

> **Charges:** Storage charges begin at creation. GPU charges begin when status reaches `running`.

### Search

```bash
vastai search offers                                     # Default: verified, on-demand, sorted by score
vastai search offers 'gpu_name=RTX_4090 num_gpus=1 verified=true direct_port_count>=1' -o 'dlperf_usd-'
vastai search offers 'num_gpus>=4 reliability>0.99' -o 'num_gpus-'
vastai search offers --type bid                          # Interruptible (spot) pricing
vastai search offers --type reserved                     # Reserved pricing
vastai search offers -n 'gpu_name=H100_SXM'             # No default filters
vastai search volumes                                    # Search volume offers
vastai search templates "pytorch"                        # Search templates
vastai search benchmarks                                 # Search benchmarks
vastai search invoices                                   # Search invoice history
```

**search offers flags:** `--type on-demand|reserved|bid`, `--order/-o FIELD[-]`, `--limit`, `--storage GB`, `--no-default/-n`

### SSH & File Transfer

```bash
vastai ssh-url <id>                                      # Get ssh:// connection URL
vastai scp-url <id>                                      # Get scp:// URL
vastai attach ssh <id> "ssh-ed25519 AAAA..."             # Attach SSH key to instance
vastai detach ssh <id> <ssh_key_id>                      # Remove SSH key (ssh_key_id from show ssh-keys)
vastai show ssh-keys                                     # List account SSH keys
vastai create ssh-key ~/.ssh/id_ed25519.pub              # Add SSH key from file (do BEFORE create instance)
vastai create ssh-key                                    # Generate new key if you don't have one
vastai create ssh-key "ssh-ed25519 AAAA..."              # Add SSH key inline
vastai delete ssh-key <id>                               # Remove SSH key from account
vastai update ssh-key <id> "ssh-ed25519 AAAA..."         # Update SSH key value
```

**Note:** `ssh-url` returns a connection string — it does not open an interactive session. Use `$(vastai ssh-url <id>)` to extract the URL, or parse `--raw` JSON output.

### File Copy

```bash
vastai copy <src> <dst>                                  # Copy between instance and local
vastai copy local:./data/ <id>:/workspace/data/          # Local → instance (preferred format)
vastai copy <id>:/workspace/results/ local:./results/    # Instance → local
vastai copy <id-a>:/workspace/ <id-b>:/workspace/        # Instance → instance
# Legacy format also works: vastai copy 12345:./data ./local-data
vastai cloud copy --src ./data --dst s3://bucket/path \
  --instance 12345 --connection <conn-id> \
  --transfer "Instance To Cloud"                         # To cloud storage (add connection in UI on settings page)
vastai cancel copy <dst-id>                              # Cancel in-progress copy
```

**cloud copy flags:** `--src`, `--dst`, `--instance`, `--connection`, `--transfer`

### Logs & Exec

```bash
vastai logs <id>                                         # Container logs (last 1000 lines)
vastai logs <id> --tail 100                              # Last 100 lines
vastai logs <id> --filter "error"                        # Grep filter
vastai execute <id> "nvidia-smi"                         # Run command on instance
vastai execute <id> "ls /workspace" --schedule DAILY     # Scheduled execution
```

### Volumes

```bash
vastai search volumes                                    # Search available volume offers
vastai show volumes                                      # List your volumes
vastai create volume <offer_id> [-s SIZE] [-n NAME]      # Create volume (offer_id from search volumes)
vastai clone volume <source_id> <dest_id> [-s SIZE]      # Clone volume (dest_id from search volumes)
vastai delete volume <id>                                # Delete volume
vastai create network-volume ...                         # Create network volume
vastai list network-volume                               # List network volumes
vastai take snapshot <instance_id> --repo REPO --docker_login_user USER --docker_login_pass PASS  # Snapshot instance to volume
```

### Serverless & Deployments

```bash
vastai show endpoints                                    # List endpoint groups
vastai create endpoint --name "my-ep" ...                # Create endpoint
vastai update endpoint <id> ...                          # Update endpoint
vastai delete endpoint <id>                              # Delete endpoint
vastai get endpt-logs <id>                               # Endpoint logs

vastai show workergroups                                 # List worker groups
vastai create workergroup --name "wg" ...                # Create worker group
vastai update workergroup <id> ...                       # Update worker group
vastai update workers <id>                               # Rolling update of workers
vastai delete workergroup <id>                           # Delete worker group
vastai get wrkgrp-logs <id>                              # Worker group logs

vastai show deployments                                  # List deployments
vastai show deployment <id>                              # Deployment details
vastai show deployment-versions <id>                     # Version history
vastai delete deployment <id>                            # Delete deployment

vastai show scheduled-jobs                               # List scheduled jobs
vastai delete scheduled-job <id>                         # Delete scheduled job
```

### Templates

```bash
vastai search templates "pytorch"                        # Search templates
vastai create template --name "x" --image "img"          # Create template
vastai update template <id> ...                          # Update template
vastai delete template <id>                              # Delete template
```

### Account & API Keys

```bash
vastai set api-key <key>                                 # Save API key locally
vastai show api-key <id>                                 # Show a specific key
vastai show api-keys                                     # List all your API keys
vastai create api-key --name "ci" --permissions '{...}'  # Create restricted key
vastai delete api-key <id>                               # Delete key
vastai reset api-key                                     # Reset main key (get new from console)
vastai show user                                         # Account info, credit balance
vastai show audit-logs                                   # Account action history
vastai show connections                                  # Cloud storage connections
vastai show ipaddrs                                      # IP address history
```

### Billing

```bash
vastai show invoices-v1                                  # Charges/invoices (paginated)
vastai show invoices-v1 --charges                        # Charges only
vastai show invoices-v1 --invoices                       # Invoices only
vastai show invoices-v1 --start-date 2026-01-01 --end-date 2026-02-01
vastai show invoices-v1 --limit 50 --latest-first
vastai show deposit <id>                                 # Reserved instance deposit info
```

### Teams

```bash
vastai create team --name "myteam"                       # Create team
vastai show members                                      # List team members
vastai invite member --email user@example.com            # Invite member
vastai remove member <id>                                # Remove member
vastai create team-role --name "viewer" ...              # Create role
vastai show team-role <id>                               # Role details
vastai show team-roles                                   # List roles
vastai update team-role <id> ...                         # Update role
vastai remove team-role <id>                             # Remove role
vastai destroy team                                      # Delete team
```

### Environment Variables

```bash
vastai show env-vars                                     # List user env vars
vastai create env-var KEY val                             # Create env var
vastai update env-var KEY newval                          # Update env var
vastai delete env-var KEY                                 # Delete env var
```

### Machine Management (hosts)

```bash
vastai show machines                                     # List your machines
vastai list machine <id>                                 # List/unlist machine on marketplace
vastai show machine <id>                                 # Machine details
vastai cleanup machine <id>                              # Clean up machine state
vastai schedule maint <id> ...                           # Schedule maintenance window
vastai cancel maint <id>                                 # Cancel scheduled maintenance
vastai show maints                                       # List maintenance windows
vastai unlist machine <id>                               # Remove from marketplace
```

## Common errors

| Error | Cause | Fix |
|-------|-------|-----|
| `401 Unauthorized` | Invalid or expired API key | `vastai set api-key <new-key>` |
| `Insufficient credits` | Account balance too low | Add credits at https://cloud.vast.ai/billing/ |
| `No offers found` | Filters too restrictive | Relax filters, try `--no-default/-n` |
| `Permission denied` | SSH key not attached | `vastai create ssh-key` before `create instance` |
| `Connection refused` | Instance not yet running | Poll `show instance <id>` until `actual_status == "running"` |
| Hangs on `destroy instance` | Confirmation prompt waiting for input | Add `-y` flag: `vastai destroy instance <id> -y` |

## URLs

### Console

```
https://console.vast.ai/instances/   # Your instances
https://console.vast.ai/create/      # Search GPU offers
https://console.vast.ai/cli          # Create and manage API keys
https://cloud.vast.ai/billing/       # Billing
```

### API

```
https://console.vast.ai/api/v0/instances/      # Instances endpoint
https://console.vast.ai/api/v0/asks/           # Offers search
```

### Instance Ports

Access a port exposed on your instance:

```
ssh://root@<ssh_host>:<ssh_port>               # SSH (from vastai ssh-url)
```

Direct connections (when `--direct` used at creation): `<direct_port_end>` field in instance JSON.

## Documentation

Fetch the complete documentation index at: https://docs.vast.ai/llms.txt
