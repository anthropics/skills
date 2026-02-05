---
name: harmonyos-build-deploy
description: >
  Build, sign, and deploy HarmonyOS/鸿蒙 applications to real devices. Supports multi-module projects
  with dependency resolution, product variants, build modes (debug/release/test), real-time device logs,
  and APP packaging for AppGallery submission. Triggers on keywords: HarmonyOS, 鸿蒙, hvigor, hdc, HAP, HSP, AppGallery.
---

# HarmonyOS Build & Deploy

One-command build, sign, and deploy for HarmonyOS applications.

## Requirements

- Node.js >= 14
- DevEco Studio or HarmonyOS SDK
- hvigorw, hdc, ohpm (included with DevEco)
- Configured signing certificate

## Quick Start

```bash
npx harmonyos-deploy --all --launch           # Build all + install + launch
npx harmonyos-deploy --all --release --launch # Release mode
npx harmonyos-deploy --app --release          # Build .app for AppGallery
```

## CLI Reference

### Build Options
| Flag | Description |
|------|-------------|
| `-a, --all` | Build all modules (auto dependency order) |
| `-m, --module <n>` | Build specific module (default: entry) |
| `-p, --product <n>` | Product flavor (default: default) |
| `-b, --build-mode <mode>` | Build mode: debug, release, test |
| `--release` | Shorthand for `-b release` |

### Device Options
| Flag | Description |
|------|-------------|
| `-d, --device <id>` | Target device ID |
| `-l, --launch` | Launch app after install |
| `-u, --uninstall` | Uninstall before install |
| `--list-devices` | List connected devices |

### APP Packaging (AppGallery)
| Flag | Description |
|------|-------------|
| `-A, --app` | Build .app for AppGallery |
| `-o, --output <dir>` | Output directory |
| `-n, --name <name>` | Custom filename |

### Logging
| Flag | Description |
|------|-------------|
| `--log` | Show device log after deploy |
| `--log-only` | Only show log, skip build |
| `--filter <tag>` | Filter log by tag |

## Build Commands

```bash
# HAP/HSP (device install)
hvigorw assembleHap --mode module -p product={product} -p buildMode={mode} --no-daemon

# APP (AppGallery, always debuggable=false)
hvigorw --mode project -p product={product} -p buildMode={mode} -p debuggable=false assembleApp --no-daemon
```

## Output Paths

```
# HAP/HSP
{module}/build/{product}/outputs/default/*.hap

# APP
build/outputs/{product}/*.app
```

## Examples

```bash
# Full workflow
npx harmonyos-deploy --all --release --launch --log

# Different products
npx harmonyos-deploy --all -p production --release
npx harmonyos-deploy --all -p staging --debug

# APP for store submission
npx harmonyos-deploy --app -p production --release -o ./dist -n MyApp.app

# Debug with logs
npx harmonyos-deploy --log-only --filter MyTag
```

## Troubleshooting

- **hdc not found**: Add SDK toolchains to PATH
- **Signing error**: Configure signing in build-profile.json5
- **Install fails**: Use `--uninstall` flag to clean install

## Links

- npm: https://www.npmjs.com/package/harmonyos-deploy
- GitHub: https://github.com/supermanaaaa/harmonyos-build-deploy
