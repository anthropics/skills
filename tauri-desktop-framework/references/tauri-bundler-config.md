# Tauri Bundler Configuration Reference

Complete guide for configuring Tauri v2.x bundlers for Windows (MSI/NSIS), macOS (DMG/App Bundle), and Linux (AppImage/DEB/RPM) distributions.

---

## Table of Contents

1. [General Bundle Configuration](#general-bundle-configuration)
2. [Windows Configuration](#windows-configuration)
3. [macOS Configuration](#macos-configuration)
4. [Linux Configuration](#linux-configuration)
5. [Code Signing](#code-signing)
6. [Updater Configuration](#updater-configuration)
7. [External Binaries](#external-binaries)

---

## General Bundle Configuration

Located in `src-tauri/tauri.conf.json` under the `bundle` key.

### Basic Configuration

```json
{
  "bundle": {
    "active": true,
    "targets": "all",
    "identifier": "com.example.myapp",
    "publisher": "My Company",
    "icon": [
      "icons/32x32.png",
      "icons/128x128.png",
      "icons/128x128@2x.png",
      "icons/icon.icns",
      "icons/icon.ico"
    ],
    "resources": [],
    "externalBin": [],
    "copyright": "Copyright © 2025 My Company",
    "category": "DeveloperTool",
    "shortDescription": "A brief description",
    "longDescription": "A detailed description of the application"
  }
}
```

### Target Platforms

**All platforms:**
```json
{
  "bundle": {
    "targets": "all"
  }
}
```

**Specific targets:**
```json
{
  "bundle": {
    "targets": ["msi", "nsis", "deb", "appimage", "dmg"]
  }
}
```

### Application Categories

**macOS categories:**
- `Business`
- `DeveloperTool`
- `Education`
- `Entertainment`
- `Finance`
- `Game`
- `ActionGame`, `AdventureGame`, `ArcadeGame`, `BoardGame`, `CardGame`
- `CasinoGame`, `DiceGame`, `EducationalGame`, `FamilyGame`, `KidsGame`
- `MusicGame`, `PuzzleGame`, `RacingGame`, `RolePlayingGame`, `SimulationGame`
- `SportsGame`, `StrategyGame`, `TriviaGame`, `WordGame`
- `Graphics`
- `Design`
- `Lifestyle`
- `Medical`
- `Music`
- `News`
- `Photography`
- `Productivity`
- `Reference`
- `SocialNetworking`
- `Sports`
- `Travel`
- `Utility`
- `Video`
- `Weather`

**Linux categories (freedesktop.org):**
- `AudioVideo`, `Audio`, `Video`
- `Development`
- `Education`
- `Game`
- `Graphics`
- `Network`
- `Office`
- `Science`
- `Settings`
- `System`
- `Utility`

---

## Windows Configuration

### MSI Installer

```json
{
  "bundle": {
    "windows": {
      "certificateThumbprint": null,
      "digestAlgorithm": "sha256",
      "timestampUrl": "http://timestamp.digicert.com",
      "tsp": false,
      "wix": {
        "language": "en-US",
        "template": null,
        "fragmentPaths": [],
        "componentGroupRefs": [],
        "componentRefs": [],
        "featureGroupRefs": [],
        "featureRefs": [],
        "mergeRefs": [],
        "skipWebviewInstall": false,
        "license": null,
        "enableElevatedUpdateTask": false,
        "bannerPath": null,
        "dialogImagePath": null
      },
      "nsis": {
        "license": null,
        "headerImage": null,
        "sidebarImage": null,
        "installerIcon": null,
        "installMode": "currentUser",
        "languages": ["English"],
        "displayLanguageSelector": false
      }
    }
  }
}
```

### MSI-Specific Configuration

**Custom WiX template:**
```json
{
  "bundle": {
    "windows": {
      "wix": {
        "template": "wix/main.wxs",
        "language": "en-US"
      }
    }
  }
}
```

**License agreement:**
```json
{
  "bundle": {
    "windows": {
      "wix": {
        "license": "LICENSE.rtf"
      }
    }
  }
}
```

**Custom installer UI:**
```json
{
  "bundle": {
    "windows": {
      "wix": {
        "bannerPath": "assets/banner.bmp",
        "dialogImagePath": "assets/dialog.bmp"
      }
    }
  }
}
```

### NSIS Installer

**NSIS configuration:**
```json
{
  "bundle": {
    "windows": {
      "nsis": {
        "license": "LICENSE.txt",
        "headerImage": "assets/nsis-header.bmp",
        "sidebarImage": "assets/nsis-sidebar.bmp",
        "installerIcon": "assets/installer.ico",
        "installMode": "perMachine",
        "languages": ["English", "French", "German"],
        "displayLanguageSelector": true,
        "template": "nsis/installer.nsi"
      }
    }
  }
}
```

**Install modes:**
- `"currentUser"` - Install for current user only (no admin required)
- `"perMachine"` - Install for all users (requires admin)
- `"both"` - Allow user to choose

---

## macOS Configuration

### DMG and App Bundle

```json
{
  "bundle": {
    "macOS": {
      "frameworks": [],
      "minimumSystemVersion": "10.13",
      "exceptionDomain": "",
      "signingIdentity": null,
      "providerShortName": null,
      "entitlements": null,
      "hardenedRuntime": true
    }
  }
}
```

### Minimum System Version

```json
{
  "bundle": {
    "macOS": {
      "minimumSystemVersion": "11.0"
    }
  }
}
```

Versions:
- `"10.13"` - High Sierra
- `"10.14"` - Mojave
- `"10.15"` - Catalina
- `"11.0"` - Big Sur
- `"12.0"` - Monterey
- `"13.0"` - Ventura
- `"14.0"` - Sonoma

### Code Signing

```json
{
  "bundle": {
    "macOS": {
      "signingIdentity": "Developer ID Application: Your Name (TEAM_ID)",
      "hardenedRuntime": true,
      "entitlements": "entitlements.plist"
    }
  }
}
```

**Entitlements file (entitlements.plist):**
```xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>com.apple.security.cs.allow-jit</key>
    <true/>
    <key>com.apple.security.cs.allow-unsigned-executable-memory</key>
    <true/>
    <key>com.apple.security.cs.disable-library-validation</key>
    <true/>
    <key>com.apple.security.files.user-selected.read-write</key>
    <true/>
    <key>com.apple.security.network.client</key>
    <true/>
</dict>
</plist>
```

### Notarization

Set environment variables before building:

```bash
export APPLE_ID="your@email.com"
export APPLE_PASSWORD="app-specific-password"
export APPLE_TEAM_ID="TEAM_ID"
export APPLE_SIGNING_IDENTITY="Developer ID Application: Your Name (TEAM_ID)"

npm run tauri build
```

**App-specific password:**
1. Go to appleid.apple.com
2. Sign in with your Apple ID
3. Security → App-Specific Passwords → Generate

---

## Linux Configuration

### AppImage Configuration

```json
{
  "bundle": {
    "linux": {
      "appimage": {
        "bundleMediaFramework": false,
        "files": {}
      }
    }
  }
}
```

### DEB Package

```json
{
  "bundle": {
    "linux": {
      "deb": {
        "depends": [],
        "files": {},
        "desktopTemplate": null
      }
    }
  }
}
```

**Dependencies example:**
```json
{
  "bundle": {
    "linux": {
      "deb": {
        "depends": [
          "libwebkit2gtk-4.0-37",
          "libssl3",
          "libgtk-3-0"
        ]
      }
    }
  }
}
```

### RPM Package

```json
{
  "bundle": {
    "linux": {
      "rpm": {
        "depends": [],
        "files": {},
        "desktopTemplate": null,
        "release": "1"
      }
    }
  }
}
```

**Dependencies example:**
```json
{
  "bundle": {
    "linux": {
      "rpm": {
        "depends": [
          "webkit2gtk4.0",
          "openssl",
          "gtk3"
        ]
      }
    }
  }
}
```

### Desktop Entry

**Custom desktop template:**
```desktop
[Desktop Entry]
Version=1.0
Type=Application
Name={{app_name}}
Comment={{short_description}}
Exec={{app_executable}}
Icon={{app_icon}}
Terminal=false
Categories={{categories}}
MimeType=application/x-myapp;
```

Usage:
```json
{
  "bundle": {
    "linux": {
      "deb": {
        "desktopTemplate": "desktop-template.desktop"
      }
    }
  }
}
```

---

## Code Signing

### Windows Code Signing

**Using certificate thumbprint:**
```json
{
  "bundle": {
    "windows": {
      "certificateThumbprint": "ABC123...",
      "digestAlgorithm": "sha256",
      "timestampUrl": "http://timestamp.digicert.com"
    }
  }
}
```

**Using PFX file (via environment variables):**
```bash
export TAURI_PRIVATE_KEY="path/to/certificate.pfx"
export TAURI_KEY_PASSWORD="certificate_password"

npm run tauri build
```

**Timestamp servers:**
- DigiCert: `http://timestamp.digicert.com`
- Comodo: `http://timestamp.comodoca.com`
- GlobalSign: `http://timestamp.globalsign.com`

### macOS Code Signing

**Via environment variables:**
```bash
export APPLE_CERTIFICATE="Developer ID Application: Your Name (TEAM_ID)"
export APPLE_CERTIFICATE_PASSWORD="cert_password"
export APPLE_SIGNING_IDENTITY="Developer ID Application: Your Name (TEAM_ID)"

npm run tauri build
```

**Hardened Runtime:**
```json
{
  "bundle": {
    "macOS": {
      "hardenedRuntime": true,
      "entitlements": "entitlements.plist"
    }
  }
}
```

---

## Updater Configuration

### Basic Updater

```json
{
  "updater": {
    "active": true,
    "endpoints": [
      "https://releases.myapp.com/{{target}}/{{current_version}}"
    ],
    "dialog": true,
    "pubkey": "YOUR_PUBLIC_KEY_HERE"
  }
}
```

### Updater JSON Format

The update server should return JSON in this format:

```json
{
  "version": "1.2.0",
  "date": "2025-11-08T12:00:00Z",
  "platforms": {
    "darwin-x86_64": {
      "signature": "BASE64_SIGNATURE",
      "url": "https://releases.myapp.com/myapp-1.2.0-x64.app.tar.gz"
    },
    "darwin-aarch64": {
      "signature": "BASE64_SIGNATURE",
      "url": "https://releases.myapp.com/myapp-1.2.0-arm64.app.tar.gz"
    },
    "linux-x86_64": {
      "signature": "BASE64_SIGNATURE",
      "url": "https://releases.myapp.com/myapp_1.2.0_amd64.AppImage.tar.gz"
    },
    "windows-x86_64": {
      "signature": "BASE64_SIGNATURE",
      "url": "https://releases.myapp.com/myapp-1.2.0-x64.msi.zip"
    }
  }
}
```

### Generate Updater Keys

```bash
# Generate public/private key pair
npm run tauri signer generate -- -w ~/.tauri/myapp.key

# This creates:
# - Private key: ~/.tauri/myapp.key
# - Public key: printed to console (add to tauri.conf.json)
```

### Sign Update

```bash
# Sign the update file
npm run tauri signer sign ~/.tauri/myapp.key /path/to/update.zip
```

---

## External Binaries

### Sidecar Binaries

For bundling Python backends, Node.js scripts, or other executables:

```json
{
  "bundle": {
    "externalBin": [
      "binaries/python-backend"
    ]
  }
}
```

**Platform-specific binaries:**
```json
{
  "bundle": {
    "externalBin": [
      "binaries/backend-x86_64-pc-windows-msvc",
      "binaries/backend-x86_64-apple-darwin",
      "binaries/backend-aarch64-apple-darwin",
      "binaries/backend-x86_64-unknown-linux-gnu"
    ]
  }
}
```

**Executing sidecar:**
```rust
use tauri::api::process::Command;

#[tauri::command]
async fn start_backend() -> Result<(), String> {
    let (mut rx, _child) = Command::new_sidecar("python-backend")
        .map_err(|e| e.to_string())?
        .spawn()
        .map_err(|e| e.to_string())?;

    Ok(())
}
```

### Large Resource Files

For model files, datasets (can be 7-20GB for AI apps):

```json
{
  "bundle": {
    "resources": [
      "models/*.gguf",
      "models/*.safetensors",
      "datasets/**/*"
    ]
  }
}
```

**Accessing resources:**
```rust
use tauri::Manager;

#[tauri::command]
fn get_model_path(app: tauri::AppHandle) -> Result<String, String> {
    let resource_path = app.path_resolver()
        .resolve_resource("models/flux-kontext.gguf")
        .ok_or("Failed to resolve resource")?;

    Ok(resource_path.to_string_lossy().to_string())
}
```

---

## Build Scripts

### Cross-Platform Build

**Package.json scripts:**
```json
{
  "scripts": {
    "tauri:build": "tauri build",
    "tauri:build:windows": "tauri build --target x86_64-pc-windows-msvc",
    "tauri:build:macos:intel": "tauri build --target x86_64-apple-darwin",
    "tauri:build:macos:arm": "tauri build --target aarch64-apple-darwin",
    "tauri:build:macos:universal": "tauri build --target universal-apple-darwin",
    "tauri:build:linux": "tauri build --target x86_64-unknown-linux-gnu"
  }
}
```

### GitHub Actions

**Example workflow:**
```yaml
name: Release
on:
  push:
    tags:
      - 'v*'

jobs:
  release:
    strategy:
      fail-fast: false
      matrix:
        platform: [macos-latest, ubuntu-20.04, windows-latest]

    runs-on: ${{ matrix.platform }}
    steps:
      - uses: actions/checkout@v3

      - name: Setup Node
        uses: actions/setup-node@v3
        with:
          node-version: 18

      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: stable

      - name: Install dependencies (ubuntu only)
        if: matrix.platform == 'ubuntu-20.04'
        run: |
          sudo apt-get update
          sudo apt-get install -y libgtk-3-dev libwebkit2gtk-4.0-dev librsvg2-dev

      - name: Install app dependencies
        run: npm install

      - uses: tauri-apps/tauri-action@v0
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
          APPLE_CERTIFICATE: ${{ secrets.APPLE_CERTIFICATE }}
          APPLE_CERTIFICATE_PASSWORD: ${{ secrets.APPLE_CERTIFICATE_PASSWORD }}
          APPLE_SIGNING_IDENTITY: ${{ secrets.APPLE_SIGNING_IDENTITY }}
          APPLE_ID: ${{ secrets.APPLE_ID }}
          APPLE_PASSWORD: ${{ secrets.APPLE_PASSWORD }}
          TAURI_PRIVATE_KEY: ${{ secrets.TAURI_PRIVATE_KEY }}
          TAURI_KEY_PASSWORD: ${{ secrets.TAURI_KEY_PASSWORD }}
        with:
          tagName: ${{ github.ref_name }}
          releaseName: 'App v__VERSION__'
          releaseBody: 'See the assets to download and install this version.'
          releaseDraft: true
          prerelease: false
```

---

## Troubleshooting

### Windows

**Issue:** "SmartScreen warning"
**Solution:** Sign your application with an EV code signing certificate

**Issue:** Antivirus false positives
**Solution:** Submit false positive reports to antivirus vendors

### macOS

**Issue:** "App is damaged and can't be opened"
**Solution:** Ensure proper code signing and notarization

**Issue:** Gatekeeper blocks app
**Solution:** Notarize the app with Apple

**Command to remove quarantine (testing only):**
```bash
xattr -cr /path/to/MyApp.app
```

### Linux

**Issue:** Missing dependencies
**Solution:** Add dependencies to DEB/RPM configuration

**Issue:** AppImage doesn't run
**Solution:** Ensure executable permissions: `chmod +x myapp.AppImage`

---

## References

- Tauri Bundler Docs: https://v2.tauri.app/distribute/
- WiX Toolset: https://wixtoolset.org/
- Apple Notarization: https://developer.apple.com/documentation/security/notarizing_macos_software_before_distribution
- FreeDesktop Standards: https://specifications.freedesktop.org/
