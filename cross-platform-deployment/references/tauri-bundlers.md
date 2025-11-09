# Tauri Bundler Configuration Guide

Complete Tauri bundler configurations for Windows, macOS, and Linux platforms.

## Windows Bundlers

### MSI (Windows Installer)

The MSI bundler creates a professional Windows installer using WiX Toolset.

**tauri.conf.json configuration:**

```json
{
  "build": {
    "windows": ["wix"]
  }
}
```

**Advanced MSI Configuration:**

```json
{
  "build": {
    "windows": ["wix"],
    "windowsConfig": {
      "wixVersion": "4.0",
      "certificatePath": "/path/to/certificate.pfx",
      "certificatePassword": "password",
      "signingIdentity": null,
      "title": "AI Miniature Repainting",
      "iconPath": "src/assets/icon.ico",
      "banner": null,
      "dialogImageX": 0,
      "dialogImageY": 0,
      "installerLanguages": ["en-US"],
      "skipWebviewInstall": false
    }
  }
}
```

**WiX Template (product.wxs):**

```xml
<?xml version="1.0" encoding="utf-8"?>
<Wix xmlns="http://schemas.microsoft.com/wix/2006/wi">
  <Product
    Id="*"
    Name="AI Miniature Repainting"
    Language="1033"
    Version="1.0.0.0"
    Manufacturer="Your Company"
    UpgradeCode="PUT-YOUR-GUID-HERE">

    <Package
      InstallerVersion="500"
      Compressed="yes"
      InstallScope="perMachine"
      Description="AI-powered desktop application for miniature repainting"
      Manufacturer="Your Company" />

    <Media Id="1" Cabinet="app.cab" EmbedCab="yes" DiskPrompt="Installation Media"/>

    <Feature Id="ProductFeature" Title="AI Miniature Repainting" Level="1">
      <ComponentRef Id="InstallDir"/>
    </Feature>

    <Directory Id="TARGETDIR" Name="SourceDir">
      <Directory Id="ProgramFilesFolder">
        <Directory Id="INSTALLFOLDER" Name="AIRepaint"/>
      </Directory>
    </Directory>

    <DirectoryRef Id="INSTALLFOLDER">
      <Component Id="InstallDir" Guid="PUT-YOUR-GUID-HERE">
        <File Id="MainExe" Name="app.exe" Source="path/to/app.exe" KeyPath="yes"/>
      </Component>
    </DirectoryRef>

  </Product>
</Wix>
```

### NSIS Bundler

For simpler, standalone installers without registry integration.

```json
{
  "build": {
    "windows": ["nsis"],
    "nsis": {
      "installerIcon": "src/assets/icon.ico",
      "installerHeader": "src/assets/banner.bmp",
      "installerHeaderIcon": "src/assets/icon.ico",
      "headerImage": "src/assets/header.bmp",
      "sidebarImage": "src/assets/sidebar.bmp",
      "uninstallerSidebarImage": "src/assets/sidebar.bmp",
      "allowToChangeInstallationDirectory": true,
      "displayLanguageSelector": false,
      "installer": "NsisInstaller"
    }
  }
}
```

## macOS Bundlers

### DMG (Disk Image)

Creates a professional macOS disk image installer with code signing support.

**tauri.conf.json:**

```json
{
  "build": {
    "macos": ["dmg"],
    "macosConfig": {
      "minimumSystemVersion": "10.13",
      "signingIdentity": "Apple Development",
      "provisioningProfile": null,
      "certificatePath": null,
      "certificatePassword": null,
      "hardening": {
        "files": {
          "all": ["read"],
          "execute": ["read", "execute"],
          "write": []
        },
        "disableMinVersionCheck": false
      }
    }
  }
}
```

**DMG Configuration (dmg-config.json):**

```json
{
  "window": {
    "x": 0,
    "y": 0,
    "width": 540,
    "height": 380
  },
  "contents": [
    {
      "x": 440,
      "y": 180,
      "type": "link",
      "path": "/Applications"
    },
    {
      "x": 100,
      "y": 180,
      "type": "file",
      "path": "path/to/AI Miniature Repainting.app"
    }
  ],
  "background": "path/to/background.png",
  "icon": "path/to/icon.icns",
  "format": "UDBZ",
  "iconSize": 128,
  "labelSize": 12,
  "textSize": 12
}
```

**Entitlements (entitlements.plist):**

```xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>com.apple.security.app-sandbox</key>
  <true/>
  <key>com.apple.security.cs.allow-jit</key>
  <true/>
  <key>com.apple.security.cs.allow-unsigned-executable-memory</key>
  <true/>
  <key>com.apple.security.files.user-selected.read-write</key>
  <true/>
  <key>com.apple.security.device.camera</key>
  <true/>
  <key>com.apple.security.device.usb</key>
  <true/>
  <key>com.apple.security.network.client</key>
  <true/>
  <key>com.apple.security.network.server</key>
  <true/>
</dict>
</plist>
```

## Linux Bundlers

### AppImage

Universal Linux package that works across most distributions.

```json
{
  "build": {
    "linux": ["appimage"],
    "linuxConfig": {
      "category": "Utility",
      "versionNumber": null,
      "unpacked": false,
      "appimage": {
        "files": {
          "../../target/release/libcuda.so": "/lib/",
          "../../target/release/libcudnn.so": "/lib/"
        },
        "bundle": ["libgtk-3", "libssl"]
      }
    }
  }
}
```

**AppImage Configuration (appimage-config.yml):**

```yaml
AppDir: app
BuilderDir: /tmp
AppImage:
  Path: AI-Miniature-Repainting.AppImage
  FileFormat: 2
  CompressionType: xz
  UpdateInformation: zsync|https://releases.example.com/AI-Miniature-Repainting-latest-x86_64.AppImage.zsync
  SignKey: KEYID
AppImage:
  - path: app/AI-Miniature-Repainting.png
    x_scale: 0
    y_scale: 0
    width: 256
    height: 256
  - path: app/AI-Miniature-Repainting-128x128.png
    x_scale: 0
    y_scale: 0
    width: 128
    height: 128

Debs:
  - debname: ai-miniature-repainting
    dist: focal
    suite: stable
    maintainer: Your Name <email@example.com>
    license: MIT
```

### DEB (Debian Package)

Creates packages for Debian-based distributions (Ubuntu, Debian, etc.).

```json
{
  "build": {
    "linux": ["deb"],
    "debConfig": {
      "files": {},
      "depends": [
        "libssl3",
        "libgtk-3-0",
        "libglib2.0-0",
        "libharfbuzz0b"
      ],
      "desktopTemplate": null,
      "maintainers": [
        {
          "name": "Your Name",
          "email": "email@example.com"
        }
      ],
      "section": "utils",
      "priority": "optional",
      "changelog": "path/to/CHANGELOG.md",
      "preInstall": null,
      "postInstall": null,
      "preRemove": null,
      "postRemove": null
    }
  }
}
```

**Debian Control File (debian-control):**

```
Package: ai-miniature-repainting
Version: 1.0.0
Architecture: amd64
Maintainer: Your Name <email@example.com>
Depends: libssl3, libgtk-3-0, libglib2.0-0, libharfbuzz0b
Homepage: https://example.com
Description: AI-powered desktop application for miniature repainting
 Uses machine learning to assist with detailed miniature painting
 Supports Windows, macOS, and Linux
```

### RPM (Red Hat Package Manager)

Creates packages for RPM-based distributions (Fedora, RHEL, openSUSE, etc.).

```json
{
  "build": {
    "linux": ["rpm"],
    "rpmConfig": {
      "files": {},
      "depends": [
        "openssl-libs",
        "gtk3",
        "glib2",
        "harfbuzz"
      ],
      "epoch": 0,
      "release": "1",
      "preInstall": null,
      "postInstall": null,
      "preRemove": null,
      "postRemove": null,
      "desktopTemplate": null,
      "license": "MIT"
    }
  }
}
```

## Complete Multi-Platform tauri.conf.json Example

```json
{
  "productName": "AI Miniature Repainting",
  "version": "1.0.0",
  "identifier": "com.example.airepainting",
  "build": {
    "beforeBuildCommand": "npm run build",
    "beforeDevCommand": "npm run dev",
    "devPath": "http://localhost:5173",
    "frontendDist": "../dist",
    "windows": ["wix", "nsis"],
    "macos": ["dmg"],
    "linux": ["appimage", "deb", "rpm"]
  },
  "app": {
    "windows": [
      {
        "title": "AI Miniature Repainting",
        "fullscreen": false,
        "resizable": true,
        "width": 1280,
        "height": 800,
        "minWidth": 400,
        "minHeight": 300
      }
    ],
    "macos": [
      {
        "title": "AI Miniature Repainting",
        "fullscreen": false,
        "resizable": true,
        "width": 1280,
        "height": 800,
        "minWidth": 400,
        "minHeight": 300,
        "transparent": false,
        "titleBarStyle": "Transparent"
      }
    ],
    "linux": [
      {
        "title": "AI Miniature Repainting",
        "fullscreen": false,
        "resizable": true,
        "width": 1280,
        "height": 800,
        "minWidth": 400,
        "minHeight": 300
      }
    ]
  },
  "bundle": {
    "active": true,
    "targets": ["msi", "nsis", "dmg", "appimage", "deb", "rpm"],
    "identifier": "com.example.airepainting",
    "icon": [
      "icons/32x32.png",
      "icons/128x128.png",
      "icons/128x128@2x.png",
      "icons/icon.icns",
      "icons/icon.ico"
    ]
  }
}
```

## Platform-Specific Build Commands

```bash
# Build for current platform
cargo tauri build --release

# Windows only
cargo tauri build --release --target x86_64-pc-windows-gnu

# macOS only
cargo tauri build --release --target x86_64-apple-darwin

# macOS ARM64 (Apple Silicon)
cargo tauri build --release --target aarch64-apple-darwin

# Linux only
cargo tauri build --release --target x86_64-unknown-linux-gnu

# Specific bundler format
cargo tauri build --release --bundles msi
cargo tauri build --release --bundles dmg
cargo tauri build --release --bundles appimage,deb,rpm
```

## Common Issues and Solutions

### Windows Code Signing Issues
- Ensure certificate is in PEM or PKCS12 format
- Check certificate is not expired
- Use timestamp server (DigiCert, GlobalSign) to prevent expiration issues

### macOS Notarization Issues
- Verify Apple ID has Developer account
- Check app-specific password is correct
- Ensure entitlements.plist allows necessary capabilities
- Remove old code signatures before re-signing

### Linux AppImage Issues
- Check linuxdeploy is installed and in PATH
- Verify all dependencies are available
- Use consistent libc versions across systems
- Test on older distributions for compatibility

### Bundling CUDA/GPU Libraries
- Place CUDA libraries in recognized library paths
- Update rpath linking for non-standard paths
- Provide CPU-only fallback when GPU unavailable
- Document CUDA version requirements for users
