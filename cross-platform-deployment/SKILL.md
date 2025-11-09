---
name: cross-platform-deployment
description: Package and distribute desktop AI application for Windows, macOS, and Linux with code signing. Use when configuring Tauri bundlers (MSI/DMG/AppImage/DEB/RPM), implementing code signing (Authenticode, Apple notarization), managing CUDA dependencies per platform, testing installers on clean VMs, or preparing production releases.
---

# Cross-Platform Desktop Deployment

## Overview

This skill enables complete packaging and distribution of Tauri-based desktop applications across Windows, macOS, and Linux with proper code signing, notarization, and dependency management. It automates the entire build-to-release pipeline including multi-platform compilation, automated signing, installer validation, and CI/CD integration via GitHub Actions.

## When to Use This Skill

Use this skill when:
- Setting up Tauri bundler configurations for Windows (MSI), macOS (DMG), and Linux (AppImage/DEB/RPM)
- Implementing code signing (Windows Authenticode, macOS notarization)
- Bundling CUDA dependencies per platform
- Testing installers on clean VMs
- Automating releases via GitHub Actions
- Preparing production-ready desktop applications

## Core Capabilities

### 1. Multi-Platform Bundling
Configure Tauri bundlers for each platform with proper asset embedding and installer generation. Each platform has unique requirements and tooling.

**Windows**: MSI via Wix Toolset or NSIS with registry entries and uninstaller integration
**macOS**: DMG bundles with code signing certificates and notarization
**Linux**: AppImage for universal compatibility, DEB/RPM for package managers

See `tauri-bundlers.md` for detailed configuration templates for each platform.

### 2. Code Signing & Notarization
Implement cryptographic signing to ensure application integrity and security.

**Windows Authenticode**: Sign with Microsoft Authenticode certificates using Signtool
**macOS Notarization**: Notarize with Apple to ensure Gatekeeper compatibility
**Linux GPG**: Sign packages for package manager verification

See `code-signing-guide.md` for certificate acquisition and signing procedures.

### 3. GPU Dependency Management
Handle CUDA toolkit and cuDNN library bundling across platforms with proper linking and fallback support.

- Detect and bundle appropriate CUDA versions
- Include cuDNN libraries per platform
- Provide CPU-only fallback paths
- Validate runtime dependencies

See `platform-specific-requirements.md` for OS-specific dependency strategies.

### 4. Automated Build System
Execute multi-platform builds with a single command, handling platform detection and conditional compilation.

Use `build-all-platforms.sh` to:
- Detect current OS and available cross-compilation tools
- Run platform-specific build procedures
- Collect and stage artifacts
- Perform signing and notarization automatically
- Generate release metadata

### 5. Installer Testing & Validation
Follow structured procedures to validate installers on clean VMs before production release.

See `installer-testing-checklist.md` for:
- VM setup procedures
- Installation validation steps
- Signature verification
- Dependency resolution testing
- Uninstall validation

### 6. CI/CD Release Automation
GitHub Actions workflow that automatically builds, signs, tests, and releases on version tag push.

Example workflow trigger:
```bash
git tag v1.0.0
git push origin v1.0.0
```

## Workflow: Building and Releasing

### Step 1: Prepare Environment
1. Install platform-specific requirements from `platform-specific-requirements.md`
2. Obtain code signing certificates (Windows Authenticode, macOS Developer Certificate)
3. Set up GitHub Secrets for CI/CD: signing certificates, Apple credentials, notarization password
4. Configure Tauri bundlers in `tauri.conf.json` using `tauri-bundlers.md` templates

### Step 2: Configure Signing
1. Review certificate requirements in `code-signing-guide.md`
2. Export certificates as needed for automation
3. Verify signing tools are available (Signtool for Windows, codesign for macOS)
4. Test signing locally before automation

### Step 3: Build Locally (Optional)
```bash
./scripts/build-all-platforms.sh
```

This builds all platform installers with automatic signing/notarization on the current OS.

### Step 4: Test Installers
1. Set up clean VMs for each OS (or use provided GitHub Actions)
2. Follow `installer-testing-checklist.md` to validate installers
3. Verify signatures with OS-native tools
4. Test uninstall and re-installation

### Step 5: Release via CI/CD
```bash
git tag v1.0.0
git push origin v1.0.0
```

GitHub Actions automatically builds all platforms, signs, tests, and publishes artifacts to GitHub Releases.

## Build Script Usage

### build-all-platforms.sh
Comprehensive multi-platform build automation:
```bash
# Build for current platform only
./scripts/build-all-platforms.sh

# Build with verbose output
./scripts/build-all-platforms.sh --verbose

# Skip signing/notarization (for testing)
./scripts/build-all-platforms.sh --no-sign
```

### sign-and-notarize.sh
Standalone signing and notarization utility:
```bash
# Sign Windows executable
./scripts/sign-and-notarize.sh --windows --file app.exe

# Notarize macOS app
./scripts/sign-and-notarize.sh --macos --file app.dmg

# Sign Linux packages
./scripts/sign-and-notarize.sh --linux --file app.AppImage
```

## GitHub Actions CI/CD

The included GitHub Actions workflow (`.github/workflows/release.yml`):
- Triggers on git version tags (e.g., `v1.0.0`)
- Builds for Windows, macOS, Linux in parallel
- Automatically signs/notarizes binaries
- Runs installer validation tests
- Creates release with artifacts
- Publishes to GitHub Releases

Required GitHub Secrets:
- `APPLE_ID`: Apple Developer account email
- `APPLE_PASSWORD`: Apple app-specific password
- `APPLE_TEAM_ID`: Apple Team ID
- `WINDOWS_PFX`: Windows code signing certificate (base64)
- `WINDOWS_PFX_PASSWORD`: Certificate password
- `GITHUB_TOKEN`: (auto-provided by GitHub)

## Platform-Specific Considerations

**Windows**:
- Requires Visual Studio Build Tools and Wix Toolset
- Authenticode signing requires valid certificate
- Users may see "Unknown Publisher" without signing
- MSI handles registry entries, NSIS is standalone

**macOS**:
- Requires macOS 10.13+
- Code signing is mandatory (can use local self-signed for testing)
- Notarization required for distribution via web
- DMG contains signed .app bundle

**Linux**:
- AppImage works on most distributions
- DEB/RPM target specific package managers
- No universal signing requirement (GPG for package managers)
- cuDNN has different locations per distro

See `platform-specific-requirements.md` for detailed requirements per OS.

## Security Best Practices

1. **Certificate Management**: Store certificates in GitHub Secrets, never in source code
2. **Notarization**: Always notarize macOS releases for distribution
3. **Signature Verification**: Document signature verification steps for users
4. **Dependency Updates**: Keep bundled CUDA/cuDNN current with security patches
5. **Testing**: Validate installers on clean VMs before release
6. **Revocation Monitoring**: Monitor for revoked code signing certificates

## Bundled Resources

### scripts/
Executable automation scripts for building, signing, and releasing applications.

**Included scripts:**
- `build-all-platforms.sh` - Multi-platform build orchestration with platform detection and artifact collection
- `sign-and-notarize.sh` - Automated code signing and macOS notarization utility

### references/
Comprehensive guides and configuration documentation for implementation.

**Included references:**
- `tauri-bundlers.md` - Complete Tauri bundler configurations for Windows (MSI/NSIS), macOS (DMG), and Linux (AppImage/DEB/RPM)
- `code-signing-guide.md` - Detailed code signing procedures: Windows Authenticode, macOS notarization, Linux GPG
- `platform-specific-requirements.md` - OS-specific dependencies, CUDA bundling strategies, and system requirements
- `installer-testing-checklist.md` - Comprehensive checklist for VM-based installer validation and testing

### assets/
Configuration templates and configuration examples for platform-specific installers.

**Included assets:**
- `installer-configs/windows/` - Windows installer configs (NSIS script, Wix template)
- `installer-configs/macos/` - macOS config (entitlements.plist, DMG settings)
- `installer-configs/linux/` - Linux config (AppImage builder config, Debian control file)
