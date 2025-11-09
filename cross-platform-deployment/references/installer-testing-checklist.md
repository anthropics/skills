# Installer Testing Checklist

Comprehensive procedures for validating installers on clean virtual machines before production release.

## Test Environment Setup

### Virtual Machine Configuration

**Recommended VM Specifications:**
- CPU: 2 cores (minimum)
- RAM: 4 GB
- Disk: 30-50 GB
- Network: Internet access for dependency downloads

**Hypervisors:**
- Windows: Hyper-V, VirtualBox, VMware
- macOS: Parallels, VMware Fusion, UTM
- Linux: KVM, VirtualBox

### Creating Clean Test VMs

**Windows Test VM:**

1. Download Windows ISO:
   - Windows 10: https://www.microsoft.com/en-us/software-download/windows10ISO
   - Windows 11: https://www.microsoft.com/en-us/software-download/windows11

2. Create VM with minimal configuration
3. Install Windows updates before testing
4. Install Visual C++ Redistributable (if required)
5. Create snapshot before testing

**macOS Test VM:**

1. Create macOS VM with clean installation
2. Update to latest security patches
3. Grant necessary permissions (Settings → Security & Privacy)
4. Create snapshot before testing

**Linux Test VM:**

1. Use latest LTS distribution image
2. Minimal installation (no development tools)
3. Update package manager cache
4. Create snapshot before testing

**Popular Distributions for Testing:**
- Ubuntu 20.04 LTS, 22.04 LTS
- Debian 11, 12
- Fedora 38, 39
- CentOS 7, 8

## Pre-Installation Verification

### File Integrity Checks

- [ ] Verify installer file size matches expected size
- [ ] Calculate and verify checksums:
  ```bash
  # Windows
  certUtil -hashfile installer.exe SHA256

  # macOS
  shasum -a 256 app.dmg

  # Linux
  sha256sum application.AppImage
  ```
- [ ] Verify digital signatures:
  ```bash
  # Windows
  signtool verify /pa installer.exe

  # macOS
  spctl -a -v -t execute app.dmg

  # Linux
  gpg --verify application.AppImage.sig
  ```

### Code Signature Verification

- [ ] Verify Windows Authenticode signature:
  ```powershell
  signtool verify /pa "C:\path\to\installer.exe"
  # Should show: "Signing certificate chain verified" ✓
  ```

- [ ] Verify macOS code signature:
  ```bash
  codesign --verify --verbose /Volumes/app.dmg/*.app
  # Should show: "valid on disk" ✓
  ```

- [ ] Verify macOS notarization:
  ```bash
  spctl -a -v -t execute "/Applications/app.app"
  # Should show: "accepted" or "notarized" ✓
  ```

- [ ] Verify Linux GPG signature:
  ```bash
  gpg --import public-key.asc
  gpg --verify application.AppImage.sig application.AppImage
  # Should show: "Good signature" ✓
  ```

## Installation Testing

### Windows Installation

**MSI Installer Testing:**

- [ ] Double-click installer
- [ ] Accept UAC prompt (if shown)
- [ ] Verify installation wizard appears
- [ ] Accept license agreement
- [ ] Choose installation location (test custom path)
- [ ] Complete installation
- [ ] Verify application appears in:
  - [ ] Start menu
  - [ ] Applications list (Control Panel → Programs)
  - [ ] Application shortcuts on desktop (if enabled)
- [ ] Registry entries created (if applicable):
  ```powershell
  reg query "HKCU\Software\Your Company\Application Name"
  ```
- [ ] Verify file permissions are correct:
  ```powershell
  icacls "C:\Program Files\Application" /T /C
  ```

**NSIS Installer Testing:**

- [ ] Execute installer
- [ ] Verify custom installation options (if available)
- [ ] Complete installation process
- [ ] Verify application directory structure
- [ ] Check file associations (if configured)

### macOS Installation

**DMG Bundle Testing:**

- [ ] Double-click DMG file
- [ ] Verify DMG mounts correctly
- [ ] Drag application to Applications folder
- [ ] Verify application icon appears in Launchpad
- [ ] Eject DMG
- [ ] Verify application can be launched from Applications folder
- [ ] Check code signature:
  ```bash
  codesign -v /Applications/app.app
  ```
- [ ] Verify bundle permissions:
  ```bash
  ls -la /Applications/app.app/Contents/MacOS/
  ```

### Linux Installation

**AppImage Testing:**

- [ ] Download AppImage
- [ ] Make executable:
  ```bash
  chmod +x application.AppImage
  ```
- [ ] Execute directly:
  ```bash
  ./application.AppImage
  # Should run without installation
  ```
- [ ] Verify FUSE2 support (if needed):
  ```bash
  mount | grep fuse
  ```

**DEB Package Testing:**

- [ ] Install package:
  ```bash
  sudo apt-get update
  sudo apt-get install -y ./application.deb
  ```
- [ ] Verify installation:
  ```bash
  dpkg -l | grep application
  ```
- [ ] Verify binary in PATH:
  ```bash
  which application
  ```
- [ ] Check application entry in menu/launcher
- [ ] Verify desktop file:
  ```bash
  ls /usr/share/applications/ | grep application
  ```

**RPM Package Testing:**

- [ ] Install package:
  ```bash
  sudo dnf install -y ./application.rpm
  # or: sudo rpm -ivh ./application.rpm
  ```
- [ ] Verify installation:
  ```bash
  rpm -qa | grep application
  ```
- [ ] Check files are in expected locations:
  ```bash
  rpm -ql application
  ```

## Post-Installation Verification

### Core Functionality

- [ ] Application launches without errors:
  ```bash
  # Windows: Check Event Viewer for errors
  # macOS: Check Console.app for error messages
  # Linux: Check journalctl for error messages
  ```

- [ ] Application GUI renders correctly:
  - [ ] All menus visible
  - [ ] Buttons are clickable
  - [ ] Text is readable
  - [ ] Images load correctly

- [ ] Basic features work:
  - [ ] Open file dialog works
  - [ ] Save file dialog works
  - [ ] Settings/preferences accessible
  - [ ] Help/about dialog displays

### Dependency Verification

- [ ] All required libraries are present:
  ```bash
  # Windows: Use Dependency Walker to check DLL dependencies
  # macOS: otool -L /Applications/app.app/Contents/MacOS/app
  # Linux: ldd $(which application)
  ```

- [ ] GPU libraries detected (if applicable):
  ```bash
  # Windows: CUDA libraries in PATH
  # macOS: Metal available via system
  # Linux: NVIDIA libraries in LD_LIBRARY_PATH
  ```

- [ ] Optional dependencies gracefully handled if missing

### Performance Baseline

- [ ] Application startup time reasonable:
  - [ ] Time from launch to fully interactive < 5 seconds
  - [ ] No excessive CPU/memory usage during startup

- [ ] Memory usage stable during idle:
  - [ ] No memory leaks over 5 minutes idle
  - [ ] Reasonable baseline memory footprint

- [ ] GPU acceleration working (if applicable):
  - [ ] Check application logs for GPU initialization
  - [ ] Monitor GPU memory with nvidia-smi (Linux/Windows)

### System Integration

- [ ] Correct file associations:
  ```bash
  # Windows: Check registry for file type associations
  # macOS: Check Launch Services
  # Linux: Check .desktop file and MIME types
  ```

- [ ] Proper uninstall metadata present:
  - [ ] Windows: Uninstall entry in Control Panel
  - [ ] macOS: Application can be dragged to Trash
  - [ ] Linux: Package can be removed via package manager

- [ ] Log files created in correct locations:
  - [ ] Windows: `%APPDATA%\YourApp\logs\`
  - [ ] macOS: `~/Library/Logs/YourApp/`
  - [ ] Linux: `~/.local/share/YourApp/logs/`

## Uninstall and Reinstall Testing

### Uninstall Process

- [ ] Uninstall application via native method:
  - [ ] Windows: Control Panel → Programs → Uninstall
  - [ ] macOS: Drag to Trash or use uninstaller script
  - [ ] Linux: `sudo apt-get remove application`

- [ ] Verify all files removed:
  ```bash
  # Windows: Check Program Files directory
  # macOS: Check /Applications/ and ~/Library/
  # Linux: Check /usr/bin/, /opt/, /usr/share/
  ```

- [ ] Verify configuration files behavior:
  - [ ] User data preserved (if expected)
  - [ ] Temp files cleaned up
  - [ ] Cache properly removed

- [ ] Registry cleaned (Windows):
  ```powershell
  reg query "HKCU\Software\Microsoft\Windows\CurrentVersion\Uninstall" | findstr /i "application"
  # Should not appear after uninstall
  ```

### Reinstall Testing

- [ ] Reinstall application fresh:
  ```bash
  # For Windows: Run MSI again
  # For macOS: Re-download and mount DMG
  # For Linux: reinstall package
  ```

- [ ] Verify reinstall works without errors
- [ ] Application starts correctly after reinstall
- [ ] Previous user data handled correctly (if applicable)

## Edge Case Testing

### System Configuration Variations

- [ ] Test on system with:
  - [ ] Minimal disk space (< 100 MB free)
  - [ ] Custom user account permissions
  - [ ] Non-English system locale
  - [ ] High DPI/Retina displays
  - [ ] Multiple monitors

- [ ] Test with antivirus software:
  - [ ] Windows Defender
  - [ ] Commercial antivirus products
  - [ ] Verify no false positives

- [ ] Test with security software:
  - [ ] SELinux (Linux)
  - [ ] AppArmor (Linux)
  - [ ] Windows Firewall

### Network Conditions

- [ ] Installation on:
  - [ ] Fast network (> 100 Mbps)
  - [ ] Slow network (< 10 Mbps)
  - [ ] Restricted network (corporate proxy)

- [ ] GPU driver download (if automated):
  - [ ] Successful on slow connections
  - [ ] Retry on connection interruption

### Error Scenarios

- [ ] Test installation with:
  - [ ] Installer path containing spaces
  - [ ] Non-ASCII characters in install path
  - [ ] Administrator permissions missing
  - [ ] Read-only filesystem

- [ ] Graceful error handling:
  - [ ] Clear error messages
  - [ ] Rollback on failure
  - [ ] Cleanup of partial installation

## Automated Testing Setup

### GitHub Actions Test Matrix

```yaml
name: Installer Testing

on:
  push:
    tags:
      - 'v*'

jobs:
  test-installers:
    strategy:
      matrix:
        os:
          - windows-latest
          - macos-latest
          - ubuntu-latest
        include:
          - os: windows-latest
            installer: build/msi/*.msi
            test-cmd: msiexec /i
          - os: macos-latest
            installer: build/dmg/*.dmg
            test-cmd: hdiutil attach
          - os: ubuntu-latest
            installer: build/appimage/*.AppImage
            test-cmd: ./

    steps:
      - uses: actions/checkout@v3

      - name: Download installer artifacts
        uses: actions/download-artifact@v3
        with:
          name: installers-${{ matrix.os }}

      - name: Verify signatures
        run: |
          # Run signature verification script
          ./scripts/verify-signatures.sh ${{ matrix.installer }}

      - name: Install application
        run: |
          # Platform-specific installation
          ./scripts/test-install.sh ${{ matrix.installer }}

      - name: Test functionality
        run: |
          # Run basic functionality tests
          ./scripts/test-functionality.sh

      - name: Uninstall application
        run: |
          # Test uninstall process
          ./scripts/test-uninstall.sh
```

## Sign-Off Checklist

### Release Manager Sign-Off

- [ ] All installation tests passed on all platforms
- [ ] All signature verifications successful
- [ ] Code review of installer configurations complete
- [ ] Security review of bundled dependencies complete
- [ ] Performance baseline acceptable
- [ ] Documentation updated for release

### Quality Assurance Sign-Off

- [ ] Functional testing completed
- [ ] Edge case testing completed
- [ ] Error handling verified
- [ ] Uninstall/reinstall tested
- [ ] No known issues in release notes

### Release Approval

- [ ] Product Manager approval
- [ ] Security team approval
- [ ] Operations team approval
- [ ] Release date and time confirmed

## Testing Documentation

### Test Report Template

```markdown
# Installer Testing Report - v1.0.0

**Test Date**: YYYY-MM-DD
**Tester**: Name
**Platform**: Windows/macOS/Linux
**OS Version**: [Version details]

## Pre-Installation Verification
- [ ] File integrity verified
- [ ] Code signatures valid
- [ ] Notarization confirmed (macOS)

## Installation Testing
- [ ] Installation completed successfully
- [ ] Files in expected locations
- [ ] Application launches correctly
- [ ] All dependencies resolved

## Functionality Testing
- [ ] Core features working
- [ ] GPU acceleration verified (if applicable)
- [ ] Performance acceptable

## Uninstall Testing
- [ ] Clean uninstall completed
- [ ] All files removed
- [ ] Registry cleaned (Windows)

## Issues Found
- [ ] Issue 1: Description
- [ ] Issue 2: Description

## Sign-Off
**Approved**: Yes / No
**Tester Signature**: _________
**Date**: _________
```

## Performance Benchmarks

### Expected Metrics

**Startup Performance:**
- Windows: < 3 seconds
- macOS: < 3 seconds
- Linux: < 2 seconds

**Memory Footprint:**
- Windows: < 200 MB baseline
- macOS: < 150 MB baseline
- Linux: < 150 MB baseline

**Installation Size:**
- Windows MSI: < 500 MB
- macOS DMG: < 600 MB
- Linux AppImage: < 400 MB
- Linux DEB: < 300 MB (without dependencies)

**First Launch:**
- GPU detection: < 500 ms
- CUDA initialization: < 2 seconds
- Model loading: < 5 seconds

## Troubleshooting Common Issues

### Installation Failures

**Symptom**: MSI installation fails with error 1603
**Solution**:
- Run as Administrator
- Check disk space
- Disable antivirus temporarily
- Check Event Viewer for details

**Symptom**: DMG won't mount
**Solution**:
- Verify DMG file integrity
- Re-download DMG
- Check if already mounted

**Symptom**: AppImage won't execute
**Solution**:
- Verify executable bit: `chmod +x app.AppImage`
- Check FUSE2 support
- Try with `--appimage-extract`

### Runtime Failures

**Symptom**: Application crashes on startup
**Solution**:
- Check system logs for errors
- Verify all dependencies installed
- Check GPU driver compatibility
- Run with verbose logging

**Symptom**: GPU not detected
**Solution**:
- Verify GPU driver installed
- Check CUDA compatibility
- Run `nvidia-smi` (Linux/Windows)
- Check System Information (macOS)

**Symptom**: Slow performance
**Solution**:
- Check CPU/memory usage
- Verify GPU acceleration enabled
- Monitor disk I/O
- Check for resource contention
