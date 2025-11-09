# Code Signing and Notarization Guide

Complete guide for implementing code signing and notarization across Windows, macOS, and Linux.

## Overview

Code signing ensures:
- **Authenticity**: Users know the application comes from a trusted publisher
- **Integrity**: Verifies the application hasn't been modified
- **Security**: Prevents trojan/malware distribution
- **Trust**: Eliminates "Unknown Publisher" warnings on Windows/macOS

## Windows Code Signing (Authenticode)

### Certificate Requirements

**For code signing you need:**
1. Code signing certificate (EV or OV level)
2. Private key
3. Certificate chain (intermediate + root)
4. Timestamp server URL

**Popular certificate providers:**
- DigiCert Code Signing
- GlobalSign Code Signing
- Sectigo (Comodo) Code Signing
- Microsoft Authenticode compatible providers

### Obtain a Code Signing Certificate

1. **Choose provider and package** (OV Code Signing ~$150-300/year)
2. **Generate Certificate Signing Request (CSR)** on your Windows machine or Linux:
   ```bash
   openssl req -new -newkey rsa:2048 -keyout private.key -out signing.csr \
     -subj "/C=US/ST=State/L=City/O=Company/CN=example.com"
   ```

3. **Submit CSR to certificate provider** with business verification
4. **Download issued certificate** (typically in PEM or PKCS12 format)

### Convert Certificate Format

**PEM to PKCS12 (for Windows signing):**
```bash
openssl pkcs12 -export \
  -in certificate.crt \
  -inkey private.key \
  -out certificate.pfx \
  -certfile ca-bundle.crt \
  -password pass:your_password
```

**Extract private key if needed:**
```bash
openssl pkey -in certificate.pfx -out private.key -passin pass:password
```

### Sign Windows Executables

**Using Signtool (Windows or WSL):**
```bash
signtool sign /f certificate.pfx /p password /fd SHA256 \
  /tr http://timestamp.digicert.com \
  /td SHA256 \
  application.exe
```

**Parameters:**
- `/f certificate.pfx` - Path to code signing certificate
- `/p password` - Certificate password
- `/fd SHA256` - File digest algorithm (SHA256 recommended)
- `/tr timestamp_url` - Timestamp server URL (prevents certificate expiration issues)
- `/td SHA256` - Timestamp digest algorithm

**Verify signature:**
```bash
signtool verify /pa application.exe
```

### Windows Timestamp Servers

Timestamp servers prevent signatures from becoming invalid when certificates expire.

**Popular timestamp servers:**
- DigiCert: `http://timestamp.digicert.com`
- GlobalSign: `http://timestamp.globalsign.com`
- Sectigo: `http://timestamp.sectigo.com`
- Microsoft: `http://timestamp.microsoft.com`

## macOS Code Signing and Notarization

### Certificate Requirements

**For macOS distribution you need:**
1. Apple Developer Account ($99/year)
2. Code Signing Certificate (Apple Development)
3. Developer ID Certificate (for distribution outside App Store)
4. Notarization credentials

### Obtain Certificates

1. **Enroll in Apple Developer Program**:
   - https://developer.apple.com/enroll/
   - Requires Apple ID, business verification

2. **Create Code Signing Certificate in Xcode**:
   ```bash
   # In Xcode:
   # Xcode → Settings → Accounts → Manage Certificates
   # Click "+" → Code Signing Certificate → Create
   ```

3. **Export certificate from Keychain**:
   ```bash
   # Open Keychain Access
   # Right-click certificate → Export
   # Save as .p12 file
   ```

### macOS Code Signing

**Sign application bundle:**
```bash
codesign --deep --force --verify --verbose \
  --sign "Developer ID Application: Your Company" \
  --options runtime \
  --entitlements entitlements.plist \
  "path/to/Application.app"
```

**Parameters:**
- `--deep` - Sign nested frameworks and bundles
- `--force` - Overwrite existing signatures
- `--verify` - Verify after signing
- `--sign identity` - Certificate identity
- `--options runtime` - Enable hardened runtime (required for notarization)
- `--entitlements` - Entitlements plist file

**Verify signature:**
```bash
codesign --verify --verbose=4 "path/to/Application.app"
```

### macOS Notarization

Notarization is required to distribute macOS applications. Without it, users see Gatekeeper warnings.

**Create App-Specific Password:**
1. Go to https://appleid.apple.com/account/security
2. Generate "App-specific password"
3. Use in notarization commands

**Notarize application:**

```bash
# Submit for notarization
xcrun notarytool submit "app.dmg" \
  --apple-id "developer@company.com" \
  --team-id "ABCD1234EF" \
  --password "app-specific-password" \
  --wait

# Result: RequestUUID returned on success
```

**Check notarization status:**
```bash
xcrun notarytool info REQUEST_UUID \
  --apple-id "developer@company.com" \
  --team-id "ABCD1234EF" \
  --password "app-specific-password"
```

**Staple notarization ticket to DMG:**
```bash
xcrun stapler staple "app.dmg"
```

**Verify notarization:**
```bash
spctl -a -v -t execute "path/to/Application.app"
```

### macOS Entitlements

Create `entitlements.plist` for required capabilities:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <!-- App Sandbox (required for notarization) -->
  <key>com.apple.security.app-sandbox</key>
  <true/>

  <!-- Allow JIT compilation (for Rust/WASM) -->
  <key>com.apple.security.cs.allow-jit</key>
  <true/>

  <!-- Allow unsigned code execution (for dynamic libraries) -->
  <key>com.apple.security.cs.allow-unsigned-executable-memory</key>
  <true/>

  <!-- File access permissions -->
  <key>com.apple.security.files.user-selected.read-write</key>
  <true/>
  <key>com.apple.security.files.downloads.read-write</key>
  <true/>

  <!-- Hardware access -->
  <key>com.apple.security.device.camera</key>
  <true/>
  <key>com.apple.security.device.usb</key>
  <true/>

  <!-- Network access -->
  <key>com.apple.security.network.client</key>
  <true/>
  <key>com.apple.security.network.server</key>
  <true/>

  <!-- Disable library validation for bundled libraries -->
  <key>com.apple.security.cs.disable-library-validation</key>
  <true/>

  <!-- Metal GPU access (for ML/AI frameworks) -->
  <key>com.apple.security.device.gpu</key>
  <true/>
</dict>
</plist>
```

## Linux Package Signing

### GPG Key Setup

**Generate GPG key:**
```bash
gpg --gen-key
# Select RSA, 4096 bits, no expiration
# Enter name, email, comment
# Enter passphrase
```

**List keys:**
```bash
gpg --list-keys
pub   rsa4096 2024-01-15 [SC]
      ABCD1234567890ABCD1234567890ABCD1234567890
uid           [ultimate] Your Name <email@example.com>
```

**Export public key for distribution:**
```bash
gpg --export --armor ABCD1234567890ABCD1234567890ABCD1234567890 > public-key.asc
```

### Sign DEB Packages

**Create signed DEB:**
```bash
# Using debsign (requires .dsc file from debuild)
debsign -k KEYID package_1.0_amd64.changes

# Using dpkg-sig
dpkg-sig --sign builder -k KEYID package_1.0_amd64.deb
```

**Verify DEB signature:**
```bash
dpkg-sig --verify package_1.0_amd64.deb
```

### Sign RPM Packages

**Import key into RPM:**
```bash
rpm --import public-key.asc
```

**Sign RPM:**
```bash
rpm --addsign -D "_gpg_name KEYID" package-1.0-1.x86_64.rpm
```

**Verify RPM signature:**
```bash
rpm -K package-1.0-1.x86_64.rpm
```

### Repository Signing

**For package repositories, sign the repository metadata:**

**APT (Debian/Ubuntu):**
```bash
# Create apt-key
apt-key add public-key.asc

# Sign Release file
gpg --clearsign -o Release.gpg Release
gpg -abs -o Release.gpg Release
```

**YUM/DNF (Red Hat/Fedora):**
```bash
# Add key to repository
rpm --import public-key.asc

# Ensure repomd.xml is signed
gpg --detach-sign --armor repomd.xml
```

## CI/CD Integration

### GitHub Actions Setup

**Store certificates in GitHub Secrets:**

1. **Windows Certificate:**
   ```bash
   # Convert PFX to base64
   base64 -i certificate.pfx | tr -d '\n' | pbcopy
   # Paste into GitHub Secret: WINDOWS_PFX
   ```

2. **macOS Credentials:**
   - `APPLE_ID`: Developer account email
   - `APPLE_PASSWORD`: App-specific password
   - `APPLE_TEAM_ID`: Team ID (e.g., ABCD1234EF)

3. **Linux GPG Key:**
   ```bash
   # Export GPG key
   gpg --export-secret-key KEYID | base64 > gpg-key.asc.base64
   # Store in GitHub Secret: GPG_KEY
   ```

**GitHub Actions Workflow Example:**

```yaml
name: Sign and Release

on:
  push:
    tags:
      - 'v*'

jobs:
  sign-and-release:
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [windows-latest, macos-latest, ubuntu-latest]

    steps:
      - uses: actions/checkout@v3

      - name: Setup Windows signing
        if: runner.os == 'Windows'
        run: |
          echo "${{ secrets.WINDOWS_PFX }}" | base64 -d > certificate.pfx
          # Use signtool to sign

      - name: Setup macOS signing
        if: runner.os == 'macOS'
        env:
          APPLE_ID: ${{ secrets.APPLE_ID }}
          APPLE_PASSWORD: ${{ secrets.APPLE_PASSWORD }}
          APPLE_TEAM_ID: ${{ secrets.APPLE_TEAM_ID }}
        run: |
          # Import certificate
          # Sign and notarize

      - name: Setup Linux signing
        if: runner.os == 'Linux'
        run: |
          echo "${{ secrets.GPG_KEY }}" | base64 -d | gpg --import
          # Sign packages
```

## Security Best Practices

1. **Certificate Management**
   - Store private keys securely (hardware tokens when possible)
   - Use strong passphrases
   - Rotate certificates periodically
   - Monitor for certificate expiration

2. **Notarization**
   - Always notarize macOS releases for web distribution
   - Notarization timestamps applications for future Gatekeeper compatibility
   - Check notarization status before distribution

3. **Timestamp Servers**
   - Always use timestamp servers for Windows signing
   - Prevents signatures from becoming invalid after certificate expiration
   - Use trusted, reliable timestamp authorities

4. **Key Management**
   - Never commit private keys to version control
   - Use GitHub Secrets or vault systems
   - Limit access to signing credentials
   - Audit and log signing operations

5. **Verification**
   - Verify signatures locally before distribution
   - Document signature verification steps for users
   - Provide signed checksums for downloads

6. **Revocation Monitoring**
   - Monitor for revoked certificates
   - Have backup certificates ready
   - Test signing with new certificates before release

## Common Issues and Solutions

### Windows Signing Issues

**"SignTool cannot find certificate"**
- Verify certificate is in PKCS12 format (.pfx)
- Check certificate password is correct
- Install Visual Studio Build Tools

**"Timestamp server unreachable"**
- Check network connectivity
- Try different timestamp server
- Use local timestamp if available

### macOS Notarization Issues

**"Invalid app signature"**
- Ensure hardened runtime is enabled: `--options runtime`
- Check entitlements.plist syntax
- Verify all nested binaries are signed

**"Notarization rejected"**
- Check Apple Security & Privacy logs
- May need to enable specific entitlements
- Ensure app has proper code signature

**"Certificate expired"**
- Generate new Developer ID certificate
- Re-sign and resubmit for notarization

### Linux Signing Issues

**"GPG key not found"**
- Verify key ID matches exported key
- Import public key on distribution system
- Check gpg keyring configuration

**"Package verification fails"**
- Ensure signature algorithm matches system expectations
- Check GPG version compatibility
- Verify repository configuration accepts signed packages
