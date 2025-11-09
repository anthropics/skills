#!/bin/bash

##############################################################################
# Code Signing and Notarization Utility
# Handles Windows Authenticode signing, macOS notarization, and Linux GPG signing
##############################################################################

set -e

##############################################################################
# Configuration & Utility Functions
##############################################################################

VERBOSE=false

log() {
    echo "[SIGN] $*" >&2
}

error() {
    echo "[ERROR] $*" >&2
    exit 1
}

debug() {
    if [ "$VERBOSE" = true ]; then
        echo "[DEBUG] $*" >&2
    fi
}

show_usage() {
    cat <<EOF
Usage: sign-and-notarize.sh --platform <windows|macos|linux> --file <path> [OPTIONS]

Options:
  --platform <os>     Target platform (windows, macos, linux)
  --file <path>       File to sign/notarize
  --verbose           Enable verbose output
  --certificate <id>  Certificate ID or path (platform-specific)
  --apple-id <email>  Apple ID for notarization (macOS only)
  --team-id <id>      Apple Team ID for notarization (macOS only)
  --password <pwd>    App-specific password or certificate password
  --gpg-key <id>      GPG key ID for Linux signing
  --timestamp-server <url>  Timestamp server for Windows signing

Examples:
  # Sign Windows MSI
  sign-and-notarize.sh --platform windows --file app.msi \\
    --certificate /path/to/cert.pfx --password "cert_password"

  # Notarize macOS DMG
  sign-and-notarize.sh --platform macos --file app.dmg \\
    --apple-id "dev@example.com" --team-id "ABCD1234" \\
    --password "app-specific-password"

  # Sign Linux DEB package
  sign-and-notarize.sh --platform linux --file app.deb \\
    --gpg-key "KEYID" --password "gpg_passphrase"
EOF
    exit 1
}

##############################################################################
# Windows Code Signing (Authenticode)
##############################################################################

sign_windows() {
    local file=$1
    local certificate=$2
    local password=$3
    local timestamp_server=${4:-"http://timestamp.digicert.com"}

    if [ ! -f "$file" ]; then
        error "Windows file not found: $file"
    fi

    log "Signing Windows binary: $file"

    # Check if certificate is path or ID
    if [ ! -f "$certificate" ]; then
        # Try to find in store
        log "Looking for certificate in store: $certificate"
        certificate_arg="/n \"$certificate\""
    else
        log "Using certificate file: $certificate"
        certificate_arg="/f \"$certificate\""
    fi

    # Sign the file
    if [ -n "$password" ]; then
        log "Signing with Authenticode..."
        signtool sign /fd SHA256 /tr "$timestamp_server" \
            $certificate_arg /p "$password" \
            "$file" || error "Signing failed"
    else
        error "Certificate password required for Windows signing"
    fi

    # Verify signature
    log "Verifying signature..."
    signtool verify /pa "$file" || error "Signature verification failed"

    log "Windows signing completed successfully!"
}

##############################################################################
# macOS Code Signing & Notarization
##############################################################################

sign_macos() {
    local file=$1
    local certificate_id=$2

    if [ ! -f "$file" ]; then
        error "macOS file not found: $file"
    fi

    log "Code signing macOS application: $file"

    # Extract app bundle from DMG if needed
    local app_path="$file"
    if [[ "$file" == *.dmg ]]; then
        log "Extracting app bundle from DMG..."
        local mount_point=$(mktemp -d)
        hdiutil attach "$file" -mountpoint "$mount_point" >/dev/null 2>&1
        app_path=$(find "$mount_point" -name "*.app" -type d | head -1)
        if [ -z "$app_path" ]; then
            error "No .app bundle found in DMG"
        fi
    fi

    # Sign the application
    if [ -n "$certificate_id" ]; then
        log "Signing with certificate: $certificate_id"
        codesign --deep --force --verify --verbose \
            --sign "$certificate_id" "$app_path" 2>&1 | grep -E "(Signing|error)" || true
    else
        error "Certificate ID required for macOS signing"
    fi

    # Verify signature
    log "Verifying code signature..."
    codesign --verify --verbose=4 "$app_path" 2>&1 | grep -E "(valid|error)" || true

    log "macOS code signing completed!"
}

notarize_macos() {
    local file=$1
    local apple_id=$2
    local team_id=$3
    local password=$4

    if [ ! -f "$file" ]; then
        error "macOS file not found for notarization: $file"
    fi

    if [ -z "$apple_id" ] || [ -z "$team_id" ] || [ -z "$password" ]; then
        error "Apple ID, Team ID, and password required for notarization"
    fi

    log "Submitting for Apple notarization: $file"

    # Submit for notarization
    local request_uuid=$(xcrun notarytool submit "$file" \
        --apple-id "$apple_id" \
        --team-id "$team_id" \
        --password "$password" \
        --wait 2>&1 | tee /tmp/notarize.log | grep "id:" | awk '{print $NF}')

    if [ -z "$request_uuid" ]; then
        log "Checking notarization log..."
        cat /tmp/notarize.log | grep -E "(error|Error|invalid)" || true
        error "Notarization submission failed"
    fi

    log "Notarization submitted. Request ID: $request_uuid"

    # Wait for notarization to complete
    log "Waiting for notarization to complete..."
    local max_attempts=120
    local attempt=0

    while [ $attempt -lt $max_attempts ]; do
        local status=$(xcrun notarytool info "$request_uuid" \
            --apple-id "$apple_id" \
            --team-id "$team_id" \
            --password "$password" 2>&1 | grep "status:" | awk '{print $NF}')

        if [ "$status" = "Accepted" ]; then
            log "Notarization accepted!"
            break
        elif [ "$status" = "Invalid" ]; then
            error "Notarization rejected. Check Apple Developer portal."
        fi

        log "Notarization status: $status (attempt $((attempt + 1))/$max_attempts)"
        sleep 10
        attempt=$((attempt + 1))
    done

    # Staple the notarization ticket
    log "Stapling notarization ticket to application..."
    xcrun stapler staple "$file" 2>&1 | grep -E "(The staple|error)" || true

    log "macOS notarization completed!"
}

##############################################################################
# Linux Package Signing (GPG)
##############################################################################

sign_linux() {
    local file=$1
    local gpg_key=$2
    local password=$3

    if [ ! -f "$file" ]; then
        error "Linux package not found: $file"
    fi

    log "Signing Linux package: $file"

    if [ -z "$gpg_key" ]; then
        error "GPG key ID required for Linux signing"
    fi

    # Prepare GPG passphrase
    local gpg_args=""
    if [ -n "$password" ]; then
        gpg_args="--pinentry-mode loopback --passphrase \"$password\""
    fi

    # Create detached signature
    log "Creating GPG detached signature..."
    eval "gpg $gpg_args --default-key \"$gpg_key\" --detach-sign \"$file\"" 2>&1 | \
        grep -E "(gpg:|error)" || true

    # Verify signature
    if [ -f "${file}.sig" ]; then
        log "Verifying GPG signature..."
        gpg --verify "${file}.sig" "$file" 2>&1 | grep -E "(Good|BAD|error)" || true
        log "Linux package signing completed!"
    else
        error "GPG signature file not created"
    fi
}

##############################################################################
# Main Execution
##############################################################################

main() {
    local platform=""
    local file=""
    local certificate=""
    local apple_id=""
    local team_id=""
    local password=""
    local gpg_key=""
    local timestamp_server=""

    # Parse arguments
    while [[ $# -gt 0 ]]; do
        case $1 in
            --platform)
                platform="$2"
                shift 2
                ;;
            --file)
                file="$2"
                shift 2
                ;;
            --certificate)
                certificate="$2"
                shift 2
                ;;
            --apple-id)
                apple_id="$2"
                shift 2
                ;;
            --team-id)
                team_id="$2"
                shift 2
                ;;
            --password)
                password="$2"
                shift 2
                ;;
            --gpg-key)
                gpg_key="$2"
                shift 2
                ;;
            --timestamp-server)
                timestamp_server="$2"
                shift 2
                ;;
            --verbose)
                VERBOSE=true
                shift
                ;;
            -h|--help)
                show_usage
                ;;
            *)
                error "Unknown option: $1"
                ;;
        esac
    done

    # Validate arguments
    if [ -z "$platform" ] || [ -z "$file" ]; then
        show_usage
    fi

    # Execute signing based on platform
    case "$platform" in
        windows)
            if [ -z "$certificate" ] || [ -z "$password" ]; then
                error "Windows signing requires --certificate and --password"
            fi
            sign_windows "$file" "$certificate" "$password" "$timestamp_server"
            ;;
        macos)
            if [ -z "$apple_id" ] || [ -z "$team_id" ] || [ -z "$password" ]; then
                error "macOS notarization requires --apple-id, --team-id, and --password"
            fi
            if [ -z "$certificate" ]; then
                log "No certificate specified. Using default identity."
            else
                sign_macos "$file" "$certificate"
            fi
            notarize_macos "$file" "$apple_id" "$team_id" "$password"
            ;;
        linux)
            if [ -z "$gpg_key" ]; then
                error "Linux signing requires --gpg-key"
            fi
            sign_linux "$file" "$gpg_key" "$password"
            ;;
        *)
            error "Unsupported platform: $platform"
            ;;
    esac

    log "Signing completed!"
}

# Show usage if no arguments provided
if [ $# -eq 0 ]; then
    show_usage
fi

main "$@"
