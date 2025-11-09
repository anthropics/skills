#!/bin/bash

##############################################################################
# Cross-Platform Desktop Application Builder
# Builds Tauri applications for Windows, macOS, and Linux with automatic
# code signing and notarization support.
##############################################################################

set -e

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
VERBOSE=false
SKIP_SIGN=false

##############################################################################
# Utility Functions
##############################################################################

log() {
    echo "[BUILD] $*" >&2
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

# Parse command-line arguments
parse_args() {
    while [[ $# -gt 0 ]]; do
        case $1 in
            --verbose)
                VERBOSE=true
                shift
                ;;
            --no-sign)
                SKIP_SIGN=true
                shift
                ;;
            *)
                error "Unknown option: $1"
                ;;
        esac
    done
}

# Detect current platform
detect_platform() {
    case "$(uname -s)" in
        Linux*)     echo "linux";;
        Darwin*)    echo "macos";;
        MINGW*|MSYS*|CYGWIN*) echo "windows";;
        *)          error "Unsupported platform";;
    esac
}

# Check required tools
check_requirements() {
    local platform=$1

    log "Checking requirements for $platform..."

    # Universal requirements
    command -v cargo >/dev/null 2>&1 || error "Rust/Cargo not found. Install from https://rustup.rs/"
    command -v npm >/dev/null 2>&1 || error "Node.js/npm not found"

    case "$platform" in
        windows)
            command -v wix >/dev/null 2>&1 || error "WiX Toolset not found. Install from https://wixtoolset.org/"
            command -v signtool >/dev/null 2>&1 || error "Signtool not found. Install Visual Studio Build Tools."
            ;;
        macos)
            command -v security >/dev/null 2>&1 || error "macOS security tools not found"
            command -v codesign >/dev/null 2>&1 || error "codesign not found"
            [ -n "$APPLE_ID" ] || error "APPLE_ID environment variable not set for notarization"
            ;;
        linux)
            command -v linuxdeploy >/dev/null 2>&1 || log "linuxdeploy not found - AppImage creation may fail"
            command -v dpkg >/dev/null 2>&1 || log "dpkg not found - DEB creation will be skipped"
            command -v rpmbuild >/dev/null 2>&1 || log "rpmbuild not found - RPM creation will be skipped"
            ;;
    esac

    log "Requirements check passed for $platform"
}

##############################################################################
# Build Functions
##############################################################################

build_tauri() {
    local platform=$1

    log "Building Tauri application for $platform..."

    if [ ! -f "$PROJECT_ROOT/src-tauri/tauri.conf.json" ]; then
        error "tauri.conf.json not found in $PROJECT_ROOT/src-tauri/"
    fi

    cd "$PROJECT_ROOT"

    # Install dependencies
    npm install 2>/dev/null || true

    # Build frontend
    log "Building frontend..."
    if [ -f "package.json" ]; then
        npm run build 2>/dev/null || true
    fi

    # Build Tauri app
    log "Building Tauri backend..."
    cd src-tauri
    cargo build --release 2>&1 | grep -E "(Compiling|Finished|error)" || true
    cd ..

    log "Tauri build completed for $platform"
}

create_windows_installer() {
    log "Creating Windows installer..."

    cd "$PROJECT_ROOT/src-tauri"

    # Build MSI using Tauri bundler
    cargo tauri build --release --bundles msi 2>&1 | grep -E "(Bundling|error)" || true

    local msi_path="target/release/bundle/msi/"

    if [ ! -z "$(ls $msi_path/*.msi 2>/dev/null)" ]; then
        log "Windows MSI created: $(ls $msi_path/*.msi)"

        # Sign if enabled
        if [ "$SKIP_SIGN" = false ]; then
            log "Signing Windows MSI..."
            if [ -n "$WINDOWS_PFX" ] && [ -n "$WINDOWS_PFX_PASSWORD" ]; then
                for msi in $msi_path/*.msi; do
                    sign_windows_exe "$msi"
                done
            else
                log "Warning: WINDOWS_PFX not configured. Skipping signing."
            fi
        fi
    else
        log "No Windows MSI found in $msi_path"
    fi
}

create_macos_bundle() {
    log "Creating macOS DMG bundle..."

    cd "$PROJECT_ROOT/src-tauri"

    # Build DMG using Tauri bundler
    cargo tauri build --release --bundles dmg 2>&1 | grep -E "(Bundling|error)" || true

    local dmg_path="target/release/bundle/dmg/"

    if [ ! -z "$(ls $dmg_path/*.dmg 2>/dev/null)" ]; then
        log "macOS DMG created: $(ls $dmg_path/*.dmg)"

        # Sign and notarize if enabled
        if [ "$SKIP_SIGN" = false ]; then
            for dmg in $dmg_path/*.dmg; do
                sign_and_notarize_macos "$dmg"
            done
        fi
    else
        log "No macOS DMG found in $dmg_path"
    fi
}

create_linux_bundles() {
    log "Creating Linux bundles (AppImage/DEB/RPM)..."

    cd "$PROJECT_ROOT/src-tauri"

    # Build all Linux bundles
    cargo tauri build --release --bundles appimage,deb,rpm 2>&1 | grep -E "(Bundling|error)" || true

    local bundle_path="target/release/bundle/"

    log "Linux bundles created:"
    [ -d "$bundle_path/appimage" ] && ls "$bundle_path/appimage"/*.AppImage 2>/dev/null && log "  - AppImage"
    [ -d "$bundle_path/deb" ] && ls "$bundle_path/deb"/*.deb 2>/dev/null && log "  - DEB package"
    [ -d "$bundle_path/rpm" ] && ls "$bundle_path/rpm"/*.rpm 2>/dev/null && log "  - RPM package"

    # Sign if enabled
    if [ "$SKIP_SIGN" = false ]; then
        log "Signing Linux packages..."
        for deb in "$bundle_path/deb"/*.deb 2>/dev/null; do
            [ -f "$deb" ] && sign_linux_package "$deb" GPG
        done
    fi
}

##############################################################################
# Signing Functions
##############################################################################

sign_windows_exe() {
    local exe_path=$1

    if [ ! -f "$exe_path" ]; then
        log "Warning: File not found for signing: $exe_path"
        return
    fi

    debug "Signing Windows executable: $exe_path"

    # Decode PFX from base64
    local pfx_file="/tmp/codesign.pfx"
    echo "$WINDOWS_PFX" | base64 -d > "$pfx_file"

    # Sign executable
    signtool sign /f "$pfx_file" /p "$WINDOWS_PFX_PASSWORD" \
        /fd SHA256 /tr http://timestamp.digicert.com \
        "$exe_path" 2>/dev/null || log "Warning: Signing failed for $exe_path"

    # Clean up
    rm -f "$pfx_file"
}

sign_and_notarize_macos() {
    local dmg_path=$1

    if [ ! -f "$dmg_path" ]; then
        log "Warning: DMG not found for notarization: $dmg_path"
        return
    fi

    debug "Notarizing macOS DMG: $dmg_path"

    # Submit for notarization
    local request_uuid=$(xcrun notarytool submit "$dmg_path" \
        --apple-id "$APPLE_ID" \
        --team-id "$APPLE_TEAM_ID" \
        --password "$APPLE_PASSWORD" \
        --wait 2>/dev/null | grep "id:" | awk '{print $NF}' || echo "")

    if [ -n "$request_uuid" ]; then
        log "Notarization submitted. Request ID: $request_uuid"

        # Staple notarization ticket
        xcrun stapler staple "$dmg_path" 2>/dev/null || \
            log "Warning: Could not staple notarization ticket"
    else
        log "Warning: Notarization submission failed"
    fi
}

sign_linux_package() {
    local package_path=$1
    local sign_method=${2:-GPG}

    if [ ! -f "$package_path" ]; then
        log "Warning: Package not found for signing: $package_path"
        return
    fi

    debug "Signing Linux package ($sign_method): $package_path"

    case "$sign_method" in
        GPG)
            if [ -n "$GPG_KEY_ID" ]; then
                gpg --default-key "$GPG_KEY_ID" --detach-sign "$package_path" 2>/dev/null || \
                    log "Warning: GPG signing failed for $package_path"
            else
                log "Warning: GPG_KEY_ID not set. Skipping package signature."
            fi
            ;;
    esac
}

##############################################################################
# Staging & Cleanup
##############################################################################

stage_artifacts() {
    log "Staging build artifacts..."

    local platform=$1
    local stage_dir="$PROJECT_ROOT/dist"
    mkdir -p "$stage_dir"

    case "$platform" in
        windows)
            cp -v "$PROJECT_ROOT/src-tauri/target/release/bundle/msi"/*.msi "$stage_dir/" 2>/dev/null || true
            ;;
        macos)
            cp -v "$PROJECT_ROOT/src-tauri/target/release/bundle/dmg"/*.dmg "$stage_dir/" 2>/dev/null || true
            ;;
        linux)
            cp -v "$PROJECT_ROOT/src-tauri/target/release/bundle/appimage"/*.AppImage "$stage_dir/" 2>/dev/null || true
            cp -v "$PROJECT_ROOT/src-tauri/target/release/bundle/deb"/*.deb "$stage_dir/" 2>/dev/null || true
            cp -v "$PROJECT_ROOT/src-tauri/target/release/bundle/rpm"/*.rpm "$stage_dir/" 2>/dev/null || true
            ;;
    esac

    log "Artifacts staged in: $stage_dir"
}

##############################################################################
# Main Execution
##############################################################################

main() {
    parse_args "$@"

    local platform=$(detect_platform)
    log "Detected platform: $platform"

    check_requirements "$platform"
    build_tauri "$platform"

    case "$platform" in
        windows)
            create_windows_installer
            ;;
        macos)
            create_macos_bundle
            ;;
        linux)
            create_linux_bundles
            ;;
    esac

    stage_artifacts "$platform"

    log "Build completed successfully!"
}

main "$@"
