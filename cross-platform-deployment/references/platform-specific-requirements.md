# Platform-Specific Requirements and Dependencies

Complete guide for platform-specific build requirements, CUDA bundling strategies, and runtime dependencies.

## Windows Requirements

### Build Requirements

**Minimum Requirements:**
- Windows 10 or later (build 17763+)
- 4 GB RAM
- 10 GB free disk space
- Administrator access for installation

**Required Software:**
- Visual Studio 2019 or later (Community edition is free)
  - Or: Visual Studio Build Tools 2019+
  - C++ build tools package required
- Rust toolchain (rustup)
- Node.js 14+
- WiX Toolset 4.0+ (for MSI creation)

**Installation Steps:**

```powershell
# Install Visual Studio Build Tools (if not using full Visual Studio)
# Download from: https://visualstudio.microsoft.com/downloads/
# Run installer, select "Desktop development with C++"

# Install Rust
# https://rustup.rs/
# Run installer and follow prompts

# Install Node.js
# https://nodejs.org/ (LTS recommended)

# Install WiX
# https://wixtoolset.org/releases/
# Download and run installer

# Verify installations
rustc --version
node --version
wix --version
```

### CUDA on Windows

**Supported CUDA Versions:**
- CUDA 12.x (latest)
- CUDA 11.8
- CUDA 11.x
- CUDA 10.2 (legacy)

**Installation:**

```powershell
# Download CUDA Toolkit
# https://developer.nvidia.com/cuda-downloads

# Run installer
# Accept default paths (C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.0)

# Verify installation
nvcc --version
where cuda.h  # Should find in CUDA installation

# Add to PATH (if not done by installer)
$env:Path += ";C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.0\bin"
$env:Path += ";C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.0\libnvvp"
```

**Bundling CUDA for Distribution:**

```powershell
# Copy necessary CUDA libraries to bundle
Copy-Item "C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.0\bin\cublas64_12.dll" -Destination "src-tauri\resources\cuda\"
Copy-Item "C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.0\bin\cudart64_12.dll" -Destination "src-tauri\resources\cuda\"
Copy-Item "C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.0\bin\cufft64_12.dll" -Destination "src-tauri\resources\cuda\"
Copy-Item "C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.0\bin\curand64_12.dll" -Destination "src-tauri\resources\cuda\"
Copy-Item "C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.0\bin\cusolver64_12.dll" -Destination "src-tauri\resources\cuda\"
Copy-Item "C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.0\bin\cusparse64_12.dll" -Destination "src-tauri\resources\cuda\"
Copy-Item "C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.0\bin\cudnn64_9.dll" -Destination "src-tauri\resources\cuda\"

# Update application to look for DLLs in bundled directory
# In Rust code:
// Add to library search paths
```

**cuDNN on Windows:**

```powershell
# Download cuDNN from NVIDIA (requires account)
# https://developer.nvidia.com/cudnn

# Extract and copy libraries
Copy-Item "cudnn/bin/cudnn64_9.dll" -Destination "src-tauri\resources\cuda\"

# Link in Rust Cargo.toml
```

## macOS Requirements

### Build Requirements

**Minimum Requirements:**
- macOS 10.13 (High Sierra) or later
- Xcode 12.0+
- 4 GB RAM
- 20 GB free disk space (for Xcode)

**Required Software:**
- Xcode Command Line Tools
- Rust toolchain
- Node.js 14+
- Code signing certificate (Apple Developer account)

**Installation Steps:**

```bash
# Install Xcode Command Line Tools
xcode-select --install

# Install Rust (with macOS target)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
rustup target add aarch64-apple-darwin  # For Apple Silicon

# Install Node.js
# Via Homebrew:
brew install node@18
# Or download from https://nodejs.org/

# Install code signing tools
# (included with Xcode)
```

### CUDA on macOS

**Important Note:** NVIDIA CUDA support on macOS is deprecated. Metal is the modern approach.

**Legacy CUDA (if needed):**

```bash
# Download CUDA Toolkit for macOS
# https://developer.nvidia.com/cuda-downloads

# Install
sudo installer -pkg cuda_macos.pkg -target /
export PATH=/usr/local/cuda/bin:$PATH

# Verify
nvcc --version
```

**Metal GPU Acceleration (Recommended):**

```bash
# Use Metal Performance Shaders instead
# No separate installation needed - built into macOS

# In Rust code, use:
// metal crate for GPU compute
// Or use High-level ML frameworks that support Metal
```

**Bundling GPU Libraries:**

For macOS, if bundling legacy CUDA:

```bash
# Copy CUDA libraries
cp /usr/local/cuda/lib/libcudart.12.dylib src-tauri/resources/cuda/
cp /usr/local/cuda/lib/libcublas.12.dylib src-tauri/resources/cuda/
cp /usr/local/cuda/lib/libcudnn.9.dylib src-tauri/resources/cuda/

# Update rpath in binary
install_name_tool -change /usr/local/cuda/lib/libcudart.12.dylib @executable_path/../Resources/cuda/libcudart.12.dylib <binary>
```

**Entitlements for GPU Access:**

Add to `entitlements.plist`:

```xml
<key>com.apple.security.device.gpu</key>
<true/>
<key>com.apple.security.device.frame-buffer</key>
<true/>
```

## Linux Requirements

### Build Requirements

**Minimum Requirements:**
- Linux kernel 4.4+
- 2 GB RAM
- 10 GB free disk space

**Ubuntu/Debian:**

```bash
sudo apt-get update
sudo apt-get install -y \
  build-essential \
  curl \
  wget \
  pkg-config \
  libssl-dev \
  libgtk-3-dev \
  libglib2.0-dev \
  libxcb-render0-dev \
  libxcb-xfixes0-dev \
  libappindicator3-dev \
  libwebkit2gtk-4.0-dev

# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env

# Install Node.js
curl -fsSL https://deb.nodesource.com/setup_18.x | sudo -E bash -
sudo apt-get install -y nodejs
```

**Fedora/RHEL/CentOS:**

```bash
sudo dnf groupinstall "Development Tools"
sudo dnf install -y \
  gcc \
  g++ \
  pkg-config \
  openssl-devel \
  gtk3-devel \
  glib2-devel \
  libxcb-devel \
  appindicator-gtk3-devel \
  webkit2gtk3-devel

# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Install Node.js
sudo dnf install -y nodejs npm
```

**Arch Linux:**

```bash
sudo pacman -Syy
sudo pacman -S --needed \
  base-devel \
  gtk3 \
  glib2 \
  libxcb \
  webkit2gtk \
  nodejs npm

curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

### CUDA on Linux

**Supported CUDA Versions:**
- CUDA 12.x (latest, tested on glibc 2.29+)
- CUDA 11.8 (widely compatible)
- CUDA 10.2 (legacy)

**Installation (Ubuntu 22.04 example):**

```bash
# Download CUDA
# https://developer.nvidia.com/cuda-downloads

# For Ubuntu:
wget https://developer.download.nvidia.com/compute/cuda/repos/ubuntu2204/x86_64/cuda-keyring_1.1-1_all.deb
sudo dpkg -i cuda-keyring_1.1-1_all.deb
sudo apt-get update
sudo apt-get install -y cuda-toolkit-12-0

# Add to PATH
export PATH=/usr/local/cuda-12.0/bin:$PATH
export LD_LIBRARY_PATH=/usr/local/cuda-12.0/lib64:$LD_LIBRARY_PATH

# Verify
nvcc --version
```

**Installation (Generic Linux):**

```bash
# Download runfile installer
# https://developer.nvidia.com/cuda-downloads

chmod +x cuda_12.0.0_linux_x86_64.run
sudo ./cuda_12.0.0_linux_x86_64.run --silent --driver --toolkit --override

# Add to ~/.bashrc or ~/.zshrc
export PATH=/usr/local/cuda/bin:$PATH
export LD_LIBRARY_PATH=/usr/local/cuda/lib64:$LD_LIBRARY_PATH
```

**cuDNN on Linux:**

```bash
# Download from NVIDIA (requires account)
# https://developer.nvidia.com/cudnn

# Extract and install
tar -xzvf cudnn-linux-x86_64-8.x.x.x_cuda12-archive.tar.xz
sudo cp cudnn-*-archive/include/cudnn.h /usr/local/cuda/include/
sudo cp cudnn-*-archive/lib/libcudnn* /usr/local/cuda/lib64/
sudo chmod a+r /usr/local/cuda/lib64/libcudnn*
```

**Bundling for AppImage/DEB/RPM:**

```bash
# Copy CUDA runtime libraries
mkdir -p src-tauri/resources/cuda/lib
cp /usr/local/cuda/lib64/libcudart.so.12 src-tauri/resources/cuda/lib/
cp /usr/local/cuda/lib64/libcublas.so.12 src-tauri/resources/cuda/lib/
cp /usr/local/cuda/lib64/libcudnn.so.9 src-tauri/resources/cuda/lib/
cp /usr/local/cuda/lib64/libcufft.so.11 src-tauri/resources/cuda/lib/

# For AppImage, use linuxdeploy
linuxdeploy --appdir=AppDir --executable=AppDir/usr/bin/app \
  --library=/usr/local/cuda/lib64/libcudart.so.12 \
  --library=/usr/local/cuda/lib64/libcublas.so.12

# For DEB, add dependencies to Debian control file
# For RPM, add to Requires field
```

**LD_LIBRARY_PATH Handling:**

For users without system-wide CUDA installation:

```bash
#!/bin/bash
# wrapper script for application

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export LD_LIBRARY_PATH="$SCRIPT_DIR/../lib/cuda:$LD_LIBRARY_PATH"
exec "$SCRIPT_DIR/ai-repainting" "$@"
```

## Cross-Platform Considerations

### Shared Dependencies

Ensure consistency across platforms:

```
Windows:  vcredist_x64.exe
macOS:    None required (system frameworks)
Linux:    glibc, libstdc++
```

### GPU Detection and Fallback

Implement graceful degradation:

```rust
// Rust example
fn detect_gpu() -> bool {
    #[cfg(target_os = "windows")]
    {
        std::process::Command::new("nvidia-smi")
            .output()
            .is_ok()
    }
    #[cfg(target_os = "macos")]
    {
        // Check for Metal support
        true  // All modern Macs support Metal
    }
    #[cfg(target_os = "linux")]
    {
        std::process::Command::new("nvidia-smi")
            .output()
            .is_ok()
    }
}
```

### Environment Variable Consistency

Document expected environment variables:

```bash
# CUDA paths
CUDA_HOME          # Installation directory
CUDA_PATH          # Installation directory (Windows)
LD_LIBRARY_PATH    # Library search path (Linux)
DYLD_LIBRARY_PATH  # Library search path (macOS)

# GPU selection
CUDA_VISIBLE_DEVICES  # Select specific GPU
CUDA_DEVICE_ORDER     # PCI or FASTEST_FIRST
```

## Minimum Supported Versions

**User Runtime Requirements:**

| Component | Windows | macOS | Linux |
|-----------|---------|-------|-------|
| OS | 10 | 10.13+ | Kernel 4.4+ |
| CUDA | 10.2+ | None | 10.2+ |
| cuDNN | 8.0+ | N/A | 8.0+ |
| glibc | N/A | N/A | 2.17+ |

## System Information Commands

Collect system info for troubleshooting:

```bash
# Windows
wmic os get version
wmic cpu get name
wmic computersystem get totalmemory
nvidia-smi

# macOS
sw_vers
system_profiler SPHardwareDataType
system_profiler SPDisplaysDataType
kextstat | grep Cuda

# Linux
lsb_release -a
uname -m
free -h
lspci | grep -i nvidia
nvidia-smi
```

## Docker Build Images

For consistent CI builds:

```dockerfile
# Windows (requires Windows container)
FROM mcr.microsoft.com/windows/servercore:ltsc2022
RUN powershell -Command Install-WindowsFeature BuildTools
# ... additional setup

# macOS (must be run on macOS runner)
FROM macos-github-actions:latest
RUN brew install rust node

# Linux
FROM ubuntu:22.04
RUN apt-get update && apt-get install -y \
    build-essential curl pkg-config libssl-dev \
    libgtk-3-dev libglib2.0-dev libxcb-render0-dev \
    libxcb-xfixes0-dev libappindicator3-dev \
    libwebkit2gtk-4.0-dev
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
```
