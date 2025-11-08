#!/bin/bash

# Tauri Project Initialization Script
# Creates a production-ready Tauri v2.x project with security and optimization defaults
#
# Usage: ./init-tauri-project.sh <project-name> [template]
# Templates: react-ts (default), react, vue-ts, vue, svelte-ts, svelte

set -e

PROJECT_NAME="${1:-my-tauri-app}"
TEMPLATE="${2:-react-ts}"

echo "🚀 Initializing Tauri v2.x project: $PROJECT_NAME"
echo "📦 Template: $TEMPLATE"
echo ""

# Check if npm is installed
if ! command -v npm &> /dev/null; then
    echo "❌ Error: npm is not installed. Please install Node.js and npm first."
    exit 1
fi

# Check if cargo is installed
if ! command -v cargo &> /dev/null; then
    echo "❌ Error: cargo is not installed. Please install Rust first."
    echo "   Visit: https://rustup.rs/"
    exit 1
fi

# Create the project
echo "📥 Creating Tauri project..."
npm create tauri-app@latest "$PROJECT_NAME" -- --template "$TEMPLATE" --yes

cd "$PROJECT_NAME"

echo ""
echo "⚙️  Applying production optimizations..."

# Update Cargo.toml with optimized release profile
cat >> src-tauri/Cargo.toml <<EOF

# Production optimization profile
[profile.release]
opt-level = "z"       # Optimize for size (critical for AI apps)
lto = true            # Link Time Optimization
codegen-units = 1     # Better optimization (slower compile)
strip = true          # Strip symbols from binary
panic = "abort"       # Reduce binary size
EOF

# Create a production-ready tauri.conf.json with security defaults
echo "🔒 Configuring security defaults..."

# Update tauri.conf.json with security settings (preserving existing structure)
cat > src-tauri/tauri.conf.json.new <<'EOF'
{
  "$schema": "https://schema.tauri.app/config/2.0",
  "productName": "PROJECT_NAME_PLACEHOLDER",
  "version": "0.1.0",
  "identifier": "com.example.PROJECT_NAME_PLACEHOLDER",
  "build": {
    "beforeDevCommand": "npm run dev",
    "devUrl": "http://localhost:5173",
    "beforeBuildCommand": "npm run build",
    "frontendDist": "../dist"
  },
  "app": {
    "windows": [
      {
        "title": "PROJECT_NAME_PLACEHOLDER",
        "width": 1200,
        "height": 800,
        "minWidth": 800,
        "minHeight": 600,
        "resizable": true,
        "fullscreen": false
      }
    ],
    "security": {
      "csp": "default-src 'self'; img-src 'self' asset: https://asset.localhost data: blob:; style-src 'self' 'unsafe-inline'"
    }
  },
  "bundle": {
    "active": true,
    "targets": "all",
    "icon": [
      "icons/32x32.png",
      "icons/128x128.png",
      "icons/128x128@2x.png",
      "icons/icon.icns",
      "icons/icon.ico"
    ],
    "resources": []
  }
}
EOF

# Replace placeholder with actual project name
sed "s/PROJECT_NAME_PLACEHOLDER/$PROJECT_NAME/g" src-tauri/tauri.conf.json.new > src-tauri/tauri.conf.json
rm src-tauri/tauri.conf.json.new

# Create commands module structure
mkdir -p src-tauri/src
cat > src-tauri/src/commands.rs <<'EOF'
// Tauri command handlers
// All functions here are exposed to the frontend via invoke()

#[tauri::command]
fn greet(name: String) -> String {
    format!("Hello, {}! Welcome to Tauri.", name)
}

// Add more commands here following the pattern:
// #[tauri::command]
// fn your_command(param: Type) -> Result<ReturnType, String> {
//     // Implementation
//     Ok(result)
// }
EOF

# Update main.rs to include commands module
cat > src-tauri/src/main.rs <<'EOF'
// Prevents additional console window on Windows in release builds
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

mod commands;

fn main() {
    tauri::Builder::default()
        .invoke_handler(tauri::generate_handler![
            commands::greet,
            // Add more commands here as you create them
        ])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
EOF

# Create .gitignore additions for Tauri
cat >> .gitignore <<EOF

# Tauri
src-tauri/target/
src-tauri/WixTools/
*.msi
*.exe
*.dmg
*.deb
*.rpm
*.AppImage
EOF

echo ""
echo "✅ Project initialized successfully!"
echo ""
echo "📋 Next steps:"
echo "   1. cd $PROJECT_NAME"
echo "   2. npm install"
echo "   3. npm run tauri dev     # Start development server"
echo "   4. npm run tauri build   # Create production build"
echo ""
echo "📚 Documentation: https://v2.tauri.app/"
echo "🔧 Edit src-tauri/src/commands.rs to add backend functionality"
echo "🎨 Edit src/ to customize your frontend"
