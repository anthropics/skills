#!/bin/bash
set -e

echo "📦 Bundling React app to single HTML artifact..."

# Check if we're in a project directory
if [ ! -f "package.json" ]; then
  echo "❌ Error: No package.json found. Run this script from your project root."
  exit 1
fi

# Check if index.html exists
if [ ! -f "index.html" ]; then
  echo "❌ Error: No index.html found in project root."
  echo "   This script requires an index.html entry point."
  exit 1
fi

PNPM_CONFIG_ARGS=(--config.strict-dep-builds=false --config.verify-deps-before-run=false)

# Install bundling dependencies
echo "📦 Installing bundling dependencies..."
pnpm "${PNPM_CONFIG_ARGS[@]}" add -D parcel @parcel/config-default parcel-resolver-tspaths html-inline

# Create Parcel config with tspaths resolver
if [ ! -f ".parcelrc" ]; then
  echo "🔧 Creating Parcel configuration with path alias support..."
  cat > .parcelrc << 'EOF'
{
  "extends": "@parcel/config-default",
  "resolvers": ["parcel-resolver-tspaths", "..."]
}
EOF
fi

# Clean previous build
echo "🧹 Cleaning previous build..."
rm -rf dist bundle.html

# Build with Parcel
echo "🔨 Building with Parcel..."
pnpm "${PNPM_CONFIG_ARGS[@]}" exec parcel build index.html --dist-dir dist --no-source-maps

# Inline everything into single HTML
echo "🎯 Inlining all assets into single HTML file..."
pnpm "${PNPM_CONFIG_ARGS[@]}" exec html-inline dist/index.html > bundle.html

echo "🔤 Inlining font assets..."
node <<'EOF'
const fs = require("fs");
const path = require("path");

const htmlPath = path.resolve("bundle.html");
const distDir = path.resolve("dist");
const fontMimeTypes = {
  ".woff": "font/woff",
  ".woff2": "font/woff2",
};

if (!fs.existsSync(htmlPath) || !fs.existsSync(distDir)) {
  process.exit(0);
}

function walk(dir) {
  return fs.readdirSync(dir, { withFileTypes: true }).flatMap((entry) => {
    const fullPath = path.join(dir, entry.name);
    return entry.isDirectory() ? walk(fullPath) : [fullPath];
  });
}

const fontFiles = new Map();
for (const file of walk(distDir)) {
  const ext = path.extname(file).toLowerCase();
  if (!fontMimeTypes[ext]) {
    continue;
  }

  const relativePath = path.relative(distDir, file).split(path.sep).join("/");
  fontFiles.set(relativePath, file);
  fontFiles.set(path.basename(file), file);
}

if (fontFiles.size === 0) {
  console.log("   No emitted font files found.");
  process.exit(0);
}

let inlinedCount = 0;
const html = fs.readFileSync(htmlPath, "utf8");
const updatedHtml = html.replace(/@font-face\s*{[^}]*}/g, (fontFaceBlock) =>
  fontFaceBlock.replace(/url\((['"]?)([^'")]+)\1\)/g, (match, _quote, rawUrl) => {
    const url = rawUrl.trim();
    if (/^(?:data:|https?:|\/\/|#)/i.test(url)) {
      return match;
    }

    const urlPath = url.split(/[?#]/)[0];
    const ext = path.extname(urlPath).toLowerCase();
    if (!fontMimeTypes[ext]) {
      return match;
    }

    let decodedPath;
    try {
      decodedPath = decodeURIComponent(urlPath);
    } catch {
      decodedPath = urlPath;
    }

    const normalizedPath = decodedPath.replace(/^\/+/, "");
    const candidates = [
      path.resolve(distDir, normalizedPath),
      fontFiles.get(normalizedPath),
      fontFiles.get(path.basename(normalizedPath)),
    ].filter(Boolean);

    const fontPath = candidates.find((candidate) => fs.existsSync(candidate));
    if (!fontPath) {
      return match;
    }

    const fontExt = path.extname(fontPath).toLowerCase();
    const fontData = fs.readFileSync(fontPath).toString("base64");
    inlinedCount += 1;
    return `url("data:${fontMimeTypes[fontExt]};base64,${fontData}")`;
  }),
);

if (updatedHtml !== html) {
  fs.writeFileSync(htmlPath, updatedHtml);
}

console.log(
  `   Inlined ${inlinedCount} font file reference${inlinedCount === 1 ? "" : "s"}.`,
);
EOF

# Get file size
FILE_SIZE=$(du -h bundle.html | cut -f1)

echo ""
echo "✅ Bundle complete!"
echo "📄 Output: bundle.html ($FILE_SIZE)"
echo ""
echo "You can now use this single HTML file as an artifact in Claude conversations."
echo "To test locally: open bundle.html in your browser"
