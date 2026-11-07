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

# Install bundling dependencies
echo "📦 Installing bundling dependencies..."
pnpm add -D --config.strict-dep-builds=false parcel @parcel/config-default parcel-resolver-tspaths html-inline

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
pnpm exec --config.verify-deps-before-run=false parcel build index.html --dist-dir dist --no-source-maps

# Inline everything into single HTML
echo "🎯 Inlining all assets into single HTML file..."
pnpm exec html-inline dist/index.html > bundle.html

# Inline fonts as base64 data URIs so the bundle is truly self-contained
node -e "
const fs = require('fs'), path = require('path');
let html = fs.readFileSync('bundle.html', 'utf8');
const re = /url\(['\"]?([^'\")\s]+\.(?:woff2?|ttf))['\"]?\)/g;
html = html.replace(re, (match, p) => {
  for (const f of [path.resolve('dist', p), path.resolve('dist', path.basename(p))]) {
    if (fs.existsSync(f)) {
      const ext = path.extname(f).slice(1);
      const mime = ext === 'woff2' ? 'font/woff2' : ext === 'woff' ? 'font/woff' : 'font/ttf';
      return 'url(data:' + mime + ';base64,' + fs.readFileSync(f).toString('base64') + ')';
    }
  }
  return match;
});
fs.writeFileSync('bundle.html', html);
"

# Get file size
FILE_SIZE=$(du -h bundle.html | cut -f1)

echo ""
echo "✅ Bundle complete!"
echo "📄 Output: bundle.html ($FILE_SIZE)"
echo ""
echo "You can now use this single HTML file as an artifact in Claude conversations."
echo "To test locally: open bundle.html in your browser"