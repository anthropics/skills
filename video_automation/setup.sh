#!/usr/bin/env bash
set -e

echo "================================================="
echo "  YouTube & TikTok Video Automation — Setup"
echo "================================================="

# Check Python version
python_version=$(python3 --version 2>&1 | awk '{print $2}')
echo "Python: $python_version"

# Create virtual environment
if [ ! -d ".venv" ]; then
    echo ""
    echo "[1/5] Creating virtual environment …"
    python3 -m venv .venv
fi

source .venv/bin/activate

# Install dependencies
echo ""
echo "[2/5] Installing Python dependencies …"
pip install --upgrade pip -q
pip install -r requirements.txt -q
echo "      Dependencies installed."

# Install system-level ffmpeg (required by moviepy)
echo ""
echo "[3/5] Checking ffmpeg …"
if ! command -v ffmpeg &> /dev/null; then
    echo "      ffmpeg not found. Attempting to install …"
    if command -v apt-get &> /dev/null; then
        sudo apt-get install -y ffmpeg -q
    elif command -v brew &> /dev/null; then
        brew install ffmpeg
    else
        echo "      [WARNING] Cannot auto-install ffmpeg. Install manually: https://ffmpeg.org/download.html"
    fi
else
    echo "      ffmpeg: $(ffmpeg -version 2>&1 | head -1)"
fi

# Download a font for better-looking videos
echo ""
echo "[4/5] Downloading Roboto font …"
FONT_DIR="assets/fonts"
FONT_FILE="$FONT_DIR/Roboto-Bold.ttf"
if [ ! -f "$FONT_FILE" ]; then
    mkdir -p "$FONT_DIR"
    FONT_URL="https://github.com/google/fonts/raw/main/apache/roboto/static/Roboto-Bold.ttf"
    if curl -fsSL "$FONT_URL" -o "$FONT_FILE" 2>/dev/null; then
        echo "      Font downloaded: $FONT_FILE"
    else
        echo "      [WARNING] Could not download font. Will use system fonts."
    fi
else
    echo "      Font already present."
fi

# Create .env if missing
echo ""
echo "[5/5] Configuration …"
if [ ! -f ".env" ]; then
    cp .env.example .env
    echo "      Created .env from .env.example"
    echo "      *** IMPORTANT: Edit .env and add your API keys! ***"
else
    echo "      .env already exists."
fi

mkdir -p output credentials

echo ""
echo "================================================="
echo "  Setup complete!"
echo ""
echo "  Next steps:"
echo "  1. Edit .env and add your ANTHROPIC_API_KEY"
echo "  2. Add other API keys (optional but recommended)"
echo "  3. Activate the environment:  source .venv/bin/activate"
echo "  4. List niches:               python main.py niches"
echo "  5. Generate a test video:     python main.py generate --niche tech"
echo "  6. Start daily automation:    python main.py run"
echo ""
echo "  For YouTube setup:  python main.py setup --platform youtube"
echo "  For TikTok setup:   python main.py setup --platform tiktok"
echo "================================================="
