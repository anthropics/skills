#!/bin/bash
# Setup script for MeloTTS LiveKit Plugin

set -e

echo "========================================="
echo "MeloTTS LiveKit Plugin Setup"
echo "========================================="
echo ""

# Check Python version
echo "Checking Python version..."
python_version=$(python3 --version 2>&1 | awk '{print $2}')
echo "Found Python $python_version"

# Check if version is >= 3.9
required_version="3.9"
if [ "$(printf '%s\n' "$required_version" "$python_version" | sort -V | head -n1)" != "$required_version" ]; then
    echo "Error: Python 3.9 or higher is required"
    exit 1
fi

echo "✓ Python version OK"
echo ""

# Setup API Server
echo "========================================="
echo "Setting up API Server"
echo "========================================="
cd api

echo "Creating virtual environment..."
python3 -m venv venv
source venv/bin/activate

echo "Installing dependencies..."
pip install --upgrade pip
pip install -r requirements.txt

echo "Downloading unidic..."
python -m unidic download

echo "✓ API Server setup complete"
echo ""

cd ..

# Setup Plugin
echo "========================================="
echo "Setting up LiveKit Plugin"
echo "========================================="
cd plugin

echo "Installing plugin dependencies..."
pip install -r requirements.txt

echo "✓ Plugin setup complete"
echo ""

cd ..

# Setup Tests
echo "========================================="
echo "Setting up Tests"
echo "========================================="
cd tests

echo "Installing test dependencies..."
pip install -r requirements.txt

echo "✓ Tests setup complete"
echo ""

cd ..

echo "========================================="
echo "Setup Complete!"
echo "========================================="
echo ""
echo "To start the TTS API server:"
echo "  cd api"
echo "  source venv/bin/activate"
echo "  python server.py"
echo ""
echo "To test the API:"
echo "  cd examples"
echo "  python test_api_client.py"
echo ""
echo "To run tests:"
echo "  cd tests"
echo "  pytest -v"
echo ""
echo "For more information, see README.md"
