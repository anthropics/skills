#!/bin/bash
# Python 3.13 Virtual Environment Setup Script
# Automates creation and configuration of Python 3.13 ML backend environment

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Configuration
PYTHON_VERSION="3.13"
VENV_DIR="${1:-.venv}"
PROJECT_NAME="${2:-ml-backend}"

echo -e "${YELLOW}Python 3.13 ML Backend Environment Setup${NC}"
echo "============================================="

# Check Python 3.13 installation
echo -e "\n${YELLOW}Step 1: Validating Python 3.13 installation${NC}"
if ! command -v python3.13 &> /dev/null; then
    echo -e "${RED}Error: Python 3.13 not found${NC}"
    echo "Please install Python 3.13 from https://www.python.org/downloads/"
    exit 1
fi

PYTHON_PATH=$(which python3.13)
PYTHON_VERSION_FULL=$($PYTHON_PATH --version)
echo -e "${GREEN}✓ Found: $PYTHON_VERSION_FULL at $PYTHON_PATH${NC}"

# Create virtual environment
echo -e "\n${YELLOW}Step 2: Creating virtual environment at '$VENV_DIR'${NC}"
if [ -d "$VENV_DIR" ]; then
    echo -e "${YELLOW}Virtual environment already exists. Skipping creation.${NC}"
else
    $PYTHON_PATH -m venv "$VENV_DIR"
    echo -e "${GREEN}✓ Virtual environment created${NC}"
fi

# Detect OS and set activation script
if [[ "$OSTYPE" == "msys" || "$OSTYPE" == "win32" ]]; then
    ACTIVATE_SCRIPT="$VENV_DIR/Scripts/activate.bat"
    echo -e "${GREEN}Detected Windows environment${NC}"
else
    ACTIVATE_SCRIPT="$VENV_DIR/bin/activate"
    echo -e "${GREEN}Detected Unix-like environment${NC}"
fi

# Upgrade pip and essential tools
echo -e "\n${YELLOW}Step 3: Upgrading pip and build tools${NC}"
source "$ACTIVATE_SCRIPT" 2>/dev/null || . "$ACTIVATE_SCRIPT"
python -m pip install --upgrade pip setuptools wheel build
echo -e "${GREEN}✓ pip and tools upgraded${NC}"

# Install core ML dependencies
echo -e "\n${YELLOW}Step 4: Installing core ML dependencies${NC}"
pip install --upgrade \
    numpy \
    scikit-learn \
    typing-extensions \
    pydantic \
    loguru
echo -e "${GREEN}✓ Core dependencies installed${NC}"

# Install async and type checking tools
echo -e "\n${YELLOW}Step 5: Installing development tools${NC}"
pip install --upgrade \
    mypy \
    pytest \
    pytest-asyncio \
    black \
    ruff \
    httpx
echo -e "${GREEN}✓ Development tools installed${NC}"

# Optional: PyTorch installation (commented out as it's large)
# echo -e "\n${YELLOW}Step 6: Installing PyTorch (optional)${NC}"
# pip install torch torchvision torchaudio --index-url https://download.pytorch.org/whl/cu118
# echo -e "${GREEN}✓ PyTorch installed${NC}"

# Create activation helper script
echo -e "\n${YELLOW}Step 6: Creating activation helper script${NC}"
if [[ "$OSTYPE" == "msys" || "$OSTYPE" == "win32" ]]; then
    cat > activate.bat << 'EOF'
@echo off
REM Activate Python 3.13 environment with JIT compilation flags
call .venv\Scripts\activate.bat
set PYTHONOPTIMIZE=2
set PYTHONJITCOUNTER=100
echo Python 3.13 environment activated with JIT enabled
python --version
EOF
    echo -e "${GREEN}✓ Created activate.bat${NC}"
else
    cat > activate.sh << 'EOF'
#!/bin/bash
# Activate Python 3.13 environment with JIT compilation flags
source .venv/bin/activate

# Enable JIT compilation and optimization
export PYTHONOPTIMIZE=2
export PYTHONJITCOUNTER=100

# Optional: Enable free-threaded mode for CPU-bound workloads
# Uncomment the next line and run with --disable-gil flag
# export PYTHONOPTIMIZE=2

echo "Python 3.13 environment activated with JIT enabled"
python --version
EOF
    chmod +x activate.sh
    echo -e "${GREEN}✓ Created activate.sh${NC}"
fi

# Generate requirements file
echo -e "\n${YELLOW}Step 7: Generating requirements.txt${NC}"
pip freeze > requirements-base.txt
echo -e "${GREEN}✓ Created requirements-base.txt${NC}"

# Display environment info
echo -e "\n${YELLOW}Step 8: Environment Summary${NC}"
echo "============================================="
source "$ACTIVATE_SCRIPT" 2>/dev/null || . "$ACTIVATE_SCRIPT"
echo -e "${GREEN}Python:${NC} $(python --version)"
echo -e "${GREEN}Pip:${NC} $(pip --version)"
echo -e "${GREEN}Location:${NC} $VENV_DIR"
echo -e "${GREEN}Packages:${NC} $(pip list | wc -l) installed"

echo -e "\n${GREEN}✓ Setup complete!${NC}"
echo -e "\nTo activate your environment, run:"
if [[ "$OSTYPE" == "msys" || "$OSTYPE" == "win32" ]]; then
    echo "  $ACTIVATE_SCRIPT"
    echo "  activate.bat"
else
    echo "  source $ACTIVATE_SCRIPT"
    echo "  ./activate.sh"
fi

echo -e "\n${YELLOW}Next steps:${NC}"
echo "1. Review pyproject.toml configuration"
echo "2. Install project dependencies: pip install -e ."
echo "3. Run tests: pytest"
echo "4. Start development!"
