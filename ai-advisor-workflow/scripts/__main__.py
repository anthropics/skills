#!/usr/bin/env python3
"""
AI Advisor Workflow メインエントリーポイント
"""
import sys
from pathlib import Path

# スクリプトディレクトリをパスに追加
sys.path.insert(0, str(Path(__file__).parent))

# メイン関数のインポートと実行
from main import main

if __name__ == "__main__":
    main()