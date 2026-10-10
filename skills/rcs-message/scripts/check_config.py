#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
5G Messaging 配置检查工具
"""

import os
import sys
from pathlib import Path

def check_credentials():
    """检查凭证配置"""
    # 检查会话凭证文件
    session_dir = Path.home() / ".5g_messaging"
    session_dir.mkdir(exist_ok=True)
    
    cred_file = session_dir / "credentials.json"
    
    if cred_file.exists():
        print("✅ 会话凭证已配置")
        print(f"   凭证文件: {cred_file}")
        return True
    else:
        print("⚠️  会话凭证未配置")
        print("   首次使用时会提示输入APP_ID和APP_SECRET")
        return False

def main():
    print("5G Messaging 配置检查")
    print("=" * 40)
    
    # 检查服务器地址（硬编码）
    print("✅ 服务器地址: https://5g.fontdo.com")
    
    # 检查凭证
    check_credentials()
    
    print("\n使用说明:")
    print("- 首次使用会提示输入APP_ID和APP_SECRET")
    print("- 凭证会保存在 ~/.5g_messaging/credentials.json")
    print("- 后续使用会自动读取保存的凭证")

if __name__ == "__main__":
    main()