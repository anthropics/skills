#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
会话凭证管理模块
用于存储和管理用户的APP_ID和APP_SECRET
"""

import os
import json
import hashlib
from pathlib import Path

# 会话凭证存储目录
CREDENTIALS_DIR = Path.home() / ".config" / "moltbot" / "5g_messaging"
CREDENTIALS_DIR.mkdir(parents=True, exist_ok=True)

def get_session_key(session_id: str) -> str:
    """根据会话ID生成唯一的会话密钥"""
    return hashlib.sha256(session_id.encode()).hexdigest()[:16]

def save_credentials(session_id: str, app_id: str, app_secret: str):
    """保存会话凭证"""
    session_key = get_session_key(session_id)
    cred_file = CREDENTIALS_DIR / f"{session_key}.json"
    
    credentials = {
        "app_id": app_id,
        "app_secret": app_secret,
        "session_id": session_id,
        "saved_at": __import__('time').time()
    }
    
    with open(cred_file, 'w') as f:
        json.dump(credentials, f)

def load_credentials(session_id: str) -> dict:
    """加载会话凭证"""
    session_key = get_session_key(session_id)
    cred_file = CREDENTIALS_DIR / f"{session_key}.json"
    
    if not cred_file.exists():
        return None
    
    try:
        with open(cred_file, 'r') as f:
            return json.load(f)
    except (json.JSONDecodeError, IOError):
        return None

def has_saved_credentials(session_id: str) -> bool:
    """检查是否已有保存的凭证"""
    return load_credentials(session_id) is not None

def clear_credentials(session_id: str):
    """清除会话凭证"""
    session_key = get_session_key(session_id)
    cred_file = CREDENTIALS_DIR / f"{session_key}.json"
    if cred_file.exists():
        cred_file.unlink()