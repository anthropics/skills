"""
此文件为兼容性转发代理。
真正的全局配置已移至：finance-assistant/config.py

本文件通过 importlib 直接加载根目录的全局配置，
保持现有脚本的 `from config import ...` 语句无需任何改动。
"""
import sys
import os
import importlib.util

# 定位到 finance-assistant/ 根目录下的全局 config.py
# 层级：scripts/ → post-market-review/ → finance-assistant/
_SCRIPTS_DIR = os.path.dirname(os.path.abspath(__file__))          # .../scripts
_SKILL_DIR   = os.path.dirname(_SCRIPTS_DIR)                       # .../post-market-review
_ROOT_DIR    = os.path.dirname(_SKILL_DIR)                         # .../finance-assistant
_ROOT_CONFIG = os.path.join(_ROOT_DIR, "config.py")

# 用 importlib 直接加载，避免命名冲突
_spec = importlib.util.spec_from_file_location("_global_config", _ROOT_CONFIG)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

# 透传所有公共变量到本模块命名空间
BASE_DIR        = _mod.BASE_DIR
OUTPUT_DIR      = _mod.OUTPUT_DIR
REPORTS_DIR     = _mod.REPORTS_DIR
WATCHLIST_ETFS  = _mod.WATCHLIST_ETFS
ETF_NAME_MAP    = _mod.ETF_NAME_MAP
INDEX_LIST      = _mod.INDEX_LIST
SCHEDULE_TIMES  = _mod.SCHEDULE_TIMES
THRESHOLDS      = _mod.THRESHOLDS
