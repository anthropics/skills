#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Privacy Protection Utilities for RCS Message Skill
"""

import re

def mask_phone_number(phone: str) -> str:
    """加密手机号码，保留前三后二，中间用*号替换"""
    # 去掉+86前缀（如果存在）
    if phone.startswith('+86'):
        digits = phone[3:]
    else:
        digits = phone
    
    # 验证是否为11位数字
    if len(digits) == 11 and digits.isdigit():
        return f"{digits[:3]}******{digits[-2:]}"
    else:
        # 如果格式不对，返回原始号码的掩码版本
        return "***********"

def mask_url(url: str) -> str:
    """加密URL，保留域名，隐藏路径和参数"""
    try:
        import urllib.parse
        parsed = urllib.parse.urlparse(url)
        if parsed.netloc:
            # 保留协议和域名，路径和参数用****替换
            return f"{parsed.scheme}://{parsed.netloc}/****"
        else:
            return "****"
    except:
        return "****"

def protect_sensitive_info(text: str) -> str:
    """保护敏感信息：加密手机号码和URL"""
    if not text:
        return text
    
    # 加密手机号码（包括+86前缀的）
    phone_pattern = r'(\+86)?1[3-9]\d{9}'
    def replace_phone(match):
        full_match = match.group(0)
        return mask_phone_number(full_match)
    
    protected_text = re.sub(phone_pattern, replace_phone, text)
    
    # 加密URL
    url_pattern = r'https?://[^\s<>"{}|\\^`\[\]]+'
    protected_text = re.sub(url_pattern, lambda m: mask_url(m.group(0)), protected_text)
    
    return protected_text