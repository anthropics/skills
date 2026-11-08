#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
5G Messaging - 用户输入解析器
提供parse_user_message函数用于解析用户输入
"""

import re
from typing import List, Optional, Dict, Any

def extract_numbers_from_text(text: str) -> List[str]:
    """从文本中提取手机号码"""
    # 匹配中国手机号码格式（包括+86前缀）
    phone_pattern = r'(?:\+86)?1[3-9]\d{9}'
    phones = re.findall(phone_pattern, text)
    
    # 标准化号码格式（添加+86前缀）
    normalized_phones = []
    for phone in phones:
        if phone.startswith('+86'):
            normalized_phones.append(phone)
        else:
            normalized_phones.append(f'+86{phone}')
    
    return normalized_phones

def extract_message_content(text: str, numbers: List[str]) -> str:
    """从文本中提取消息内容，移除号码部分"""
    content = text
    
    # 移除号码
    for number in numbers:
        content = content.replace(number, '')
        # 移除不带+86的版本
        if number.startswith('+86'):
            content = content.replace(number[3:], '')
    
    # 移除"群发消息"、"转发消息"等关键词
    keywords = ['群发消息', '转发消息', '群发', '转发', '发送', '给', '内容是', '内容']
    for keyword in keywords:
        content = content.replace(keyword, '')
    
    # 清理多余的空格和标点
    content = re.sub(r'[：:\s]+', ' ', content).strip()
    content = re.sub(r'^[，。！？\s]+|[，。！？\s]+$', '', content)
    
    return content

def is_group_send_intent(user_input: str) -> bool:
    """判断是否为群发/转发消息意图"""
    group_keywords = ['群发消息', '转发消息', '群发', '批量发送', '给多人发']
    return any(keyword in user_input for keyword in group_keywords)

def parse_user_message(user_input: str) -> Optional[Dict[str, Any]]:
    """解析用户输入，返回结构化数据"""
    if not is_group_send_intent(user_input):
        return None
    
    # 提取号码
    numbers = extract_numbers_from_text(user_input)
    if not numbers:
        return None
    
    # 提取消息内容
    message_content = extract_message_content(user_input, numbers)
    if not message_content:
        return None
    
    return {
        "action": "broadcast" if "群发" in user_input else "forward",
        "numbers": numbers[:100],  # 限制最多100个号码
        "message": message_content,
        "original_input": user_input
    }