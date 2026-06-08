#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RCS Message Group Send Script
安全限制：号码数量、内容长度、发送频率
"""

import os
import sys
import json
import time
import hashlib
import argparse
from typing import List, Optional, Dict, Any
import requests

# 导入隐私保护功能
# 导入隐私保护函数
import os
import sys
sys.path.append(os.path.dirname(__file__))
from privacy_protect import protect_sensitive_info

# 安全限制配置
MAX_PHONE_NUMBERS = 100  # 限制为100个号码（远低于API的1000上限）
MAX_MESSAGE_LENGTH = 1000  # 最大消息长度
MIN_INTERVAL_SECONDS = 60  # 最小发送间隔（60秒）
RATE_LIMIT_FILE = "/tmp/5g_messaging_last_send.txt"

# API配置 - SERVER_ROOT 固定为 5g.fontdo.com
SERVER_ROOT = "https://5g.fontdo.com"
APP_ID = None
APP_SECRET = None

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

def get_app_credentials():
    """获取APP ID和SECRET，优先从环境变量，否则交互式输入"""
    global APP_ID, APP_SECRET
    
    # 先尝试从环境变量获取
    env_app_id = os.getenv("FIVE_G_APP_ID")
    env_app_secret = os.getenv("FIVE_G_APP_SECRET")
    
    if env_app_id and env_app_secret:
        APP_ID = env_app_id
        APP_SECRET = env_app_secret
        return True
    
    # 如果环境变量不存在，提示用户输入
    print("⚠️  首次使用5G消息服务，请输入您的认证信息:")
    print("   (这些信息将用于本次会话，建议后续设置环境变量)")
    
    try:
        app_id_input = input("请输入 APP ID: ").strip()
        app_secret_input = input("请输入 APP SECRET: ").strip()
        
        if not app_id_input or not app_secret_input:
            print("❌ APP ID 和 APP SECRET 不能为空", file=sys.stderr)
            return False
        
        APP_ID = app_id_input
        APP_SECRET = app_secret_input
        print("✅ 认证信息已保存到当前会话")
        return True
        
    except KeyboardInterrupt:
        print("\n❌ 用户取消输入", file=sys.stderr)
        return False
    except EOFError:
        print("\n❌ 输入错误", file=sys.stderr)
        return False

def get_last_send_time() -> float:
    """获取上次发送时间"""
    try:
        with open(RATE_LIMIT_FILE, 'r') as f:
            return float(f.read().strip())
    except (FileNotFoundError, ValueError):
        return 0

def update_last_send_time():
    """更新上次发送时间"""
    with open(RATE_LIMIT_FILE, 'w') as f:
        f.write(str(time.time()))

def validate_phone_numbers(numbers: List[str]) -> List[str]:
    """验证电话号码格式"""
    validated = []
    for number in numbers:
        # 验证：必须以+86开头，后面跟11位数字（总共14位）
        if number.startswith('+86') and len(number) == 14 and number[3:].isdigit() and len(number[3:]) == 11:
            validated.append(number)
        else:
            print(f"警告: 跳过无效号码 {number}", file=sys.stderr)
    
    if len(validated) == 0:
        raise ValueError("没有有效的电话号码")
    
    if len(validated) > MAX_PHONE_NUMBERS:
        raise ValueError(f"电话号码数量超过限制 ({len(validated)} > {MAX_PHONE_NUMBERS})")
    
    return validated[:MAX_PHONE_NUMBERS]

def validate_message_content(text: str) -> str:
    """验证消息内容"""
    if not text or not text.strip():
        raise ValueError("消息内容不能为空")
    
    if len(text) > MAX_MESSAGE_LENGTH:
        raise ValueError(f"消息长度超过限制 ({len(text)} > {MAX_MESSAGE_LENGTH})")
    
    return text.strip()

def check_rate_limit():
    """检查发送频率限制"""
    last_send = get_last_send_time()
    current_time = time.time()
    
    if current_time - last_send < MIN_INTERVAL_SECONDS:
        wait_time = MIN_INTERVAL_SECONDS - (current_time - last_send)
        raise ValueError(f"发送频率限制，请等待 {wait_time:.1f} 秒后再试")

def generate_signature(method: str, uri: str, timestamp: str) -> str:
    """生成SHA256签名"""
    signature_string = f"{method}{uri}{APP_ID}{APP_SECRET}{timestamp}"
    return hashlib.sha256(signature_string.encode('utf-8')).hexdigest()

def send_group_message(
    numbers: List[str], 
    message_type: str = "TEXT",
    text: Optional[str] = None,
    template_id: Optional[str] = None,
    params: Optional[List[Dict[str, str]]] = None,
    fallback_aim: Optional[Dict[str, Any]] = None,
    fallback_mms: Optional[Dict[str, Any]] = None,
    fallback_sms: Optional[Dict[str, Any]] = None
) -> Dict[str, Any]:
    """发送群发消息"""
    
    # 验证输入
    validated_numbers = validate_phone_numbers(numbers)
    
    if message_type == "TEXT":
        if not text:
            raise ValueError("TEXT类型必须提供text参数")
        validated_text = validate_message_content(text)
    elif message_type in ["RCS", "AIM", "MMS", "SMS"]:
        if not template_id:
            raise ValueError(f"{message_type}类型必须提供templateId参数")
    else:
        raise ValueError(f"不支持的消息类型: {message_type}")
    
    # 检查频率限制
    check_rate_limit()
    
    # 构建请求体
    payload = {
        "templateType": message_type,
        "numbers": validated_numbers
    }
    
    if message_type == "TEXT":
        payload["text"] = validated_text
    else:
        payload["templateId"] = template_id
        if params:
            payload["params"] = params
    
    # 添加回落配置
    if fallback_aim:
        payload["fallbackAim"] = fallback_aim
    if fallback_mms:
        payload["fallbackMms"] = fallback_mms
    if fallback_sms:
        payload["fallbackSms"] = fallback_sms
    
    # 准备API请求
    url = f"{SERVER_ROOT}/messenger/api/v1/group/send"
    uri = "/messenger/api/v1/group/send"
    timestamp = str(int(time.time() * 1000))
    signature = generate_signature("POST", uri, timestamp)
    
    headers = {
        "AppId": APP_ID,
        "Timestamp": timestamp,
        "Signature": signature,
        "Content-Type": "application/json"
    }
    
    try:
        response = requests.post(url, json=payload, headers=headers, timeout=30)
        response.raise_for_status()
        
        # 更新发送时间戳
        update_last_send_time()
        
        return {
            "success": True,
            "response": response.json(),
            "sent_numbers": validated_numbers,  # 返回实际发送的号码列表
            "sent_count": len(validated_numbers),
            "message_type": message_type,
            "message": validated_text if message_type == "TEXT" else None
        }
        
    except requests.exceptions.RequestException as e:
        return {
            "success": False,
            "error": str(e),
            "sent_count": 0,
            "message_type": message_type
        }

def main():
    parser = argparse.ArgumentParser(description="RCS消息群发工具")
    parser.add_argument("-n", "--numbers", required=True, 
                       help="电话号码列表，用逗号分隔 (例: +8613900001234,+8613900002234)")
    parser.add_argument("-m", "--message", 
                       help="发送的文本内容 (TEXT类型必需)")
    parser.add_argument("-t", "--type", default="TEXT", choices=["TEXT", "RCS", "AIM", "MMS", "SMS"],
                       help="消息类型，默认TEXT")
    parser.add_argument("--template-id", 
                       help="模板ID (非TEXT类型必需)")
    parser.add_argument("--dry-run", action="store_true",
                       help="仅验证参数，不实际发送")
    
    args = parser.parse_args()
    
    # 解析电话号码
    phone_numbers = [num.strip() for num in args.numbers.split(',') if num.strip()]
    
    if not phone_numbers:
        print("错误: 必须提供至少一个电话号码", file=sys.stderr)
        sys.exit(1)
    
    # 获取认证信息
    if not get_app_credentials():
        sys.exit(1)
    
    try:
        if args.dry_run:
            # 仅验证参数
            validated_numbers = validate_phone_numbers(phone_numbers)
            if args.type == "TEXT":
                if not args.message:
                    raise ValueError("TEXT类型必须提供消息内容")
                validate_message_content(args.message)
            elif not args.template_id:
                raise ValueError(f"{args.type}类型必须提供模板ID")
            
            # 加密显示号码
            masked_numbers = [mask_phone_number(num) for num in validated_numbers]
            
            print(f"✅ 参数验证通过")
            print(f"   发送号码: {len(validated_numbers)} 个 ({', '.join(masked_numbers)})")
            print(f"   消息类型: {args.type}")
            if args.type == "TEXT":
                print(f"   消息长度: {len(args.message)} 字符")
            else:
                print(f"   模板ID: {args.template_id}")
            print(f"   API服务器: {SERVER_ROOT}")
            print(f"   安全限制: 最大 {MAX_PHONE_NUMBERS} 个号码, {MAX_MESSAGE_LENGTH} 字符, {MIN_INTERVAL_SECONDS}秒间隔")
            
        else:
            # 实际发送
            result = send_group_message(
                numbers=phone_numbers,
                message_type=args.type,
                text=args.message,
                template_id=args.template_id
            )
            
            if result["success"]:
                # 加密显示成功发送的号码
                masked_numbers = [mask_phone_number(num) for num in result['sent_numbers']]
                
                # 加密任务ID中的敏感信息
                task_id = result['response'].get('data', 'N/A')
                protected_task_id = protect_sensitive_info(task_id)
                
                print(f"【蜂动Claw】✅ **发送成功**")
                print(f"   发送号码: {result['sent_count']} 个 ({', '.join(masked_numbers)})")
                if result['message']:
                    protected_message = protect_sensitive_info(result['message'])
                    print(f"   消息内容: {protected_message[:50]}{'...' if len(protected_message) > 50 else ''}")
                print(f"   任务ID: {protected_task_id}")
            else:
                print(f"❌ 发送失败: {result['error']}", file=sys.stderr)
                sys.exit(1)
                
    except ValueError as e:
        print(f"❌ 参数错误: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"❌ 未知错误: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()