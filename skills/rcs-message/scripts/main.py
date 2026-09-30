#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RCS Message Main Entry Point
处理用户自然语言输入并调用发送脚本
"""

import os
import sys
import json
import argparse
from pathlib import Path
from handle_user_input import parse_user_message

def mask_phone_number(phone: str) -> str:
    """将手机号码加密为前三后二格式，如 137******01"""
    # 移除+86前缀（如果存在）
    if phone.startswith('+86'):
        clean_phone = phone[3:]
    else:
        clean_phone = phone
    
    # 验证是否为11位数字
    if len(clean_phone) == 11 and clean_phone.isdigit():
        return f"{clean_phone[:3]}******{clean_phone[-2:]}"
    else:
        # 如果格式不正确，返回原号码（或部分隐藏）
        return phone

def get_session_config_dir():
    """获取会话配置目录"""
    config_dir = Path.home() / ".config" / "moltbot" / "rcs-message"
    config_dir.mkdir(parents=True, exist_ok=True)
    return config_dir

def get_session_credential_file(session_id: str):
    """获取会话凭证文件路径"""
    config_dir = get_session_config_dir()
    return config_dir / f"{session_id}.json"

def load_session_credentials(session_id: str):
    """从会话文件加载凭证"""
    credential_file = get_session_credential_file(session_id)
    if credential_file.exists():
        try:
            with open(credential_file, 'r') as f:
                return json.load(f)
        except (json.JSONDecodeError, IOError):
            pass
    return None

def save_session_credentials(session_id: str, app_id: str, app_secret: str):
    """保存会话凭证到文件"""
    credential_file = get_session_credential_file(session_id)
    credentials = {
        "app_id": app_id,
        "app_secret": app_secret
    }
    with open(credential_file, 'w') as f:
        json.dump(credentials, f)

def main():
    parser = argparse.ArgumentParser(description="RCS消息群发主入口")
    parser.add_argument("user_input", help="用户输入的自然语言消息")
    parser.add_argument("--session-id", default="default", help="会话ID，默认为'default'")
    parser.add_argument("--debug", action="store_true", help="启用调试模式")
    
    args = parser.parse_args()
    
    # 解析用户输入
    parsed_data = parse_user_message(args.user_input)
    if not parsed_data:
        print("❌ 无法解析消息格式，请使用：'群发消息给13900001234 内容是测试消息'", file=sys.stderr)
        sys.exit(1)
    
    if args.debug:
        print(f"🔍 解析结果: {parsed_data}", file=sys.stderr)
    
    # 获取APP凭证（优先使用会话凭证，然后尝试环境变量，最后交互式输入）
    session_credentials = load_session_credentials(args.session_id)
    if session_credentials:
        app_id = session_credentials.get("app_id")
        app_secret = session_credentials.get("app_secret")
        if args.debug:
            print(f"✅ 使用会话凭证 (session: {args.session_id})", file=sys.stderr)
    else:
        # 尝试从环境变量获取
        app_id = os.getenv("FIVE_G_APP_ID")
        app_secret = os.getenv("FIVE_G_APP_SECRET")
        if app_id and app_secret:
            # 保存到会话文件
            save_session_credentials(args.session_id, app_id, app_secret)
            if args.debug:
                print(f"✅ 使用环境变量凭证并保存到会话 (session: {args.session_id})", file=sys.stderr)
        else:
            # 交互式输入
            print("【蜂动Claw】首次使用需要认证信息。")
            print("**需要输入：**")
            print("1. **APP ID**")
            print("2. **APP SECRET**")
            print("这些是蜂动科技的 API 凭证。你有吗？")
            print("如果没有，需要：")
            print("1. 注册蜂动科技5G消息服务")
            print("2. 创建应用获取 APP_ID 和 APP_SECRET")
            print("**你有凭证吗？**")
            try:
                app_id = input("请输入 APP ID: ").strip()
                app_secret = input("请输入 APP SECRET: ").strip()
            except EOFError:
                print("\n❌ 输入错误", file=sys.stderr)
                sys.exit(1)
            
            if not app_id or not app_secret:
                print("❌ APP ID和APP SECRET不能为空", file=sys.stderr)
                sys.exit(1)
            
            # 保存到会话文件
            save_session_credentials(args.session_id, app_id, app_secret)
            print(f"✅ 凭证已保存到会话 '{args.session_id}'，下次使用将自动加载")
    
    # 设置环境变量供send.py使用
    os.environ["FIVE_G_APP_ID"] = app_id
    os.environ["FIVE_G_APP_SECRET"] = app_secret
    
    # 导入并直接调用send.py的功能
    sys.path.insert(0, os.path.dirname(__file__))
    try:
        from send import send_group_message
        
        result = send_group_message(
            numbers=parsed_data["numbers"],
            message_type="TEXT",
            text=parsed_data["message"]
        )
        
        if result["success"]:
            # 加密显示成功发送的号码
            masked_numbers = [mask_phone_number(num) for num in result['sent_numbers']]
            
            print(f"【蜂动Claw】✅ **发送成功**")
            print(f"   发送号码: {result['sent_count']} 个 ({', '.join(masked_numbers)})")
            if result['message']:
                print(f"   消息内容: {result['message'][:50]}{'...' if len(result['message']) > 50 else ''}")
            print(f"   任务ID: {result['response'].get('data', 'N/A')}")
        else:
            print(f"❌ 发送失败: {result['error']}", file=sys.stderr)
            sys.exit(1)
            
    except Exception as e:
        print(f"❌ 发送错误: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()