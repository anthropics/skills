#!/usr/bin/env python3
"""
短信链接文书下载脚本
从法院送达短信中提取链接，下载相关PDF文书
"""

import re
import json
import os
import sys
import requests
from pathlib import Path
from urllib.parse import urlparse, parse_qs
from datetime import datetime


def extract_url_from_sms(sms_content: str) -> str | None:
    """从短信内容中提取URL"""
    url_pattern = r'https?://[^\s]+'
    matches = re.findall(url_pattern, sms_content)
    if matches:
        return matches[0]
    return None


def parse_url_params(url: str) -> dict | None:
    """解析URL中的参数（qdbh, sdbh, sdsin）"""
    try:
        parsed = urlparse(url)
        # 参数可能在hash中，也可能在search中
        if parsed.fragment and '?' in parsed.fragment:
            # #/pagesAjkj/app/wssd/index?qdbh=...
            query_part = parsed.fragment.split('?')[1]
            params = parse_qs(query_part)
        else:
            params = parse_qs(parsed.query)

        # 获取单个值（parse_qs返回列表）
        result = {
            'qdbh': params.get('qdbh', [None])[0],
            'sdbh': params.get('sdbh', [None])[0],
            'sdsin': params.get('sdsin', [None])[0]
        }

        if all(result.values()):
            return result
        return None
    except Exception as e:
        print(f"URL解析失败: {e}")
        return None


def fetch_file_list(params: dict) -> list:
    """调用API获取文件列表"""
    api_endpoint = "https://zxfw.court.gov.cn/yzw/yzw-zxfw-sdfw/api/v1/sdfw/getWsListBySdbhNew"

    headers = {
        'Content-Type': 'application/json',
        'Accept': 'application/json'
    }

    try:
        response = requests.post(api_endpoint, json=params, headers=headers, timeout=30)
        response.raise_for_status()

        result = response.json()
        if result.get('code') == 200 and isinstance(result.get('data'), list):
            return result['data']
        else:
            print(f"API返回错误: {result.get('msg', '未知错误')}")
            return []
    except requests.RequestException as e:
        print(f"API请求失败: {e}")
        return []


def download_file(file_url: str, filename: str, output_dir: Path) -> bool:
    """下载单个文件，同名文件大小不同时加 _2 后缀"""
    output_path = output_dir / filename

    # Check if file exists and is different (true duplicate with same name)
    if output_path.exists():
        existing_size = output_path.stat().st_size
        # We can't know the new file size before downloading, so download to temp
        import tempfile
        tmp_path = output_dir / f".tmp_{filename}"
        try:
            response = requests.get(file_url, timeout=60)
            response.raise_for_status()
            new_size = len(response.content)

            if new_size == existing_size:
                print(f"  - 跳过: {filename} (已存在，大小相同)")
                return True  # same file, skip

            # Different content, find a _N suffix
            base, ext = os.path.splitext(filename)
            n = 2
            while output_path.exists():
                new_name = f"{base}_{n}{ext}"
                output_path = output_dir / new_name
                # Check if this one also exists with same size
                if output_path.exists() and output_path.stat().st_size == new_size:
                    print(f"  - 跳过: {new_name} (已存在，大小相同)")
                    return True
                n += 1

            with open(output_path, 'wb') as f:
                f.write(response.content)
            print(f"  ✓ 已下载: {output_path.name} (同名异内容，已加后缀)")
            return True
        except requests.RequestException as e:
            print(f"  ✗ 下载失败: {filename} - {e}")
            return False
        finally:
            if tmp_path.exists():
                tmp_path.unlink()

    try:
        response = requests.get(file_url, timeout=60)
        response.raise_for_status()

        with open(output_path, 'wb') as f:
            f.write(response.content)

        print(f"  ✓ 已下载: {filename}")
        return True
    except requests.RequestException as e:
        print(f"  ✗ 下载失败: {filename} - {e}")
        return False


def extract_case_number(sms_content: str) -> str | None:
    """从短信中提取案件号"""
    # 匹配案件号格式如：(2026)浙0381执3963号
    pattern = r'[\(（]?\d{4}[\)）]?[\u4e00-\u9fa5]+\d+[\u4e00-\u9fa5]*\d*号'
    match = re.search(pattern, sms_content)
    if match:
        # 清理格式，移除括号
        case_num = match.group()
        case_num = re.sub(r'[\(（）]', '', case_num)
        return case_num
    return None


def extract_court_name(sms_content: str) -> str | None:
    """从短信中提取法院名称"""
    # 匹配格式如：【瑞安市人民法院】
    pattern = r'【(.+人民法院|.+法院)】'
    match = re.search(pattern, sms_content)
    if match:
        return match.group(1)
    return None


def main(sms_content: str = None, output_base: Path = None) -> dict:
    """主函数，返回结构化JSON结果"""
    # 如果没有提供短信内容，从命令行参数获取
    if sms_content is None:
        if len(sys.argv) < 2:
            print("使用方式: python download_sms_docs.py <短信内容>")
            print("或直接粘贴短信内容作为参数")
            sys.exit(1)
        sms_content = sys.argv[1]

    # 默认输出目录
    if output_base is None:
        output_base = Path.home() / "Desktop" / "文书下载"

    print("=" * 50)
    print("短信链接文书下载工具")
    print("=" * 50)

    # 1. 提取URL
    url = extract_url_from_sms(sms_content)
    if not url:
        print("错误: 未找到短信中的链接")
        sys.exit(1)
    print(f"提取到链接: {url}")

    # 2. 解析参数
    params = parse_url_params(url)
    if not params:
        print("错误: 无法解析链接参数")
        sys.exit(1)
    print(f"解析参数: qdbh={params['qdbh'][:8]}..., sdbh={params['sdbh'][:8]}...")

    # 3. 提取案件号作为子目录名
    case_number = extract_case_number(sms_content)
    court_name = extract_court_name(sms_content)

    if case_number:
        output_dir = output_base / case_number
    else:
        output_dir = output_base / f"未知案件_{datetime.now().strftime('%Y%m%d%H%M%S')}"

    # 创建输出目录
    output_dir.mkdir(parents=True, exist_ok=True)
    print(f"输出目录: {output_dir}")

    # 4. 获取文件列表
    print("\n正在获取文书列表...")
    files = fetch_file_list(params)

    if not files:
        print("未获取到任何文书")
        sys.exit(0)

    print(f"获取到 {len(files)} 个文书:")
    for f in files:
        print(f"  - {f.get('c_wsmc', '未命名')}.{f.get('c_wjgs', 'pdf')}")

    # 5. 下载文件
    print("\n开始下载...")
    success_count = 0
    fail_count = 0
    downloaded_files = []
    document_types = []

    for i, file_info in enumerate(files, 1):
        file_name = file_info.get('c_wsmc', f'文书_{i}')
        file_ext = file_info.get('c_wjgs', 'pdf')
        file_url = file_info.get('wjlj', '')

        full_filename = f"{file_name}.{file_ext}"

        print(f"\n[{i}/{len(files)}] {full_filename}")

        if download_file(file_url, full_filename, output_dir):
            success_count += 1
            downloaded_files.append(str(output_dir / full_filename))
            document_types.append(file_name)
        else:
            fail_count += 1

    # 6. 总结
    print("\n" + "=" * 50)
    print(f"下载完成: 成功 {success_count}, 失败 {fail_count}")
    print(f"文件位置: {output_dir}")
    print("=" * 50)

    # 7. 输出JSON供后续处理
    result = {
        "success": success_count > 0,
        "output_dir": str(output_dir),
        "files": downloaded_files,
        "case_number": case_number,
        "court": court_name,
        "document_types": document_types,
        "sms_content": sms_content
    }

    print("\n__JSON_OUTPUT__")
    print(json.dumps(result, ensure_ascii=False))
    print("__JSON_OUTPUT_END__")

    return result


if __name__ == "__main__":
    main()