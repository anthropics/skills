#!/usr/bin/env python3
"""
ワークショップ参加者スプレッドシート（CSV）パーサー

Usage:
    python parse_spreadsheet.py <csv_file_path>
    python parse_spreadsheet.py --url <google_spreadsheet_csv_url>

Output:
    JSON形式で参加者リストを出力
"""

import csv
import json
import sys
import urllib.request
import urllib.error
from pathlib import Path
from typing import List, Dict, Optional
import io


def parse_csv_content(content: str) -> List[Dict[str, str]]:
    """CSVコンテンツをパースして参加者リストを返す"""
    participants = []

    # BOMを除去
    if content.startswith('\ufeff'):
        content = content[1:]

    reader = csv.DictReader(io.StringIO(content))

    # ヘッダーの正規化（様々な表記に対応）
    name_keys = ['名前', 'name', 'Name', '氏名', '参加者名']
    profession_keys = ['職業', 'profession', 'Profession', '職種', '仕事', 'job', 'Job']
    pain_keys = ['ペイン', 'pain', 'Pain', '課題', '悩み', '困っていること', 'problem', 'Problem']

    def find_key(fieldnames: List[str], candidates: List[str]) -> Optional[str]:
        for candidate in candidates:
            if candidate in fieldnames:
                return candidate
        return None

    fieldnames = reader.fieldnames or []
    name_key = find_key(fieldnames, name_keys)
    profession_key = find_key(fieldnames, profession_keys)
    pain_key = find_key(fieldnames, pain_keys)

    if not all([name_key, profession_key, pain_key]):
        missing = []
        if not name_key:
            missing.append("名前")
        if not profession_key:
            missing.append("職業")
        if not pain_key:
            missing.append("ペイン")
        raise ValueError(f"必須列が見つかりません: {', '.join(missing)}\n検出された列: {fieldnames}")

    for row in reader:
        name = row.get(name_key, '').strip()
        profession = row.get(profession_key, '').strip()
        pain = row.get(pain_key, '').strip()

        # 空行をスキップ
        if not name or not profession:
            continue

        participants.append({
            'name': name,
            'profession': profession,
            'pain': pain if pain else '特になし'
        })

    return participants


def fetch_from_url(url: str) -> str:
    """URLからCSVコンテンツを取得"""
    # GoogleスプレッドシートURLをCSVエクスポートURLに変換
    if 'docs.google.com/spreadsheets' in url:
        if '/export?' not in url:
            # 共有URLからIDを抽出
            import re
            match = re.search(r'/d/([a-zA-Z0-9-_]+)', url)
            if match:
                spreadsheet_id = match.group(1)
                url = f"https://docs.google.com/spreadsheets/d/{spreadsheet_id}/export?format=csv"

    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
        with urllib.request.urlopen(req, timeout=30) as response:
            return response.read().decode('utf-8')
    except urllib.error.URLError as e:
        raise RuntimeError(f"URLからの取得に失敗しました: {e}")


def main():
    if len(sys.argv) < 2:
        print("Usage: python parse_spreadsheet.py <csv_file_path>")
        print("       python parse_spreadsheet.py --url <google_spreadsheet_url>")
        sys.exit(1)

    try:
        if sys.argv[1] == '--url':
            if len(sys.argv) < 3:
                print("Error: URLを指定してください")
                sys.exit(1)
            content = fetch_from_url(sys.argv[2])
        else:
            file_path = Path(sys.argv[1])
            if not file_path.exists():
                print(f"Error: ファイルが見つかりません: {file_path}")
                sys.exit(1)
            content = file_path.read_text(encoding='utf-8')

        participants = parse_csv_content(content)

        # 結果を出力
        result = {
            'total_participants': len(participants),
            'participants': participants
        }

        print(json.dumps(result, ensure_ascii=False, indent=2))

    except Exception as e:
        print(json.dumps({
            'error': str(e),
            'success': False
        }, ensure_ascii=False, indent=2))
        sys.exit(1)


if __name__ == '__main__':
    main()
