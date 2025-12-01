---
name: contract-analyzer
description: "日本語契約書PDFを分析し、重要項目を構造化して抽出。契約当事者、金額、期間、支払条件、責任範囲、リスク事項などを表形式で整理し、リスクレベルを3段階評価して警告を付与します。"
---

# Contract Analyzer Skill

## Overview
日本語契約書PDFを分析し、重要項目を構造化して抽出するスキル。契約当事者、金額、期間、支払条件、責任範囲、リスク事項などの主要項目を表形式で整理し、リスクレベルを3段階評価(高・中・低)して警告を付与します。

## 対象契約書類型
- 業務委託契約
- 秘密保持契約(NDA)
- 売買契約
- その他商取引契約(10ページ程度まで)

## 抽出項目一覧

### 基本項目
1. **契約当事者** - 委託者/受託者、売主/買主など
2. **契約金額** - 総額、単価、その他金銭条件
3. **契約期間** - 開始日、終了日、期間
4. **支払条件** - 支払時期、方法、条件
5. **責任範囲** - 各当事者の義務と責任
6. **リスク事項** - 一般的なリスク条項

### 重要追加項目(優先度:高)
7. **契約解除条件** - 解除事由、通知期間、効果
8. **損害賠償の上限額** - 上限設定の有無、金額、範囲
9. **知的財産権の帰属** - 成果物の権利帰属、利用範囲

### 重要追加項目(優先度:中)
10. **秘密保持義務** - 範囲、期間、例外事項
11. **準拠法・管轄裁判所** - 適用法、専属管轄の有無
12. **契約の自動更新条項** - 更新条件、通知期限

## リスク評価基準

### 高リスク(⚠️ 警告)
以下の条件に該当する場合:
- 損害賠償の上限設定がない、または過大
- 一方的に不利な解除条件
- 知的財産権の全面譲渡(特に対価不明確)
- 無制限の秘密保持義務期間
- 曖昧で包括的な責任条項
- 自動更新かつ短い解約通知期間
- 不利な準拠法・遠方の専属管轄

### 中リスク(⚡注意)
以下の条件に該当する場合:
- 損害賠償上限が高額(契約金額の2倍超)
- 解除条件が厳しいが合理的範囲
- 知的財産権の共有(利用範囲不明確)
- 秘密保持期間が5年超
- 責任範囲が広いが業界標準的
- 自動更新だが通知期間が妥当(3ヶ月程度)

### 低リスク(✓ 標準的)
以下の条件に該当する場合:
- 損害賠償上限が明確かつ妥当
- 双方公平な解除条件
- 知的財産権の帰属が明確
- 秘密保持期間が適切(3-5年)
- 責任範囲が具体的で限定的
- 更新条件が明確
- 準拠法・管轄が妥当

## 実装手順

### STEP 1: PDFの読み込みと解析
```python
import openpyxl
from openpyxl.styles import Font, PatternFill, Alignment, Border, Side
from datetime import datetime
import re

# PDFからテキストを抽出(既にコンテキストにある場合はそれを使用)
# Claude can see PDF content directly in the conversation
```

### STEP 2: 項目抽出のプロンプト設計
契約書のテキストを読み込んだ後、以下の構造で情報を抽出:

```
契約書から以下の項目を抽出してください:

【基本情報】
- 契約当事者(甲/乙の正式名称、代表者)
- 契約金額(総額、単価、消費税の扱い)
- 契約期間(開始日、終了日、自動更新の有無)
- 支払条件(時期、方法、支払サイト)
- 責任範囲(各当事者の主要義務)

【重要条項】
- 契約解除条件(解除事由、通知期間、解除の効果)
- 損害賠償(上限額の有無、範囲、計算方法)
- 知的財産権(成果物の帰属、利用許諾の範囲)
- 秘密保持義務(対象情報、保持期間、例外事項)
- 準拠法・管轄(準拠法、管轄裁判所、専属か合意か)
- 自動更新(更新条件、解約通知期限)

【リスク評価】
各項目について、リスクレベル(高・中・低)を評価し、
高リスクと判断した理由を簡潔に記載してください。
```

### STEP 3: Excel出力フォーマット

#### シート1: 契約概要
| 項目 | 内容 | リスクレベル | 備考・警告 |
|------|------|------------|----------|

#### シート2: リスクサマリー
リスクレベル別の一覧と推奨アクション

### STEP 4: Excelファイルの作成コード

```python
def create_contract_analysis_excel(contract_data, output_path):
    """
    契約書分析結果をExcelファイルとして出力
    
    Args:
        contract_data: 抽出した契約情報の辞書
        output_path: 出力ファイルパス
    """
    wb = openpyxl.Workbook()
    
    # スタイル定義
    header_fill = PatternFill(start_color="366092", end_color="366092", fill_type="solid")
    header_font = Font(color="FFFFFF", bold=True, size=11)
    
    risk_high_fill = PatternFill(start_color="FF6B6B", end_color="FF6B6B", fill_type="solid")
    risk_medium_fill = PatternFill(start_color="FFD93D", end_color="FFD93D", fill_type="solid")
    risk_low_fill = PatternFill(start_color="95E1D3", end_color="95E1D3", fill_type="solid")
    
    border = Border(
        left=Side(style='thin'),
        right=Side(style='thin'),
        top=Side(style='thin'),
        bottom=Side(style='thin')
    )
    
    # シート1: 契約概要
    ws1 = wb.active
    ws1.title = "契約概要"
    
    headers = ["分類", "項目", "内容", "リスクレベル", "警告・備考"]
    ws1.append(headers)
    
    # ヘッダーのスタイル設定
    for cell in ws1[1]:
        cell.fill = header_fill
        cell.font = header_font
        cell.alignment = Alignment(horizontal="center", vertical="center")
        cell.border = border
    
    # 列幅設定
    ws1.column_dimensions['A'].width = 12
    ws1.column_dimensions['B'].width = 18
    ws1.column_dimensions['C'].width = 40
    ws1.column_dimensions['D'].width = 12
    ws1.column_dimensions['E'].width = 45
    
    # データ行の追加
    categories = {
        "基本情報": ["契約当事者", "契約金額", "契約期間", "支払条件", "責任範囲"],
        "解除・賠償": ["契約解除条件", "損害賠償の上限額"],
        "権利義務": ["知的財産権の帰属", "秘密保持義務"],
        "その他重要事項": ["準拠法・管轄裁判所", "契約の自動更新"]
    }
    
    row_num = 2
    for category, items in categories.items():
        for item in items:
            if item in contract_data:
                data = contract_data[item]
                ws1.append([
                    category,
                    item,
                    data.get("content", ""),
                    data.get("risk_level", ""),
                    data.get("warning", "")
                ])
                
                # リスクレベルに応じた色付け
                risk_cell = ws1.cell(row=row_num, column=4)
                if data.get("risk_level") == "高":
                    risk_cell.fill = risk_high_fill
                    risk_cell.font = Font(bold=True)
                elif data.get("risk_level") == "中":
                    risk_cell.fill = risk_medium_fill
                elif data.get("risk_level") == "低":
                    risk_cell.fill = risk_low_fill
                
                # セルの書式設定
                for col in range(1, 6):
                    cell = ws1.cell(row=row_num, column=col)
                    cell.border = border
                    cell.alignment = Alignment(vertical="top", wrap_text=True)
                
                row_num += 1
    
    # シート2: リスクサマリー
    ws2 = wb.create_sheet("リスクサマリー")
    ws2.append(["リスクレベル", "項目数", "主な項目", "推奨アクション"])
    
    for cell in ws2[1]:
        cell.fill = header_fill
        cell.font = header_font
        cell.alignment = Alignment(horizontal="center", vertical="center")
        cell.border = border
    
    ws2.column_dimensions['A'].width = 15
    ws2.column_dimensions['B'].width = 10
    ws2.column_dimensions['C'].width = 40
    ws2.column_dimensions['D'].width = 50
    
    # リスク集計
    risk_summary = {"高": [], "中": [], "低": []}
    for item, data in contract_data.items():
        if "risk_level" in data:
            risk_summary[data["risk_level"]].append(item)
    
    actions = {
        "高": "⚠️ 至急レビュー必要。法務部門または弁護士への相談を推奨。条項の修正交渉を検討してください。",
        "中": "⚡ 注意が必要。詳細を確認し、必要に応じて相手方と協議してください。",
        "低": "✓ 標準的な内容。通常の社内承認プロセスで問題ありません。"
    }
    
    for level in ["高", "中", "低"]:
        items = risk_summary[level]
        ws2.append([
            level,
            len(items),
            "、".join(items) if items else "該当なし",
            actions[level]
        ])
        
        row = ws2.max_row
        risk_cell = ws2.cell(row=row, column=1)
        if level == "高":
            risk_cell.fill = risk_high_fill
        elif level == "中":
            risk_cell.fill = risk_medium_fill
        else:
            risk_cell.fill = risk_low_fill
        
        for col in range(1, 5):
            cell = ws2.cell(row=row, column=col)
            cell.border = border
            cell.alignment = Alignment(vertical="top", wrap_text=True)
    
    # ファイル保存
    wb.save(output_path)
    return output_path
```

## 使用例

### ユーザーからの指示例:
```
この契約書PDFを分析して、契約当事者、金額、期間、支払条件、責任範囲、
リスク事項を表形式で抽出してください。リスクレベルを3段階評価してください。
```

### 処理フロー:
1. PDFの内容を確認(既にコンテキストにある)
2. 重要項目を構造化して抽出
3. 各項目のリスクレベルを評価
4. Excel形式で出力(/mnt/user-data/outputs/に保存)
5. 分析結果のサマリーと高リスク項目の警告を提示

## 実装時の注意事項

### 1. 日本語契約書特有の表現への対応
- 「甲」「乙」などの当事者表記
- 「本契約」「本件」などの指示語
- 条項番号(第○条)の参照関係
- 「善良なる管理者の注意義務」などの法律用語

### 2. リスク評価のポイント
- 契約類型による標準条項との比較
- 一方当事者に過度に不利な条項の検出
- 曖昧で解釈の余地が大きい条項
- 金額的インパクトの大きさ

### 3. 出力の品質管理
- 項目の抜け漏れチェック
- リスク評価の妥当性検証
- 警告文の具体性と実用性

## エラーハンドリング

- PDFが読み取れない場合: エラーメッセージと対処法を提示
- 項目が見つからない場合: 「記載なし」または「不明」と明記
- リスク評価が困難な場合: 「要確認」として法務レビューを推奨

## 出力ファイル名の規則

```
契約書分析_{契約種別}_{日付}.xlsx
例: 契約書分析_業務委託契約_20250120.xlsx
```

## スキルの改善・拡張

将来的な機能追加候補:
- 複数契約書の一括比較機能
- 業界別のベンチマーク比較
- 過去契約との差分分析
- リスク評価の学習・調整機能
