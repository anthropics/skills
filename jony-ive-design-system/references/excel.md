# Excel固有のデザイン仕様

## 基本設定

### グリッド線
```python
ws.sheet_view.showGridLines = False  # 必須：グリッド線を非表示
```

### ウィンドウ枠の固定
```python
ws.freeze_panes = "B5"  # ヘッダー行と左列を固定
```

## 列幅・行高さ

### 推奨列幅

| 列タイプ | 幅 | 例 |
|----------|-----|-----|
| 狭い（番号、記号） | 5-8 | WBS番号、ステータス記号 |
| 標準（短いテキスト） | 10-14 | 日付、担当者名 |
| 広い（長いテキスト） | 30-40 | タスク名、説明 |
| 最大 | 50-60 | 備考、詳細説明 |

### 推奨行高さ

| 行タイプ | 高さ | 用途 |
|----------|------|------|
| タイトル | 25-30 | ドキュメントタイトル |
| ヘッダー | 20-22 | 表のヘッダー行 |
| フェーズ | 20-22 | グループ行 |
| データ | 16-18 | 通常データ行 |
| 凡例 | 16 | 凡例項目 |

## セルスタイル

### ヘッダー行
```python
header_fill = PatternFill(start_color="333333", fill_type="solid")
header_font = Font(name="メイリオ", size=10, bold=True, color="FFFFFF")
header_alignment = Alignment(horizontal='center', vertical='center')
```

### フェーズ/グループ行
```python
phase_fill = PatternFill(start_color="F5F5F5", fill_type="solid")
phase_font = Font(name="メイリオ", size=10, bold=True, color="333333")
```

### データ行
```python
data_font = Font(name="メイリオ", size=10, color="333333")
data_border = Border(bottom=Side(style='thin', color='E0E0E0'))
```

## 罫線

### 使用パターン

| パターン | スタイル | 色 | 用途 |
|----------|----------|-----|------|
| 区切り線 | thin | #E0E0E0 | 行の下線 |
| ヘッダー下 | thin | #333333 | ヘッダー下部 |

### 避けるパターン
- 全面グリッド罫線
- 太い罫線
- 二重線
- 外枠のみの罫線

```python
# 推奨: 下線のみ
thin_border = Border(bottom=Side(style='thin', color='E0E0E0'))

# 避ける: 全面グリッド
# box_border = Border(
#     left=Side(...), right=Side(...),
#     top=Side(...), bottom=Side(...)
# )
```

## 数値フォーマット

| データ型 | フォーマット | 例 |
|----------|-------------|-----|
| 日付 | YYYY/MM/DD | 2025/01/06 |
| 金額 | #,##0 | 1,234,567 |
| 金額（円） | ¥#,##0 | ¥1,234,567 |
| パーセント | 0.0% | 12.3% |
| 整数 | #,##0 | 1,234 |

## 条件付き書式

### ステータス連動の例
```python
from openpyxl.formatting.rule import FormulaRule

# 進行中 → 青背景
progress_fill = PatternFill(start_color="4472C4", fill_type="solid")
ws.conditional_formatting.add(
    range,
    FormulaRule(
        formula=['$G5="進行中"'],
        fill=progress_fill
    )
)
```

## ドロップダウン（データ検証）

```python
from openpyxl.worksheet.datavalidation import DataValidation

status_validation = DataValidation(
    type="list",
    formula1='"未着手,進行中,完了,保留"',
    allow_blank=True
)
ws.add_data_validation(status_validation)
status_validation.add(ws['G5'])
```

## Python完全例

```python
from openpyxl.styles import Font, PatternFill, Alignment, Border, Side

# 色定数（グレースケール＋1アクセント）
COLORS = {
    # 基本グレースケール
    "black": "000000",
    "dark_gray": "333333",
    "medium_gray": "666666",
    "light_gray": "999999",
    "pale_gray": "CCCCCC",
    "separator": "E0E0E0",
    "bg_gray": "F5F5F5",
    "white": "FFFFFF",
    
    # アクセント（1色のみ）
    "accent": "5B7B94",
    
    # ステータス（グレー濃淡）
    "status_pending": "CCCCCC",    # 未着手
    "status_progress": "666666",   # 進行中
    "status_done": "333333",       # 完了
    "status_hold": "FFFFFF",       # 保留（枠線付き）
    "milestone": "5B7B94",         # マイルストーン（唯一のアクセント）
    
    # 構造
    "header_bg": "333333",         # ヘッダー背景
    "phase_bg": "F5F5F5",          # フェーズ背景
}

FONT_NAME = "メイリオ"

# スタイル定義
def get_styles():
    return {
        "title": Font(name=FONT_NAME, size=14, bold=True, color=COLORS["black"]),
        "header": Font(name=FONT_NAME, size=10, bold=True, color=COLORS["white"]),
        "header_fill": PatternFill(start_color=COLORS["header_bg"], fill_type="solid"),
        "phase": Font(name=FONT_NAME, size=10, bold=True, color=COLORS["dark_gray"]),
        "phase_fill": PatternFill(start_color=COLORS["bg_gray"], fill_type="solid"),
        "body": Font(name=FONT_NAME, size=10, color=COLORS["dark_gray"]),
        "caption": Font(name=FONT_NAME, size=9, color=COLORS["light_gray"]),
        "border": Border(bottom=Side(style='thin', color=COLORS["separator"])),
    }
```
