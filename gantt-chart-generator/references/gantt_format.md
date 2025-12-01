# ガントチャートフォーマット詳細

## PROJECT_DATAの構造

```python
PROJECT_DATA = {
    "project_name": str,      # プロジェクト名
    "start_date": str,        # 開始日（YYYY-MM-DD形式）
    "responsible": str,       # 責任者名
    "description": str,       # プロジェクト概要（任意）
    "phases": [               # フェーズのリスト
        {
            "name": str,      # フェーズ名
            "tasks": [        # タスクのリスト
                {
                    "name": str,       # タスク名
                    "assignee": str,   # 担当者
                    "days": int,       # 所要日数
                }
            ],
            "milestone": {    # マイルストーン（任意）
                "name": str,                  # マイルストーン名
                "days_from_phase_start": int  # フェーズ開始からの日数
            }
        }
    ]
}
```

## カスタマイズオプション

### 週数の調整
デフォルトは最大24週。変更する場合:
```python
total_weeks = min(total_weeks, 24)  # この値を変更
```

### ステータスの追加
```python
# DataValidationの選択肢を変更
status_validation = DataValidation(
    type="list",
    formula1='"未着手,進行中,完了,保留,レビュー中"',  # 選択肢を追加
    allow_blank=True
)
```

### 色のカスタマイズ
```python
COLORS = {
    "status_pending": "CCCCCC",   # 未着手
    "status_progress": "4472C4",  # 進行中
    "status_done": "70AD47",      # 完了
    "status_hold": "ED7D31",      # 保留
    # 新しいステータス色を追加
    "status_review": "9966CC",    # レビュー中
}
```

### 日単位表示への変更
短期プロジェクト（2週間以下）の場合:
```python
# 週ではなく日を表示
for day in range(total_days):
    day_date = start_date + timedelta(days=day)
    header = day_date.strftime("%m/%d")
```

## 契約書からの情報抽出ガイド

### 抽出すべき情報
1. **契約期間**: 開始日・終了日
2. **納品物**: マイルストーンとして設定
3. **検収日**: 最終マイルストーンとして設定
4. **業務内容**: フェーズ/タスクに分解

### 典型的なフェーズ構成例

#### コンサルティング案件
1. 現状分析
2. 課題整理・提案
3. 実装支援
4. 定着化

#### システム開発案件
1. 要件定義
2. 設計
3. 開発
4. テスト
5. 導入・運用

#### 研修・トレーニング案件
1. 準備・計画
2. 教材作成
3. 研修実施
4. フォローアップ

## 出力ファイル仕様

### ファイル名
`ガントチャート_{プロジェクト名}.xlsx`

### シート構成
1. **プロジェクト概要**: 基本情報、フェーズ一覧、マイルストーン一覧
2. **タスク**: WBS、ガントチャート、ステータス管理

### 印刷設定
A4横向き推奨。週数が多い場合は用紙サイズをA3に変更。
