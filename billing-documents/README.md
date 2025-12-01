# Billing Documents Generator

請求書・見積書を自動生成する統合Agent Skill

## 概要

| 文書タイプ | トリガーワード | スクリプト |
|-----------|---------------|-----------|
| 請求書 | 請求書、インボイス、invoice | `create_invoice.py` |
| 見積書 | 見積書、見積もり、quotation | `create_quotation.py` |

## 機能

### 請求書（Invoice）
- 月額固定型
- 消費税10%自動計算
- 支払期限: 請求月末
- 振込先情報含む

### 見積書（Quotation）
- 月額顧問型 / 時間単価型 / プロジェクト型
- 有効期限: 30日後（デフォルト）
- 支払条件・契約期間記載

## 出力形式

**Excel形式** で出力

- Excel: 編集可能、そのまま送付も可能
- PDF送付が必要な場合は、Excelから印刷メニューでPDF保存

## デザイン

Jony Iveデザインシステム準拠
- グレースケール基調
- メイリオフォント統一
- ミニマルで洗練されたレイアウト

## 使用方法

```bash
# 請求書作成
python scripts/create_invoice.py

# 見積書作成
python scripts/create_quotation.py
```

## ディレクトリ構成

```
billing-documents/
├── SKILL.md
├── README.md
├── scripts/
│   ├── create_invoice.py
│   └── create_quotation.py
└── references/
    ├── invoice_format.md
    └── quotation_format.md
```

## バージョン履歴

- v2.1 (2025-12-02): PDF出力を廃止、Excel出力のみに変更
- v2.0 (2025-12-01): invoice-generator + quotation-generator を統合
- v1.0: 個別スキルとして提供
