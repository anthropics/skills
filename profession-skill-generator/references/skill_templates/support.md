# カスタマーサポート向けスキルテンプレート

## 5軸評価の傾向

| 軸 | 典型的評価 |
|---|---|
| 時間軸 | 現在志向（即時対応） |
| 対象軸 | 外部特化 |
| 処理軸 | ルーチン重視〜判断重視 |
| 価値軸 | オペレーション |
| 専門軸 | 汎用型〜専門型 |

## 7業務カテゴリー例

1. **問い合わせ対応業務** - チケット対応、チャット
2. **技術サポート業務** - トラブルシューティング
3. **エスカレーション管理業務** - 上位対応、専門部門連携
4. **ナレッジ管理業務** - FAQ作成、ドキュメント更新
5. **品質管理・モニタリング業務** - QA、応対品質チェック
6. **顧客フィードバック分析業務** - VOC分析、改善提案
7. **チーム運営・育成業務** - 研修、シフト管理

## よくあるペインと対応スキル案

### ペイン: 同じ質問に何度も回答している
- `faq-auto-suggester` - FAQ自動提案
- `template-response-finder` - テンプレ回答検索
- `knowledge-gap-detector` - ナレッジ不足検出

### ペイン: 回答文の作成に時間がかかる
- `reply-drafter` - 返信文ドラフト作成
- `tone-adjuster` - トーン調整（丁寧⇔カジュアル）
- `technical-simplifier` - 技術用語の平易化

### ペイン: エスカレーション判断が難しい
- `escalation-classifier` - エスカレーション判定
- `severity-assessor` - 重要度評価
- `routing-recommender` - 振り分け先推奨

### ペイン: FAQやドキュメント更新が追いつかない
- `faq-draft-generator` - FAQ下書き生成
- `doc-update-suggester` - ドキュメント更新提案
- `changelog-summarizer` - 変更履歴要約

### ペイン: 顧客の声の分析が大変
- `voc-categorizer` - VOC分類
- `sentiment-analyzer` - 感情分析
- `improvement-insight-extractor` - 改善インサイト抽出

## スキル命名規則

- サポート業務 + アクション の kebab-case
- 例: `reply-drafter`, `faq-auto-suggester`
