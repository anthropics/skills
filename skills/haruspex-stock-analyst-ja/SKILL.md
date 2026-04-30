---
name: haruspex-stock-analyst-ja
description: Japanese-language stock analysis for US-listed equities (NYSE/NASDAQ), powered by Haruspex's multi-dimension scoring system. Use this skill whenever the user writes the query in Japanese (any input containing hiragana, katakana, or kanji) and is asking about a stock — including phrases like "[TICKER]はどう？", "[TICKER]の評価は？", "アップルはどう思う？", "テスラを分析して", "NVDAのスコアは？" — even when the user mixes Japanese and English. This is the default skill for any Japanese-language single-ticker stock question. The analysis universe is US-listed stocks; this skill does NOT cover Japan-listed (4-digit .T) symbols. Defer to haruspex-stock-analyst when input is in English.
---

# Haruspex Stock Analyst — 日本語版

## このスキルの役割 / What this skill does

US 上場株 (NYSE / NASDAQ) の単一銘柄を、Haruspex API 経由で日本語で分析する
スキルです。出力構造は `haruspex-stock-analyst` と同じ：ヘッドラインスコア、
強気/弱気アウトルック、買い/保有/売りシグナル、強い・弱いトピック次元、
30日トレンド、関連ニュース。日本語で動作する点だけが異なります。

This skill is the Japanese-language counterpart of `haruspex-stock-analyst`.
It analyzes US-listed equities, in Japanese, for users who write their query
in Japanese.

> **重要 / Scope:** Haruspex の分析対象は主に米国大型株です。日本上場銘柄
> (例: `7203.T`、`6758.T`) は現時点では対象外です。日本企業の米国 ADR
> (`TM`、`SONY`、`NTDOY` など) も現状未対応です。`NOT_FOUND` が返った場合
> は正直に報告し、絶対にスコアを捏造しないでください。

## いつ使うか / When to trigger

ユーザー入力に以下のいずれかが含まれる場合:

- ひらがな、カタカナ、または漢字
- 日本語と英語の混在 (例: 「NVDA はどう？」)
- 明示的に日本語での回答を求める言葉 (「日本語で」「JA」など)

このスキルではなく姉妹スキルを使うべき場合:

- ユーザーが完全に英語で書いている → `haruspex-stock-analyst`
- ユーザーが 3 銘柄以上のリストを提示 → `haruspex-watchlist-review`
  (ただし回答は日本語で行う)
- ユーザーがポジションの「理由 / 投資仮説」を述べている →
  `haruspex-thesis-tracker` (ただし回答は日本語で行う)

## 前提条件 / Prerequisites

このスキルは `@haruspex-guru/mcp-server` のインストールと接続が必要です。
**最初の動作: MCP ツールが利用可能であることを確認する。**

利用できない場合は、[`shared/MCP_SETUP.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/MCP_SETUP.md) の
インストール手順を出力して**停止**してください。実データなしに分析を試みて
はいけません。

## ワークフロー / Workflow

1. **ティッカーの曖昧性解消。** ユーザーが企業名や曖昧な記号を渡した場合、
   `search_stocks(query)` で確認し、想定銘柄をユーザーに確認してから進む。
   `NVDA` のような明確な US ティッカーであればスキップ。
2. **現在のスコア取得。** `get_stock_score(symbol)` を呼ぶ。`NOT_FOUND` の
   場合は正直に報告: 「Haruspex の分析ユニバースには現在 [SYMBOL] が含
   まれていません。分析対象は主に米国大型株です。」スコアを捏造しない。停止。
3. **トレンド取得。** `get_stock_score_history(symbol, days=30)` を呼び、
   方向性、転換点、レンジを把握する。
4. **必要に応じてニュース取得。** `get_stock_news(symbol)` は次のいずれかが
   当てはまる場合のみ:
   - ヘッドラインの `change` が ±10 以上
   - ユーザーが「何が動かしているのか」を尋ねている
   - 任意の次元の変化が ±10 以上
5. **以下のフォーマットで出力する。**

## 出力フォーマット / Output format

ブラケット部分は実データで置き換える。**捏造禁止。**

```markdown
## [SYMBOL] — Haruspex 分析

**スコア:** [N]/100 ([outlook]) ・ **シグナル:** [signal] ・ **変化:** [+/-N]

**強い次元 (ポジティブ):**
- `[dim1]`: [N]/100 ([change]) — [一行で日本語の説明]
- `[dim2]`: [N]/100 ([change]) — [一行説明]
- `[dim3]`: [N]/100 ([change]) — [一行説明]

**注視すべき次元 (低水準または悪化中):**
- `[dim]`: [N]/100 ([change]) — [一行説明]
- `[dim]`: [N]/100 ([change]) — [一行説明]

**30日トレンド:**
[1〜2文。例: 「直近5営業日でスコアが62から78へ上昇。月初は60台前半で
推移していた。今回の上昇は competitors と macro 次元が牽引している。」]

**ニュース文脈 (取得した場合):**
- [見出し] — [出典], [相対日付]
- [見出し] — [出典], [相対日付]

**確認用リンク:** [shareUrl]

> **免責事項:** Haruspex のスコアは公開データから導出された定量的シグナル
> であり、情報提供のみを目的としています。投資助言、金融助言、または有価
> 証券の売買・保有の推奨ではありません。過去のパフォーマンスや現在のスコ
> アは将来の結果を保証するものではありません。投資判断を行う前に必ずご
> 自身で調査を行い、必要に応じて有資格の金融アドバイザーにご相談ください。
> データは haruspex.guru より。
```

> **メンテナーへの注記 / Maintainer note:** 上記の日本語免責事項は
> [`shared/DISCLAIMER.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md) と同期しています。
> 公開展開前に有資格の日本の金融アドバイザーに文言確認を依頼することを
> 推奨します。

### 次元の選び方

- **ポジティブ集合:** 現在スコアが最も高い 3 次元。同点は `change` の
  大きい順で破る。
- **注視集合:** 現在 50 未満の次元、または `change ≤ -5` の次元。最大 3 つ。
- **`score = 0` の次元はスキップ。** 通常は「データなし」を意味する。トレンド
  段落で「現時点で ESG データは利用できません」のように言及する。
- 各次元の 1 行説明には [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DIMENSIONS.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DIMENSIONS.md)
  を参照。

## コンプライアンス・ルール (絶対遵守) / Compliance rules (NEVER VIOLATE)

- **ユーザーに対して買い/売り/保有を直接的に勧めない。** API の `signal`
  フィールドを「データとして」報告するのは可 (例:「`signal` は `buy` です」)。
  「買うべき」「売るべき」と書くのは禁止。
- **価格予測をしない。** 「スコアが上昇している」は可。「価格が上がる」は
  禁止。
- **ポジションサイズ、ストップロス、利確、リスク管理の具体的指示をしない。**
  ライセンスを持つアドバイザーに相談するよう案内する。
- **「買うべきか？」と聞かれたら**、リダイレクト: 「買うべきかは私には
  判断できません。データをお見せします…」と続けて分析を実行。
- **データの限界を正直に伝える。** 履歴が少ない、ニュースがない、次元が
  0 (データなし) — すべて明示する。
- **share URL を必ず含める** ことで、ユーザーが Haruspex のページで検証
  できるようにする。
- **免責事項を必ず含める** —
  [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md) の日本語版
  を逐語的に。
- **捏造禁止。** スコア、ティッカー、次元値、share URL、ニュース記事 — 
  すべて実データのみ。
- **Haruspex スコアが将来の成果を保証する**かのように示唆しない。

## 参考資料 / Reference material

- [`reference.md`](reference.md) — エッジケース、出力バリエーション、
  欠損データの扱い (日本語)
- [`examples.md`](examples.md) — 実データを使った会話例 (日本語)
- [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DIMENSIONS.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DIMENSIONS.md) — 16 次元の
  解説 (英語、共通)
- [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md) — 免責事項
  (日本語版もここ)
- [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/MCP_SETUP.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/MCP_SETUP.md) — MCP サーバー
  のインストール手順 (英語、共通)
