# リファレンス: haruspex-stock-analyst-ja

`SKILL.md` に入りきらなかった詳細、エッジケース、出力バリエーション。

> **メンテナーへの注記:** このファイルの内容は `haruspex-stock-analyst` の
> `reference.md` の日本語訳版です。仕様変更があった場合は両方を同期して
> ください。

## API レスポンス形状

`get_stock_score(symbol)` の返却例:

```json
{
  "status": "success",
  "data": {
    "symbol": "NVDA",
    "score": 78,
    "previousScore": 62,
    "change": 16,
    "outlook": "bullish",
    "signal": "buy",
    "topicScores": {
      "ai-exposure":      { "score": 57, "change": 0 },
      "competitors":      { "score": 75, "change": 5 },
      "earnings":         { "score": 72, "change": 0 },
      "us_china_official":{ "score": 35, "change": -9 },
      "us_china_unofficial":{ "score": 35, "change": -9 }
    },
    "shareUrl": "https://haruspex.guru/s/9JWj9_sZzYKtcBgfhpkB4K3m"
  }
}
```

`get_stock_score_history(symbol, days=N)` は同じ per-day オブジェクトの
配列を `data.scores` で返す (新しい順)。

`get_stock_news(symbol)` は `data.articles` を返す:
`{title, url, publishedAt, source, image}`。

## アウトルック vs シグナル

これらは独立した 2 つのフィールドで、一致しないこともある。

- **`outlook`** = 方向感 (`bullish` / `bearish` / `neutral`)
- **`signal`** = アクション・シグナル (`buy` / `hold` / `sell`)

両者が食い違う場合は両方を提示し、ユーザーに判断を委ねる。一方だけを
選ばない。

## エッジケース: NOT_FOUND

```json
{
  "status": "error",
  "error": {
    "code": "NOT_FOUND",
    "message": "No Haruspex Score found for symbol \"TM\". The stock may not be in our analysis universe."
  }
}
```

正直に伝える。ユーザーが企業名を入力した場合は `search_stocks(name)` を
試すよう提案 — ただし検索が役立つ可能性がある場合に限る。**スコアの捏造は
絶対にしない。**

例の言い回し: 「現在 Haruspex の分析ユニバースには TOYOF (Toyota OTC) は
含まれていません。分析対象は主に米国大型株です。」

## エッジケース: スコアが厳密に 0 の次元

「データなし」と解釈する。低スコアではない。

例: NVDA は現在 `esg: 0`。正しい言い回しは「ESG データは現時点で NVDA に
ついては利用できません」。「NVDA の ESG はひどい」とは言わない。

## エッジケース: 履歴が少ない

`data.count` が約 10 未満の場合、トレンド段落でその旨を明示:
「履歴は N 日分しかないため、トレンドの読み取りは暫定的です。」
データを超えた外挿はしない。

## エッジケース: 直近の変化なし

ヘッドライン `change` が 0 で、どの次元も数ポイント以上動いていない場合、
ニュース取得をスキップし、トレンド段落でスコアの安定を簡潔に述べる。

## エッジケース: `cached: true`

API はキャッシュ済みスコアを返すことがある。`analyzedAt` のタイムスタンプ
で実分析時刻が分かる。`analyzedAt` が約 24 時間以上前なら出力に明記:
「(スコア最終更新: [日付])」。

## 注視集合の選び方

次のいずれかを満たす次元:

- 現在の `score` < 50
- `change` ≤ -5
- **リスク次元** (`climate-risk`, `concentration-risk`,
  `us_china_official`, `us_china_unofficial`) — 低スコア = 高リスクなので、
  50 未満でなくても悪化中なら含める

最大 3 つ。`change` の負の幅が大きい順、同点は現在スコアの低い順。

## セクター別の優先次元

| セクター系統             | 優先表示する次元                                  |
|--------------------------|---------------------------------------------------|
| 半導体 / AI インフラ     | ai-exposure, supplychain, us_china_*               |
| ソフトウェア / SaaS       | github-activity, ai-exposure, earnings              |
| 銀行 / 金融               | regulatory, macro, earnings                          |
| エネルギー / 素材         | climate-risk, supplychain, macro                     |
| 消費財 (小売、CPG)        | macro, supplychain, concentration-risk               |
| 製薬 / バイオ             | regulatory, patents, management                      |
| 大型分散                  | competitors, institutional, regulatory               |

これは事前確率としての参考。実際の `change` 値が示すものを優先する。

## 言語ミラーリングについて

このスキルは「ユーザーが日本語で書いた → 日本語で答える」専用です。

- ユーザーが英語で書いた場合 → `haruspex-stock-analyst` に委譲。
- ユーザーが日本語と英語を混ぜた場合 → 日本語が含まれていればこのスキル
  を使い、回答は日本語で行う。
- ユーザーが回答途中で言語を切り替えた場合 → ユーザーの最新の言語に合わ
  せる。

ティッカー記号、API スラッグ (`competitors`、`us_china_official` など)、
`shareUrl`、技術用語は英語のまま保持する — 翻訳しない。
