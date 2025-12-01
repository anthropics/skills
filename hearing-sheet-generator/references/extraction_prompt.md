# 文字起こし解析プロンプト

## 用途

ヒアリングの文字起こしテキストから、ヒアリングシートの各項目に記入すべき情報を抽出する。

## プロンプトテンプレート

```
あなたはヒアリング内容を分析し、構造化データに変換するアシスタントです。

以下の文字起こしテキストを分析し、ヒアリングシートの各項目に該当する情報を抽出してください。

## 対象企業情報
- 業種: {industry}
- 対象部門: {departments}

## 文字起こしテキスト
---
{transcript}
---

## 抽出ルール

1. **確信度の判定基準**
   - high: 明確な固有名詞、具体的な数値、断定的な発言がある
   - medium: 文脈から推測可能だが、曖昧な表現や不確かな発言
   - low: 複数の解釈が可能、または断片的な情報のみ
   - none: 該当する発言が見つからない

2. **選択肢のマッチング**
   - 発言内容を最も近い選択肢にマッチングする
   - 表記ゆれを吸収する（例: 「フリー」→「freee」）
   - 複数該当する場合は最新または主要なものを選択

3. **課題（issues）の抽出**
   - 困っている、大変、時間がかかる、などのネガティブな発言を検出
   - 該当する課題項目にマッチングする
   - 複数の課題が言及されている場合はすべて抽出

4. **自由記述の抽出**
   - 具体的なエピソード、数値を含む発言を抽出
   - 要約せず、できるだけ原文に近い形で記録

## 出力形式

以下のJSON形式で出力してください。

```json
{
  "basic_info": {
    "company_name": {
      "value": "抽出した値",
      "confidence": "high|medium|low|none",
      "note": "確信度がmedium/lowの場合の補足説明"
    },
    // ... 他の項目
  },
  "it_environment": {
    "accounting_software": {
      "value": "freee",
      "confidence": "high",
      "note": null
    },
    // ... 他の項目
  },
  "departments": {
    "経理": {
      "staff_count": {
        "value": "2",
        "confidence": "high",
        "note": null
      },
      "issues": {
        "selected": ["請求書の手入力が多い", "月次決算に時間がかかる"],
        "confidence": "high",
        "note": null
      },
      "episode": {
        "value": "月末は毎回残業。請求書が100枚以上あって、全部手で入力している",
        "confidence": "high",
        "note": null
      }
    },
    // ... 他の部門
  },
  "priority": {
    "priority_1": {
      "value": "請求書処理の効率化",
      "confidence": "high",
      "note": null
    },
    "ideal_state": {
      "value": "月末の残業をなくしたい",
      "confidence": "high",
      "note": null
    },
    "budget": {
      "value": "100〜300万円",
      "confidence": "medium",
      "note": "「100万くらいなら...」という発言から推測"
    }
  }
}
```

## 注意事項

1. 発言がない項目は `"value": null, "confidence": "none"` とする
2. 曖昧な発言は無理に解釈せず、確信度を下げて補足説明を付ける
3. 矛盾する発言がある場合は、より新しい/具体的な方を採用し、noteに補足
4. 数値は半角数字で統一
5. 選択肢がある項目は、定義された選択肢のいずれかにマッチングする
```

## 使用例

### 入力例

```
業種: 製造業
部門: 経理, 現場・製造

文字起こし:
---
えーと、うちは金属加工の部品を作ってる会社で、従業員は45人くらいですね。
経理は私含めて2人でやってます。決算は3月です。

会計ソフトはfreee使ってます。勤怠は...なんだっけ、ジョブなんとかっていうやつ。
請求書は紙で届くんで、それを見ながらfreeeに手入力してるんですよ。
月末は100枚以上あるんで、毎回残業になっちゃって。

現場の方は、作業指示は紙でやってます。ホワイトボードに書いて、
あとは口頭で伝えたり。実績は日報に手書きして、事務が後からExcelに入力してる感じ。
二重入力になっちゃってるんですよね、これがなんとかならないかなと。

予算は...そうですね、100万くらいまでなら社長も考えてくれるかな。
まずは請求書の処理を何とかしたいです。
---
```

### 出力例

```json
{
  "basic_info": {
    "company_name": {"value": null, "confidence": "none", "note": null},
    "business_description": {"value": "金属加工部品の製造", "confidence": "high", "note": null},
    "employees": {"value": "45", "confidence": "high", "note": null}
  },
  "it_environment": {
    "accounting_software": {"value": "freee", "confidence": "high", "note": null},
    "attendance_system": {"value": "ジョブカン", "confidence": "medium", "note": "「ジョブなんとか」という発言から推測"}
  },
  "departments": {
    "経理": {
      "staff_count": {"value": "2", "confidence": "high", "note": null},
      "fiscal_month": {"value": "3", "confidence": "high", "note": null},
      "invoice_processing": {"value": "紙", "confidence": "high", "note": null},
      "issues": {
        "selected": ["請求書の手入力が多い"],
        "confidence": "high",
        "note": null
      },
      "episode": {"value": "月末は100枚以上の請求書があり、毎回残業になる", "confidence": "high", "note": null}
    },
    "現場・製造": {
      "work_instruction": {"value": "紙", "confidence": "high", "note": "ホワイトボードと口頭も併用"},
      "result_input": {"value": "紙", "confidence": "high", "note": "日報に手書き→Excelに転記"},
      "issues": {
        "selected": ["実績入力が二重になっている"],
        "confidence": "high",
        "note": null
      },
      "episode": {"value": "日報に手書きして、事務が後からExcelに入力。二重入力になっている", "confidence": "high", "note": null}
    }
  },
  "priority": {
    "priority_1": {"value": "請求書処理の効率化", "confidence": "high", "note": null},
    "budget": {"value": "50〜100万円", "confidence": "medium", "note": "「100万くらいまでなら」という発言から"}
  }
}
```

## バリエーション

### 構造化インタビュー向け

質問順に沿って話している場合は、発言の順序も考慮して抽出精度を上げる。

### 非構造化インタビュー向け

自由に話している場合は、トピックの切り替わりを検出し、関連する項目に振り分ける。
同じ項目について複数回言及がある場合は、より具体的・最新の発言を優先。
