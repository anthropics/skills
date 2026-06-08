# AI Copyright: Training Data, AI Outputs, and Emerging Law

## US Copyright Office Position on AI-Generated Works

The Copyright Office has issued a multi-part report on AI and copyright. Current position (as of 2025–2026):

**Part 2 (January 29, 2025) — Copyrightability of AI Outputs**:
- Works generated **entirely by AI** are **not copyrightable** — human authorship is a bedrock requirement
- Works with **AI assistance** may be copyrightable if a human made sufficient creative choices in selection, arrangement, or modification of AI-generated content
- **Detailed prompting alone** does not constitute the requisite human authorship — the Copyright Office evaluates case-by-case whether the human's creative expression is perceptible in the final work
- A human who selects which AI outputs to include, arranges them in a creative way, or substantially modifies AI-generated elements retains copyright in those elements of original expression

**Practical consequence**: Pure AI-generated images, text, or code cannot be copyrighted. Startups building products on AI-generated content should not assume copyright protection for that output. Document human creative input carefully if copyright protection is sought.

**Part 1 (July 31, 2024) — Digital Replicas**:
- Recommended federal legislation for unauthorized AI-generated replicas of individuals (voice cloning, deepfakes). See references/enforcement.md.

**Part 3 (Draft released May 9, 2025) — AI Training and Copyright**:
- Examines fair use, licensing frameworks, and liability for training on copyrighted data
- Concluded that "some uses of copyrighted works for AI training will qualify as fair use, and some will not" — cannot prejudge outcomes
- Recommended a licensing market solution but stopped short of mandating it
- No blanket safe harbor for AI training on copyrighted data was recommended

## The Training Data Copyright Litigation Wave

Over 164 copyright lawsuits against AI companies were pending as of early 2026. The litigation landscape:

### Getty Images v. Stability AI
- Filed in US and UK courts
- UK High Court ruled November 4, 2025: Rejected the central copyright allegation of primary infringement; found limited trademark liability for watermark reproduction
- US case ongoing — discovery phase, no fair use ruling expected before mid-2026
- Key allegation: Stable Diffusion trained on 12M+ Getty Images photos without license, reproducing watermarks in outputs

### NYT v. OpenAI & Microsoft
- Filed December 2023 in SDNY
- Alleges millions of Times articles used to train ChatGPT
- OpenAI and Microsoft assert fair use defense
- In discovery as of June 2026; no fair use ruling yet
- Settlement talks reported but inconclusive
- Potential damages: billions in statutory damages if infringement found and registration prerequisites met

### Other Active Cases (as of 2026)
- Authors Guild, Sarah Silverman, George R.R. Martin and other authors v. OpenAI/Meta — class action
- Musicians, visual artists, and software developers (GitHub Copilot case) v. Microsoft/GitHub/OpenAI
- German cases: Munich Regional Court held OpenAI's use of German song lyrics in GPT-4 training violated German copyright law — one of the first European AI training rulings

### Fair Use Analysis for AI Training (Four-Factor Test)

When courts evaluate AI training as potential fair use under 17 U.S.C. § 107, they consider:

1. **Purpose and character of use**: Is the use transformative? Training creates statistical patterns, not copies of specific works. OpenAI argues training is transformative; plaintiffs argue it competes with original works. Courts have not yet ruled definitively.

2. **Nature of the copyrighted work**: Factual works receive less protection than creative works. Training on news articles (factual) differs from training on novels or artwork.

3. **Amount and substantiality taken**: Training on entire works weighs against fair use. Wholesale ingestion of complete books, articles, or images is a significant factor.

4. **Effect on the market**: Does the AI output compete with or substitute for the original? If AI-generated images can replace stock photo subscriptions, Getty's market harm argument is strong.

**Current state**: No US court has ruled on fair use in AI training as of June 2026. The outcome is genuinely uncertain. Both positions have merit.

## EU AI Act: Copyright Obligations for AI Providers

The **EU AI Act** (published July 12, 2024; copyright obligations effective August 2, 2025) imposes specific requirements on General Purpose AI (GPAI) model providers:

**Article 53(1)(c)**: GPAI providers must implement a policy to comply with EU copyright law and the opt-out mechanism for text and data mining (TDM) under **Directive (EU) 2019/790 Article 4(3)**.

**Article 53(1)(d)**: GPAI providers must publish a "sufficiently detailed summary" of training content using the template issued by the European AI Office (template published July 2025).

**The TDM opt-out**: Under the EU Copyright Directive, copyright holders can opt out of permitting text and data mining for commercial purposes. AI providers training on EU internet content must honor these opt-outs (expressed via robots.txt or other machine-readable means). Failure to honor opt-outs is copyright infringement in the EU.

**Practical implication for US AI startups with EU users**: If you place a GPAI model on the EU market (even from the US), these obligations apply regardless of where training occurred. This is a significant compliance burden.

## Strategies for Navigating AI Training Data Copyright

**Option 1 — Licensed Data**
- License training data directly from content owners (expensive but legally safe)
- Emerging data licensing deals: Reddit ($203M in data licensing), news publishers
- Commercial licensing platforms for AI training data are emerging

**Option 2 — Public Domain and Permissively Licensed Data**
- Project Gutenberg, Common Crawl (subject to robots.txt compliance), Creative Commons CC0 or CC BY datasets
- Wikipedia under CC BY-SA (copyleft — may require attribution or share-alike)
- Stack Overflow data license changed in 2023 — older data may have different terms

**Option 3 — Synthetic Data**
- Generates artificial data mimicking real-world statistical properties
- No copyright in synthetic data (no human authorship to copy)
- Avoids GDPR personal data issues
- Tradeoffs: may not capture full distribution of real data, "model collapse" risk if trained only on AI-generated data
- Companies generating high-quality synthetic data: AI21 Labs, Gretel.ai, Mostly AI

**Option 4 — Differential Privacy / Federated Learning**
- Training with privacy guarantees (differential privacy adds mathematical noise)
- Reduces risk of memorization and reproduction of copyrighted training examples
- Federated learning trains on distributed devices without centralizing data

**Option 5 — Fair Use with Documentation**
- Some argue training is transformative and fair use — relying on this defense is risky pre-lawsuit
- Maintain detailed documentation of training data provenance, any licensing terms considered, and the transformative purpose of training
- Ensures the best possible fair use defense if litigation occurs

## AI-Specific Copyright Issues for Startups

**Model weights**: Are model weights themselves copyrightable? Unsettled. They're mathematical matrices — likely lack the human authorship required for copyright. Trade secret protection is more reliable (see references/trade-secrets.md).

**Fine-tuning**: Copyright risk of fine-tuning on proprietary data is less studied. If fine-tuning data is legitimately licensed, the resulting model's fine-tuned weights should not infringe.

**RAG (Retrieval-Augmented Generation)**: Real-time retrieval and use of copyrighted content to generate outputs raises different questions than training. Injecting copyrighted text into prompts and generating outputs based on that content may be closer to reproduction than training.

**Output indemnification**: Some AI vendors (Microsoft/GitHub Copilot, Google) now offer copyright indemnification for AI-generated output used in their products. Review vendor agreements for this protection before building on their platforms.
