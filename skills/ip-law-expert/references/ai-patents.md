# AI-Specific Patent Issues

## Can AI Be an Inventor? (Thaler v. Vidal)

**Answer: No. Only natural persons can be named inventors under current US law.**

The Federal Circuit in **Thaler v. Vidal**, No. 21-2347 (Fed. Cir. Aug. 5, 2022), held unanimously that the Patent Act requires inventors to be natural persons. The court relied on the Patent Act's use of personal pronouns ("himself," "herself") and the oath requirement compelling a human to sign an inventorship declaration. The US Supreme Court denied certiorari on April 23, 2023.

**Practical implication for AI startups**: AI systems cannot be listed as inventors. If an AI tool assists in creating an invention, the human(s) who directed, configured, or conceived the invention — not the AI — must be named inventors. Inventorship requires **conception** (the formation in the mind of a definite and permanent idea of the complete and operative invention). A human who meaningfully directed the AI's application to a problem may qualify.

**The "don't ask, don't tell" issue (2025)**: USPTO's current practice does not require disclosure of whether AI was used in the inventive process if a human inventor can be identified. However, intentional inventorship fraud (listing inventors who didn't actually conceive the invention) can render a patent unenforceable. Consult an attorney on disclosure obligations as this area evolves.

**International**: UK IPO, EPO, and CNIPA all similarly require human inventors as of 2025.

## Machine Learning Patent Eligibility: Recentive Analytics v. Fox Corp.

**Recentive Analytics, Inc. v. Fox Corp.**, 134 F.4th 1205 (Fed. Cir. 2025) is the Federal Circuit's **first precedential ruling specifically addressing machine learning and § 101 patent eligibility**.

**What the patents covered**: Applying machine learning models to optimize TV broadcast event scheduling and network map generation.

**The court's holding**: Claims directed to "no more than applying existing methods of machine learning to a new data environment" are patent-ineligible. Merely performing a task previously done by humans more efficiently using ML, without reciting improvements to the ML process itself, does not confer patent eligibility.

**The key test from Recentive**: Patent protection is available for inventions that **improve AI/ML itself** (new architectures, training methods, optimization techniques). Patent protection is NOT available for claims that merely **apply existing ML techniques to a new domain or data type**.

**What fails after Recentive**:
- "Use ML to schedule events" (applied ML with no technical innovation in the ML)
- "Train a model on [new domain] data" (iterative training is inherent to ML)
- "Use a neural network to predict [business outcome]" (generic ML application)
- Applying transformer architecture to a new text type without improving the architecture

**What survives after Recentive**:
- Novel training methodologies that reduce compute requirements by X%
- New neural network architectures with measurable technical advantages
- Specific hardware-software co-design innovations
- Novel data preprocessing techniques that improve model accuracy through specific technical means
- Methods for reducing hallucination through specific architectural changes
- New attention mechanisms with specific structural improvements

**The WilmerHale observation (2025)**: Recentive "underscores the potential value of trade secrecy to protecting AI innovation." When a core ML algorithm can't be patented under § 101, trade secret protection of training methodologies, hyperparameter choices, and model weights becomes the primary IP protection strategy.

**SCOTUS denial**: On December 8, 2025, the Supreme Court declined Recentive's petition seeking clarity on ML patent eligibility. The Federal Circuit's restrictive standard stands.

## How to Patent AI Methods: Surviving Alice and Recentive

**Strategy 1 — Improve the AI itself**: Claim innovations in training processes, loss functions, architectures, or inference efficiency. Frame the claim as "a method of training a neural network comprising: [specific novel steps that achieve measurable technical improvement]" — not "a method of [business task] using a neural network."

**Strategy 2 — Specific application with technical novelty**: Claim AI applied to a problem that requires a technical solution not previously achievable. Medical imaging AI that detects previously undetectable patterns through specific signal processing steps (not just "use ML on medical images").

**Strategy 3 — Hardware-software integration**: Claim specific hardware configurations that work synergistically with the AI model. Co-designed chip + model innovations have better eligibility than pure software.

**Strategy 4 — Novel data representation**: If the innovation is in how training data is structured, labeled, or processed (not the ML model itself), those preprocessing methods may be separately patentable.

**Strategy 5 — System claims over method claims**: Method claims are most vulnerable under Alice. System claims with specific structural components (specialized processors, specific memory architectures, dedicated inference units) can sometimes survive where method claims fail.

## AI Patent Landscape (LLMs, Diffusion Models, Transformers)

**Scale of activity**: Over 70,000 AI-related patent applications filed at USPTO in 2024. The LLM patent landscape covers 13,418 patents filed since 2010, with exponential growth post-2017 (Transformer architecture).

**WIPO GenAI Patent Report (2024)**: GenAI patent families grew from 733 in 2014 to 14,000+ in 2023 — over 800% increase since the Transformer (2017). China leads in raw filings; US leads in high-value foundational AI patents.

**Key patent areas being filed**:
- Transformer efficiency (attention approximations, sparse attention, FlashAttention variants)
- Training optimizations (mixed precision, gradient checkpointing, distributed training)
- RLHF and alignment techniques
- Model compression (quantization, pruning, distillation)
- RAG (retrieval-augmented generation) architectures
- Multimodal fusion techniques
- Inference acceleration (speculative decoding, batching strategies)
- Diffusion model samplers and noise schedules

**NPE risk in AI**: Patent trolls acquired AI patents at scale in 2024-2025. NPEs account for 90.3% of high-tech patent litigation. AI startups are targets. Pre-fundraising FTO analyses should cover the AI patent landscape.

## International AI Patent Eligibility Comparison

### United States
- Standard: Alice/Mayo two-step; requires practical application or improvement to technology
- After Recentive (2025): Applying existing ML to new domain = ineligible
- Must improve AI itself or show specific technical application
- AI cannot be inventor (Thaler v. Vidal)

### European Patent Office (EPO)
- Standard: "Technical character" — invention must solve a technical problem by technical means
- AI/ML methods are generally patentable if they produce a "technical effect" beyond mere information processing
- More favorable to AI patents than US in practice (no Alice equivalent)
- AI inventions framed as tools for technical applications (medical, manufacturing) fare well
- Guidelines for Examination Chapter II-2.3.6 (2025) covers AI/ML
- AI cannot be inventor (G 1/22 EPO decision)

### China (CNIPA)
- Standard: "Technical solution" must solve technical problems using technical means following natural laws
- CNIPA issued "Guidelines for Patent Applications for AI-Related Inventions (Trial Implementation)" effective December 31, 2024
- Generally more permissive than US for AI drug discovery and industrial AI claims
- AI applied to neural network architecture optimization is patentable if technical effects are specific
- AI cannot be inventor

### Key Takeaway for Startups
File in the US first (establishes priority date). Consider EPO and CNIPA via PCT for AI innovations — often easier to get AI patents granted in EU and China than in the US post-Recentive.
