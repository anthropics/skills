# AI Data Rights, Privacy, and Emerging Issues

## Who Owns Data?

**The foundational legal principle**: Data, as raw facts, is generally not copyrightable under 17 U.S.C. § 102(b). The phone book case (*Feist Publications v. Rural Tel. Service*, 1991) established that compilations of facts require original selection, arrangement, or coordination to be copyrightable.

**Implications for AI training data**:
- Raw factual data (prices, temperatures, GPS coordinates) — not copyrightable
- Creative expression within data (articles, photographs, artwork) — copyrightable
- A creative compilation/arrangement of data — the compilation structure may be copyrightable, but not the underlying facts
- Databases in the EU have **sui generis database rights** (15-year protection for databases representing substantial investment) — no US equivalent

**Who "owns" a dataset in practice**:
- The company/person who created it has trade secret rights if they took reasonable measures to protect it
- Third-party data (user data, web-scraped data, licensed data) — ownership is governed by the contracts and terms under which the data was obtained
- Users' personal data — subject to GDPR/CCPA rights (right to access, right to deletion, right to portability)

## Data Licensing Agreements

When licensing data for AI training, the agreement must address:

**Key provisions**:
1. **Scope of permitted use**: Training, fine-tuning, validation, testing — specify all intended uses
2. **Sublicensing rights**: Can you share the trained model or derivative datasets with third parties?
3. **Exclusivity**: Is the license exclusive (expensive) or non-exclusive?
4. **Term**: Is the license perpetual or time-limited? Does termination require you to delete models trained on the data?
5. **Model output restrictions**: Some data licenses prohibit the trained model from reproducing the training data verbatim or in a way that competes with the licensor
6. **Attribution and credit**: Some licenses require crediting the data source
7. **Indemnification**: Who bears liability if the licensed data contains unlicensed content?
8. **Audit rights**: Does the licensor have the right to audit your training processes?

**Emerging data licensing market**:
- Reddit licensed its data for $203M (as of 2025) — a signal that platform data licensing for AI is now a real revenue stream
- Gannett, AP, and other publishers have signed AI licensing deals
- Creative content platforms (Getty, Shutterstock, Adobe) have launched licensed training data products
- The AI-friendly content licensing market is nascent but growing rapidly

## GDPR Compliance for AI Training

The **EU General Data Protection Regulation (GDPR)** imposes significant constraints on training AI models on personal data (any information relating to an identified or identifiable natural person).

**Key GDPR requirements for AI training**:

1. **Legal basis for processing**: Must have one of six lawful bases — consent, contract, legal obligation, vital interests, public task, or legitimate interests. For most AI training on personal data, legitimate interests (Article 6(1)(f)) is the claimed basis, requiring a Legitimate Interests Assessment (LIA) balancing your interests against data subjects' rights.

2. **Purpose limitation**: Data collected for one purpose (e.g., service delivery) cannot be repurposed for AI training without additional legal basis or compatibility analysis.

3. **Data minimization**: Only use personal data necessary for the training purpose.

4. **Accuracy**: Training data should be accurate and up-to-date.

5. **Storage limitation**: Don't retain personal training data longer than necessary.

6. **Security**: Appropriate technical measures (encryption, access controls) for training data.

7. **Data Subject Rights**:
   - **Right to erasure ("right to be forgotten")**: If a data subject requests erasure, you must delete their data from training sets — technically complex and potentially requiring model retraining
   - **Right to object to automated decision-making**: Article 22 gives rights against solely automated decisions with significant effects
   - **Data portability**: Rights to receive data in machine-readable format

**GDPR and model weights**: If personal data is embedded in model weights (memorized by the model), a right to erasure request may technically require retraining the model. This is an unsolved technical and legal problem; machine unlearning is an active research area.

**EU AI Act intersection**: The EU AI Act requires GPAI model providers to comply with EU copyright law for training data. Article 53 combined with GDPR creates a dual compliance burden for companies training AI on EU data.

## CCPA/CPRA Compliance for AI Training

The **California Consumer Privacy Act (CCPA)** and its 2020 amendment, the **California Privacy Rights Act (CPRA)**, regulate personal information of California residents.

**Key rights affecting AI training**:
- **Right to know**: What personal information is collected and how it's used (including AI training)
- **Right to delete**: Right to request deletion of personal information — same model retraining problem as GDPR
- **Right to opt out of sale/sharing**: Right to opt out of selling personal information or sharing for cross-context behavioral advertising
- **Right to correct**: Right to correct inaccurate personal information
- **Right to limit use of sensitive information**: Sensitive categories (SSNs, financial, health, biometric, location) have additional restrictions

**AI-specific CCPA issues**:
- Training AI models on customer behavioral data collected for service delivery may constitute "sharing" for advertising purposes if the trained model is used for ad targeting
- Automated decision-making rules under CPRA require opt-out rights for significant decisions
- Privacy notices must disclose AI training uses of personal information

## State Privacy Laws Beyond CCPA

As of 2025-2026, 20+ US states have enacted comprehensive privacy laws. Key ones affecting AI:
- **Texas (TDPSA)**: In effect July 2024; includes automated processing rights
- **Virginia (VCDPA)**: In effect 2023; opt-out rights for profiling
- **Colorado (CPA)**: In effect 2023; opt-out for profiling
- **Washington (My Health MY Data Act)**: In effect 2024; very broad health data protections affecting health AI

## Privacy-Preserving AI Training Techniques

**Synthetic data**:
- Generates artificial data statistically similar to real data
- No personal data = no GDPR/CCPA obligations for synthetic data
- No copyright in purely AI-generated synthetic data
- Limitations: "Model collapse" risk if only trained on synthetic data; may not capture tail distributions or rare events
- Leading providers: Gretel.ai, Mostly AI, YData, Syntheticus

**Differential privacy**:
- Mathematical technique adding calibrated noise to training to prevent memorization of individual records
- Provides provable privacy guarantees (ε-differential privacy bounds)
- Tradeoff: Some accuracy loss, especially for rare subgroups
- Used by: Apple, Google, Meta in production systems

**Federated learning**:
- Training occurs on distributed devices/servers; only model updates (gradients) transmitted to a central server — raw data never leaves local environment
- Particularly valuable for healthcare, finance, and telecommunications where data residency is required
- Technical challenges: Non-IID data, communication overhead, gradient inversion attacks

**De-identification and anonymization**:
- Under GDPR, truly anonymized data (cannot be re-identified with any reasonable effort) is not personal data
- CCPA: "De-identified" data (cannot reasonably be used to infer information) is excluded from most requirements
- Challenge: Modern AI can sometimes re-identify purportedly anonymized data

## Voice Cloning, Deepfakes, and Emerging Rights

**Right of Publicity**: The right to control commercial use of one's name, likeness, and voice. Currently governed by state law in the US with wide variation.

**Tennessee ELVIS Act (2024)**: First state law expressly protecting against AI-generated voice clones. Effective July 1, 2024. Prohibits:
1. Using an individual's name, photograph, voice, or likeness without consent for advertising/fundraising
2. Making available an individual's voice or likeness without authorization
3. Distributing software whose primary purpose is generating unauthorized voice clones

**Lehrman v. Lovo, Inc. (SDNY 2024)**: Voice actors sued Lovo for training AI voice models on their voices without authorization. Court denied motion to dismiss on right-of-publicity and copyright claims — case proceeds.

**New York AI voice cloning case (2025)**: SDNY case examining legality of AI voice replication under NY's right of publicity law.

**NO FAKES Act (reintroduced 2025)**: Federal bill that would establish a federal "digital replication right" — a federal right of publicity against voice/likeness cloning without consent. Not yet enacted as of June 2026.

**Deepfake laws**: 20+ states have enacted deepfake-specific laws as of 2025, covering non-consensual intimate imagery, election interference, and fraud. California (AB 602, AB 730), Texas, Virginia among first movers.

**Implications for AI startups**:
- Voice cloning products require consent mechanisms from all individuals whose voices are used for training
- Image/video generation products should implement controls against generating realistic depictions of real individuals
- Consider right of publicity licensing for any product using celebrity likenesses
- Build opt-out mechanisms for individuals whose likenesses appear in training data
