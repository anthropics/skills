# Domain-Specific AI Use Case Patterns

Reference this file to proactively suggest relevant use cases based on the user's industry.
Use these as starting hypotheses — validate against what the user's product actually does.

---

## FinTech / Banking / Payments

| Use Case | AI Approach | Common Data |
|---|---|---|
| Transaction fraud detection | Anomaly detection, classification | Transaction logs, device fingerprints |
| Credit risk scoring | Gradient boosting, neural nets | Financial history, behavioral signals |
| AML / suspicious activity detection | Graph ML, anomaly detection | Transaction networks, counterparties |
| Document processing (KYC, loan apps) | Document AI, OCR + NLP | PDFs, images, forms |
| Personalized financial advice | RAG + LLM | User portfolio, market data |
| Churn prediction | Classification | Usage patterns, customer history |
| Smart dispute resolution | Classification + RAG | Support tickets, transaction context |
| Regulatory reporting automation | NLP, extraction | Reports, filings, structured data |
| Market sentiment analysis | NLP | News, earnings calls, social data |
| Expense categorization | Classification | Transaction descriptions |

**Common Regulatory Flags**: RBI (India), SEBI, EU AI Act (credit = high-risk), GDPR, PCI-DSS.
**Key Data Challenge**: Class imbalance in fraud data; PII restrictions on training data.

---

## Healthcare / HealthTech / MedTech

| Use Case | AI Approach | Common Data |
|---|---|---|
| Clinical note summarization | LLM / Summarization | EHR notes, SOAP notes |
| Diagnostic support / triage | Classification, multimodal | Images, lab results, vitals |
| Drug interaction checks | Knowledge graph + RAG | Medication databases, patient records |
| Prior authorization automation | Classification + extraction | Insurance forms, clinical docs |
| Patient no-show prediction | Classification | Appointment history, demographics |
| Remote monitoring anomaly detection | Time-series anomaly | Wearable / IoT data |
| Medical coding (ICD-10) | Classification + NLP | Clinical text |
| Care gap identification | Predictive modeling | Claims data, patient history |
| Clinical trial matching | RAG + semantic search | Trial criteria, patient profiles |
| Mental health sentiment tracking | NLP, time-series | Session notes, mood logs |

**Common Regulatory Flags**: HIPAA, CE marking (EU MedTech), FDA SaMD guidelines, DPDP (India).
**Key Data Challenge**: Small labeled datasets; consent requirements; de-identification needed.

---

## SaaS / B2B Software

| Use Case | AI Approach | Common Data |
|---|---|---|
| In-product AI assistant / copilot | LLM + RAG | Product data, user context, docs |
| Semantic search | Embeddings + vector DB | Product content, user-generated data |
| Auto-generated reports / summaries | LLM | Structured data, metrics, events |
| Smart onboarding / feature discovery | Recommendation | User behavior, feature usage logs |
| Churn prediction | Classification | Usage patterns, engagement signals |
| Support ticket deflection | RAG + classification | Knowledge base, past tickets |
| Lead scoring | Gradient boosting | CRM data, behavioral signals |
| Anomaly alerts on user metrics | Time-series anomaly | Usage metrics, KPIs |
| Auto-tagging / categorization | Classification | User-created content |
| Natural language to query/filter | LLM (text-to-SQL/filter) | Schema, sample data |

**Common Regulatory Flags**: GDPR, SOC2 (data handling), AI transparency in B2B contracts.
**Key Data Challenge**: Multi-tenant data isolation; customer data usage permissions.

---

## E-Commerce / Retail / Marketplace

| Use Case | AI Approach | Common Data |
|---|---|---|
| Product recommendations | Collaborative filtering, two-tower | Purchase history, views, ratings |
| Search ranking & personalization | Learning to rank, embeddings | Search logs, catalog, behavior |
| Dynamic pricing | Regression, RL | Demand signals, competitor pricing |
| Demand forecasting | Time-series (Prophet, LSTM) | Sales history, seasonality, events |
| Review summarization | LLM | Product reviews |
| Return reason prediction | Classification | Return records, product data |
| Visual product search | Multimodal embeddings | Product images |
| Inventory optimization | Optimization + prediction | Stock levels, lead times, demand |
| Fake review detection | Classification | Review text, reviewer behavior |
| Customer segmentation | Clustering | Purchase history, demographics |

**Common Regulatory Flags**: GDPR for personalization; FTC guidelines on AI-generated reviews.
**Key Data Challenge**: Cold start for new products/users; catalog quality.

---

## Logistics / Supply Chain

| Use Case | AI Approach | Common Data |
|---|---|---|
| Route optimization | Graph algorithms + ML | Maps, traffic, delivery history |
| ETA prediction | Regression, LSTM | GPS traces, historical routes |
| Demand & inventory forecasting | Time-series | Order history, lead times |
| Predictive maintenance | Anomaly detection, classification | Sensor data, maintenance logs |
| Document extraction (bills of lading, invoices) | Document AI | PDFs, images |
| Warehouse slot optimization | Optimization | SKU velocity, picking patterns |
| Carrier performance scoring | Regression | Delivery outcomes, SLAs |
| Carbon footprint estimation | Regression | Route data, vehicle specs |

**Common Regulatory Flags**: GDPR for driver data; sector-specific safety regulations.
**Key Data Challenge**: GPS data quality; inconsistent document formats.

---

## EdTech / Learning Platforms

| Use Case | AI Approach | Common Data |
|---|---|---|
| Adaptive learning path | Recommendation, knowledge tracing | Quiz results, engagement, progress |
| Automated essay / answer grading | LLM + rubric evaluation | Submissions, rubrics |
| Doubt resolution chatbot | RAG + LLM | Course content, past Q&As |
| Learner dropout prediction | Classification | Engagement signals, assessment results |
| Content gap analysis | NLP + clustering | Course content, learner queries |
| Auto-generated practice questions | LLM | Course content |
| Plagiarism / academic integrity | Classification, similarity | Submission text |
| Teacher productivity tools | LLM | Lesson plans, reports |

**Common Regulatory Flags**: COPPA (under-13 users in the US); FERPA; DPDP (India).
**Key Data Challenge**: Age-restricted user data; sparse engagement data for new learners.

---

## HR Tech / Workforce Platforms

| Use Case | AI Approach | Common Data |
|---|---|---|
| Resume screening / ranking | Embeddings + ranking | Job descriptions, resumes |
| Job description optimization | LLM | JDs, application outcomes |
| Employee attrition prediction | Classification | HR data, engagement, performance |
| Skills gap analysis | NLP + knowledge graph | Job roles, employee profiles |
| Interview question generation | LLM | JDs, role competencies |
| Benefits recommendation | Recommendation | Employee profile, past selections |
| Sentiment analysis on surveys | NLP | Employee survey responses |

**Common Regulatory Flags**: EU AI Act classifies some recruitment AI as high-risk; EEOC guidelines (US); bias auditing requirements.
**Key Data Challenge**: Bias in historical hiring data; explainability requirements for adverse decisions.

---

## DevTools / Developer Platforms

| Use Case | AI Approach | Common Data |
|---|---|---|
| Code completion / suggestion | LLM (code) | Codebase, edit history |
| Bug prediction | Classification | Git history, test results, code metrics |
| Automated code review | LLM | PRs, code diff, style guides |
| Test generation | LLM | Source code, existing tests |
| Incident root cause analysis | RAG + LLM | Logs, runbooks, past incidents |
| Documentation generation | LLM | Code, docstrings, comments |
| Dependency vulnerability scanning | Classification | Dependency graph, CVE data |
| Natural language to code | LLM | Schema, APIs, user intent |

**Common Regulatory Flags**: Licensing concerns for code trained on OSS; IP considerations.
**Key Data Challenge**: Codebase privacy; context window limits for large codebases.

---

## Cross-Industry Patterns (Apply Broadly)

These use cases appear in almost every domain:

| Pattern | When to Suggest |
|---|---|
| **Intelligent search** | Any product with a search bar and significant content corpus |
| **In-product copilot / assistant** | Any product where users perform repeated complex tasks |
| **Document intelligence** | Any product that ingests or processes PDFs, forms, emails |
| **Anomaly detection** | Any product with time-series operational or user data |
| **Personalization** | Any product with enough user history (>50 interactions) |
| **Churn / engagement prediction** | Any subscription or retention-dependent product |
| **Auto-summarization** | Any product with long-form content or reports |
| **Classification / tagging** | Any product with unstructured content needing categorization |
| **Conversational AI / support deflection** | Any product with a support or help channel |