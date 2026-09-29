---
name: sap-rpt1-oss-predictor
description: Use SAP-RPT-1-OSS open source tabular foundation model for predictive analytics on SAP business data. Handles classification and regression tasks including customer churn prediction, delivery delay forecasting, payment default risk, demand planning, and financial anomaly detection. Use when asked to predict, forecast, classify, or analyze patterns in SAP tabular data exports (CSV/DataFrame). Runs locally via Hugging Face model.
---

# SAP-RPT-1-OSS Predictor

SAP-RPT-1-OSS is SAP's open source tabular foundation model (Apache 2.0) for predictions on structured business data. Unlike LLMs that predict text, RPT-1 predicts field values in table rows using in-context learning—no model training required.

**Repository**: https://github.com/SAP-samples/sap-rpt-1-oss
**Model**: https://huggingface.co/SAP/sap-rpt-1-oss

## Setup

### 1. Install Package

```bash
pip install git+https://github.com/SAP-samples/sap-rpt-1-oss
```

### 2. Hugging Face Authentication

Model weights require HF login and license acceptance:

```bash
# Install HF CLI
pip install huggingface_hub

# Login (creates ~/.huggingface/token)
huggingface-cli login
```

Then accept model terms at: https://huggingface.co/SAP/sap-rpt-1-oss

### 3. Hardware Requirements

| Config | GPU Memory | Context Size | Bagging | Use Case |
|--------|------------|--------------|---------|----------|
| Optimal | 80GB (A100) | 8192 | 8 | Production, best accuracy |
| Standard | 40GB (A6000) | 4096 | 4 | Good balance |
| Minimal | 24GB (RTX 4090) | 2048 | 2 | Development |
| CPU | N/A | 1024 | 1 | Testing only (slow) |

## Quick Start

### Classification (Customer Churn, Payment Default)

```python
import pandas as pd
from sap_rpt_oss import SAP_RPT_OSS_Classifier

# Load SAP data export
df = pd.read_csv("sap_customers.csv")
X = df.drop(columns=["CHURN_STATUS"])
y = df["CHURN_STATUS"]

# Split data
X_train, X_test = X[:400], X[400:]
y_train, y_test = y[:400], y[400:]

# Initialize and predict
clf = SAP_RPT_OSS_Classifier(max_context_size=4096, bagging=4)
clf.fit(X_train, y_train)

predictions = clf.predict(X_test)
probabilities = clf.predict_proba(X_test)
```

### Regression (Delivery Delay Days, Demand Quantity)

```python
from sap_rpt_oss import SAP_RPT_OSS_Regressor

reg = SAP_RPT_OSS_Regressor(max_context_size=4096, bagging=4)
reg.fit(X_train, y_train)
predictions = reg.predict(X_test)
```

## Core Workflow

1. **Extract SAP data** → Export to CSV from relevant tables
2. **Prepare dataset** → Include 50-500 rows with known outcomes
3. **Rename fields** → Use semantic names (see Data Preparation)
4. **Run prediction** → Fit on training data, predict on new data
5. **Interpret results** → Probabilities for classification, values for regression

## SAP Use Cases

See `references/sap-use-cases.md` for detailed extraction queries:

- **FI-AR**: Payment default probability (BSID, BSAD, KNA1)
- **FI-GL**: Journal entry anomaly detection (ACDOCA, BKPF)
- **SD**: Delivery delay prediction (VBAK, VBAP, LIKP)
- **SD**: Customer churn likelihood (VBRK, VBRP, KNA1)
- **MM**: Vendor performance scoring (EKKO, EKPO, EBAN)
- **PP**: Production delay risk (AFKO, AFPO)

## Data Preparation

### Semantic Column Names (Important!)

RPT-1-OSS uses an LLM to embed column names and values. Descriptive names improve accuracy:

```python
# Good: Model understands business context
CUSTOMER_CREDIT_LIMIT, DAYS_SINCE_LAST_ORDER, PAYMENT_DELAY_DAYS

# Bad: Generic names lose semantic value
COL1, VALUE, FIELD_A
```

Use `scripts/prepare_sap_data.py` to rename SAP technical fields:

```python
from scripts.prepare_sap_data import SAPDataPrep

prep = SAPDataPrep()
df = prep.rename_sap_fields(df)  # BUKRS → COMPANY_CODE, etc.
```

### Dataset Size
- Minimum: 50 training examples
- Recommended: 200-500 examples
- Maximum context: 8192 rows (GPU dependent)

## Scripts

- `scripts/rpt1_oss_predict.py` - Local model prediction wrapper
- `scripts/prepare_sap_data.py` - SAP field renaming and SQL templates
- `scripts/batch_predict.py` - Chunked processing for large datasets

## Alternative: RPT Playground API

For users with SAP access, the closed-source RPT-1 is available via API:

```python
from scripts.rpt1_api import RPT1Client

client = RPT1Client(token="YOUR_RPT_TOKEN")  # Get from rpt-playground.sap.com
result = client.predict(data="data.csv", target_column="TARGET", task_type="classification")
```

See `references/api-reference.md` for RPT Playground API documentation.

## Limitations

- Tabular data only (no images, text documents)
- Requires labeled examples for in-context learning
- First prediction is slow (model loading)
- GPU strongly recommended for production use
