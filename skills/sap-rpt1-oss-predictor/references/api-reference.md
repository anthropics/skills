# SAP-RPT-1-OSS API Reference

Complete documentation for the open source SAP-RPT-1-OSS model and optional RPT Playground API.

## Table of Contents

1. [OSS Model Setup](#oss-model-setup)
2. [OSS Model API](#oss-model-api)
3. [Hardware Configuration](#hardware-configuration)
4. [Alternative: RPT Playground API](#alternative-rpt-playground-api)
5. [Error Handling](#error-handling)

---

## OSS Model Setup

### Step 1: Install Package

```bash
# From GitHub (recommended)
pip install git+https://github.com/SAP-samples/sap-rpt-1-oss

# Or clone and install locally
git clone https://github.com/SAP-samples/sap-rpt-1-oss.git
cd sap-rpt-1-oss
pip install -e .
```

### Step 2: Hugging Face Authentication

Model weights are hosted on Hugging Face and require authentication:

```bash
# Install Hugging Face CLI
pip install huggingface_hub

# Login interactively (recommended)
huggingface-cli login

# Or set environment variable
export HF_TOKEN="hf_your_token_here"
```

**Important**: Accept the model license at https://huggingface.co/SAP/sap-rpt-1-oss

### Step 3: Verify Installation

```python
# Test import
from sap_rpt_oss import SAP_RPT_OSS_Classifier, SAP_RPT_OSS_Regressor

# Test model loading (downloads weights on first run ~65MB)
clf = SAP_RPT_OSS_Classifier(max_context_size=1024, bagging=1)
print("✅ SAP-RPT-1-OSS ready!")
```

---

## OSS Model API

### Classification

```python
from sap_rpt_oss import SAP_RPT_OSS_Classifier
import pandas as pd

# Load data
df = pd.read_csv("sap_customers.csv")
X = df.drop(columns=["CHURN_STATUS"])
y = df["CHURN_STATUS"]

# Split
X_train, X_test = X[:400], X[400:]
y_train, y_test = y[:400], y[400:]

# Initialize classifier
clf = SAP_RPT_OSS_Classifier(
    max_context_size=4096,  # Context window (rows of context)
    bagging=4               # Ensemble size for better accuracy
)

# Fit on training data
clf.fit(X_train, y_train)

# Predict labels
predictions = clf.predict(X_test)

# Predict probabilities (for confidence scores)
probabilities = clf.predict_proba(X_test)
```

### Regression

```python
from sap_rpt_oss import SAP_RPT_OSS_Regressor

# Initialize regressor
reg = SAP_RPT_OSS_Regressor(
    max_context_size=4096,
    bagging=4
)

# Fit and predict
reg.fit(X_train, y_train)
predictions = reg.predict(X_test)
```

### Input Formats

```python
import pandas as pd
import numpy as np

# DataFrame input (recommended - preserves column names for semantics)
X_train = pd.DataFrame({
    "CUSTOMER_CREDIT_LIMIT": [50000, 75000, 30000],
    "DAYS_SINCE_LAST_ORDER": [10, 45, 180],
    "PAYMENT_DELAY_AVG": [2, 5, 25]
})
y_train = pd.Series(["ACTIVE", "ACTIVE", "AT_RISK"])

# NumPy array input (loses column semantics)
X_train = np.array([[50000, 10, 2], [75000, 45, 5], [30000, 180, 25]])
y_train = np.array(["ACTIVE", "ACTIVE", "AT_RISK"])
```

### Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| max_context_size | int | 8192 | Maximum rows in context window |
| bagging | int | 8 | Ensemble size (higher = better accuracy, more memory) |

### Using the Skill Scripts

```python
from scripts.rpt1_oss_predict import predict_classification, predict_regression

# Classification
result = predict_classification(
    train_data="train.csv",
    test_data="test.csv",
    target_column="CHURN_STATUS",
    max_context_size=4096,
    bagging=4
)
print(result["predictions"])
print(result["probabilities"])

# Regression
result = predict_regression(
    train_data="deliveries_train.csv",
    test_data="deliveries_test.csv",
    target_column="DELAY_DAYS"
)
print(result["predictions"])
```

---

## Hardware Configuration

### GPU Requirements

| Config | GPU Memory | Context Size | Bagging | Accuracy | Speed |
|--------|------------|--------------|---------|----------|-------|
| Optimal | 80GB (A100) | 8192 | 8 | Best | Fast |
| Standard | 40GB (A6000) | 4096 | 4 | Good | Good |
| Minimal | 24GB (RTX 4090) | 2048 | 2 | OK | OK |
| CPU | N/A | 1024 | 1 | OK | Slow |

### Auto-Detection

```python
from scripts.rpt1_oss_predict import get_optimal_config

config = get_optimal_config()
# Returns: {"max_context_size": 4096, "bagging": 4, "device": "cuda"}
```

### Memory Management for Large Datasets

```python
# Reduce memory footprint
clf = SAP_RPT_OSS_Classifier(
    max_context_size=2048,  # Smaller context
    bagging=1               # No ensemble
)

# Process in chunks
chunk_size = 100
all_preds = []
for i in range(0, len(X_test), chunk_size):
    chunk = X_test.iloc[i:i+chunk_size]
    preds = clf.predict(chunk)
    all_preds.extend(preds)
```

---

## Alternative: RPT Playground API

For users with SAP access, the closed-source RPT-1 is available via hosted API.

### Authentication

1. Navigate to https://rpt-playground.sap.com
2. Log in with SAP credentials
3. Scroll to bottom of page, copy API token

```bash
export RPT_TOKEN="your-token-here"
```

### Usage

```python
from scripts.rpt1_api import RPT1Client

client = RPT1Client()  # Uses RPT_TOKEN env var
# Or: client = RPT1Client(token="your-token")

result = client.predict(
    data="sap_export.csv",
    target_column="CHURN_STATUS",
    task_type="classification",
    model_version="accurate"  # or "fast"
)

print(result["predictions"])
print(result["probabilities"])
```

### API Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| /predict | POST | Single prediction request |
| /batch-predict | POST | Separate train/predict sets |
| /health | GET | Health check |

### Rate Limits

| Tier | Requests/Hour | Max Rows |
|------|---------------|----------|
| Free | 100 | 1000 |
| Standard | 1000 | 5000 |

---

## Error Handling

### OSS Model Errors

```python
from sap_rpt_oss import SAP_RPT_OSS_Classifier

try:
    clf = SAP_RPT_OSS_Classifier(max_context_size=4096)
    clf.fit(X_train, y_train)
    predictions = clf.predict(X_test)
except ImportError:
    print("Install: pip install git+https://github.com/SAP-samples/sap-rpt-1-oss")
except OSError as e:
    if "token" in str(e).lower():
        print("Run: huggingface-cli login")
    else:
        raise
except RuntimeError as e:
    if "out of memory" in str(e).lower():
        print("Reduce max_context_size or bagging parameter")
    else:
        raise
```

### Data Validation

```python
def validate_data(df, target_column):
    errors = []
    
    if target_column not in df.columns:
        errors.append(f"Target column '{target_column}' not found")
    
    if len(df) < 50:
        errors.append("Minimum 50 training examples recommended")
    
    if df.isna().all().any():
        errors.append("Some columns are entirely empty")
    
    # Check for semantic column names
    generic_names = [c for c in df.columns if c.upper() in ["COL1", "VALUE", "DATA", "FIELD"]]
    if generic_names:
        errors.append(f"Use descriptive column names instead of: {generic_names}")
    
    return errors
```

---

## Complete Workflow Example

```python
import pandas as pd
from sap_rpt_oss import SAP_RPT_OSS_Classifier
from scripts.prepare_sap_data import SAPDataPrep

# 1. Load and prepare SAP data
prep = SAPDataPrep()
df = pd.read_csv("sap_export.csv")
df = prep.rename_sap_fields(df)  # BUKRS → COMPANY_CODE, etc.

# 2. Split data
target = "PAYMENT_STATUS"
train_df = df.iloc[:400]
test_df = df.iloc[400:]

X_train = train_df.drop(columns=[target])
y_train = train_df[target]
X_test = test_df.drop(columns=[target])

# 3. Run prediction
clf = SAP_RPT_OSS_Classifier(max_context_size=4096, bagging=4)
clf.fit(X_train, y_train)

predictions = clf.predict(X_test)
probabilities = clf.predict_proba(X_test)

# 4. Add results to test data
test_df["PREDICTED"] = predictions
test_df["CONFIDENCE"] = [max(p) for p in probabilities]

# 5. Save output
test_df.to_csv("predictions.csv", index=False)
print(f"✅ Saved {len(predictions)} predictions")
```
