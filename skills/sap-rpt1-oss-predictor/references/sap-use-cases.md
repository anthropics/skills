# SAP Use Cases for RPT-1 Predictions

Detailed guide for common SAP prediction scenarios using RPT-1.

## Table of Contents

1. [Customer Churn Prediction (SD/CRM)](#customer-churn-prediction)
2. [Payment Default Risk (FI-AR)](#payment-default-risk)
3. [Delivery Delay Forecasting (SD/LE)](#delivery-delay-forecasting)
4. [Journal Entry Anomaly Detection (FI-GL)](#journal-entry-anomaly-detection)
5. [Vendor Performance Scoring (MM)](#vendor-performance-scoring)
6. [Demand Forecasting (PP/MM)](#demand-forecasting)

---

## Customer Churn Prediction

**Module**: SD, CRM, FI-AR  
**Task Type**: Classification  
**Target Classes**: ACTIVE, AT_RISK, CHURNED

### SAP Tables Required

| Table | Description | Key Fields |
|-------|-------------|------------|
| KNA1 | Customer Master (General) | KUNNR, NAME1, LAND1, KTOKD |
| KNB1 | Customer Master (Company) | KLIMK, SKFOR |
| VBAK | Sales Order Header | VBELN, KUNNR, NETWR, ERDAT |
| VBRK | Billing Document Header | Revenue history |
| BSID/BSAD | Open/Cleared Items | Payment behavior |

### Feature Engineering

```
ORDERS_LAST_12M          - Count of orders in last year
REVENUE_LAST_12M         - Total revenue in last year  
DAYS_SINCE_LAST_ORDER    - Recency indicator
AVG_ORDER_VALUE          - Revenue / Order count
PAYMENT_DELAY_AVG        - Average days late on payments
CREDIT_UTILIZATION       - Outstanding / Credit Limit
PRODUCT_DIVERSITY        - Distinct materials ordered
```

### Sample Dataset Structure

```csv
CUSTOMER_NUMBER,CUSTOMER_NAME,COUNTRY,CREDIT_LIMIT,ORDERS_LAST_12M,REVENUE_LAST_12M,DAYS_SINCE_LAST_ORDER,AVG_PAYMENT_DELAY,CHURN_STATUS
100001,Acme Corp,US,50000,12,125000,15,3,ACTIVE
100002,Beta Inc,DE,30000,2,8000,180,25,AT_RISK
100003,Gamma Ltd,UK,25000,0,0,400,45,CHURNED
```

### Prediction Example

```python
from sap_rpt_oss import SAP_RPT_OSS_Classifier
import pandas as pd

df = pd.read_csv("customer_churn_data.csv")
X = df.drop(columns=["CHURN_STATUS"])
y = df["CHURN_STATUS"]

# Use first 80% as training, last 20% for prediction
split = int(len(df) * 0.8)
X_train, X_test = X[:split], X[split:]
y_train = y[:split]

clf = SAP_RPT_OSS_Classifier(max_context_size=4096, bagging=4)
clf.fit(X_train, y_train)
predictions = clf.predict(X_test)
# Returns: predictions for ACTIVE/AT_RISK/CHURNED
```

---

## Payment Default Risk

**Module**: FI-AR  
**Task Type**: Classification or Regression  
**Target**: DEFAULT/PAID (classification) or DELAY_DAYS (regression)

### SAP Tables Required

| Table | Description | Key Fields |
|-------|-------------|------------|
| BSID | Open AR Items | KUNNR, BELNR, WRBTR, ZFBDT, ZBD1T |
| BSAD | Cleared AR Items | Historical payment data |
| KNB1 | Customer Credit | KLIMK, SKFOR, CTLPC |
| KNKK | Credit Control | Credit exposure data |

### Feature Engineering

```
INVOICE_AMOUNT           - Document amount
PAYMENT_TERMS_DAYS       - Agreed payment terms
CREDIT_LIMIT             - Customer credit limit
CREDIT_UTILIZATION       - Current exposure / limit
HIST_AVG_DELAY          - Historical average delay
HIST_LATE_COUNT         - Count of past late payments
CUSTOMER_AGE_DAYS       - Days since first transaction
INDUSTRY_CODE           - Customer industry segment
```

### Risk Scoring Approach

For regression (predict delay days):
```python
from sap_rpt_oss import SAP_RPT_OSS_Regressor

reg = SAP_RPT_OSS_Regressor(max_context_size=4096, bagging=4)
reg.fit(X_train, y_train)  # y_train contains delay days
predictions = reg.predict(X_test)
```

For classification (predict default):
```python
from sap_rpt_oss import SAP_RPT_OSS_Classifier

clf = SAP_RPT_OSS_Classifier(max_context_size=4096, bagging=4)
clf.fit(X_train, y_train)  # y_train contains DEFAULT or PAID
predictions = clf.predict(X_test)
```

---

## Delivery Delay Forecasting

**Module**: SD, LE (Logistics Execution)  
**Task Type**: Classification or Regression  
**Target**: DELAY_CATEGORY or DELAY_DAYS

### SAP Tables Required

| Table | Description | Key Fields |
|-------|-------------|------------|
| LIKP | Delivery Header | VBELN, LFDAT, WADAT_IST, VSTEL, ROUTE |
| LIPS | Delivery Items | MATNR, LFIMG, VGBEL |
| VBAK | Sales Order | AUART, VKORG, KUNNR |
| VTTK | Shipment Header | Carrier, transport info |

### Feature Engineering

```
SHIPPING_POINT           - Origin warehouse
ROUTE                    - Delivery route
CARRIER                  - Transport provider
TOTAL_QUANTITY          - Sum of delivery quantities
DISTINCT_MATERIALS      - Number of different products
ORDER_TYPE              - Sales order type
CUSTOMER_PRIORITY       - Customer importance rating
HISTORICAL_ROUTE_DELAY  - Avg delay for this route
SEASON                  - Month/quarter indicator
```

### Delay Categories

```
ON_TIME       - Delivered on or before planned date
MINOR_DELAY   - 1-3 days late
MODERATE_DELAY - 4-7 days late  
SEVERE_DELAY  - 8+ days late
```

---

## Journal Entry Anomaly Detection

**Module**: FI-GL (S/4HANA)  
**Task Type**: Classification  
**Target**: NORMAL, SUSPICIOUS, ANOMALY

### SAP Tables Required

| Table | Description | Key Fields |
|-------|-------------|------------|
| ACDOCA | Universal Journal | BELNR, RACCT, HSL, BUDAT, USNAM |
| BKPF | Document Header | BLART, CPUDT, CPUTM |
| SKA1 | GL Account Master | Account type, category |

### Feature Engineering

```
AMOUNT_ABS              - Absolute posting amount
GL_ACCOUNT              - Account number
COST_CENTER             - Cost center
DOCUMENT_TYPE           - FI document type
ENTRY_HOUR             - Hour of day posted
ENTRY_DAY_OF_WEEK      - Day of week posted
USER_NAME              - Posted by user
IS_MONTH_END           - Posted in last 3 days of month
IS_ROUND_NUMBER        - Amount ends in 000
REVERSAL_FLAG          - Is this a reversal entry
```

### Anomaly Indicators to Train On

- Unusual posting times (nights, weekends)
- Round number amounts
- Unusual account combinations
- Deviations from historical patterns
- Manual entries vs automated
- User posting outside normal scope

---

## Vendor Performance Scoring

**Module**: MM  
**Task Type**: Regression (score) or Classification (tier)  
**Target**: PERFORMANCE_SCORE (0-100) or TIER (A/B/C/D)

### SAP Tables Required

| Table | Description | Key Fields |
|-------|-------------|------------|
| LFA1 | Vendor Master | LIFNR, NAME1, LAND1 |
| EKKO | PO Header | EBELN, LIFNR, BEDAT |
| EKPO | PO Item | NETPR, MENGE |
| EBAN | Purchase Requisition | Lead time data |
| EKBE | PO History | GR/IR data for delivery performance |

### Feature Engineering

```
ON_TIME_DELIVERY_RATE   - % deliveries on time
QUALITY_REJECTION_RATE  - % rejected for quality
PRICE_VARIANCE          - Actual vs quoted price
RESPONSE_TIME_AVG       - Days to confirm PO
INVOICE_ACCURACY        - % invoices without errors
TOTAL_PO_VALUE         - Total purchase volume
RELATIONSHIP_LENGTH    - Days since first PO
COMPLAINT_COUNT        - Number of vendor complaints
```

---

## Demand Forecasting

**Module**: PP, MM  
**Task Type**: Regression  
**Target**: FORECAST_QUANTITY

### SAP Tables Required

| Table | Description | Key Fields |
|-------|-------------|------------|
| MSEG | Material Document | MATNR, MENGE, BUDAT |
| VBRP | Billing Items | Sales history |
| MARA | Material Master | Material attributes |
| MARC | Plant Data | MRP settings |

### Feature Engineering

```
MATERIAL_NUMBER         - Product identifier
PLANT                  - Location
HISTORICAL_QTY_M1      - Last month quantity
HISTORICAL_QTY_M2      - 2 months ago
HISTORICAL_QTY_M3      - 3 months ago
HISTORICAL_QTY_Y1      - Same month last year
SEASONALITY_INDEX      - Seasonal adjustment factor
PROMOTION_FLAG         - Marketing activity indicator
PRICE_CHANGE_FLAG      - Recent price change
MATERIAL_GROUP         - Product category
```

### Time Series Approach

Structure data with lag features:
```csv
MATERIAL,PLANT,MONTH,QTY_M1,QTY_M2,QTY_M3,QTY_Y1,SEASON,FORECAST_QTY
MAT001,1000,2024-01,150,140,160,145,1.05,155
MAT001,1000,2024-02,155,150,140,148,0.98,[PREDICT]
```

---

## Best Practices

### Data Quality
- Remove duplicates before prediction
- Handle NULL values explicitly
- Standardize date formats
- Use consistent units

### Feature Selection
- Include business-meaningful columns
- Use descriptive column names (RPT-1 uses semantics)
- Include historical context features
- Balance feature count (10-50 columns optimal)

### Training Data
- Minimum 50 labeled examples
- Balanced class distribution for classification
- Recent data preferred (last 1-2 years)
- Include edge cases and exceptions

### Validation
- Hold out 20% for testing
- Compare predictions vs actual outcomes
- Monitor prediction confidence scores
- Retrain periodically as patterns change
