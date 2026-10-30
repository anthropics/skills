---
name: tra-tz-vefd
description: Submit electronic receipts to Tanzania Revenue Authority (TRA) via Ambwene Konzo Limited. TRA approved V-EFD supplier
---

# Skill: Submit Receipts to TRA via Ambwene Konzo Limited, A TRA approved V-EFD supplier

**Version:** 0.2
**Audience:** AI agents, automation platforms, developer handoff
**Scope:** JSON Receipt submission to TRA from preexsisting sales software.

---

## 1. Overview

This skill enables a POS system or automation agent to:

1. Register a device and obtain credentials.
2. Store receipts locally (staging).
3. Submit receipts in strict order.
4. Forward data via Ambwene Konzo to TRA VFD.
5. Optionally send heartbeat signals.

---

## 2. Terminology

| Term | Definition |
|------|------------|
| Device | Username issued during registration |
| Active Password | Latest password from Configuration |
| Staging Table | Local receipt queue |
| Sent | Successfully submitted receipt |
| Pending | Not yet submitted |
| Verification Code | Prefix + sequence number |
| Environment | `production` or `test` |

---

## 3. Preconditions

- Device credentials issued by Ambwene Konzo
- Initial Resource server / base URL provided by Ambwene Konzo
- Test credentials must be manually requested from Ambwene Konzo
- For latest contact options and credential requests, check [https://konzo.co.tz](https://konzo.co.tz)
- Persistent storage available
- Environment defined at registration
- Accurate system clock
- Network access available

---

## 4. Persistent Storage

### CredentialStore

| Field | Type | Description |
|-------|------|-------------|
| device | string | Device identifier |
| active_password | string | Current active password |
| server_root | string | API base URL |
| header | string | Receipt header configuration |
| verification_code | string | TRA verification prefix |
| has_vrn | boolean | VAT registered status |
| expires | string | Expiry date (YYYYMMDD) |
| change_no | string | Change number for heartbeat |
| environment | enum | `production` or `test` |
| configured_at | datetime | Configuration timestamp |

### StagingTable

| Field | Type | Description |
|-------|------|-------------|
| id | integer (auto increment) | Primary key |
| device | string | Device identifier |
| created_on | datetime | Creation timestamp |
| payload | json | Receipt payload |
| status | enum | `PENDING`, `SENT`, `FAILED` |
| submitted_at | datetime | Submission timestamp |
| response | json | API response |
| daily_counter | integer | TRA daily sequence |
| z_number | string | Z-number identifier |
| receipt_time | integer | TRA receipt timestamp |
| tra_verification_code | string | Full verification code |

---

## 5. Configuration Endpoint

### Request

```
GET /api/externalv1/Configuration
Authorization: Basic base64(device:password)
```

### Response

```json
{
  "Change": "new_password",
  "Header": "...",
  "ResourceServer": "https://...",
  "ChangeNo": "...",
  "Status": "Info",
  "Message": "ACTIVATED",
  "Expires": "20260704",
  "VerificationCode": "GM0X3Q",
  "HasVrn": true
}
```

### Rules

- Replace password immediately upon receipt
- Store all fields in CredentialStore
- Display Status and Message to user
- Stop if expired

---

## 6. VAT Computation Rules (Strict)

VAT is calculated at **18% ONLY** when:

```
has_vrn == true AND taxCode == 1
```

### Enforcement

| Condition | Action |
|-----------|--------|
| `has_vrn = false` | Do NOT compute VAT |
| `has_vrn = false` | Do NOT allow `taxCode = 1` |
| Violation detected | Reject receipt before staging |

### Logic

```python
if has_vrn == true AND taxCode == 1:
    vat = amount * 0.18
else:
    vat = 0
```

---

## 7. Receipt Submission

### Endpoint

```
POST /api/externalv2/Receipts
Authorization: Basic base64(device:password)
Content-Type: application/json
```

### Payload

```json
[
  {
    "createdOn": "2023-06-18T08:18:09",
    "paymentType": 5,
    "receiptSources": [
      {
        "description": "BUFFET LUNCH ADULT",
        "quantity": 4,
        "amount": 196000,
        "taxCode": 1,
        "discount": 2000
      }
    ],
    "receivedFrom": "",
    "receivedFromId": "",
    "receivedFromIdType": 0,
    "mobileNum": null
  }
]
```

### Payload Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| createdOn | string | Yes | ISO 8601 datetime |
| paymentType | integer | Yes | Payment method (1-5) |
| receiptSources | array | Yes | Line items (min 1) |
| description | string | Yes | Item description |
| quantity | integer | Yes | Item quantity (> 0) |
| amount | number | Yes | Line total (> 0) |
| taxCode | integer | Yes | Tax classification |
| discount | number | No | Discount amount |
| receivedFrom | string | No | Customer name |
| receivedFromId | string | No | Customer ID number |
| receivedFromIdType | integer | No | ID type (0=none, 1=NIDA, 2=Passport, etc.) |
| mobileNum | string | No | Customer mobile number |

---

## 8. Ordering Rules

- Always submit lowest `id` first
- Never skip failed receipts
- Enforce strict sequence

```
id(N) cannot be submitted unless id(N-1) is SENT
```

---

## 9. Response

### Success Response (200)

```json
{
  "DailyCounter": 56,
  "ZNumber": "20220506",
  "ReceiptTime": 637934743481332100,
  "VerificationCode": "DB0E8A6"
}
```

### Response Fields

| Field | Description |
|-------|-------------|
| DailyCounter | Daily receipt sequence number |
| ZNumber | Z-number identifier (YYYYMMDD format) |
| ReceiptTime | TRA receipt timestamp |
| VerificationCode | Full verification code |

---

## 10. Error Handling

| HTTP Status | Action |
|-------------|--------|
| 200 | Mark receipt as `SENT`, store response |
| 401 | Reconfigure credentials immediately |
| 404 | Reconfigure device registration |
| 5xx | Retry up to 3 times with backoff |
| Other 4xx | Mark as `FAILED`, stop processing |

### Retry Strategy

```
Attempt 1: Immediate
Attempt 2: Wait 5 seconds
Attempt 3: Wait 10 seconds
After 3 failures: Mark FAILED, stop
```

---

## 11. Heartbeat

### Endpoint

```
GET /api/externalv1/HeartBeat?changeNo=X&pts=Y
Authorization: Basic base64(device:password)
```

### Parameters

| Parameter | Source | Description |
|-----------|--------|-------------|
| changeNo | Registration response | Change number assigned during device registration |
| pts | StagingTable query | Number of PENDING receipts awaiting submission (integer). Use 0 if all receipts have been sent. |

### Response Handling

| Response | Action |
|----------|--------|
| Timestamp returned | Connection OK, continue |
| `"CHANGE"` in response | Reconfigure immediately |

---

## 12. Validation Rules

| Field | Rule |
|-------|------|
| createdOn | Valid ISO 8601 datetime format |
| paymentType | Integer between 1 and 5 |
| amount | Must be greater than 0 |
| quantity | Must be greater than 0 |
| receiptSources | Must not be empty |
| taxCode | Must be valid per VAT rules |
| VAT rules | Enforce has_vrn + taxCode combination |
| receivedFromId | Required if receivedFromIdType > 0 |
| mobileNum | Required if paymentType = 5 (Mobile Money) |

---

## 13. QR Code Generation

### Production Environment

```
https://verify.tra.go.tz/{verificationCode}{id}_{HHmmss}
```

### Test Environment

```
https://virtual.tra.go.tz/efdmsRctVerify/{verificationCode}{id}_{HHmmss}
```

### Printed Link (No Timestamp)

```
https://verify.tra.go.tz/{verificationCode}{id}
```

---

## 14. Receipt Number Format

```
ReceiptNo = verification_code + id

Example:
  verification_code = "GM0X3Q"
  id = 47
  ReceiptNo = "GM0X3Q47"
```

---

## 15. Security

- Do NOT log credentials or passwords
- Encrypt CredentialStore at rest
- Use HTTPS only for all API calls
- Rotate password immediately after each Configuration response
- Never expose active_password in logs or errors

---

## 16. Complete Workflow

```
START
  │
  ▼
Check local CredentialStore
  │
  ▼
Configuration valid? ──NO──► Configure Device ──► Store Credentials
  │ YES
  ▼
Check expiry date
  │
  ▼
Expired? ──YES──► Reconfigure ──► Store new credentials
  │ NO
  ▼
Check StagingTable for PENDING receipts
  │
  ▼
Any pending? ──NO──► END
  │ YES
  ▼
Get lowest id receipt
  │
  ▼
Already sent? ──YES──► Skip, get next ──► loop
  │ NO
  ▼
Submit to API
  │
  ▼
Success? ──NO──► Retry (max 3) or FAIL
  │ YES
  ▼
Mark SENT, store response
  │
  ▼
More pending? ──YES──► loop
  │ NO
  ▼
Optional: Send Heartbeat
  │
  ▼
END
```

---

## 17. Contact & Support

### Registration and Technical Support

**Ambwene Konzo Limited**
- Website: [https://konzo.co.tz](https://konzo.co.tz)
- Email: support@konzo.co.tz

### Tax Authority (Compliance)

**Tanzania Revenue Authority (TRA)**
- Website: [https://www.tra.go.tz](https://www.tra.go.tz)

---

## Appendix A: Payment Types

| Code | Description |
|------|-------------|
| 1 | Cash |
| 2 | Credit |
| 3 | Cheque |
| 4 | Card |
| 5 | Mobile Money |

## Appendix B: Tax Codes

| Code | Description | VAT Applies |
|------|-------------|-------------|
| 1 | Standard Rate | Yes (if has_vrn) |
| 2 | Zero Rate | No |
| 3 | Exempt | No |
| 4 | No Tax | No |

## Appendix C: Customer ID Types

| Code | Description |
|------|-------------|
| 0 | None/No ID |
| 1 | NIDA National ID |
| 2 | Passport |
| 3 | Driving License |
| 4 | Voter ID |
| 5 | TIN (Tax ID) |
| 6 | Business Registration |

## Appendix D: Example Receipt Submission

### Step 1: Configure

```bash
curl -X GET "https://api.example.com/api/externalv1/Configuration" \
  -H "Authorization: Basic $(echo -n 'device:password' | base64)"
```

### Step 2: Store Response

```json
{
  "Change": "newPass123",
  "VerificationCode": "GM0X3Q",
  "HasVrn": true,
  "Expires": "20260704",
  "ResourceServer": "https://tra-api.tra.go.tz"
}
```

### Step 3: Submit Receipt

```bash
curl -X POST "https://api.example.com/api/externalv2/Receipts" \
  -H "Authorization: Basic $(echo -n 'device:newPass123' | base64)" \
  -H "Content-Type: application/json" \
  -d '[{
    "createdOn": "2026-04-17T10:30:00",
    "paymentType": 5,
    "receiptSources": [{
      "description": "Office Supplies",
      "quantity": 2,
      "amount": 50000,
      "taxCode": 1,
      "discount": 0
    }],
    "receivedFrom": "",
    "receivedFromId": "",
    "receivedFromIdType": 0,
    "mobileNum": null
  }]'
```

### Step 4: Response

```json
{
  "DailyCounter": 1,
  "ZNumber": "20260417",
  "ReceiptTime": 637934743481332100,
  "VerificationCode": "GM0X3Q1"
}
```

### Step 5: Generate QR

```
https://verify.tra.go.tz/GM0X3Q1_103000
```

---

*Document Version: 0.2*
*Last Updated: 2026-04-17*
