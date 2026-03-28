---
name: ask-rosetta
description: HTS classification and duty calculation for US Customs. When Claude needs to classify products for import/export, calculate tariffs and duties, or determine landed costs for international trade.
license: MIT
author: OneMarket.World
repository: https://github.com/onemarket/ask-rosetta
---

# Ask Rosetta - Trade Classification Guide

## Overview

Ask Rosetta helps classify products using the Harmonized Tariff Schedule (HTS) for US Customs and calculate import duties. Use this skill when users ask about:

- HTS codes for products
- Import duty rates
- Landed cost calculations
- Customs classification

## Quick Start

```bash
# API endpoint
curl -X POST https://api.onemarket.world/classify \
  -H "Content-Type: application/json" \
  -d '{"description": "cotton t-shirt from Vietnam"}'
```

## Classification Process

### 1. Gather Product Information

Before classifying, collect:
- **Product description**: What is it? (e.g., "men's cotton t-shirt")
- **Material composition**: Primary material (cotton, leather, polyester)
- **Country of origin**: Where was it manufactured?

### 2. Classify the Product

Use the API to get the HTS code:

```python
import requests

response = requests.post(
    "https://api.onemarket.world/classify",
    json={
        "description": "cotton t-shirt for men",
        "material": "cotton",
        "country_of_origin": "Vietnam"
    }
)

result = response.json()
# {
#   "hts_code": "6109.10.0012",
#   "hts_description": "T-shirts, singlets... of cotton",
#   "duty_rate": "16.5%",
#   "confidence": 0.95
# }
```

### 3. Calculate Landed Cost

For a complete cost breakdown:

```python
product_value = 20.00  # USD
quantity = 100
duty_rate = 0.165  # 16.5%

duty_amount = product_value * quantity * duty_rate
mpf = min(max(product_value * quantity * 0.003464, 31.67), 614.35)
shipping = 15.00 * quantity  # estimate

total_landed = (product_value * quantity) + duty_amount + mpf + shipping
```

## HTS Code Structure

HTS codes are 10 digits:
- **Chapter (2 digits)**: Broad category (e.g., 61 = Knitted apparel)
- **Heading (4 digits)**: Product type (e.g., 6109 = T-shirts)
- **Subheading (6 digits)**: Specific characteristics
- **US suffix (8-10 digits)**: Statistical reporting

### Common Chapters

| Chapter | Category |
|---------|----------|
| 61 | Knitted/crocheted apparel |
| 62 | Woven apparel |
| 64 | Footwear |
| 42 | Leather goods |
| 84 | Machinery |
| 85 | Electronics |

## Trade Agreements

### USMCA (US-Mexico-Canada)
Products from Mexico or Canada often qualify for **duty-free** treatment under USMCA.

### GSP (Generalized System of Preferences)
Certain developing countries get reduced or zero duties.

## Best Practices

1. **Always verify country of origin** - it affects duty rates significantly
2. **Material matters** - cotton vs synthetic changes the HTS code
3. **Check trade agreements** - USMCA can eliminate duties entirely
4. **Use professional guidance** - for actual shipments, consult a customs broker

## API Reference

### POST /classify

Classify a product and get HTS code.

**Request:**
```json
{
  "description": "string (required)",
  "material": "string (optional)",
  "country_of_origin": "string (optional)"
}
```

**Response:**
```json
{
  "hts_code": "6109.10.0012",
  "hts_description": "T-shirts, singlets...",
  "chapter": "61",
  "duty_rate": "16.5%",
  "confidence": 0.95,
  "reasoning": "Cotton knitted apparel..."
}
```

### POST /batch

Classify multiple products (max 100).

### GET /health

Health check endpoint.

### GET /docs

Interactive API documentation.

## Examples

### Example 1: Apparel
```
Product: "Women's leather jacket from Italy"
HTS: 4203.10.4000
Duty: 6%
```

### Example 2: Electronics
```
Product: "Wireless bluetooth headphones from China"
HTS: 8518.30.2000
Duty: Free
```

### Example 3: Footwear
```
Product: "Men's leather dress shoes from Vietnam"
HTS: 6403.59.9065
Duty: 8.5%
```

## Resources

- [USITC HTS Search](https://hts.usitc.gov/)
- [CBP Rulings](https://rulings.cbp.gov/)
- [Ask Rosetta API](https://api.onemarket.world/docs)
