---
name: data-cleaner
description: Automatically clean data files (CSV/Excel/TSV/JSON) with intelligent preprocessing. Handles missing values, detects and flags outliers, converts data types, removes duplicates, and normalizes strings (trimming, case, full-width/half-width). Outputs cleaned data in original format with detailed Japanese quality report. Use when users upload data files and request "clean this data", "preprocess data", or before visualization/analysis tasks.
---

# Data Cleaner

Automatically analyze and clean data files with intelligent preprocessing and comprehensive quality reporting in Japanese.

## Purpose

Transform raw data files into analysis-ready datasets by automatically detecting and resolving data quality issues. Preserves original file format while providing full transparency through detailed processing reports.

## Workflow

1. **Load data file**
   - Auto-detect format: CSV, Excel (.xlsx, .xls), TSV, JSON
   - Support Japanese encodings: UTF-8, Shift-JIS, CP932
   - Display initial data overview

2. **Analyze data quality**
   - Calculate completeness: missing value counts and percentages
   - Detect data types: numeric, categorical, datetime, text
   - Identify potential issues: duplicates, outliers, type mismatches
   - Generate quality score (0-100)

3. **Process missing values** (automatic decision)
   - **High missing rate (>50%)**: Drop column entirely
   - **Numeric columns**: Impute with median (robust to outliers)
   - **Categorical columns**: Impute with mode (most frequent value)
   - **Datetime columns**: Forward fill or backward fill
   - **Low missing rate (<5%)**: Drop rows
   - **Medium missing rate (5-50%)**: Impute based on column type

4. **Detect and flag outliers** (preserve data)
   - Use IQR method: values outside [Q1 - 1.5×IQR, Q3 + 1.5×IQR]
   - Add flag column: `{column_name}_outlier_flag` (True/False)
   - Do NOT delete outliers - only mark them
   - Apply only to numeric columns

5. **Convert data types**
   - Auto-detect and convert mistyped columns
   - Numeric: Convert string numbers to int/float
   - Datetime: Parse date strings to datetime objects
   - Categorical: Identify low-cardinality text as categories

6. **Remove duplicates**
   - Detect complete row duplicates
   - Keep first occurrence, drop subsequent duplicates
   - Report number of duplicates removed

7. **Normalize strings**
   - **Trim whitespace**: Remove leading/trailing spaces
   - **Case normalization**: Convert to lowercase (configurable)
   - **Full-width/Half-width** (Japanese): Convert to half-width for numbers/alphanumeric

8. **Output cleaned data**
   - Save in original format (CSV → CSV, Excel → Excel, etc.)
   - Filename: `cleaned_{original_filename}`
   - Location: `/mnt/user-data/outputs/`

9. **Generate quality report** (Japanese)
   - Before/after data summary
   - Detailed processing log
   - Quality score with breakdown
   - Recommendations for next steps

## Technical Implementation

### Required Libraries

```python
import pandas as pd
import numpy as np
import json
from pathlib import Path
from datetime import datetime
```

### File Format Detection

```python
def load_data(file_path):
    """Auto-detect and load data file."""
    suffix = Path(file_path).suffix.lower()
    
    if suffix == '.csv':
        # Try multiple encodings
        for enc in ['utf-8', 'shift-jis', 'cp932']:
            try:
                return pd.read_csv(file_path, encoding=enc)
            except:
                continue
    elif suffix in ['.xlsx', '.xls']:
        return pd.read_excel(file_path)
    elif suffix == '.tsv':
        return pd.read_csv(file_path, sep='\t')
    elif suffix == '.json':
        return pd.read_json(file_path)
    else:
        raise ValueError(f"Unsupported file format: {suffix}")
```

### Missing Value Processing

```python
def process_missing_values(df):
    """Handle missing values with automatic strategy selection."""
    log = []
    
    for col in df.columns:
        missing_rate = df[col].isnull().sum() / len(df)
        
        # High missing rate: drop column
        if missing_rate > 0.5:
            df = df.drop(columns=[col])
            log.append(f"列'{col}'を削除（欠損率{missing_rate:.1%}）")
            continue
        
        # Low missing rate: drop rows
        if missing_rate < 0.05:
            before = len(df)
            df = df.dropna(subset=[col])
            after = len(df)
            log.append(f"列'{col}'の欠損行を{before-after}件削除")
            continue
        
        # Medium missing rate: impute
        if pd.api.types.is_numeric_dtype(df[col]):
            median = df[col].median()
            df[col].fillna(median, inplace=True)
            log.append(f"列'{col}'を中央値({median:.2f})で補完")
        elif pd.api.types.is_datetime64_any_dtype(df[col]):
            df[col].fillna(method='ffill', inplace=True)
            log.append(f"列'{col}'を前方補完")
        else:
            mode = df[col].mode()[0] if not df[col].mode().empty else "Unknown"
            df[col].fillna(mode, inplace=True)
            log.append(f"列'{col}'を最頻値({mode})で補完")
    
    return df, log
```

### Outlier Detection and Flagging

```python
def flag_outliers(df):
    """Detect outliers using IQR method and add flag columns."""
    log = []
    
    for col in df.select_dtypes(include=[np.number]).columns:
        Q1 = df[col].quantile(0.25)
        Q3 = df[col].quantile(0.75)
        IQR = Q3 - Q1
        
        lower_bound = Q1 - 1.5 * IQR
        upper_bound = Q3 + 1.5 * IQR
        
        outliers = (df[col] < lower_bound) | (df[col] > upper_bound)
        outlier_count = outliers.sum()
        
        if outlier_count > 0:
            df[f'{col}_outlier_flag'] = outliers
            log.append(f"列'{col}'で{outlier_count}件の異常値を検出（フラグ追加）")
    
    return df, log
```

### Data Type Conversion

```python
def convert_data_types(df):
    """Auto-detect and convert data types."""
    log = []
    
    for col in df.columns:
        # Skip if already numeric or datetime
        if pd.api.types.is_numeric_dtype(df[col]) or pd.api.types.is_datetime64_any_dtype(df[col]):
            continue
        
        # Try numeric conversion
        try:
            df[col] = pd.to_numeric(df[col])
            log.append(f"列'{col}'を数値型に変換")
            continue
        except:
            pass
        
        # Try datetime conversion
        try:
            df[col] = pd.to_datetime(df[col])
            log.append(f"列'{col}'を日付型に変換")
            continue
        except:
            pass
        
        # Check if categorical (low cardinality)
        unique_ratio = df[col].nunique() / len(df)
        if unique_ratio < 0.05:  # Less than 5% unique values
            df[col] = df[col].astype('category')
            log.append(f"列'{col}'をカテゴリ型に変換")
    
    return df, log
```

### String Normalization

```python
def normalize_strings(df):
    """Normalize string columns."""
    import unicodedata
    log = []
    
    for col in df.select_dtypes(include=['object', 'string']).columns:
        if df[col].dtype == 'object':
            # Trim whitespace
            df[col] = df[col].str.strip()
            
            # Convert full-width to half-width (Japanese)
            df[col] = df[col].apply(
                lambda x: unicodedata.normalize('NFKC', str(x)) if pd.notna(x) else x
            )
            
            log.append(f"列'{col}'の文字列を正規化（トリミング、全角半角統一）")
    
    return df, log
```

### Quality Score Calculation

```python
def calculate_quality_score(df_before, df_after):
    """Calculate data quality score (0-100)."""
    scores = []
    
    # Completeness (40 points)
    completeness = 1 - (df_after.isnull().sum().sum() / (df_after.shape[0] * df_after.shape[1]))
    scores.append(completeness * 40)
    
    # No duplicates (20 points)
    duplicate_rate = df_after.duplicated().sum() / len(df_after)
    scores.append((1 - duplicate_rate) * 20)
    
    # Type consistency (20 points)
    numeric_cols = df_after.select_dtypes(include=[np.number]).shape[1]
    type_score = min(numeric_cols / max(df_after.shape[1] * 0.3, 1), 1)
    scores.append(type_score * 20)
    
    # Outlier handling (20 points)
    outlier_flag_cols = [col for col in df_after.columns if '_outlier_flag' in col]
    outlier_score = 20 if len(outlier_flag_cols) > 0 else 15
    scores.append(outlier_score)
    
    return sum(scores)
```

## Quality Report Format

The report (in Japanese) includes:

### 1. データ概要
```
【処理前】
- 行数: 1,000
- 列数: 15
- 欠損値: 150セル (1.0%)
- 重複行: 25件 (2.5%)

【処理後】
- 行数: 975
- 列数: 14
- 欠損値: 0セル (0%)
- 重複行: 0件 (0%)
```

### 2. 処理詳細
```
【欠損値処理】
- 列'売上金額'を中央値(150000.00)で補完: 45件
- 列'備考'を削除（欠損率65.5%）

【異常値検出】
- 列'価格'で12件の異常値を検出（フラグ追加）

【データ型変換】
- 列'注文日'を日付型に変換
- 列'商品コード'を数値型に変換

【重複削除】
- 完全一致の重複行を25件削除

【文字列正規化】
- 列'顧客名'の文字列を正規化（トリミング、全角半角統一）
```

### 3. データ品質スコア
```
総合スコア: 92/100

内訳:
- 完全性（欠損値なし）: 40/40
- 重複なし: 20/20
- 型整合性: 18/20
- 異常値対応: 14/20
```

### 4. 推奨事項
```
✓ データは分析可能な状態です
✓ 異常値フラグ列を確認し、必要に応じて除外してください
- 次のステップ: smart-chart-generatorで可視化を実行できます
```

## Input Requirements

- **Formats**: CSV, Excel (.xlsx, .xls), TSV, JSON
- **Encodings**: UTF-8, Shift-JIS, CP932
- **Column names**: Japanese or English
- **Size**: Recommended < 1,000,000 rows

## Output Specification

### Cleaned Data File
- **Format**: Same as input (CSV → CSV, Excel → Excel)
- **Naming**: `cleaned_{original_filename}`
- **Location**: `/mnt/user-data/outputs/`
- **Additions**: Outlier flag columns (`{col}_outlier_flag`)

### Quality Report
- **Format**: Markdown (`.md`)
- **Naming**: `cleaning_report.md`
- **Language**: Japanese
- **Location**: `/mnt/user-data/outputs/`

## Constraints

### DO
- Auto-detect optimal cleaning strategies
- Preserve original file format
- Flag outliers without deletion
- Generate transparent processing logs
- Support Japanese text and encodings
- Calculate data quality scores

### DO NOT
- Delete outliers (only flag them)
- Perform domain-specific transformations
- Conduct statistical analysis or visualization
- Merge or join multiple datasets
- Modify column names or structure unnecessarily

## Integration with smart-chart-generator

This skill is designed to work seamlessly before `smart-chart-generator`:

```
User uploads raw data
    ↓
data-cleaner: Clean and prepare data
    ↓
Output: cleaned_data.csv
    ↓
smart-chart-generator: Visualize cleaned data
    ↓
Output: Multiple charts + insights
```

Users can say: "このデータをクレンジングして、その後グラフを作成して"

## Error Handling

Common issues and solutions:

1. **Unsupported file format**
   - Check file extension
   - Provide clear error message
   - Suggest supported formats

2. **Encoding errors**
   - Try multiple encodings sequentially
   - Report which encoding worked
   - Suggest UTF-8 for future uploads

3. **Empty or invalid data**
   - Check for empty DataFrame after loading
   - Validate minimum data requirements
   - Provide helpful error message

4. **Memory issues with large files**
   - Warn if file > 1M rows
   - Suggest chunked processing
   - Recommend splitting large datasets

## Processing Decision Logic

### Missing Value Strategy Decision Tree

```
IF missing_rate > 50%:
    → Drop column
ELIF missing_rate < 5%:
    → Drop rows
ELSE:
    IF column is numeric:
        → Impute with median
    ELIF column is datetime:
        → Forward fill
    ELSE:
        → Impute with mode
```

### Outlier Detection Strategy

```
FOR each numeric column:
    Calculate Q1, Q3, IQR
    lower_bound = Q1 - 1.5 × IQR
    upper_bound = Q3 + 1.5 × IQR
    
    IF value < lower_bound OR value > upper_bound:
        → Flag as outlier (add boolean column)
    
    Do NOT delete flagged values
```

### Type Conversion Priority

```
1. Try numeric conversion first
2. If fails, try datetime conversion
3. If fails, check cardinality for categorical
4. Otherwise, keep as string/object
```
