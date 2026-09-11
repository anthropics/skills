#!/usr/bin/env python3
"""
SAP Data Preparation Utilities for RPT-1

Utilities for extracting and preparing SAP data for RPT-1 predictions.
Includes SQL templates for common SAP tables and data transformation functions.

Usage:
    from prepare_sap_data import SAPDataPrep
    
    prep = SAPDataPrep()
    df = prep.prepare_for_prediction(
        data="sap_export.csv",
        target_column="PAYMENT_DEFAULT",
        prediction_rows=[100, 101, 102]  # Row indices to predict
    )
"""

import pandas as pd
import numpy as np
from typing import List, Optional, Union, Dict
from pathlib import Path
from datetime import datetime, timedelta


class SAPDataPrep:
    """Utilities for preparing SAP data for RPT-1 predictions."""
    
    # Common SAP date formats
    SAP_DATE_FORMATS = ["%Y%m%d", "%Y-%m-%d", "%d.%m.%Y", "%m/%d/%Y"]
    
    # SAP field semantic mappings for better RPT-1 understanding
    FIELD_DESCRIPTIONS = {
        # FI Fields
        "BUKRS": "COMPANY_CODE",
        "GJAHR": "FISCAL_YEAR",
        "BELNR": "DOCUMENT_NUMBER",
        "BUZEI": "LINE_ITEM",
        "DMBTR": "AMOUNT_LOCAL_CURRENCY",
        "WRBTR": "AMOUNT_DOC_CURRENCY",
        "SHKZG": "DEBIT_CREDIT_INDICATOR",
        "ZFBDT": "BASELINE_DATE",
        "ZBD1T": "PAYMENT_TERMS_DAYS",
        "SGTXT": "ITEM_TEXT",
        
        # SD Fields
        "VBELN": "SALES_ORDER_NUMBER",
        "POSNR": "ITEM_NUMBER",
        "MATNR": "MATERIAL_NUMBER",
        "KWMENG": "ORDER_QUANTITY",
        "NETWR": "NET_VALUE",
        "WAERK": "CURRENCY",
        "ERDAT": "CREATED_DATE",
        "LFDAT": "DELIVERY_DATE",
        "KUNNR": "CUSTOMER_NUMBER",
        
        # MM Fields
        "EBELN": "PURCHASE_ORDER",
        "EBELP": "PO_ITEM",
        "LIFNR": "VENDOR_NUMBER",
        "MENGE": "QUANTITY",
        "MEINS": "UNIT",
        "NETPR": "NET_PRICE",
        "EINDT": "DELIVERY_DATE_REQUESTED",
        
        # Master Data
        "NAME1": "NAME",
        "LAND1": "COUNTRY",
        "ORT01": "CITY",
        "PSTLZ": "POSTAL_CODE",
        "KTOKD": "CUSTOMER_ACCOUNT_GROUP",
        "KLIMK": "CREDIT_LIMIT",
    }
    
    def __init__(self):
        """Initialize SAP data preparation utilities."""
        pass
    
    def rename_sap_fields(self, df: pd.DataFrame, custom_mappings: Dict[str, str] = None) -> pd.DataFrame:
        """
        Rename SAP technical field names to semantic descriptions.
        RPT-1 performs better with descriptive column names.
        
        Args:
            df: DataFrame with SAP field names
            custom_mappings: Additional field mappings to apply
            
        Returns:
            DataFrame with renamed columns
        """
        mappings = self.FIELD_DESCRIPTIONS.copy()
        if custom_mappings:
            mappings.update(custom_mappings)
        
        # Only rename columns that exist in dataframe
        rename_dict = {k: v for k, v in mappings.items() if k in df.columns}
        return df.rename(columns=rename_dict)
    
    def parse_sap_dates(self, df: pd.DataFrame, date_columns: List[str]) -> pd.DataFrame:
        """
        Parse SAP date formats to standard datetime.
        
        Args:
            df: DataFrame with SAP dates
            date_columns: List of column names containing dates
            
        Returns:
            DataFrame with parsed dates
        """
        df = df.copy()
        for col in date_columns:
            if col not in df.columns:
                continue
            
            for fmt in self.SAP_DATE_FORMATS:
                try:
                    df[col] = pd.to_datetime(df[col], format=fmt, errors="coerce")
                    if df[col].notna().any():
                        break
                except Exception:
                    continue
        
        return df
    
    def calculate_derived_features(
        self,
        df: pd.DataFrame,
        date_column: str,
        reference_date: Optional[datetime] = None
    ) -> pd.DataFrame:
        """
        Calculate derived features useful for predictions.
        
        Args:
            df: DataFrame with parsed dates
            date_column: Name of date column for calculations
            reference_date: Reference date for age calculations (default: today)
            
        Returns:
            DataFrame with additional derived columns
        """
        df = df.copy()
        reference_date = reference_date or datetime.now()
        
        if date_column in df.columns and pd.api.types.is_datetime64_any_dtype(df[date_column]):
            df[f"DAYS_SINCE_{date_column}"] = (reference_date - df[date_column]).dt.days
            df[f"MONTH_OF_{date_column}"] = df[date_column].dt.month
            df[f"QUARTER_OF_{date_column}"] = df[date_column].dt.quarter
            df[f"YEAR_OF_{date_column}"] = df[date_column].dt.year
            df[f"DAY_OF_WEEK_{date_column}"] = df[date_column].dt.dayofweek
        
        return df
    
    def prepare_for_prediction(
        self,
        data: Union[str, Path, pd.DataFrame],
        target_column: str,
        prediction_rows: Optional[List[int]] = None,
        mask_value: str = "[PREDICT]"
    ) -> pd.DataFrame:
        """
        Prepare dataset for RPT-1 prediction by masking target values.
        
        Args:
            data: CSV path or DataFrame
            target_column: Column to predict
            prediction_rows: Row indices to predict (default: last 10%)
            mask_value: Placeholder for prediction (default: [PREDICT])
            
        Returns:
            DataFrame ready for RPT-1 with masked values
        """
        if isinstance(data, (str, Path)):
            df = pd.read_csv(data)
        else:
            df = data.copy()
        
        if target_column not in df.columns:
            raise ValueError(f"Target column '{target_column}' not found")
        
        # Default: predict last 10% of rows
        if prediction_rows is None:
            n_predict = max(1, len(df) // 10)
            prediction_rows = list(range(len(df) - n_predict, len(df)))
        
        # Mask target values for prediction rows
        df[target_column] = df[target_column].astype(str)
        df.loc[prediction_rows, target_column] = mask_value
        
        return df
    
    def split_train_predict(
        self,
        data: Union[str, Path, pd.DataFrame],
        target_column: str,
        train_ratio: float = 0.8
    ) -> tuple:
        """
        Split data into training and prediction sets.
        
        Args:
            data: CSV path or DataFrame
            target_column: Column containing target values
            train_ratio: Fraction of data for training (default: 0.8)
            
        Returns:
            Tuple of (train_df, predict_df)
        """
        if isinstance(data, (str, Path)):
            df = pd.read_csv(data)
        else:
            df = data.copy()
        
        n_train = int(len(df) * train_ratio)
        train_df = df.iloc[:n_train].copy()
        predict_df = df.iloc[n_train:].copy()
        
        # Remove target values from prediction set
        predict_df[target_column] = "[PREDICT]"
        
        return train_df, predict_df


# SQL Templates for SAP Data Extraction
SQL_TEMPLATES = {
    "customer_churn": """
-- Customer Churn Analysis Dataset
-- Extract from SAP SD/FI for churn prediction

SELECT 
    kna1.KUNNR AS CUSTOMER_NUMBER,
    kna1.NAME1 AS CUSTOMER_NAME,
    kna1.LAND1 AS COUNTRY,
    kna1.KTOKD AS ACCOUNT_GROUP,
    knb1.KLIMK AS CREDIT_LIMIT,
    
    -- Order metrics (last 12 months)
    COUNT(DISTINCT vbak.VBELN) AS ORDERS_LAST_12M,
    SUM(vbak.NETWR) AS REVENUE_LAST_12M,
    MAX(vbak.ERDAT) AS LAST_ORDER_DATE,
    DATEDIFF(DAY, MAX(vbak.ERDAT), CURRENT_DATE) AS DAYS_SINCE_LAST_ORDER,
    
    -- Payment behavior
    AVG(bsid.VERZN) AS AVG_PAYMENT_DELAY_DAYS,
    COUNT(CASE WHEN bsid.VERZN > 30 THEN 1 END) AS LATE_PAYMENTS_COUNT,
    
    -- Target: Define based on business rules
    CASE 
        WHEN DATEDIFF(DAY, MAX(vbak.ERDAT), CURRENT_DATE) > 365 THEN 'CHURNED'
        WHEN DATEDIFF(DAY, MAX(vbak.ERDAT), CURRENT_DATE) > 180 THEN 'AT_RISK'
        ELSE 'ACTIVE'
    END AS CHURN_STATUS

FROM KNA1 kna1
LEFT JOIN KNB1 knb1 ON kna1.KUNNR = knb1.KUNNR
LEFT JOIN VBAK vbak ON kna1.KUNNR = vbak.KUNNR 
    AND vbak.ERDAT >= ADD_MONTHS(CURRENT_DATE, -12)
LEFT JOIN BSID bsid ON kna1.KUNNR = bsid.KUNNR

GROUP BY kna1.KUNNR, kna1.NAME1, kna1.LAND1, kna1.KTOKD, knb1.KLIMK
""",

    "payment_default": """
-- Payment Default Prediction Dataset
-- Extract from SAP FI-AR

SELECT
    bsid.KUNNR AS CUSTOMER_NUMBER,
    bsid.BUKRS AS COMPANY_CODE,
    bsid.BELNR AS DOCUMENT_NUMBER,
    bsid.GJAHR AS FISCAL_YEAR,
    bsid.WRBTR AS INVOICE_AMOUNT,
    bsid.WAERS AS CURRENCY,
    bsid.ZFBDT AS BASELINE_DATE,
    bsid.ZBD1T AS PAYMENT_TERMS_DAYS,
    
    -- Customer credit info
    knb1.KLIMK AS CREDIT_LIMIT,
    knb1.SKFOR AS OUTSTANDING_BALANCE,
    
    -- Historical payment behavior
    (SELECT AVG(VERZN) FROM BSAD WHERE KUNNR = bsid.KUNNR) AS HIST_AVG_DELAY,
    (SELECT COUNT(*) FROM BSAD WHERE KUNNR = bsid.KUNNR AND VERZN > 60) AS HIST_SEVERE_DELAYS,
    
    -- Target: Payment default indicator
    CASE 
        WHEN bsad.AUGDT IS NULL AND DATEDIFF(DAY, bsid.ZFBDT + bsid.ZBD1T, CURRENT_DATE) > 90 
        THEN 'DEFAULT'
        ELSE 'PAID'
    END AS PAYMENT_STATUS

FROM BSID bsid
LEFT JOIN BSAD bsad ON bsid.BUKRS = bsad.BUKRS AND bsid.BELNR = bsad.BELNR
LEFT JOIN KNB1 knb1 ON bsid.KUNNR = knb1.KUNNR AND bsid.BUKRS = knb1.BUKRS

WHERE bsid.KOART = 'D'  -- Customer items only
""",

    "delivery_delay": """
-- Delivery Delay Prediction Dataset
-- Extract from SAP SD

SELECT
    likp.VBELN AS DELIVERY_NUMBER,
    likp.KUNNR AS CUSTOMER_NUMBER,
    likp.LFDAT AS PLANNED_DELIVERY_DATE,
    likp.WADAT_IST AS ACTUAL_DELIVERY_DATE,
    likp.VSTEL AS SHIPPING_POINT,
    likp.ROUTE AS ROUTE,
    
    -- Order details
    vbak.AUART AS ORDER_TYPE,
    vbak.VKORG AS SALES_ORG,
    SUM(lips.LFIMG) AS TOTAL_QUANTITY,
    COUNT(DISTINCT lips.MATNR) AS DISTINCT_MATERIALS,
    
    -- Carrier info
    likp.TDLNR AS CARRIER,
    
    -- Target: Delay in days (for regression) or category (for classification)
    DATEDIFF(DAY, likp.LFDAT, likp.WADAT_IST) AS DELAY_DAYS,
    CASE 
        WHEN DATEDIFF(DAY, likp.LFDAT, likp.WADAT_IST) <= 0 THEN 'ON_TIME'
        WHEN DATEDIFF(DAY, likp.LFDAT, likp.WADAT_IST) <= 3 THEN 'MINOR_DELAY'
        WHEN DATEDIFF(DAY, likp.LFDAT, likp.WADAT_IST) <= 7 THEN 'MODERATE_DELAY'
        ELSE 'SEVERE_DELAY'
    END AS DELAY_CATEGORY

FROM LIKP likp
JOIN LIPS lips ON likp.VBELN = lips.VBELN
JOIN VBAK vbak ON lips.VGBEL = vbak.VBELN

WHERE likp.WADAT_IST IS NOT NULL  -- Completed deliveries only

GROUP BY likp.VBELN, likp.KUNNR, likp.LFDAT, likp.WADAT_IST, 
         likp.VSTEL, likp.ROUTE, vbak.AUART, vbak.VKORG, likp.TDLNR
""",

    "journal_anomaly": """
-- Journal Entry Anomaly Detection Dataset
-- Extract from SAP FI-GL (S/4HANA ACDOCA)

SELECT
    acdoca.RCLNT AS CLIENT,
    acdoca.RBUKRS AS COMPANY_CODE,
    acdoca.GJAHR AS FISCAL_YEAR,
    acdoca.BELNR AS DOCUMENT_NUMBER,
    acdoca.DOCLN AS LINE_ITEM,
    acdoca.RACCT AS GL_ACCOUNT,
    acdoca.RCNTR AS COST_CENTER,
    acdoca.HSL AS AMOUNT_LOCAL,
    acdoca.RHCUR AS LOCAL_CURRENCY,
    acdoca.BUDAT AS POSTING_DATE,
    acdoca.CPUDT AS ENTRY_DATE,
    acdoca.USNAM AS USER_NAME,
    acdoca.BLART AS DOCUMENT_TYPE,
    
    -- Time-based features
    EXTRACT(HOUR FROM acdoca.CPUTM) AS ENTRY_HOUR,
    EXTRACT(DOW FROM acdoca.CPUDT) AS ENTRY_DAY_OF_WEEK,
    
    -- Amount analysis
    ABS(acdoca.HSL) AS AMOUNT_ABS,
    CASE WHEN acdoca.HSL < 0 THEN 'CREDIT' ELSE 'DEBIT' END AS DC_INDICATOR,
    
    -- Target: Anomaly flag (define based on business rules or historical labels)
    -- This should be labeled by auditors for training data
    anomaly_label AS ANOMALY_FLAG

FROM ACDOCA acdoca
LEFT JOIN anomaly_labels ON acdoca.BELNR = anomaly_labels.BELNR  -- Your labeled data

WHERE acdoca.GJAHR >= YEAR(CURRENT_DATE) - 2
"""
}


def get_sql_template(use_case: str) -> str:
    """
    Get SQL extraction template for SAP use case.
    
    Args:
        use_case: One of 'customer_churn', 'payment_default', 
                  'delivery_delay', 'journal_anomaly'
                  
    Returns:
        SQL template string
    """
    if use_case not in SQL_TEMPLATES:
        available = list(SQL_TEMPLATES.keys())
        raise ValueError(f"Unknown use case '{use_case}'. Available: {available}")
    
    return SQL_TEMPLATES[use_case]


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: python prepare_sap_data.py <use_case>")
        print("Available use cases:", list(SQL_TEMPLATES.keys()))
        sys.exit(1)
    
    use_case = sys.argv[1]
    print(f"\n--- SQL Template for {use_case} ---\n")
    print(get_sql_template(use_case))
