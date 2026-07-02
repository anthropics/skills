#!/usr/bin/env python3
"""
SAP-RPT-1 Playground API Client

A Python client for interacting with SAP's RPT-1 tabular prediction model
through the RPT Playground API.

Usage:
    from rpt1_api import RPT1Client
    
    client = RPT1Client(token="YOUR_TOKEN")
    result = client.predict(data="sales_data.csv", target_column="CHURN", task_type="classification")
"""

import os
import json
import pandas as pd
from typing import Union, Optional, Literal
from pathlib import Path

try:
    import httpx
except ImportError:
    import subprocess
    subprocess.run(["pip", "install", "httpx", "--quiet", "--break-system-packages"])
    import httpx


class RPT1Client:
    """Client for SAP RPT-1 Playground API."""
    
    BASE_URL = "https://rpt-playground.sap.com/api"
    
    def __init__(self, token: Optional[str] = None):
        """
        Initialize RPT1 client.
        
        Args:
            token: RPT Playground API token. If not provided, reads from
                   RPT_TOKEN environment variable.
        """
        self.token = token or os.environ.get("RPT_TOKEN")
        if not self.token:
            raise ValueError(
                "RPT token required. Get it from https://rpt-playground.sap.com "
                "(bottom of page) and pass as token= or set RPT_TOKEN env var."
            )
        self.client = httpx.Client(
            base_url=self.BASE_URL,
            headers={"Authorization": f"Bearer {self.token}"},
            timeout=120.0
        )
    
    def predict(
        self,
        data: Union[str, Path, pd.DataFrame],
        target_column: str,
        task_type: Literal["classification", "regression"] = "classification",
        model_version: Literal["fast", "accurate"] = "accurate"
    ) -> dict:
        """
        Run prediction on tabular data.
        
        Args:
            data: CSV file path or pandas DataFrame with training examples
            target_column: Column name to predict (will be masked with [PREDICT])
            task_type: "classification" for categories, "regression" for numbers
            model_version: "fast" for low latency, "accurate" for best results
            
        Returns:
            dict with predictions and confidence scores
            
        Example:
            >>> client = RPT1Client(token="xxx")
            >>> result = client.predict(
            ...     data="customers.csv",
            ...     target_column="CHURN_RISK",
            ...     task_type="classification"
            ... )
            >>> print(result["predictions"])
        """
        # Load data
        if isinstance(data, (str, Path)):
            df = pd.read_csv(data)
        else:
            df = data.copy()
        
        # Validate target column exists
        if target_column not in df.columns:
            raise ValueError(f"Target column '{target_column}' not found. Available: {list(df.columns)}")
        
        # Prepare payload
        payload = {
            "data": df.to_dict(orient="records"),
            "target_column": target_column,
            "task_type": task_type,
            "model_version": model_version
        }
        
        response = self.client.post("/predict", json=payload)
        response.raise_for_status()
        return response.json()
    
    def predict_with_mask(
        self,
        data: Union[str, Path, pd.DataFrame],
        model_version: Literal["fast", "accurate"] = "accurate"
    ) -> dict:
        """
        Run prediction on data where target values are already marked with [PREDICT].
        
        Args:
            data: CSV/DataFrame with [PREDICT] placeholders in cells to predict
            model_version: "fast" or "accurate"
            
        Returns:
            dict with filled predictions
        """
        if isinstance(data, (str, Path)):
            df = pd.read_csv(data)
        else:
            df = data.copy()
        
        payload = {
            "data": df.to_dict(orient="records"),
            "model_version": model_version
        }
        
        response = self.client.post("/predict-masked", json=payload)
        response.raise_for_status()
        return response.json()
    
    def batch_predict(
        self,
        train_data: Union[str, Path, pd.DataFrame],
        predict_data: Union[str, Path, pd.DataFrame],
        target_column: str,
        task_type: Literal["classification", "regression"] = "classification",
        model_version: Literal["fast", "accurate"] = "accurate"
    ) -> dict:
        """
        Batch prediction with separate training and prediction datasets.
        
        Args:
            train_data: CSV/DataFrame with labeled examples (known outcomes)
            predict_data: CSV/DataFrame with rows to predict (target column will be filled)
            target_column: Column to predict
            task_type: "classification" or "regression"
            model_version: "fast" or "accurate"
            
        Returns:
            dict with predictions for predict_data rows
        """
        # Load data
        if isinstance(train_data, (str, Path)):
            train_df = pd.read_csv(train_data)
        else:
            train_df = train_data.copy()
            
        if isinstance(predict_data, (str, Path)):
            predict_df = pd.read_csv(predict_data)
        else:
            predict_df = predict_data.copy()
        
        payload = {
            "train_data": train_df.to_dict(orient="records"),
            "predict_data": predict_df.to_dict(orient="records"),
            "target_column": target_column,
            "task_type": task_type,
            "model_version": model_version
        }
        
        response = self.client.post("/batch-predict", json=payload)
        response.raise_for_status()
        return response.json()
    
    def health_check(self) -> bool:
        """Check if API is accessible."""
        try:
            response = self.client.get("/health")
            return response.status_code == 200
        except Exception:
            return False


def predict_from_csv(
    csv_path: str,
    target_column: str,
    task_type: str = "classification",
    token: Optional[str] = None
) -> pd.DataFrame:
    """
    Convenience function to predict from CSV file.
    
    Args:
        csv_path: Path to CSV file
        target_column: Column to predict
        task_type: "classification" or "regression"
        token: RPT API token (or set RPT_TOKEN env var)
        
    Returns:
        DataFrame with predictions added
    """
    client = RPT1Client(token=token)
    result = client.predict(csv_path, target_column, task_type)
    
    df = pd.read_csv(csv_path)
    df[f"{target_column}_PREDICTED"] = result.get("predictions", [])
    
    if "probabilities" in result:
        df[f"{target_column}_CONFIDENCE"] = [
            max(p.values()) if isinstance(p, dict) else p 
            for p in result["probabilities"]
        ]
    
    return df


if __name__ == "__main__":
    # Example usage
    import sys
    
    if len(sys.argv) < 3:
        print("Usage: python rpt1_api.py <csv_file> <target_column> [task_type]")
        print("Example: python rpt1_api.py customers.csv CHURN_RISK classification")
        sys.exit(1)
    
    csv_file = sys.argv[1]
    target_col = sys.argv[2]
    task = sys.argv[3] if len(sys.argv) > 3 else "classification"
    
    result_df = predict_from_csv(csv_file, target_col, task)
    
    output_file = csv_file.replace(".csv", "_predictions.csv")
    result_df.to_csv(output_file, index=False)
    print(f"Predictions saved to: {output_file}")
