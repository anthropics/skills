#!/usr/bin/env python3
"""
Batch Prediction Script for SAP-RPT-1-OSS

Process large SAP datasets in batches using the local OSS model.
Handles chunking, memory management, and result aggregation.

Usage:
    python batch_predict.py train.csv test.csv target_column output.csv --task classification
"""

import argparse
import time
import pandas as pd
import numpy as np
from pathlib import Path
from typing import Optional, Literal, Union

# Check for sap_rpt_oss
try:
    from sap_rpt_oss import SAP_RPT_OSS_Classifier, SAP_RPT_OSS_Regressor
    RPT_OSS_AVAILABLE = True
except ImportError:
    RPT_OSS_AVAILABLE = False


def get_optimal_config() -> dict:
    """Detect GPU and return optimal configuration."""
    try:
        import torch
        if torch.cuda.is_available():
            gpu_mem = torch.cuda.get_device_properties(0).total_memory / (1024**3)
            if gpu_mem >= 80:
                return {"max_context_size": 8192, "bagging": 8}
            elif gpu_mem >= 40:
                return {"max_context_size": 4096, "bagging": 4}
            elif gpu_mem >= 24:
                return {"max_context_size": 2048, "bagging": 2}
            else:
                return {"max_context_size": 1024, "bagging": 1}
    except:
        pass
    return {"max_context_size": 1024, "bagging": 1}


def batch_predict_oss(
    train_file: str,
    test_file: str,
    target_column: str,
    output_file: str,
    task_type: Literal["classification", "regression"] = "classification",
    chunk_size: int = 100,
    max_context_size: Optional[int] = None,
    bagging: Optional[int] = None
) -> pd.DataFrame:
    """
    Run batch predictions using SAP-RPT-1-OSS local model.
    
    Args:
        train_file: Path to training CSV (with labels)
        test_file: Path to test CSV (to predict)
        target_column: Column to predict
        output_file: Path for output CSV
        task_type: "classification" or "regression"
        chunk_size: Rows per prediction batch
        max_context_size: Override auto-detected context size
        bagging: Override auto-detected bagging
        
    Returns:
        DataFrame with predictions
    """
    if not RPT_OSS_AVAILABLE:
        raise ImportError(
            "sap_rpt_oss not installed.\n"
            "Install with: pip install git+https://github.com/SAP-samples/sap-rpt-1-oss\n"
            "Then login: huggingface-cli login"
        )
    
    # Load data
    train_df = pd.read_csv(train_file)
    test_df = pd.read_csv(test_file)
    
    print(f"📂 Loaded {len(train_df)} training rows, {len(test_df)} test rows")
    
    if target_column not in train_df.columns:
        raise ValueError(f"Target '{target_column}' not in training data")
    
    # Prepare X, y
    X_train = train_df.drop(columns=[target_column])
    y_train = train_df[target_column]
    
    # Remove target from test if present
    if target_column in test_df.columns:
        X_test = test_df.drop(columns=[target_column])
    else:
        X_test = test_df.copy()
    
    # Get config
    config = get_optimal_config()
    max_context_size = max_context_size or config["max_context_size"]
    bagging = bagging or config["bagging"]
    
    print(f"🔧 Config: context={max_context_size}, bagging={bagging}")
    
    # Initialize model
    print("🚀 Loading SAP-RPT-1-OSS model...")
    if task_type == "classification":
        model = SAP_RPT_OSS_Classifier(max_context_size=max_context_size, bagging=bagging)
    else:
        model = SAP_RPT_OSS_Regressor(max_context_size=max_context_size, bagging=bagging)
    
    # Fit model
    print("📈 Fitting model on training data...")
    model.fit(X_train, y_train)
    
    # Predict in chunks
    print(f"🔮 Predicting {len(X_test)} rows in chunks of {chunk_size}...")
    all_predictions = []
    all_probabilities = []
    
    n_chunks = (len(X_test) + chunk_size - 1) // chunk_size
    
    for i in range(0, len(X_test), chunk_size):
        chunk_idx = i // chunk_size + 1
        chunk = X_test.iloc[i:i + chunk_size]
        
        print(f"  Processing chunk {chunk_idx}/{n_chunks}...", end=" ")
        start_time = time.time()
        
        preds = model.predict(chunk)
        all_predictions.extend(preds.tolist() if hasattr(preds, 'tolist') else list(preds))
        
        if task_type == "classification" and hasattr(model, 'predict_proba'):
            probs = model.predict_proba(chunk)
            all_probabilities.extend(probs.tolist() if hasattr(probs, 'tolist') else list(probs))
        
        elapsed = time.time() - start_time
        print(f"✓ ({elapsed:.1f}s)")
    
    # Add predictions to test data
    result_df = test_df.copy()
    result_df[f"{target_column}_PREDICTED"] = all_predictions
    
    if all_probabilities:
        result_df[f"{target_column}_CONFIDENCE"] = [
            max(p) if isinstance(p, (list, np.ndarray)) else p
            for p in all_probabilities
        ]
    
    # Save results
    result_df.to_csv(output_file, index=False)
    print(f"\n✅ Saved {len(all_predictions)} predictions to: {output_file}")
    
    return result_df


def main():
    parser = argparse.ArgumentParser(
        description="Batch prediction using SAP-RPT-1-OSS"
    )
    parser.add_argument("train_file", help="Training CSV with labels")
    parser.add_argument("test_file", help="Test CSV to predict")
    parser.add_argument("target_column", help="Column to predict")
    parser.add_argument("output_file", help="Output CSV path")
    parser.add_argument(
        "--task",
        choices=["classification", "regression"],
        default="classification",
        help="Task type (default: classification)"
    )
    parser.add_argument(
        "--chunk-size",
        type=int,
        default=100,
        help="Rows per batch (default: 100)"
    )
    parser.add_argument(
        "--context-size",
        type=int,
        help="Context window size (auto-detected if not set)"
    )
    parser.add_argument(
        "--bagging",
        type=int,
        help="Bagging ensemble size (auto-detected if not set)"
    )
    
    args = parser.parse_args()
    
    batch_predict_oss(
        train_file=args.train_file,
        test_file=args.test_file,
        target_column=args.target_column,
        output_file=args.output_file,
        task_type=args.task,
        chunk_size=args.chunk_size,
        max_context_size=args.context_size,
        bagging=args.bagging
    )


if __name__ == "__main__":
    main()
