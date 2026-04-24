#!/usr/bin/env python3
"""
SAP-RPT-1-OSS Local Model Prediction

Wrapper for running predictions using the open source SAP-RPT-1-OSS model
from Hugging Face.

Requirements:
    pip install git+https://github.com/SAP-samples/sap-rpt-1-oss
    huggingface-cli login  # Accept model terms at HF

Usage:
    from rpt1_oss_predict import predict_classification, predict_regression
    
    predictions = predict_classification(
        train_data="train.csv",
        test_data="test.csv",
        target_column="CHURN_STATUS"
    )
"""

import os
import sys
import warnings
from typing import Union, Optional, Literal, Tuple
from pathlib import Path

import pandas as pd
import numpy as np

# Check for sap_rpt_oss installation
try:
    from sap_rpt_oss import SAP_RPT_OSS_Classifier, SAP_RPT_OSS_Regressor
    RPT_OSS_AVAILABLE = True
except ImportError:
    RPT_OSS_AVAILABLE = False
    warnings.warn(
        "sap_rpt_oss not installed. Install with:\n"
        "pip install git+https://github.com/SAP-samples/sap-rpt-1-oss\n"
        "Then login to Hugging Face: huggingface-cli login"
    )


def check_hf_auth() -> bool:
    """Check if Hugging Face authentication is configured."""
    token_path = Path.home() / ".huggingface" / "token"
    hf_token_env = os.environ.get("HF_TOKEN") or os.environ.get("HUGGING_FACE_HUB_TOKEN")
    
    if token_path.exists() or hf_token_env:
        return True
    
    print("⚠️  Hugging Face authentication required!")
    print("\nSetup steps:")
    print("1. pip install huggingface_hub")
    print("2. huggingface-cli login")
    print("3. Accept model terms at: https://huggingface.co/SAP/sap-rpt-1-oss")
    print("\nOr set HF_TOKEN environment variable")
    return False


def get_optimal_config() -> dict:
    """
    Detect available GPU and return optimal configuration.
    
    Returns:
        dict with max_context_size and bagging parameters
    """
    try:
        import torch
        if torch.cuda.is_available():
            gpu_memory = torch.cuda.get_device_properties(0).total_memory / (1024**3)
            
            if gpu_memory >= 80:
                return {"max_context_size": 8192, "bagging": 8, "device": "cuda"}
            elif gpu_memory >= 40:
                return {"max_context_size": 4096, "bagging": 4, "device": "cuda"}
            elif gpu_memory >= 24:
                return {"max_context_size": 2048, "bagging": 2, "device": "cuda"}
            else:
                return {"max_context_size": 1024, "bagging": 1, "device": "cuda"}
        else:
            print("⚠️  No GPU detected. Using CPU (will be slow)")
            return {"max_context_size": 1024, "bagging": 1, "device": "cpu"}
    except ImportError:
        print("⚠️  PyTorch not found. Install with: pip install torch")
        return {"max_context_size": 1024, "bagging": 1, "device": "cpu"}


def load_data(
    data: Union[str, Path, pd.DataFrame],
    target_column: Optional[str] = None
) -> Tuple[pd.DataFrame, Optional[pd.Series]]:
    """
    Load data from CSV or DataFrame.
    
    Args:
        data: CSV path or DataFrame
        target_column: Column to extract as target (optional)
        
    Returns:
        Tuple of (features DataFrame, target Series or None)
    """
    if isinstance(data, (str, Path)):
        df = pd.read_csv(data)
    else:
        df = data.copy()
    
    if target_column and target_column in df.columns:
        y = df[target_column]
        X = df.drop(columns=[target_column])
        return X, y
    
    return df, None


def predict_classification(
    train_data: Union[str, Path, pd.DataFrame],
    test_data: Union[str, Path, pd.DataFrame],
    target_column: str,
    max_context_size: Optional[int] = None,
    bagging: Optional[int] = None,
    return_probabilities: bool = True
) -> dict:
    """
    Run classification prediction using SAP-RPT-1-OSS.
    
    Args:
        train_data: Training data with known labels (CSV path or DataFrame)
        test_data: Test data to predict (CSV path or DataFrame)
        target_column: Column name containing class labels
        max_context_size: Context window size (auto-detected if None)
        bagging: Ensemble size for bagging (auto-detected if None)
        return_probabilities: Whether to return class probabilities
        
    Returns:
        dict with 'predictions', 'probabilities' (if requested), 'classes'
        
    Example:
        >>> result = predict_classification(
        ...     train_data="train.csv",
        ...     test_data="test.csv", 
        ...     target_column="CHURN_STATUS"
        ... )
        >>> print(result["predictions"])
    """
    if not RPT_OSS_AVAILABLE:
        raise ImportError("sap_rpt_oss not installed. See setup instructions.")
    
    if not check_hf_auth():
        raise EnvironmentError("Hugging Face authentication required")
    
    # Load data
    X_train, y_train = load_data(train_data, target_column)
    X_test, y_test = load_data(test_data, target_column)
    
    if y_train is None:
        raise ValueError(f"Target column '{target_column}' not found in training data")
    
    # Get optimal config
    config = get_optimal_config()
    max_context_size = max_context_size or config["max_context_size"]
    bagging = bagging or config["bagging"]
    
    print(f"🔧 Config: context_size={max_context_size}, bagging={bagging}, device={config['device']}")
    print(f"📊 Training samples: {len(X_train)}, Test samples: {len(X_test)}")
    
    # Initialize and fit classifier
    print("🚀 Loading SAP-RPT-1-OSS model...")
    clf = SAP_RPT_OSS_Classifier(
        max_context_size=max_context_size,
        bagging=bagging
    )
    
    print("📈 Fitting model...")
    clf.fit(X_train, y_train)
    
    # Predict
    print("🔮 Running predictions...")
    predictions = clf.predict(X_test)
    
    result = {
        "predictions": predictions.tolist() if hasattr(predictions, 'tolist') else list(predictions),
        "classes": clf.classes_.tolist() if hasattr(clf, 'classes_') else None,
        "n_samples": len(X_test),
        "config": {"max_context_size": max_context_size, "bagging": bagging}
    }
    
    if return_probabilities:
        print("📊 Computing probabilities...")
        probabilities = clf.predict_proba(X_test)
        result["probabilities"] = probabilities.tolist() if hasattr(probabilities, 'tolist') else probabilities
    
    print("✅ Prediction complete!")
    return result


def predict_regression(
    train_data: Union[str, Path, pd.DataFrame],
    test_data: Union[str, Path, pd.DataFrame],
    target_column: str,
    max_context_size: Optional[int] = None,
    bagging: Optional[int] = None
) -> dict:
    """
    Run regression prediction using SAP-RPT-1-OSS.
    
    Args:
        train_data: Training data with known values (CSV path or DataFrame)
        test_data: Test data to predict (CSV path or DataFrame)
        target_column: Column name containing target values
        max_context_size: Context window size (auto-detected if None)
        bagging: Ensemble size for bagging (auto-detected if None)
        
    Returns:
        dict with 'predictions' and config info
        
    Example:
        >>> result = predict_regression(
        ...     train_data="deliveries_train.csv",
        ...     test_data="deliveries_test.csv",
        ...     target_column="DELAY_DAYS"
        ... )
        >>> print(result["predictions"])
    """
    if not RPT_OSS_AVAILABLE:
        raise ImportError("sap_rpt_oss not installed. See setup instructions.")
    
    if not check_hf_auth():
        raise EnvironmentError("Hugging Face authentication required")
    
    # Load data
    X_train, y_train = load_data(train_data, target_column)
    X_test, y_test = load_data(test_data, target_column)
    
    if y_train is None:
        raise ValueError(f"Target column '{target_column}' not found in training data")
    
    # Get optimal config
    config = get_optimal_config()
    max_context_size = max_context_size or config["max_context_size"]
    bagging = bagging or config["bagging"]
    
    print(f"🔧 Config: context_size={max_context_size}, bagging={bagging}, device={config['device']}")
    print(f"📊 Training samples: {len(X_train)}, Test samples: {len(X_test)}")
    
    # Initialize and fit regressor
    print("🚀 Loading SAP-RPT-1-OSS model...")
    reg = SAP_RPT_OSS_Regressor(
        max_context_size=max_context_size,
        bagging=bagging
    )
    
    print("📈 Fitting model...")
    reg.fit(X_train, y_train)
    
    # Predict
    print("🔮 Running predictions...")
    predictions = reg.predict(X_test)
    
    print("✅ Prediction complete!")
    return {
        "predictions": predictions.tolist() if hasattr(predictions, 'tolist') else list(predictions),
        "n_samples": len(X_test),
        "config": {"max_context_size": max_context_size, "bagging": bagging}
    }


def predict_from_single_file(
    data: Union[str, Path, pd.DataFrame],
    target_column: str,
    task_type: Literal["classification", "regression"] = "classification",
    train_ratio: float = 0.8,
    **kwargs
) -> pd.DataFrame:
    """
    Convenience function: split single file into train/test and predict.
    
    Args:
        data: CSV path or DataFrame with all data
        target_column: Column to predict
        task_type: "classification" or "regression"
        train_ratio: Fraction for training (default: 0.8)
        **kwargs: Additional args for predict functions
        
    Returns:
        DataFrame with predictions added
    """
    if isinstance(data, (str, Path)):
        df = pd.read_csv(data)
    else:
        df = data.copy()
    
    # Split data
    n_train = int(len(df) * train_ratio)
    train_df = df.iloc[:n_train]
    test_df = df.iloc[n_train:]
    
    # Run prediction
    if task_type == "classification":
        result = predict_classification(train_df, test_df, target_column, **kwargs)
    else:
        result = predict_regression(train_df, test_df, target_column, **kwargs)
    
    # Add predictions to test data
    test_df = test_df.copy()
    test_df[f"{target_column}_PREDICTED"] = result["predictions"]
    
    if "probabilities" in result and result["probabilities"]:
        # Get max probability as confidence
        test_df[f"{target_column}_CONFIDENCE"] = [
            max(p) if isinstance(p, (list, np.ndarray)) else p 
            for p in result["probabilities"]
        ]
    
    return test_df


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="SAP-RPT-1-OSS Prediction")
    parser.add_argument("train_file", help="Training CSV file")
    parser.add_argument("test_file", help="Test CSV file")
    parser.add_argument("target_column", help="Column to predict")
    parser.add_argument("--task", choices=["classification", "regression"], 
                        default="classification", help="Task type")
    parser.add_argument("--context-size", type=int, help="Context window size")
    parser.add_argument("--bagging", type=int, help="Bagging ensemble size")
    parser.add_argument("--output", "-o", help="Output CSV file")
    
    args = parser.parse_args()
    
    # Run prediction
    if args.task == "classification":
        result = predict_classification(
            args.train_file, args.test_file, args.target_column,
            max_context_size=args.context_size, bagging=args.bagging
        )
    else:
        result = predict_regression(
            args.train_file, args.test_file, args.target_column,
            max_context_size=args.context_size, bagging=args.bagging
        )
    
    # Save or print results
    if args.output:
        test_df = pd.read_csv(args.test_file)
        test_df[f"{args.target_column}_PREDICTED"] = result["predictions"]
        test_df.to_csv(args.output, index=False)
        print(f"💾 Saved predictions to: {args.output}")
    else:
        print("\n📋 Predictions:")
        for i, pred in enumerate(result["predictions"][:10]):
            print(f"  [{i}] {pred}")
        if len(result["predictions"]) > 10:
            print(f"  ... and {len(result['predictions']) - 10} more")
