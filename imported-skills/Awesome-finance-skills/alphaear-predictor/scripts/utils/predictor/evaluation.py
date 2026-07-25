import os
import sys
import torch
import pandas as pd
import numpy as np
import glob
from loguru import logger
from datetime import datetime, timedelta

# Setup paths
KRONOS_DIR = os.path.dirname(os.path.abspath(__file__))
SRC_DIR = os.path.dirname(os.path.dirname(KRONOS_DIR))
if SRC_DIR not in sys.path:
    sys.path.insert(0, SRC_DIR)

from ..kronos.auto_synthesis_training import AutoSynthesisTrainer
from ..kronos.model import KronosPredictor
from ..visualizer import VisualizerTools
from ..schema.models import ForecastResult, KLinePoint

class NewsModelEvaluator:
    def __init__(self, model_path=None):
        self.trainer = AutoSynthesisTrainer()
        self.device = self.trainer.device
        
        if model_path is None:
            # Try to find the latest model in exports/models
            model_files = glob.glob(os.path.join(SRC_DIR, "exports/models/*.pt"))
            if not model_files:
                logger.warning("⚠️ No trained models found in exports/models/. Using base model (zero-init proj).")
            else:
                model_path = max(model_files, key=os.path.getctime)
        
        if model_path:
            self.load_weights(model_path)

    def load_weights(self, path):
        logger.info(f"🔄 Loading model weights from {path}...")
        checkpoint = torch.load(path, map_location=self.device)
        self.trainer.model.news_proj.load_state_dict(checkpoint['news_proj_state_dict'])
        logger.success("✅ News projection layer loaded.")

    def evaluate_range(self, start_idx=100, end_idx=200, pred_len=5):
        # 1. Fetch Tickers
        res = self.trainer.db.execute_query("SELECT code FROM stock_list")
        all_tickers = [row['code'] for row in res]
        test_tickers = all_tickers[start_idx:end_idx]
        
        if not test_tickers:
            logger.error(f"No tickers found in range {start_idx}-{end_idx}")
            return

        logger.info(f"🚀 Evaluating News Model on stocks {start_idx} to {end_idx}...")
        
        # 2. Discover Shocks
        shocks = self.trainer.discover_shocks(test_tickers, pred_len=pred_len)
        
        # 3. Associate News & Predict
        self.trainer.model.eval()
        predictor = KronosPredictor(self.trainer.model, self.trainer.tokenizer, device=self.device)
        
        save_dir = os.path.join(SRC_DIR, "exports/evaluation_results")
        os.makedirs(save_dir, exist_ok=True)

        count = 0
        for shock in shocks:
            summary = self.trainer.find_reason_and_verify(shock)
            if not summary:
                continue
            
            logger.info(f"📈 Testing shock: {shock['ticker']} on {shock['date']}")
            
            # Embedding news
            news_emb = self.trainer.embedder.encode(summary)
            
            # Prediction
            h = shock['history']
            t = shock['target']
            actuals = t['close'].values[:pred_len]
            
            x_ts = pd.to_datetime(h['date'])
            future_dates = pd.date_range(start=x_ts.iloc[-1] + timedelta(days=1), periods=pred_len, freq='B')
            y_ts = pd.Series(future_dates)
            
            # A. Base Prediction (No news)
            p_base = predictor.predict(h, x_ts, y_ts, pred_len=pred_len, news_emb=None, verbose=False)
            
            # B. News-Aware Prediction
            p_news = predictor.predict(h, x_ts, y_ts, pred_len=pred_len, news_emb=news_emb, verbose=False)
            
            # Calculate Improvement
            b_preds = p_base['close'].values[:len(actuals)]
            n_preds = p_news['close'].values[:len(actuals)]
            b_mae = np.mean(np.abs(b_preds - actuals))
            n_mae = np.mean(np.abs(n_preds - actuals))
            improvement = (b_mae - n_mae) / (b_mae + 1e-6) * 100

            # C. Visualize
            try:
                def to_kp_list(preds_df):
                    points = []
                    for idx, row in preds_df.iterrows():
                        points.append(KLinePoint(
                            date=str(idx)[:10], open=row['open'], high=row['high'],
                            low=row['low'], close=row['close'], volume=row.get('volume', 0)
                        ))
                    return points

                forecast_obj = ForecastResult(
                    ticker=shock['ticker'],
                    base_forecast=to_kp_list(p_base),
                    adjusted_forecast=to_kp_list(p_news),
                    rationale=summary
                )

                chart = VisualizerTools.generate_stock_chart(
                    df=h, ticker=shock['ticker'],
                    title=f"Test Eval: {shock['ticker']} ({shock['date']}) Imp: {improvement:.1f}%",
                    forecast=forecast_obj,
                    ground_truth=t[['date', 'open', 'high', 'low', 'close', 'volume']]
                )
                
                safe_date = shock['date'].replace("-", "")
                filename = f"test_{shock['ticker']}_{safe_date}.html"
                VisualizerTools.render_chart_to_file(chart, os.path.join(save_dir, filename))
                
                logger.success(f"📊 Result for {shock['ticker']} saved. Base MAE: {b_mae:.4f}, News MAE: {n_mae:.4f}")
                count += 1
            except Exception as e:
                logger.error(f"Visualization failed: {e}")

        logger.info(f"🏁 Finished evaluation. {count} cases visualized in {save_dir}")

if __name__ == "__main__":
    # If you have a specific model, pass the path here. Otherwise it picks the latest.
    evaluator = NewsModelEvaluator()
    evaluator.evaluate_range(start_idx=100, end_idx=200, pred_len=1)
