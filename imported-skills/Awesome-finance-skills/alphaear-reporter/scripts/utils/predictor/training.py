import os
import sys
import time
import torch
import torch.nn as nn
import pandas as pd
import numpy as np
import json
import random
from loguru import logger
from datetime import datetime, timedelta
from sentence_transformers import SentenceTransformer
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

# Setup paths
KRONOS_DIR = os.path.dirname(os.path.abspath(__file__))
SRC_DIR = os.path.dirname(os.path.dirname(KRONOS_DIR))
if SRC_DIR not in sys.path:
    sys.path.insert(0, SRC_DIR)

from ..kronos.model import Kronos, KronosTokenizer, KronosPredictor
from ..database_manager import DatabaseManager
from ..stock_tools import StockTools
from ..search_tools import SearchTools
from ..llm.factory import get_model
from ..visualizer import VisualizerTools
from ..schema.models import ForecastResult, KLinePoint
from agno.agent import Agent

class AutoSynthesisTrainer:
    def __init__(self, news_dim=384):
        self.device = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
        self.db = DatabaseManager()
        self.tools = StockTools(self.db)
        self.searcher = SearchTools(self.db)
        # Try loading from local cache first to avoid network timeouts
        model_name = os.getenv('EMBEDDING_MODEL', 'sentence-transformers/all-MiniLM-L6-v2')
        try:
            logger.info(f"🔄 Attempting to load {model_name} from local cache...")
            self.embedder = SentenceTransformer(model_name, device=self.device, local_files_only=True)
            logger.success("✅ Model loaded from local cache.")
        except Exception:
            logger.warning("⚠️ Local cache not found or incomplete. Attempting to download...")
            self.embedder = SentenceTransformer(model_name, device=self.device)
        self.news_dim = news_dim
        
        # Try loading from local cache first to avoid network timeouts
        try:
            logger.info("🔄 Attempting to load Kronos and Tokenizer from local cache...")
            self.tokenizer = KronosTokenizer.from_pretrained("NeoQuasar/Kronos-Tokenizer-base", local_files_only=True).to(self.device)
            base_model = Kronos.from_pretrained("NeoQuasar/Kronos-base", local_files_only=True)
            logger.success("✅ Kronos and Tokenizer loaded from local cache.")
        except Exception:
            logger.warning("⚠️ Local Kronos/Tokenizer not found or incomplete. Attempting to download...")
            self.tokenizer = KronosTokenizer.from_pretrained("NeoQuasar/Kronos-Tokenizer-base").to(self.device)
            base_model = Kronos.from_pretrained("NeoQuasar/Kronos-base")
            
        self.model = Kronos(
            base_model.s1_bits, base_model.s2_bits, base_model.n_layers, 
            base_model.d_model, base_model.n_heads, base_model.ff_dim,
            base_model.ffn_dropout_p, base_model.attn_dropout_p,
            base_model.resid_dropout_p, base_model.token_dropout_p,
            base_model.learn_te, news_dim=self.news_dim
        ).to(self.device)
        self.model.load_state_dict(base_model.state_dict(), strict=False)
        
        # LLM for causality verification
        provider = os.getenv("LLM_PROVIDER", "ust")
        model_id = os.getenv("LLM_MODEL", "Qwen")
        self.llm_agent = Agent(model=get_model(provider, model_id))

    def discover_shocks(self, ticker_list, threshold=2.0, limit_per_stock=5, days=365, pred_len=5):
        """1. Find days with significant price movements (Look back 1 year)"""
        shocks = []
        end_date = datetime.now().strftime("%Y-%m-%d")
        start_date = (datetime.now() - timedelta(days=days)).strftime("%Y-%m-%d")
        
        for ticker in ticker_list:
            df = self.tools.get_stock_price(ticker, start_date=start_date, end_date=end_date)
            if df.empty or len(df) < 60:
                continue
            
            # Look for big moves
            moves = df[df['change_pct'].abs() > threshold].copy()
            if moves.empty: continue
            
            count = 0
            for idx, row in moves.iterrows():
                # Ensure we have history before this day AND enough future days for eval
                date_idx = df.index.get_loc(idx)
                if date_idx < 50 or date_idx + pred_len > len(df): continue
                
                shocks.append({
                    'ticker': ticker,
                    'date': row['date'],
                    'change': row['change_pct'],
                    'history': df.iloc[date_idx-50:date_idx],
                    'target': df.iloc[date_idx:date_idx + pred_len] # Now capturing pred_len days
                })
                count += 1
                if count >= limit_per_stock: break
        
        logger.info(f"✨ Discovered {len(shocks)} potential price shocks over the last {days} days.")
        return shocks

    def find_reason_and_verify(self, shock):
        """2. Search for reasons and verify causality using LLM"""
        ticker_info = self.db.get_stock_by_code(shock['ticker'])
        name = ticker_info['name'] if ticker_info else shock['ticker']
        date_str = shock['date']
        
        # Try multiple query variations and engines
        queries = [
            f"{name} ({shock['ticker']}) {date_str} 为什么涨跌 原因",
            f"{name} {date_str} 异动 原因",
            f"{shock['ticker']} {date_str} 新闻"
        ]
        
        search_results = []
        for query in queries:
            logger.info(f"🔍 Searching for reason: {query}")
            # Try alternate engines
            for engine in ["baidu"]:
                try:
                    results = self.searcher.search_list(query, engine=engine, max_results=3, enrich=False)
                    if results:
                        search_results = results
                        break
                except Exception as e:
                    logger.warning(f"Search failed for {query} on {engine}: {e}")
            
            if search_results:
                break
            time.sleep(random.uniform(1.0, 2.0))
            
        if not search_results:
            logger.warning(f"⚠️ No search results found for {name} on {date_str} after multiple attempts.")
            return None
        
        context = "\n".join([f"- {r['title']}: {r.get('content', '')[:300]}" for r in search_results])
        
        prompt = f"""
        任务：判断以下新闻是否解释了该股票在 {date_str} 的 {shock['change']:.2f}% 价格变动。
        
        股票：{name}
        日期：{date_str}
        变动：{shock['change']:.2f}%
        
        搜索结果：
        {context}
        
        要求：
        1. 该新闻是否在该日期左右发生？
        2. 该新闻是否能逻辑上解释这种大幅波动（如财报、利好政策、重组、大环境暴跌等）？
        3. 如果是，请总结一段 100 字以内的“核心推动原因”。
        4. 返回 JSON: {{"is_causal": true/false, "summary": "原因摘要"}}
        """
        
        try:
            res = self.llm_agent.run(prompt)
            data = json.loads(res.content.replace('```json', '').replace('```', '').strip())
            if data.get('is_causal'):
                logger.success(f"✅ Verified cause for {name} on {date_str}: {data['summary']}")
                return data['summary']
            else:
                logger.warning(f"❌ Verified cause for {name} on {date_str}: {data['summary']}")
                return None
        except Exception as e:
            logger.warning(f"Verification failed: {e}")
        return None

    def save_model(self, path=None):
        """Save the news_proj weights"""
        if path is None:
            save_dir = os.path.join(SRC_DIR, "exports/models")
            os.makedirs(save_dir, exist_ok=True)
            path = os.path.join(save_dir, f"kronos_news_v1_{datetime.now().strftime('%Y%m%d_%H%M')}.pt")
        
        # We only really need to save the news_proj part as it's the only one we train
        torch.save({
            'news_proj_state_dict': self.model.news_proj.state_dict(),
            'news_dim': self.news_dim,
            'd_model': self.model.d_model
        }, path)
        logger.success(f"💾 Model weights saved to {path}")
        return path

    def run_synthesis_and_train(self, tickers, pred_len=5):
        # 1. Discovery
        shocks = self.discover_shocks(tickers, pred_len=pred_len)
        print(f'find {len(shocks)} shocks')
        
        # 2. News Association & Verification
        dataset = []
        max_news_items = 200 # Limit to 200 news items per session to avoid search bans
        
        logger.info(f"🧬 Starting News Association for {len(shocks)} shocks (Max limit: {max_news_items})")
        
        for i, shock in enumerate(shocks):
            if len(dataset) >= max_news_items:
                logger.info("Reached maximum news items limit for this session.")
                break
                
            summary = self.find_reason_and_verify(shock)
            if summary:
                # 3. Embedding news
                emb = self.embedder.encode(summary)
                dataset.append({
                    'history': shock['history'],
                    'target': shock['target'],
                    'news_emb': emb,
                    'summary': summary
                })
            
            # Add delay after search with randomness to avoid being blocked
            if i < len(shocks) - 1:
                delay = random.uniform(2.0, 4.0)
                time.sleep(delay)
        
        if not dataset:
            logger.error("❌ No verified news-price pairs found. Adjust threshold or check if news is available in that period.")
            return

        # 4. Train/Val Split
        random.seed(42)
        random.shuffle(dataset)
        
        if len(dataset) < 2:
            train_set = dataset
            val_set = []
            logger.warning(f"⚠️ Only {len(dataset)} sample(s) found. Training on all, skipping validation.")
        else:
            split_idx = max(1, int(len(dataset) * 0.8))
            if split_idx >= len(dataset):
                split_idx = len(dataset) - 1
                
            train_set = dataset[:split_idx]
            val_set = dataset[split_idx:]
            logger.info(f"🏗️ Dataset Split: {len(train_set)} samples for training, {len(val_set)} for validation.")

        if not train_set:
            logger.error("❌ No samples for training.")
            return

        # 5. Training (Few-shot)
        optimizer = torch.optim.Adam(self.model.news_proj.parameters(), lr=1e-3)
        criterion = nn.CrossEntropyLoss()
        self.model.train()
        
        loss_history = []
        logger.info(f"🚀 Training for 30 epochs...")
        for epoch in range(30):
            total_loss = 0
            for item in train_set:
                optimizer.zero_grad()
                
                # Prep Data
                hist_df = item['history']
                # For training, we still focus on the immediate next point (teacher forcing)
                target_df = item['target'].iloc[:1]
                
                hist_raw = hist_df[['open', 'high', 'low', 'close', 'volume']].values.astype(np.float32)
                hist_raw = np.column_stack([hist_raw, hist_raw[:, 3] * hist_raw[:, 4]]) 
                
                mean, std = hist_raw.mean(axis=0), hist_raw.std(axis=0) + 1e-5
                hist_norm = torch.from_numpy((hist_raw - mean) / std).unsqueeze(0).to(self.device)
                
                target_raw = target_df[['open', 'high', 'low', 'close', 'volume']].values.astype(np.float32)
                target_raw = np.column_stack([target_raw, target_raw[:, 3] * target_raw[:, 4]])
                target_norm = torch.from_numpy((target_raw - mean) / std).unsqueeze(0).to(self.device)
                
                with torch.no_grad():
                    z_indices = self.tokenizer.encode(hist_norm, half=True)
                    t_indices = self.tokenizer.encode(target_norm, half=True)
                    s1_ids, s2_ids = z_indices[0], z_indices[1]
                    t_s1, t_s2 = t_indices[0], t_indices[1]
                
                news_t = torch.from_numpy(item['news_emb']).unsqueeze(0).to(self.device)
                s1_logits, s2_logits = self.model(s1_ids, s2_ids, news_emb=news_t, use_teacher_forcing=True, s1_targets=t_s1)
                
                loss = (criterion(s1_logits[:, -1, :], t_s1[:, 0]) + criterion(s2_logits[:, -1, :], t_s2[:, 0])) / 2
                loss.backward()
                optimizer.step()
                total_loss += loss.item()
                
            avg_epoch_loss = total_loss / max(1, len(train_set))
            loss_history.append(avg_epoch_loss)
            
            if (epoch + 1) % 10 == 0:
                logger.info(f"Epoch {epoch+1} Loss: {avg_epoch_loss:.4f}")

        # 5.1 Visualize Loss Curve
        loss_chart = VisualizerTools.generate_loss_chart(loss_history)
        VisualizerTools.render_chart_to_file(loss_chart, os.path.join(SRC_DIR, "exports/training_results/loss_curve.html"))

        # 5.2 Save final model
        self.save_model()

        # 6. Final Evaluation on Validation Set
        if not val_set:
            logger.warning("⚠️ Validation set is empty. Skipping statistical analysis.")
            return

        logger.info(f"🧪 Final Evaluation: Base vs News-Integrated ({pred_len}-day Window)")
        self.model.eval()
        predictor = KronosPredictor(self.model, self.tokenizer, device=self.device)
        
        base_maes = []
        news_maes = []
        
        print("\n" + "="*90)
        print(f"{'Date':<12} | {'Ticker':<8} | {'Base MAE':<15} | {'News MAE':<15} | {'Improvement'}")
        print("-" * 90)

        for item in val_set:
            h = item['history']
            t = item['target']
            actuals = t['close'].values[:pred_len]
            
            x_ts = pd.to_datetime(h['date'])
            # Future timestamps: handle business days if possible, or just simple offset
            future_dates = pd.date_range(start=x_ts.iloc[-1] + timedelta(days=1), periods=pred_len, freq='B')
            y_ts = pd.Series(future_dates)
            
            # A. Base Prediction
            p_base = predictor.predict(h, x_ts, y_ts, pred_len=pred_len, news_emb=None, verbose=False)
            b_preds = p_base['close'].values[:len(actuals)]
            
            # B. News-Aware Prediction
            p_news = predictor.predict(h, x_ts, y_ts, pred_len=pred_len, news_emb=item['news_emb'], verbose=False)
            n_preds = p_news['close'].values[:len(actuals)]
            
            # Calculate MAE over the window
            b_mae = np.mean(np.abs(b_preds - actuals))
            n_mae = np.mean(np.abs(n_preds - actuals))
            
            base_maes.append(b_mae)
            news_maes.append(n_mae)
            
            improvement = (b_mae - n_mae) / (b_mae + 1e-6) * 100
            
            date_str = str(t['date'].values[0])[:10]
            ticker = h.iloc[-1]['ticker'] if 'ticker' in h.columns else "Stock"
            print(f"{date_str:<12} | {ticker:<8} | {b_mae:<15.4f} | {n_mae:<15.4f} | {improvement:>+7.1f}%")

            # C. Generate Visualization for this case
            try:
                # Helper to convert DF to KLinePoints
                def to_kp_list(preds_df):
                    points = []
                    for idx, row in preds_df.iterrows():
                        points.append(KLinePoint(
                            date=str(idx)[:10],
                            open=row['open'],
                            high=row['high'],
                            low=row['low'],
                            close=row['close'],
                            volume=row['volume'] if 'volume' in row else 0
                        ))
                    return points

                forecast_obj = ForecastResult(
                    ticker=ticker,
                    base_forecast=to_kp_list(p_base),
                    adjusted_forecast=to_kp_list(p_news),
                    rationale=item['summary']
                )

                # Ground truth for visualizer expects a DataFrame with 'date' and 'close'
                gt_df = t[['date', 'open', 'high', 'low', 'close', 'volume']]
                
                chart = VisualizerTools.generate_stock_chart(
                    df=h, 
                    ticker=ticker, 
                    title=f"Training Eval: {ticker} ({date_str}) Improvement: {improvement:.1f}%",
                    forecast=forecast_obj,
                    ground_truth=gt_df
                )
                
                safe_date = date_str.replace("-", "")
                filename = f"eval_{ticker}_{safe_date}.html"
                VisualizerTools.render_chart_to_file(chart, os.path.join(SRC_DIR, f"exports/training_results/{filename}"))
            except Exception as e:
                logger.error(f"Failed to generate eval chart for {ticker}: {e}")

        # Summary Statistics
        avg_base_err = sum(base_maes) / max(1, len(base_maes))
        avg_news_err = sum(news_maes) / max(1, len(news_maes))
        overall_imp = (avg_base_err - avg_news_err) / (avg_base_err + 1e-6) * 100
        
        print("-" * 90)
        print(f"{'AVERAGE':<12} | {'-':<8} | {avg_base_err:<15.4f} | {avg_news_err:<15.4f} | {overall_imp:>+7.1f}%")
        print("="*90 + "\n")
        
        logger.success(f"🏁 Statistical Analysis Complete. Avg Error Reduction ({pred_len}-day): {overall_imp:.2f}%")
        logger.info(f"📊 Visualization results saved to: {os.path.join(SRC_DIR, 'exports/training_results/')}")

if __name__ == "__main__":
    trainer = AutoSynthesisTrainer()
    
    logger.info("📂 Fetching all stock codes from database...")
    res = trainer.db.execute_query("SELECT code FROM stock_list")
    all_tickers = [row['code'] for row in res]
    
    if not all_tickers:
        logger.warning("⚠️ No tickers found in stock_list table. Trying to sync...")
        trainer.tools._check_and_update_stock_list(force=True)
        res = trainer.db.execute_query("SELECT code FROM stock_list")
        all_tickers = [row['code'] for row in res]

    logger.info(f"🚀 Starting training on potential stocks (1-year scan)...")
    # 为了演示，我们扫描前 100 个股票，寻找最近一年的冲击点
    trainer.run_synthesis_and_train(all_tickers[:100], pred_len=1)
