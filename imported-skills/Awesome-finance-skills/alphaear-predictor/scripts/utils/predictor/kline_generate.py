# Ref: https://github.com/shiyu-coder/Kronos

from model import Kronos, KronosTokenizer, KronosPredictor
import pandas as pd
import sqlite3
import torch
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from pandas.tseries.offsets import BusinessDay
import numpy as np

def get_device():
    device = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
    print(f"Using device: {device}")
    return device

def load_predictor():
    tokenizer = KronosTokenizer.from_pretrained("NeoQuasar/Kronos-Tokenizer-base")
    model = Kronos.from_pretrained("NeoQuasar/Kronos-base")
    device = get_device()
    tokenizer = tokenizer.to(device)
    model = model.to(device)
    return KronosPredictor(model, tokenizer, device=device, max_context=512)

def load_data(ticker="002111", db_path="AlphaEar/data/signal_flux.db"):
    with sqlite3.connect(db_path) as conn:
        df = pd.read_sql_query(f"SELECT * FROM stock_prices WHERE ticker = '{ticker}'", conn)
    df['date'] = pd.to_datetime(df['date'])
    df = df.sort_values('date').reset_index(drop=True)
    return df

def plot_kline_matplotlib(ax, ax_vol, dates, df, label_suffix="", color_up='#ef4444', color_down='#22c55e', alpha=1.0, is_prediction=False):
    """
    绘制 K 线图和成交量
    """
    # X axis mapping to integers for consistent spacing
    x = np.arange(len(dates))
    
    # K-line data
    opens = df['open'].values
    closes = df['close'].values
    highs = df['high'].values
    lows = df['low'].values
    volumes = df['volume'].values
    
    # Width of the candlestick
    width = 0.6
    
    for i in range(len(x)):
        color = color_up if closes[i] >= opens[i] else color_down
        linestyle = '--' if is_prediction else '-'
        
        # Wick
        ax.vlines(x[i], lows[i], highs[i], color=color, linewidth=1, alpha=alpha, linestyle=linestyle)
        
        # Body
        rect_bottom = min(opens[i], closes[i])
        rect_height = abs(opens[i] - closes[i])
        if rect_height == 0: rect_height = 0.001 # Visual hair
        
        ax.add_patch(plt.Rectangle((x[i] - width/2, rect_bottom), width, rect_height, 
                                 edgecolor=color, facecolor=color if not is_prediction else 'none', 
                                 alpha=alpha, linewidth=1, linestyle=linestyle))
        
        # Volume
        ax_vol.bar(x[i], volumes[i], color=color, alpha=alpha * 0.5, width=width)

def render_comparison_chart(history_df, actual_df, pred_df, title):
    """
    渲染组合图：历史 K 线 + 真值 K 线 + 预测 K 线
    """
    # Combine all dates for X axis
    all_dates = pd.concat([history_df['date'], actual_df['date'] if actual_df is not None else pred_df.index.to_series()]).unique()
    all_dates = sorted(all_dates)
    date_to_idx = {date: i for i, date in enumerate(all_dates)}
    
    fig = plt.figure(figsize=(14, 8), facecolor='white')
    gs = gridspec.GridSpec(2, 1, height_ratios=[3, 1], hspace=0.1)
    ax_main = fig.add_subplot(gs[0])
    ax_vol = fig.add_subplot(gs[1], sharex=ax_main)
    
    # 1. Plot History
    hist_indices = [date_to_idx[d] for d in history_df['date']]
    # We use a custom x for plotting to ensure continuity
    plot_kline_matplotlib(ax_main, ax_vol, history_df['date'], history_df, alpha=0.8)
    
    offset = len(history_df)
    
    # 2. Plot Actual if exists
    if actual_df is not None:
        # Shift indices
        actual_x = np.arange(len(actual_df)) + offset
        # Plotting manually to handle offset
        for i in range(len(actual_df)):
            idx = actual_x[i]
            row = actual_df.iloc[i]
            color = '#ef4444' if row['close'] >= row['open'] else '#22c55e'
            ax_main.vlines(idx, row['low'], row['high'], color=color, linewidth=1, alpha=0.9)
            ax_main.add_patch(plt.Rectangle((idx - 0.3, min(row['open'], row['close'])), 0.6, abs(row['open']-row['close']), 
                                         edgecolor=color, facecolor=color, alpha=0.9))
            ax_vol.bar(idx, row['volume'], color=color, alpha=0.4)
            
    # 3. Plot Prediction
    pred_x = np.arange(len(pred_df)) + offset
    for i in range(len(pred_df)):
        idx = pred_x[i]
        row = pred_df.iloc[i]
        color = '#ff8c00' # Orange for prediction to distinguish
        ax_main.vlines(idx, row['low'], row['high'], color=color, linewidth=1.5, linestyle='--')
        ax_main.add_patch(plt.Rectangle((idx - 0.3, min(row['open'], row['close'])), 0.6, abs(row['open']-row['close']), 
                                     edgecolor=color, facecolor='none', linewidth=1.5, linestyle='--'))
        # Plot secondary prediction line for close
        if i == 0:
            # Connect to history
            ax_main.plot([offset-1, idx], [history_df['close'].iloc[-1], row['close']], color=color, linestyle='--', alpha=0.6)
        elif i > 0:
            ax_main.plot([idx-1, idx], [pred_df['close'].iloc[i-1], row['close']], color=color, linestyle='--', alpha=0.6)

    # Styling
    ax_main.set_title(title, fontsize=14, fontweight='bold')
    ax_main.grid(True, linestyle=':', alpha=0.6)
    ax_vol.grid(True, linestyle=':', alpha=0.6)
    ax_vol.set_ylabel('Volume')
    ax_main.set_ylabel('Price')
    
    # Set X ticks
    step = max(1, len(all_dates) // 10)
    ax_vol.set_xticks(np.arange(0, len(all_dates), step))
    ax_vol.set_xticklabels([all_dates[i].strftime('%Y-%m-%d') for i in range(0, len(all_dates), step)], rotation=45)
    
    plt.tight_layout()
    plt.show()
    plt.close()

def run_backtest(df, predictor, lookback, pred_len, start_index=0):
    total_len = len(df)
    history_start = start_index
    history_end = start_index + lookback 
    pred_start = history_end
    
    available_pred_len = total_len - pred_start
    if available_pred_len <= 0: return
    actual_pred_len = min(pred_len, available_pred_len)
    pred_end = pred_start + actual_pred_len
    
    x_df = df.iloc[history_start : history_end].copy()
    y_true_df = df.iloc[pred_start : pred_end].copy()
    y_timestamp = y_true_df['date']
    
    print(f"Backtesting: {x_df['date'].iloc[0].date()} to {y_timestamp.iloc[-1].date()}")
    
    pred_df = predictor.predict(
        df=x_df[['open', 'high', 'low', 'close', 'volume']],
        x_timestamp=x_df['date'],
        y_timestamp=y_timestamp,
        pred_len=actual_pred_len,
        T=1.0, top_p=0.9, sample_count=1
    )
    
    render_comparison_chart(x_df, y_true_df, pred_df, f"Backtest: {TICKER} K-Line Comparison")

def run_forecast(df, predictor, lookback, pred_len):
    if len(df) < lookback: return
    x_df = df.iloc[-lookback:].copy()
    last_date = x_df['date'].iloc[-1]
    future_dates = pd.date_range(start=last_date + BusinessDay(1), periods=pred_len, freq='B')
    future_dates = pd.Series(future_dates)
    
    print(f"Forecasting: Starting from {future_dates.iloc[0].date()}")
    
    pred_df = predictor.predict(
        df=x_df[['open', 'high', 'low', 'close', 'volume']],
        x_timestamp=x_df['date'],
        y_timestamp=future_dates,
        pred_len=pred_len,
        T=1.0, top_p=0.9, sample_count=1
    )
    
    render_comparison_chart(x_df, None, pred_df, f"Forecast: {TICKER} Future K-Line")

if __name__ == "__main__":
    LOOKBACK = 20
    PRED_LEN = 10
    TICKER = '002111'
    
    pred_model = load_predictor()
    stock_data = load_data(TICKER)
    
    total_rows = len(stock_data)
    backtest_start = max(0, total_rows - LOOKBACK - PRED_LEN - 10) # Leave some space to see trend
    
    print("\n--- Running Backtest ---")
    run_backtest(stock_data, pred_model, LOOKBACK, PRED_LEN, start_index=backtest_start)
    
    print("\n--- Running Forecast ---")
    run_forecast(stock_data, pred_model, LOOKBACK, PRED_LEN)