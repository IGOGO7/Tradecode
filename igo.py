import tkinter as tk
from tkinter import ttk
from datetime import datetime
import time as time_module
import pytz
from futu import *

# ======================
# 配置区
# ======================
FUTU_HOST = '127.0.0.1'
FUTU_PORT = 11111
ALERT_COOLDOWN = 300

PRE_MARKET_HIGHS: dict[str, float | None] = {}
PRE_MARKET_LOWS: dict[str, float | None] = {}
US_EAST = pytz.timezone("US/Eastern")

STRATEGY_A_START = datetime.strptime("09:30:00", "%H:%M:%S").time()
STRATEGY_A_END = datetime.strptime("10:30:00", "%H:%M:%S").time()
STRATEGY_B_START = datetime.strptime("09:30:00", "%H:%M:%S").time()
STRATEGY_B_END = datetime.strptime("09:35:00", "%H:%M:%S").time()


def load_stocks() -> list[str]:
    try:
        with open('stocks.txt', 'r', encoding='utf-8') as f:
            return [line.strip() for line in f if line.strip()]
    except FileNotFoundError:
        print("⚠️ stocks.txt 未找到，使用默认股票池")
        return ["US.AAPL", "US.TSLA", "US.NVDA"]


def fetch_pre_market_range(ctx: OpenQuoteContext, code: str) -> tuple[float | None, float | None]:
    today_ny = datetime.now(tz=US_EAST).strftime('%Y-%m-%d')
    ret, data, _ = ctx.request_history_kline(
        code, start=today_ny, end=today_ny,
        ktype=KLType.K_1M, autype=AuType.QFQ,
        fields=['high', 'low', 'time_key'], extended_time=True
    )
    pm_high, pm_low = None, None

    if ret == RET_OK and data is not None and not data.empty:
        data['ny_time'] = data['time_key'].apply(
            lambda x: US_EAST.localize(datetime.strptime(x, "%Y-%m-%d %H:%M:%S"))
        )
        data['ny_hm'] = data['ny_time'].dt.strftime('%H:%M:%S')
        pm_data = data[(data['ny_hm'] >= '04:00:00') & (data['ny_hm'] < '09:30:00')]
        if not pm_data.empty:
            pm_high = float(pm_data['high'].max())
            pm_low = float(pm_data['low'].min())

    if pm_high is None or pm_low is None:
        ret_snap, snap = ctx.get_market_snapshot([code])
        if ret_snap == RET_OK and not snap.empty:
            row = snap.iloc[0]
            pm_high = float(row.get('pre_high_price', 0)) or None
            pm_low = float(row.get('pre_low_price', 0)) or None

    if pm_high == 0 or pm_low == 0:
        pm_high, pm_low = None, None
    return pm_high, pm_low


class MonitorApp:
    def __init__(self, master: tk.Tk):
        self.root = master
        self.root.title("美股双策略监控（分区显示）")
        self.root.geometry("850x600")

        # ✅ 上方窗口：策略A - 5分钟K收在盘前高点之上
        frame_top = ttk.LabelFrame(master, text="📈 策略A：09:30-10:30 5分钟K收盘 ≥ 盘前高点")
        frame_top.pack(fill=tk.BOTH, expand=True, padx=5, pady=(5, 2))
        self.tree_high = ttk.Treeview(frame_top, columns=("stock", "signal"), show="headings")
        self.tree_high.heading("stock", text="股票代码")
        self.tree_high.heading("signal", text="触发详情")
        self.tree_high.column("stock", width=120)
        self.tree_high.pack(fill=tk.BOTH, expand=True)

        # ✅ 下方窗口：策略B - 开盘首5分钟实时击穿盘前低点
        frame_bottom = ttk.LabelFrame(master, text="📉 策略B：09:30-09:35 实时报价 ≤ 盘前低点")
        frame_bottom.pack(fill=tk.BOTH, expand=True, padx=5, pady=(2, 5))
        self.tree_low = ttk.Treeview(frame_bottom, columns=("stock", "signal"), show="headings")
        self.tree_low.heading("stock", text="股票代码")
        self.tree_low.heading("signal", text="触发详情")
        self.tree_low.column("stock", width=120)
        self.tree_low.pack(fill=tk.BOTH, expand=True)

        # ✅ 分表独立防抖
        self.last_alert_ts: dict[str, float] = {}
        self.ctx = OpenQuoteContext(host=FUTU_HOST, port=FUTU_PORT)
        self.subscribed_codes: set[str] = set()
        self.refresh()

    def refresh(self):
        self.tree_high.delete(*self.tree_high.get_children())
        self.tree_low.delete(*self.tree_low.get_children())
        pool = load_stocks()

        for code in pool:
            high, low = fetch_pre_market_range(self.ctx, code)
            PRE_MARKET_HIGHS[code] = high
            PRE_MARKET_LOWS[code] = low

        new_codes = [c for c in pool if c not in self.subscribed_codes]
        if new_codes:
            ret, msg = self.ctx.subscribe(new_codes, [SubType.K_5M, SubType.QUOTE], is_first_push=True)
            self.subscribed_codes.update(new_codes)
            print(f"新增订阅 {new_codes} | ret={ret} | msg={msg}")

    def update_signal(self, stock: str, msg: str, signal_type: str):
        """
        signal_type: 'HIGH' 或 'LOW'，决定写入哪个表格
        """
        now = time_module.time()
        alert_key = f"{stock}_{signal_type}"
        if now - self.last_alert_ts.get(alert_key, 0) < ALERT_COOLDOWN:
            return
        self.last_alert_ts[alert_key] = now

        target_tree = self.tree_high if signal_type == "HIGH" else self.tree_low
        self.root.after(0, lambda t=target_tree, s=stock, m=msg: t.insert("", 0, values=(s, m)))


class KLine5MHandler(CurKlineHandlerBase):
    def __init__(self, gui: MonitorApp):
        super().__init__()
        self.gui = gui

    def on_recv_rsp(self, rsp_pb):
        ret, data = super().on_recv_rsp(rsp_pb)
        if ret != RET_OK:
            return RET_ERROR, data

        code = data['code'][0]
        close = float(data['close'][0])
        kline_time_str = data['time_key'][0]

        try:
            kline_dt = datetime.strptime(kline_time_str, "%Y-%m-%d %H:%M:%S")
            kline_time = kline_dt.time()
            kline_hms = kline_dt.strftime("%H:%M:%S")
        except ValueError:
            return RET_OK, data

        if STRATEGY_A_START <= kline_time < STRATEGY_A_END:
            pm_high = PRE_MARKET_HIGHS.get(code)
            if pm_high and close >= pm_high:
                # ✅ 指定 signal_type="HIGH" → 写入上方表格
                self.gui.update_signal(
                    code,
                    f"{kline_hms} 收盘:{close:.2f} ≥ 盘前高:{pm_high:.2f}",
                    signal_type="HIGH"
                )
        return RET_OK, data


class QuoteHandler(StockQuoteHandlerBase):
    def __init__(self, gui: MonitorApp):
        super().__init__()
        self.gui = gui

    def on_recv_rsp(self, rsp_pb):
        ret, data = super().on_recv_rsp(rsp_pb)
        if ret != RET_OK:
            return RET_ERROR, data

        now_ny = datetime.now(tz=US_EAST).time()
        if not (STRATEGY_B_START <= now_ny < STRATEGY_B_END):
            return RET_OK, data

        for _, row in data.iterrows():
            code = row['code']
            cur_price = float(row['cur_price'])
            pm_low = PRE_MARKET_LOWS.get(code)

            if pm_low and cur_price <= pm_low:
                hms = datetime.now(tz=US_EAST).strftime("%H:%M:%S")
                # ✅ 指定 signal_type="LOW" → 写入下方表格
                self.gui.update_signal(
                    code,
                    f"{hms} 现价:{cur_price:.2f} ≤ 盘前低:{pm_low:.2f}",
                    signal_type="LOW"
                )
        return RET_OK, data


if __name__ == "__main__":
    app_root = tk.Tk()
    app = MonitorApp(app_root)
    app.ctx.set_handler(KLine5MHandler(app))
    app.ctx.set_handler(QuoteHandler(app))
    try:
        app_root.mainloop()
    finally:
        app.ctx.close()