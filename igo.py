"""
盘前 S 线监控

核心票池 / 更新票池：
1. 美东 04:00-09:25 统计当天盘前高、盘前低。
2. 昨日收盘价和昨日最高价固定读取上一交易日不复权日 K。
3. UI 显示：股票代码、盘前高点、昨日收盘价、最新完整 5 分钟 K 收盘价，以及相对 QQQ 的昨收涨幅差。
4. 点击股票代码，可手动切换绿色重点标签；标签在下一监控日美东 04:00 自动清空。
5. S = 盘前高点，昨日收盘价仅作界面参考，不参与 S 线计算。
6. 美东 04:00 盘前起读取最新完整 5 分钟 K；完整 K 收盘价 > 盘前高点时，5M收盘价单元格显示柔和绿色描边呼吸效果。
7. 相对 QQQ = 个股相对昨收涨幅 − QQQ 相对昨收涨幅；现价取同一根完整 5M 收盘价，不是 5 分钟 K 自身涨跌幅。
8. 16:00 后继续确认并读取 15:55-16:00 最后一根常规盘完整 5 分钟 K；盘后会动态增加返回根数，避免 16:00 K 被后续盘后 K 挤出。

界面与记忆：
1. 使用浅色主题，核心票池与更新票池之间的横向分割线可以拖动。
2. 顶部可在「全部票池」与「突破票」两个页面间切换；突破票页只显示突破盘前高且涨幅大于 QQQ 的股票，并按相对强度从高到低排序。
3. 关闭程序时自动保存窗口大小、窗口位置和分割线位置；下次启动自动恢复。
4. 表格隐藏右侧滚动条，使用鼠标滚轮浏览。

市场广度与 API 优化：
1. 盘中调用富途 get_rise_fall_distribution(Market.US)，每 5 分钟更新一次全美股涨跌广度。
2. 盘前历史 K 线刷新由每分钟降为每 5 分钟，09:26 仍强制精确锁定。
3. 到价提醒改为一次读取全美股提醒后本地筛选，避免逐股读取触发限频。
4. 自动同步仅处理新增/移出股票；手动同步仍执行完整提醒审计。

富途自选组与到价提醒同步：
1. 顶部“同步 X 组 + 提醒”按钮可随时手动执行完整同步。
2. 同步进 X 组需同时满足：突破盘前高，且相对昨收涨幅大于 QQQ；任一条件不满足则移出。
3. X 组按相对强度排序：富途无官方排序接口。手动「同步 X」才会整组移出再按序加回；自动同步只做进出增减，避免频繁打满限频。
4. 美东 09:35-16:00，每根完整 5 分钟 K 更新后检查一次；自动模式只有进出名单变化时才访问富途。
5. 对 X 组股票同步两类到价提醒：盘前高、盘前低。
6. 程序只管理备注为 IGO盘前高、IGO盘前低的提醒，不改动用户手动创建的其他提醒。
7. 同步时会清理旧版本创建的 IGO VWAP 提醒。
8. 首次使用前，请先在富途牛牛中手动创建名为 X 的自定义组。
"""


import math
import re
import tkinter as tk
from datetime import datetime, timedelta
from decimal import Decimal, ROUND_DOWN
from pathlib import Path

import pandas as pd
import pytz
from futu import (
    AuType,
    KLType,
    Market,
    ModifyUserSecurityOp,
    OpenQuoteContext,
    PriceReminderFreq,
    PriceReminderMarketStatus,
    PriceReminderType,
    RET_OK,
    Session,
    SetPriceReminderOp,
    SubType,
)


# ============================================================
# 配置
# ============================================================

FUTU_HOST = "127.0.0.1"
FUTU_PORT = 11111

# 程序只会同步自定义组 X。首次使用前，请在富途牛牛中手动创建名为 X 的组。
FUTU_SIGNAL_GROUP_NAME = "X"

# 只管理这些固定备注的提醒，不碰用户自行创建的其他到价提醒。
REMINDER_NOTE_PM_HIGH = "IGO盘前高"
REMINDER_NOTE_PM_LOW = "IGO盘前低"
# 仅用于清理旧版本已经创建的提醒，不再新增或更新 VWAP 提醒。
LEGACY_REMINDER_NOTE_VWAP = "IGO VWAP"
PROGRAM_REMINDER_NOTES = {
    REMINDER_NOTE_PM_HIGH,
    REMINDER_NOTE_PM_LOW,
    LEGACY_REMINDER_NOTE_VWAP,
}

US_EAST = pytz.timezone("US/Eastern")

PRE_START = datetime.strptime("04:00:00", "%H:%M:%S").time()
# 盘前高低点只统计到 09:25（包含 time_key=09:25 的 1 分钟 K）。
PRE_END = datetime.strptime("09:25:00", "%H:%M:%S").time()
# 09:25 这一根 1 分钟 K 到 09:26 才完整，因此 09:26 起锁定盘前高低点。
PRE_LOCK_TIME = datetime.strptime("09:26:00", "%H:%M:%S").time()
# 最新完整 5 分钟收盘价从美东 04:00 盘前开始监控。
# 第一根完整 K 为 04:00-04:05，因此 04:05 起才有可确认收盘价。
FIVE_MINUTE_START = PRE_START
FIRST_5M_END = datetime.strptime("04:05:00", "%H:%M:%S").time()
RTH_FIRST_5M_END = datetime.strptime("09:35:00", "%H:%M:%S").time()
CLOSE_TIME = datetime.strptime("16:00:00", "%H:%M:%S").time()

# 个股相对强弱基准：始终跟踪 QQQ 的昨收与同时间完整 5M 收。
BENCHMARK_CODE = "US.QQQ"

# 实盘监控统一使用不复权原始价格，和富途报价/分时图显示口径一致。
# 昨收、盘前高低点和 5 分钟收盘价必须使用同一价格口径。
PRICE_AUTYPE = AuType.NONE

# 五分钟边界后等待几秒，让 OpenD 完成上一根 K 的最终收盘更新。
# 例如 09:35:00 到达边界后，09:35:03 才确认 09:30-09:35。
KLINE_CONFIRM_DELAY_SECONDS = 3
KLINE_RETRY_SECONDS = 5

# 盘前高低点使用历史 1 分钟 K 全量回看；5 分钟刷新足够覆盖低频日内需求。
# 09:26 锁定时仍会强制再取一次完整盘前数据，因此不会影响最终盘前高低点。
PM_REFRESH_MS = 5 * 60_000
KLINE_CHECK_MS = 1_000

# 富途直接提供全美股涨跌分布，一次请求即可获得市场广度，
# 不占订阅额度，也不占历史 K 线额度。低频日内按 5 分钟刷新。
MARKET_BREADTH_REFRESH_MS = 5 * 60_000
MARKET_BREADTH_TIMER_MS = 30_000
MARKET_BREADTH_START = RTH_FIRST_5M_END
MARKET_BREADTH_END = CLOSE_TIME
MARKET_BREADTH_STRONG_SHARE = 0.60
MARKET_BREADTH_WEAK_SHARE = 0.40

# 自动同步采用短暂防抖，把同一轮中多只股票同时触发合并为一次请求。
AUTO_SYNC_DEBOUNCE_MS = 800
# 五分钟边界刚到时，富途 K 线可能尚未刷新；最多等待这些秒再使用当前结果同步。
AUTO_SYNC_MAX_WAIT_SECONDS = 20
# 16:00 最后一根完整 5M K 允许在收盘后短暂补一次同步。
AUTO_SYNC_FINAL_GRACE_SECONDS = 60

# 查询昨日收盘价时向前覆盖足够多的自然日，自动跨周末和休市日。
PREVIOUS_CLOSE_LOOKBACK_DAYS = 20


# ============================================================
# 股票列表文件
# ============================================================

BASE_DIR = Path(__file__).resolve().parent
CORE_STOCKS_FILE = BASE_DIR / "stocks.txt"
UPDATE_STOCKS_FILE = BASE_DIR / "update_stocks.txt"
MANUAL_HIGHLIGHTS_FILE = BASE_DIR / "highlighted_stocks.txt"
PANE_LAYOUT_FILE = BASE_DIR / "pane_layout.txt"
WINDOW_GEOMETRY_FILE = BASE_DIR / "window_geometry.txt"

DEFAULT_CORE_STOCKS = [
    "US.NVDA",
    "US.AMD",
    "US.TSLA",
    "US.META",
    "US.MSFT",
]


def normalize_stock_code(value):
    """把 NVDA、us.nvda 等输入统一为 US.NVDA。"""

    code = value.strip().upper()

    if not code:
        return None

    if not code.startswith("US."):
        code = f"US.{code}"

    if not re.fullmatch(r"US\.[A-Z0-9][A-Z0-9.\-]*", code):
        return None

    return code


def load_stock_file(path, fallback=None):
    """读取股票文件，忽略空行、注释及重复代码。"""

    try:
        with path.open("r", encoding="utf-8") as file:
            result = []
            seen = set()

            for line in file:
                text = line.strip()

                if not text or text.startswith("#"):
                    continue

                code = normalize_stock_code(text)

                if code is None or code in seen:
                    continue

                seen.add(code)
                result.append(code)

            if result or fallback is None:
                return result

    except FileNotFoundError:
        if fallback is None:
            return []

        print(f"未找到 {path.name}，使用默认核心票池")

    except OSError as error:
        if fallback is None:
            print(f"读取 {path.name} 失败：{error}")
        else:
            print(f"读取 {path.name} 失败，使用默认核心票池：{error}")

    return list(fallback or [])


def save_stock_file(path, stocks, label):
    """保存股票列表。"""

    try:
        content = "\n".join(stocks)

        if content:
            content += "\n"

        path.write_text(content, encoding="utf-8")

    except OSError as error:
        print(f"保存{label}失败：{error}")


def load_daily_highlights(path, session_day):
    """
    读取当前监控日的手动重点标签。

    文件首行记录监控日。若文件属于旧监控日，直接返回空集合，
    避免程序隔天重新启动时恢复昨日的手动标签。
    """

    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except FileNotFoundError:
        return set()
    except OSError as error:
        print(f"读取手动高亮列表失败：{error}")
        return set()

    expected_header = f"# SESSION_DAY={session_day.isoformat()}"

    if not lines or lines[0].strip() != expected_header:
        return set()

    result = set()

    for line in lines[1:]:
        text = line.strip()

        if not text or text.startswith("#"):
            continue

        code = normalize_stock_code(text)

        if code is not None:
            result.add(code)

    return result


def save_daily_highlights(path, session_day, stocks):
    """保存手动标签，并写入其所属的美东监控日。"""

    try:
        lines = [f"# SESSION_DAY={session_day.isoformat()}"]
        lines.extend(sorted(stocks))
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    except OSError as error:
        print(f"保存手动高亮列表失败：{error}")


def short_code(code):
    return code.removeprefix("US.")


# ============================================================
# 时间处理
# ============================================================


def eastern_now():
    return datetime.now(US_EAST)


def naive_eastern(now=None):
    """富途 time_key 为无时区美东时间，因此比较时去掉 tzinfo。"""

    if now is None:
        now = eastern_now()

    return now.replace(tzinfo=None)


def get_session_day(now):
    """美东 04:00 前仍显示上一监控日的数据。"""

    if now.time() < PRE_START:
        return (now - timedelta(days=1)).date()

    return now.date()


def floor_to_5_minutes(value):
    return value.replace(
        minute=(value.minute // 5) * 5,
        second=0,
        microsecond=0,
    )


# ============================================================
# 富途 K 线请求及清洗
# ============================================================


def prepare_kline_data(data):
    """清洗富途历史 K 线。"""

    if data is None or data.empty:
        return pd.DataFrame()

    work = data.copy()

    work["_datetime"] = pd.to_datetime(
        work["time_key"],
        errors="coerce",
    )

    numeric_columns = [
        "open",
        "close",
        "high",
        "low",
        "volume",
        "turnover",
    ]

    for column in numeric_columns:
        if column in work.columns:
            work[column] = pd.to_numeric(
                work[column],
                errors="coerce",
            )

    work = work.dropna(subset=["_datetime"])
    work = work.sort_values("_datetime")
    work = work.reset_index(drop=True)

    return work


def request_kline_range(
    ctx,
    code,
    start_day,
    end_day,
    ktype,
    extended_time,
    session,
    max_count=1000,
):
    """请求指定日期范围的历史 K 线，并兼容旧版 SDK。"""

    arguments = {
        "code": code,
        "start": start_day.strftime("%Y-%m-%d"),
        "end": end_day.strftime("%Y-%m-%d"),
        "ktype": ktype,
        "autype": PRICE_AUTYPE,
        "max_count": max_count,
        "extended_time": extended_time,
    }

    # 日 K 等不需要分时段参数的请求，直接省略 session。
    if session is None:
        return ctx.request_history_kline(**arguments)

    try:
        return ctx.request_history_kline(
            **arguments,
            session=session,
        )

    except TypeError as error:
        print(f"{code} 当前 SDK 不支持 session 参数，使用兼容模式：{error}")
        return ctx.request_history_kline(**arguments)


def request_day_kline(
    ctx,
    code,
    trading_day,
    ktype,
    extended_time,
    session,
):
    return request_kline_range(
        ctx=ctx,
        code=code,
        start_day=trading_day,
        end_day=trading_day,
        ktype=ktype,
        extended_time=extended_time,
        session=session,
        max_count=1000,
    )


# ============================================================
# 昨日收盘价
# ============================================================


def get_previous_trading_close(ctx, code, trading_day):
    """
    读取 trading_day 之前最近一个交易日的不复权日 K，
    同时返回昨日收盘价、昨日最高价和交易日。

    因此周一会自动得到上周五，节后会自动跳过休市日。
    """

    start_day = trading_day - timedelta(days=PREVIOUS_CLOSE_LOOKBACK_DAYS)
    end_day = trading_day - timedelta(days=1)

    try:
        ret, data, _ = request_kline_range(
            ctx=ctx,
            code=code,
            start_day=start_day,
            end_day=end_day,
            ktype=KLType.K_DAY,
            extended_time=False,
            session=None,
            max_count=100,
        )

    except Exception as error:
        print(f"{code} 获取昨日行情异常：{error}")
        return None, None, None

    if ret != RET_OK:
        print(f"{code} 获取昨日行情失败：{data}")
        return None, None, None

    work = prepare_kline_data(data)

    if (
        work.empty
        or "close" not in work.columns
        or "high" not in work.columns
    ):
        print(f"{code} 没有可用的历史日 K 收盘价或最高价")
        return None, None, None

    work = work.dropna(subset=["close", "high"])
    work = work[work["_datetime"].dt.date < trading_day]

    if work.empty:
        print(f"{code} 未找到 {trading_day} 之前的交易日行情")
        return None, None, None

    row = work.iloc[-1]
    previous_day = row["_datetime"].date()
    previous_close = float(row["close"])
    previous_high = float(row["high"])

    print(
        f"{code} 昨日行情：交易日={previous_day} "
        f"close={previous_close} high={previous_high} "
        f"来源=不复权历史日K/RTH"
    )

    return previous_close, previous_high, previous_day


# ============================================================
# 盘前高低点
# ============================================================


def get_pm_range(ctx, code, trading_day):
    """获取美东 04:00-09:25 的盘前高点和盘前低点。"""

    try:
        ret, data, _ = request_day_kline(
            ctx=ctx,
            code=code,
            trading_day=trading_day,
            ktype=KLType.K_1M,
            extended_time=True,
            session=Session.ETH,
        )

    except Exception as error:
        print(f"{code} 获取盘前数据异常：{error}")
        return None, None

    if ret != RET_OK:
        print(f"{code} 盘前数据请求失败：{data}")
        return None, None

    work = prepare_kline_data(data)

    if work.empty:
        print(f"{code} 没有有效盘前数据")
        return None, None

    if "high" not in work.columns or "low" not in work.columns:
        print(f"{code} 盘前数据缺少 high 或 low")
        return None, None

    work = work.dropna(subset=["high", "low"])
    times = work["_datetime"].dt.time

    # 只统计到 09:25，并把富途返回的 time_key=09:25 这一根纳入。
    pm = work[
        (times >= PRE_START)
        & (times <= PRE_END)
    ]

    if pm.empty:
        print(f"{code} 筛选后没有 04:00-09:25 盘前 K")
        return None, None

    pm_high = float(pm["high"].max())
    pm_low = float(pm["low"].min())
    last_row = pm.iloc[-1]

    print(
        f"{code} 盘前最后一根：time={last_row['time_key']} "
        f"high={float(last_row['high'])} low={float(last_row['low'])}"
    )
    print(
        f"{code} 盘前统计：high={pm_high} low={pm_low} 数量={len(pm)}"
    )

    return pm_high, pm_low


# ============================================================
# 主程序
# ============================================================


class App:

    # 清爽浅色交易终端配色。
    APP_BG = "#EEF3F8"
    PANEL_BG = "#FFFFFF"
    TABLE_BG = "#FFFFFF"
    NORMAL_BG = "#FFFFFF"
    HEADER_BG = "#E7EEF6"
    BORDER_BG = "#C7D2DE"
    INPUT_BG = "#F8FAFC"

    TEXT_PRIMARY = "#17212B"
    TEXT_SECONDARY = "#46576A"
    TEXT_MUTED = "#718096"

    ACCENT_BLUE = "#2878E6"
    BUTTON_ACTIVE_BG = "#1F67C8"
    # 手动重点标签保留绿色语义，但改用浅绿色底，避免浅色主题下过于刺眼。
    ATTENTION_BG = "#DDF7EC"
    ATTENTION_FG = "#087553"
    SIGNAL_GREEN = "#00A874"
    SIGNAL_ORANGE = "#F28C00"
    SIGNAL_YELLOW = "#D6A400"
    SIGNAL_RED = "#E43D4F"
    SIGNAL_OFF = "#B5C0CB"
    ERROR_FG = "#D92D20"

    # 个股信号在“5M收”单元格中做低幅度、慢速描边呼吸。
    # 背景变化很小，主要通过边框和文字颜色变化提示，避免刺眼闪烁。
    SIGNAL_BREATH_INTERVAL_MS = 60
    SIGNAL_BREATH_PERIOD_SECONDS = 2.0

    # 高饱和度呼吸：最低状态也是明显的深绿/深红。
    CLOSE_GREEN_BG_LOW = "#087A58"
    CLOSE_GREEN_BG_HIGH = "#21C98B"
    CLOSE_GREEN_FG_LOW = "#FFFFFF"
    CLOSE_GREEN_FG_HIGH = "#FFFFFF"
    CLOSE_GREEN_BORDER_LOW = "#055E45"
    CLOSE_GREEN_BORDER_HIGH = "#49E3AD"

    def __init__(self, root):
        self.root = root
        self.root.title("盘前 S 线监控 · 浅色主题")
        self.root.configure(bg=self.APP_BG)

        screen_height = self.root.winfo_screenheight()
        window_height = min(max(screen_height - 60, 720), 1040)

        default_geometry = f"390x{window_height}+0+25"
        self.root.minsize(350, 520)
        self.root.maxsize(430, screen_height)
        self.restore_window_geometry(default_geometry)
        self.root.attributes("-topmost", True)

        self.closed = False
        self.signal_breath_phase = 0.0
        self.signal_breath_job = None

        self.ctx = OpenQuoteContext(
            host=FUTU_HOST,
            port=FUTU_PORT,
        )

        self.core_stocks = load_stock_file(
            CORE_STOCKS_FILE,
            fallback=DEFAULT_CORE_STOCKS,
        )
        loaded_update_stocks = load_stock_file(
            UPDATE_STOCKS_FILE,
            fallback=None,
        )

        # 核心票不再写入“更新票池”来触发高亮；
        # 自动清理旧版本遗留在 update_stocks.txt 中的核心票。
        self.update_stocks = [
            code for code in loaded_update_stocks
            if code not in self.core_stocks
        ]

        if self.update_stocks != loaded_update_stocks:
            save_stock_file(
                UPDATE_STOCKS_FILE,
                self.update_stocks,
                "更新票池",
            )

        now = eastern_now()
        self.session_day = get_session_day(now)

        # 手动绿色标签只在当前美东监控日内保留。
        # 同一天重启程序仍可恢复；到下一天美东 04:00 自动清空。
        self.manual_highlighted_codes = load_daily_highlights(
            MANUAL_HIGHLIGHTS_FILE,
            self.session_day,
        )

        # 把旧版无日期文件或昨日文件立即改写成当前监控日格式。
        save_daily_highlights(
            MANUAL_HIGHLIGHTS_FILE,
            self.session_day,
            self.manual_highlighted_codes,
        )

        self.core_rows = {}
        self.update_rows = {}
        self.breakout_rows = {}
        self.current_page = "all"

        # 盘前数据。
        self.pm_high = {}
        self.pm_low = {}
        self.locked_high = {}
        self.locked_low = {}

        # 前一交易日收盘和最高价。
        self.previous_close = {}
        self.previous_high = {}
        self.previous_close_day = {}

        # 最新完整 5 分钟 K 收盘价，同时用于界面显示和突破判断。
        self.latest_close = {}

        # 信号状态（仅盘前高突破）。
        self.breakout_state = {}

        # 富途自选组同步状态，避免按钮连续点击造成重复请求。
        self.sync_in_progress = False
        # 记录最近一次成功同步的进出名单（frozenset，忽略排序）。
        # 自动模式只在进出变化时访问富途；完整强度排序仅手动同步。
        self.last_successful_sync_target = None
        # 富途 ADD 批量加入后，列表顺序是否与传入顺序相反。
        # None 表示尚未探测；True/False 表示已确认。
        self.futu_add_list_reversed = None
        # 记录已经处理过的常规盘 5 分钟边界，避免同一根 K 重复检查。
        self.last_auto_sync_boundary = None
        # 多只股票同时触发时，使用 after 任务做短暂合并。
        self.auto_sync_job = None
        self.auto_sync_pending_reason = None

        # 窗口移动/缩放的延迟保存任务。
        self.geometry_save_job = None

        # K 线读取状态。
        self.last_completed_end = {}
        self.last_kline_request_at = {}
        # 已成功订阅实时 5 分钟 K 的股票。
        self.subscribed_5m = set()

        # 全美股市场广度。富途 get_rise_fall_distribution 一次返回整个市场，
        # 不需要自己遍历数千只股票。
        self.market_breadth_last_request_at = None
        self.market_breadth_up = None
        self.market_breadth_down = None
        self.market_breadth_flat = None

        self.build_ui()

        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.bind(
            "<Configure>",
            self.schedule_window_geometry_save,
            add="+",
        )
        self.signal_breath_job = self.root.after(
            self.SIGNAL_BREATH_INTERVAL_MS,
            self.animate_close_signals,
        )
        self.root.after(300, self.initialize)

    # ========================================================
    # 股票集合
    # ========================================================

    def get_s_stocks(self):
        """需要进行 S 线判断的股票。"""

        return list(dict.fromkeys(
            self.core_stocks + self.update_stocks
        ))

    def get_all_stocks(self):
        """所有需要向富途请求数据的股票（含 QQQ 基准，不进票池表格）。"""

        return list(dict.fromkeys(
            self.get_s_stocks() + [BENCHMARK_CODE]
        ))

    def code_is_used(self, code):
        return code in self.get_s_stocks()

    def needs_market_data(self, code):
        """票池股票或 QQQ 基准都需要订阅/拉取行情。"""

        return self.code_is_used(code) or code == BENCHMARK_CODE

    # ========================================================
    # 行控件与显示值
    # ========================================================

    def iter_s_rows(self, code):
        core_row = self.core_rows.get(code)

        if core_row is not None:
            yield core_row

        update_row = self.update_rows.get(code)

        if update_row is not None:
            yield update_row

        breakout_row = self.breakout_rows.get(code)

        if breakout_row is not None:
            yield breakout_row

    def get_relative_strength(self, code):
        """个股相对昨收涨幅 − QQQ；缺数据返回 None。"""

        stock_pct = self.get_change_vs_prev_close_pct(code)
        qqq_pct = self.get_change_vs_prev_close_pct(BENCHMARK_CODE)

        if stock_pct is None or qqq_pct is None:
            return None

        return stock_pct - qqq_pct

    def get_breakout_codes(self):
        """
        返回突破票：突破盘前高且涨幅大于 QQQ，
        按相对强度（较QQQ）从高到低排序。
        """

        scored = []

        for code in self.get_s_stocks():
            if not self.breakout_state.get(code, False):
                continue

            if not self.is_stronger_than_qqq(code):
                continue

            strength = self.get_relative_strength(code)

            if strength is None:
                continue

            scored.append((strength, code))

        scored.sort(key=lambda item: item[0], reverse=True)
        return [code for _, code in scored]

    def sync_breakout_page(self):
        """名单或排序变化时才重绘突破票页，避免无意义闪烁。"""

        if not hasattr(self, "breakout_table"):
            return

        desired = self.get_breakout_codes()
        current = list(self.breakout_rows.keys())

        if desired != current:
            self.render_breakout_rows()
        elif (
            hasattr(self, "page_hint_label")
            and self.current_page == "breakout"
        ):
            self.page_hint_label.config(
                text=f"当前 {len(desired)} 只 · 强→弱"
            )

    def set_s_cell(self, code, key, text):
        for row in self.iter_s_rows(code):
            widget = row.get(key)

            if widget is not None:
                widget.config(text=text)


    @staticmethod
    def format_price(value):
        return "-" if value is None else f"{value:.2f}"

    def display_pm_high(self, code):
        value = self.locked_high.get(code)

        if value is None:
            value = self.pm_high.get(code)

        return self.format_price(value)

    def display_previous_close(self, code):
        return self.format_price(self.previous_close.get(code))

    def display_latest_close(self, code):
        return self.format_price(self.latest_close.get(code))

    def get_change_vs_prev_close_pct(self, code):
        """
        相对昨收的涨幅百分比。

        现价取最新完整 5M 收盘价，仅作同步采样点；
        涨幅口径是 (现价 - 昨收) / 昨收，不是单根 5 分钟 K 的涨跌幅。
        """

        previous = self.previous_close.get(code)
        latest = self.latest_close.get(code)

        try:
            previous = float(previous)
            latest = float(latest)
        except (TypeError, ValueError):
            return None

        if (
            not pd.notna(previous)
            or not pd.notna(latest)
            or previous <= 0
            or latest <= 0
        ):
            return None

        return (latest / previous - 1.0) * 100.0

    def display_vs_qqq(self, code):
        """
        个股相对昨收涨幅 − QQQ 相对昨收涨幅。

        正数表示同期强于 QQQ，负数表示弱于 QQQ。
        """

        stock_pct = self.get_change_vs_prev_close_pct(code)
        qqq_pct = self.get_change_vs_prev_close_pct(BENCHMARK_CODE)

        if stock_pct is None or qqq_pct is None:
            return "-", self.TEXT_MUTED

        diff = stock_pct - qqq_pct

        if diff > 0:
            color = self.SIGNAL_GREEN
        elif diff < 0:
            color = self.SIGNAL_RED
        else:
            color = self.TEXT_SECONDARY

        return f"{diff:+.2f}%", color

    def update_vs_qqq(self, code, sync_breakout=True):
        text, color = self.display_vs_qqq(code)

        for row in self.iter_s_rows(code):
            widget = row.get("vs_qqq")

            if widget is not None:
                widget.config(text=text, fg=color)

        if sync_breakout:
            self.sync_breakout_page()

    def refresh_all_vs_qqq(self):
        for code in self.get_s_stocks():
            self.update_vs_qqq(code, sync_breakout=False)

        self.sync_breakout_page()


    # ========================================================
    # 界面总布局
    # ========================================================

    def build_ui(self):
        header = tk.Frame(self.root, bg=self.APP_BG)
        header.pack(fill=tk.X, padx=6, pady=(5, 3))

        title_row = tk.Frame(header, bg=self.APP_BG)
        title_row.pack(fill=tk.X)

        tk.Label(
            title_row,
            text="盘前 S 线",
            bg=self.APP_BG,
            fg=self.TEXT_PRIMARY,
            font=("微软雅黑", 11, "bold"),
        ).pack(side=tk.LEFT)

        self.kline_status_label = tk.Label(
            title_row,
            text="5M：等待",
            bg=self.APP_BG,
            fg=self.TEXT_MUTED,
            font=("微软雅黑", 8),
        )
        self.kline_status_label.pack(side=tk.RIGHT)

        breadth_row = tk.Frame(header, bg=self.APP_BG)
        breadth_row.pack(fill=tk.X, pady=(2, 0))

        self.market_breadth_frame = tk.Frame(
            breadth_row,
            bg=self.APP_BG,
        )
        self.market_breadth_frame.pack(side=tk.LEFT)

        self.market_breadth_canvas = tk.Canvas(
            self.market_breadth_frame,
            width=14,
            height=14,
            bg=self.APP_BG,
            highlightthickness=0,
            bd=0,
        )
        self.market_breadth_canvas.pack(side=tk.LEFT, padx=(0, 3))

        self.market_breadth_circle = self.market_breadth_canvas.create_oval(
            3,
            3,
            11,
            11,
            fill=self.SIGNAL_OFF,
            outline=self.SIGNAL_OFF,
        )

        self.market_breadth_label = tk.Label(
            self.market_breadth_frame,
            text="广度：待09:35",
            bg=self.APP_BG,
            fg=self.TEXT_MUTED,
            font=("微软雅黑", 8, "bold"),
        )
        self.market_breadth_label.pack(side=tk.LEFT)

        tk.Frame(
            self.root,
            height=1,
            bg=self.ACCENT_BLUE,
        ).pack(fill=tk.X, padx=7, pady=(0, 5))

        sync_bar = tk.Frame(self.root, bg=self.APP_BG)
        sync_bar.pack(fill=tk.X, padx=8, pady=(0, 5))

        self.sync_button = tk.Button(
            sync_bar,
            text="同步 X",
            bg=self.ACCENT_BLUE,
            fg="#FFFFFF",
            activebackground=self.BUTTON_ACTIVE_BG,
            activeforeground="#FFFFFF",
            disabledforeground="#E9EEF5",
            relief=tk.FLAT,
            bd=0,
            cursor="hand2",
            padx=8,
            pady=3,
            font=("微软雅黑", 9, "bold"),
            command=self.sync_lit_stocks_to_futu,
        )
        self.sync_button.pack(side=tk.LEFT)

        self.sync_status_label = tk.Label(
            sync_bar,
            text=(
                f"{FUTU_SIGNAL_GROUP_NAME}组 · 自动只进出 / 手动才重排"
            ),
            anchor="w",
            justify=tk.LEFT,
            wraplength=245,
            bg=self.APP_BG,
            fg=self.TEXT_MUTED,
            font=("微软雅黑", 9),
        )
        self.sync_status_label.pack(
            side=tk.LEFT,
            fill=tk.X,
            expand=True,
            padx=(8, 0),
        )

        page_bar = tk.Frame(self.root, bg=self.APP_BG)
        page_bar.pack(fill=tk.X, padx=8, pady=(0, 5))

        self.page_all_button = tk.Button(
            page_bar,
            text="全部票池",
            relief=tk.FLAT,
            bd=0,
            cursor="hand2",
            padx=8,
            pady=3,
            font=("微软雅黑", 9, "bold"),
            command=lambda: self.show_page("all"),
        )
        self.page_all_button.pack(side=tk.LEFT)

        self.page_breakout_button = tk.Button(
            page_bar,
            text="突破票",
            relief=tk.FLAT,
            bd=0,
            cursor="hand2",
            padx=8,
            pady=3,
            font=("微软雅黑", 9, "bold"),
            command=lambda: self.show_page("breakout"),
        )
        self.page_breakout_button.pack(side=tk.LEFT, padx=(6, 0))

        self.page_hint_label = tk.Label(
            page_bar,
            text="",
            anchor="w",
            bg=self.APP_BG,
            fg=self.TEXT_MUTED,
            font=("微软雅黑", 8),
        )
        self.page_hint_label.pack(
            side=tk.LEFT,
            fill=tk.X,
            expand=True,
            padx=(8, 0),
        )

        main = tk.Frame(self.root, bg=self.APP_BG)
        main.pack(fill=tk.BOTH, expand=True, padx=6, pady=(0, 6))
        main.grid_rowconfigure(0, weight=1)
        main.grid_columnconfigure(0, weight=1)

        # ---------------- 全部票池页 ----------------
        self.all_page = tk.Frame(main, bg=self.APP_BG)
        self.all_page.grid(row=0, column=0, sticky="nsew")

        # 两个区域由 PanedWindow 管理。中间横向分割线可直接拖动，
        # 关闭程序时会保存其位置，下次启动自动恢复。
        self.vertical_panes = tk.PanedWindow(
            self.all_page,
            orient=tk.VERTICAL,
            bg=self.BORDER_BG,
            bd=0,
            relief=tk.FLAT,
            sashwidth=7,
            sashrelief=tk.FLAT,
            sashpad=0,
            showhandle=False,
            opaqueresize=True,
            cursor="sb_v_double_arrow",
        )
        self.vertical_panes.pack(fill=tk.BOTH, expand=True)
        self.vertical_panes.bind(
            "<ButtonRelease-1>",
            lambda _event: self.save_pane_layout(),
            add="+",
        )

        # ---------------- 核心票池 ----------------
        core_group = self.create_panel(
            self.vertical_panes,
            "核心票池",
        )
        self.vertical_panes.add(core_group, minsize=125, stretch="always")

        (
            self.core_canvas,
            self.core_table,
            self.core_window,
        ) = self.create_scroll_table(core_group, height=220)

        self.build_s_header(self.core_table, removable=False)

        for row_number, code in enumerate(self.core_stocks, start=1):
            self.core_rows[code] = self.create_s_row(
                parent=self.core_table,
                row_number=row_number,
                code=code,
                removable=False,
            )

        # ---------------- 更新票池 ----------------
        update_group = self.create_panel(
            self.vertical_panes,
            "更新票池",
        )
        self.vertical_panes.add(update_group, minsize=135, stretch="always")

        self.update_entry, self.update_status_label = self.create_input_bar(
            parent=update_group,
            button_text="添加",
            command=self.add_update_stock,
            hint="输入 NVDA 或 US.NVDA",
        )

        (
            self.update_canvas,
            self.update_table,
            self.update_window,
        ) = self.create_scroll_table(update_group, height=160)

        self.render_update_rows()

        # ---------------- 突破票页 ----------------
        self.breakout_page = tk.Frame(main, bg=self.APP_BG)
        self.breakout_page.grid(row=0, column=0, sticky="nsew")

        breakout_group = self.create_panel(
            self.breakout_page,
            "突破票 · 突破且强于QQQ · 按相对强度排序",
        )
        breakout_group.pack(fill=tk.BOTH, expand=True)

        (
            self.breakout_canvas,
            self.breakout_table,
            self.breakout_window,
        ) = self.create_scroll_table(breakout_group, height=360)

        self.render_breakout_rows()
        self.show_page("all")
        self.update_all_code_highlights()


        # Windows / macOS 鼠标滚轮以及 Linux 滚轮事件。
        # 只有鼠标所在的表格区域会滚动。
        self.root.bind_all("<MouseWheel>", self.on_table_mousewheel, add="+")
        self.root.bind_all("<Button-4>", self.on_table_mousewheel, add="+")
        self.root.bind_all("<Button-5>", self.on_table_mousewheel, add="+")

        # 等窗口完成布局后恢复上次拖动后的分割位置。
        self.root.after_idle(self.restore_pane_layout)

        self.update_entry.focus_set()

    def style_page_button(self, button, active):
        if active:
            button.config(
                bg=self.ACCENT_BLUE,
                fg="#FFFFFF",
                activebackground=self.BUTTON_ACTIVE_BG,
                activeforeground="#FFFFFF",
            )
        else:
            button.config(
                bg=self.HEADER_BG,
                fg=self.TEXT_SECONDARY,
                activebackground=self.BORDER_BG,
                activeforeground=self.TEXT_PRIMARY,
            )

    def show_page(self, page):
        """切换全部票池 / 突破票页面。"""

        if page not in {"all", "breakout"}:
            return

        self.current_page = page

        if page == "all":
            self.all_page.tkraise()
            self.page_hint_label.config(text="核心 + 更新")
            self.root.after_idle(self.restore_pane_layout)
        else:
            self.breakout_page.tkraise()
            self.render_breakout_rows()

        self.style_page_button(self.page_all_button, page == "all")
        self.style_page_button(self.page_breakout_button, page == "breakout")

    def create_panel(self, parent, title):
        return tk.LabelFrame(
            parent,
            text=title,
            bg=self.PANEL_BG,
            fg=self.TEXT_PRIMARY,
            font=("微软雅黑", 10, "bold"),
            bd=1,
            relief=tk.SOLID,
            highlightthickness=0,
            padx=5,
            pady=5,
        )

    def create_input_bar(self, parent, button_text, command, hint):
        control = tk.Frame(parent, bg=self.PANEL_BG)
        control.pack(fill=tk.X, pady=(0, 3))

        tk.Label(
            control,
            text="代码",
            bg=self.PANEL_BG,
            fg=self.TEXT_SECONDARY,
            font=("微软雅黑", 9),
        ).pack(side=tk.LEFT, padx=(1, 5))

        entry = tk.Entry(
            control,
            bg=self.INPUT_BG,
            fg=self.TEXT_PRIMARY,
            insertbackground=self.TEXT_PRIMARY,
            selectbackground=self.ACCENT_BLUE,
            selectforeground="#FFFFFF",
            relief=tk.FLAT,
            bd=0,
            highlightthickness=1,
            highlightbackground=self.BORDER_BG,
            highlightcolor=self.ACCENT_BLUE,
            font=("Consolas", 10),
        )
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True, ipady=3, padx=(0, 5))
        entry.bind("<Return>", command)

        tk.Button(
            control,
            text=button_text,
            width=5,
            bg=self.ACCENT_BLUE,
            fg="#FFFFFF",
            activebackground=self.BUTTON_ACTIVE_BG,
            activeforeground="#FFFFFF",
            relief=tk.FLAT,
            bd=0,
            cursor="hand2",
            padx=3,
            pady=2,
            font=("微软雅黑", 9, "bold"),
            command=command,
        ).pack(side=tk.LEFT)

        status_label = tk.Label(
            parent,
            text=hint,
            anchor="w",
            justify=tk.LEFT,
            wraplength=320,
            bg=self.PANEL_BG,
            fg=self.TEXT_MUTED,
            font=("微软雅黑", 8),
        )
        status_label.pack(fill=tk.X, pady=(0, 3))

        return entry, status_label

    def create_scroll_table(self, parent, height):
        """
        创建无可见右侧滚动条的表格。

        区域高度由外层可拖动分割线控制；当股票行超过当前区域时，
        把鼠标放在该表格内并滚动滚轮即可上下浏览。
        """

        body = tk.Frame(parent, bg=self.PANEL_BG)
        body.pack(fill=tk.BOTH, expand=True)

        canvas = tk.Canvas(
            body,
            bg=self.TABLE_BG,
            highlightthickness=0,
            bd=0,
            height=height,
        )
        canvas.pack(fill=tk.BOTH, expand=True)

        table = tk.Frame(canvas, bg=self.TABLE_BG)
        window = canvas.create_window(
            (0, 0),
            window=table,
            anchor="nw",
        )

        # 给事件目标向上查找时留下所属 Canvas 标记。
        body._scroll_canvas = canvas
        canvas._scroll_canvas = canvas
        table._scroll_canvas = canvas

        table.bind(
            "<Configure>",
            lambda _event, current_canvas=canvas: current_canvas.configure(
                scrollregion=current_canvas.bbox("all")
            ),
        )
        canvas.bind(
            "<Configure>",
            lambda event, current_canvas=canvas, current_window=window: (
                current_canvas.itemconfigure(current_window, width=event.width)
            ),
        )

        return canvas, table, window

    def find_scroll_canvas(self, widget):
        """从鼠标所在控件向父级查找其所属表格 Canvas。"""

        current = widget

        while current is not None:
            canvas = getattr(current, "_scroll_canvas", None)

            if canvas is not None:
                return canvas

            current = getattr(current, "master", None)

        return None

    def on_table_mousewheel(self, event):
        """只滚动鼠标当前所在的票池表格，不显示右侧竖向滚动条。"""

        canvas = self.find_scroll_canvas(event.widget)

        if canvas is None:
            return None

        region = canvas.bbox("all")

        if not region or region[3] <= canvas.winfo_height():
            return None

        if getattr(event, "num", None) == 4:
            units = -3
        elif getattr(event, "num", None) == 5:
            units = 3
        else:
            delta = getattr(event, "delta", 0)

            if delta == 0:
                return None

            # Windows 常见为 ±120，macOS 可能返回较小连续值。
            units = -int(delta / 120) * 3

            if units == 0:
                units = -1 if delta > 0 else 1

        canvas.yview_scroll(units, "units")
        return "break"

    def restore_pane_layout(self):
        """恢复上次关闭软件时保存的核心票池/更新票池分割线位置。"""

        if self.closed or not hasattr(self, "vertical_panes"):
            return

        self.root.update_idletasks()
        total_height = self.vertical_panes.winfo_height()

        if total_height <= 1:
            return

        position = int(total_height * 0.55)

        try:
            raw = PANE_LAYOUT_FILE.read_text(encoding="utf-8").strip()
            first_part = raw.split(",", 1)[0].strip()

            if first_part:
                position = int(first_part)

        except (FileNotFoundError, OSError, ValueError):
            pass

        minimum = 125
        maximum = max(total_height - 135, minimum)
        position = max(minimum, min(position, maximum))

        try:
            self.vertical_panes.sash_place(0, 0, position)
        except tk.TclError:
            pass

    def save_pane_layout(self):
        """保存用户拖动后的单条分割线位置。"""

        if not hasattr(self, "vertical_panes"):
            return

        try:
            position = self.vertical_panes.sash_coord(0)[1]
            PANE_LAYOUT_FILE.write_text(
                str(position),
                encoding="utf-8",
            )
        except (tk.TclError, OSError) as error:
            print(f"保存分割线位置失败：{error}")

    def restore_window_geometry(self, default_geometry):
        """恢复位置和高度，但旧版保存的宽度统一压缩到390像素。"""

        geometry = default_geometry

        try:
            saved = WINDOW_GEOMETRY_FILE.read_text(
                encoding="utf-8"
            ).strip()

            match = re.fullmatch(
                r"(\d+)x(\d+)([+-]\d+)([+-]\d+)",
                saved,
            )

            if match:
                _saved_width, saved_height, x_pos, y_pos = match.groups()
                height = max(
                    520,
                    min(
                        int(saved_height),
                        self.root.winfo_screenheight(),
                    ),
                )
                geometry = f"390x{height}{x_pos}{y_pos}"

        except (FileNotFoundError, OSError, ValueError):
            pass

        self.root.geometry(geometry)

    def schedule_window_geometry_save(self, event=None):
        """窗口移动或缩放后延迟保存，避免拖动过程中频繁写文件。"""

        if self.closed:
            return

        if event is not None and event.widget is not self.root:
            return

        if self.geometry_save_job is not None:
            try:
                self.root.after_cancel(self.geometry_save_job)
            except tk.TclError:
                pass

        self.geometry_save_job = self.root.after(
            500,
            self.save_window_geometry,
        )

    def save_window_geometry(self):
        """保存当前窗口宽高和屏幕位置。"""

        self.geometry_save_job = None

        try:
            self.root.update_idletasks()
            WINDOW_GEOMETRY_FILE.write_text(
                self.root.geometry(),
                encoding="utf-8",
            )
        except (tk.TclError, OSError) as error:
            print(f"保存窗口位置和大小失败：{error}")

    # ========================================================
    # S 线表格
    # ========================================================

    def build_s_header(self, parent, removable):
        headers = ["股票", "盘高", "昨收", "5M收", "较QQQ"]

        if removable:
            headers.append("删")

        for column, header in enumerate(headers):
            tk.Label(
                parent,
                text=header,
                bg=self.HEADER_BG,
                fg=self.TEXT_SECONDARY,
                relief=tk.FLAT,
                bd=0,
                highlightthickness=1,
                highlightbackground=self.BORDER_BG,
                pady=3,
                font=("微软雅黑", 9, "bold"),
            ).grid(row=0, column=column, sticky="nsew")

        weights = [16, 16, 16, 18, 20]
        minimums = [48, 52, 52, 58, 64]

        if removable:
            weights.append(8)
            minimums.append(24)

        for column, (weight, minimum) in enumerate(zip(weights, minimums)):
            parent.grid_columnconfigure(
                column,
                weight=weight,
                minsize=minimum,
                uniform="s_table",
            )

    def create_s_row(self, parent, row_number, code, removable):
        row = {}
        vs_text, vs_color = self.display_vs_qqq(code)

        values = [
            ("code", short_code(code), self.TEXT_PRIMARY),
            ("high", self.display_pm_high(code), self.TEXT_PRIMARY),
            ("previous", self.display_previous_close(code), self.TEXT_PRIMARY),
            ("close", self.display_latest_close(code), self.TEXT_PRIMARY),
            ("vs_qqq", vs_text, vs_color),
        ]

        for column, (key, value, color) in enumerate(values):
            label = tk.Label(
                parent,
                text=value,
                relief=tk.FLAT,
                bd=0,
                highlightthickness=1,
                highlightbackground=self.BORDER_BG,
                pady=3,
                padx=1,
                bg=self.NORMAL_BG,
                fg=color,
                font=("Consolas", 10),
            )
            label.grid(row=row_number, column=column, sticky="nsew")
            row[key] = label

            if key == "code":
                label.config(cursor="hand2")
                label.bind(
                    "<Button-1>",
                    lambda _event, stock=code: self.toggle_manual_highlight(stock),
                )
                self.bind_code_hover(label, code)

        if removable:
            button = tk.Button(
                parent,
                text="×",
                width=2,
                bg=self.NORMAL_BG,
                fg=self.TEXT_MUTED,
                activebackground="#FDE8EA",
                activeforeground=self.SIGNAL_RED,
                relief=tk.FLAT,
                bd=0,
                cursor="hand2",
                padx=0,
                pady=0,
                font=("Arial", 10, "bold"),
                command=lambda stock=code: self.remove_update_stock(stock),
            )
            button.grid(row=row_number, column=5, sticky="nsew")
            row["remove"] = button

        return row

    def render_update_rows(self):
        for child in self.update_table.winfo_children():
            child.destroy()

        self.update_rows.clear()
        self.build_s_header(self.update_table, removable=True)

        visible_stocks = [
            code
            for code in self.update_stocks
            if code not in self.core_stocks
        ]

        if not visible_stocks:
            tk.Label(
                self.update_table,
                text="暂无非核心股票",
                bg=self.TABLE_BG,
                fg=self.TEXT_MUTED,
                pady=12,
                relief=tk.FLAT,
                bd=0,
                highlightthickness=1,
                highlightbackground=self.BORDER_BG,
                font=("微软雅黑", 9),
            ).grid(row=1, column=0, columnspan=6, sticky="nsew")
            return

        for row_number, code in enumerate(visible_stocks, start=1):
            self.update_rows[code] = self.create_s_row(
                parent=self.update_table,
                row_number=row_number,
                code=code,
                removable=True,
            )

        self.update_all_code_highlights()

    def render_breakout_rows(self):
        """渲染突破且强于 QQQ 的股票，按相对强度从高到低。"""

        if not hasattr(self, "breakout_table"):
            return

        for child in self.breakout_table.winfo_children():
            child.destroy()

        self.breakout_rows.clear()
        self.build_s_header(self.breakout_table, removable=False)

        breakout_codes = self.get_breakout_codes()

        if hasattr(self, "page_hint_label") and self.current_page == "breakout":
            self.page_hint_label.config(
                text=f"当前 {len(breakout_codes)} 只 · 强→弱"
            )

        if not breakout_codes:
            tk.Label(
                self.breakout_table,
                text="暂无突破且强于QQQ的股票",
                bg=self.TABLE_BG,
                fg=self.TEXT_MUTED,
                pady=12,
                relief=tk.FLAT,
                bd=0,
                highlightthickness=1,
                highlightbackground=self.BORDER_BG,
                font=("微软雅黑", 9),
            ).grid(row=1, column=0, columnspan=5, sticky="nsew")
            return

        for row_number, code in enumerate(breakout_codes, start=1):
            self.breakout_rows[code] = self.create_s_row(
                parent=self.breakout_table,
                row_number=row_number,
                code=code,
                removable=False,
            )
            self.apply_close_signal_style(code)

        self.update_all_code_highlights()


    # ========================================================
    # 股票代码高亮
    # ========================================================

    def save_manual_highlights(self):
        save_daily_highlights(
            MANUAL_HIGHLIGHTS_FILE,
            self.session_day,
            self.manual_highlighted_codes,
        )

    def toggle_manual_highlight(self, code):
        """点击代码，切换手动“重点关注”标签。"""

        if code in self.manual_highlighted_codes:
            self.manual_highlighted_codes.remove(code)
        else:
            self.manual_highlighted_codes.add(code)

        self.save_manual_highlights()
        self.update_code_highlight(code)

    def update_code_highlight(self, code):
        # 仅保留手动重点标签。
        # 已移除“盘前低点 > 昨日收盘价”自动变绿，避免误标。
        manual = code in self.manual_highlighted_codes
        background = self.ATTENTION_BG if manual else self.NORMAL_BG

        for row in self.iter_s_rows(code):
            row["code"].config(
                bg=background,
                fg=(self.ATTENTION_FG if manual else self.TEXT_PRIMARY),
                font=(
                    "微软雅黑",
                    10,
                    "bold" if manual else "normal",
                ),
            )

    def bind_code_hover(self, label, code):
        def on_enter(_event):
            if code not in self.manual_highlighted_codes:
                label.config(bg="#EEF4FA")

        def on_leave(_event):
            self.update_code_highlight(code)

        label.bind("<Enter>", on_enter)
        label.bind("<Leave>", on_leave)

    def update_all_code_highlights(self):
        for code in self.get_s_stocks():
            self.update_code_highlight(code)

    # ========================================================
    # 新增及删除股票
    # ========================================================

    @staticmethod
    def parse_codes(raw_text):
        pieces = re.split(r"[\s,，;；]+", raw_text.strip())
        valid = []
        invalid = []

        for piece in pieces:
            if not piece:
                continue

            code = normalize_stock_code(piece)

            if code is None:
                invalid.append(piece)
            else:
                valid.append(code)

        return valid, invalid

    def set_status(self, label, text, error=False):
        label.config(
            text=text,
            fg=self.ERROR_FG if error else self.TEXT_SECONDARY,
        )

    def add_update_stock(self, _event=None):
        raw_text = self.update_entry.get().strip()

        if not raw_text:
            self.set_status(self.update_status_label, "请输入股票代码", error=True)
            return

        codes, invalid = self.parse_codes(raw_text)
        added = []
        existing = []

        core_existing = []

        for code in codes:
            if code in self.core_stocks:
                core_existing.append(code)
                continue

            if code in self.update_stocks:
                existing.append(code)
                continue

            self.update_stocks.append(code)
            added.append(code)

        if added:
            save_stock_file(
                UPDATE_STOCKS_FILE,
                self.update_stocks,
                "更新票池",
            )
            self.render_update_rows()
            self.update_all_code_highlights()

            for index, code in enumerate(added):
                self.root.after(
                    100 + index * 60,
                    lambda stock=code: self.initialize_added_stock(stock),
                )

        # 只要输入中包含可识别代码，就清空输入框。
        # 已有核心票会被直接忽略，不新增，也不会改变高亮。
        if codes:
            self.update_entry.delete(0, tk.END)

        messages = []

        if added:
            messages.append(
                "已添加：" + ", ".join(short_code(code) for code in added)
            )

        if core_existing:
            messages.append(
                "已忽略核心票：" + ", ".join(
                    short_code(code) for code in core_existing
                )
            )

        if existing:
            messages.append(
                "已存在：" + ", ".join(short_code(code) for code in existing)
            )

        if invalid:
            messages.append("格式无效：" + ", ".join(invalid))

        self.set_status(
            self.update_status_label,
            "；".join(messages),
            error=(not added and bool(invalid)),
        )

    def remove_update_stock(self, code):
        if code not in self.update_stocks:
            return

        self.update_stocks.remove(code)
        save_stock_file(
            UPDATE_STOCKS_FILE,
            self.update_stocks,
            "更新票池",
        )

        self.render_update_rows()
        self.render_breakout_rows()
        self.update_all_code_highlights()
        self.cleanup_unused_code(code)

        self.set_status(
            self.update_status_label,
            f"已从更新票池删除：{short_code(code)}",
        )


    def cleanup_unused_code(self, code):
        """仅当代码已不属于任何区域时，才清理其缓存。"""

        if self.code_is_used(code):
            return

        mappings = [
            self.pm_high,
            self.pm_low,
            self.locked_high,
            self.locked_low,
            self.previous_close,
            self.previous_high,
            self.previous_close_day,
            self.latest_close,
            self.breakout_state,
            self.last_completed_end,
            self.last_kline_request_at,
        ]

        for mapping in mappings:
            mapping.pop(code, None)

        self.subscribed_5m.discard(code)

        if code in self.manual_highlighted_codes:
            self.manual_highlighted_codes.remove(code)
            self.save_manual_highlights()

    def initialize_added_stock(self, code):
        """新增股票后，立即按当前美东时段补齐数据。"""

        if self.closed or not self.code_is_used(code):
            return

        self.load_previous_closes(codes=[code])

        now = eastern_now()

        if now.time() < PRE_START:
            self.load_and_lock_pm(self.session_day, codes=[code])

        elif now.time() < PRE_LOCK_TIME:
            self.refresh_pm(self.session_day, codes=[code])

        else:
            self.load_and_lock_pm(self.session_day, codes=[code])

        # 新增股票先订阅实时 5 分钟 K。
        self.ensure_5m_subscription([code])

        # 美东 04:05 起可取得第一根 04:00-04:05 完整 5 分钟 K。
        if now.time() >= FIRST_5M_END:
            self.load_latest_completed_bars(force=True, codes=[code])
            self.update_vs_qqq(code)

    # ========================================================
    # 富途牛牛信号自选组同步
    # ========================================================

    def is_stronger_than_qqq(self, code):
        """个股相对昨收涨幅是否严格大于 QQQ。"""

        stock_pct = self.get_change_vs_prev_close_pct(code)
        qqq_pct = self.get_change_vs_prev_close_pct(BENCHMARK_CODE)

        if stock_pct is None or qqq_pct is None:
            return False

        return stock_pct > qqq_pct

    def get_active_signal_codes(self):
        """
        返回应同步进 X 组的股票：与突破票页相同，
        突破盘前高且涨幅大于 QQQ，按相对强度从高到低。
        """

        return self.get_breakout_codes()

    def extract_security_codes(self, data):
        """从 get_user_security 返回值提取组内代码，保留牛牛当前顺序。"""

        if (
            not isinstance(data, pd.DataFrame)
            or data.empty
            or "code" not in data.columns
        ):
            return []

        return [
            str(code)
            for code in data["code"].tolist()
            if pd.notna(code)
        ]

    def read_group_codes(self, group_name):
        """读取自定义组当前股票列表（含顺序）。"""

        ret, data = self.ctx.get_user_security(group_name)

        if ret != RET_OK:
            return False, data

        return True, self.extract_security_codes(data)

    def rewrite_group_ordered(self, group_name, target_codes, move_out_op):
        """
        整组移出后再按目标顺序加回，尽量让牛牛 X 组与相对强度排序一致。

        富途 OpenAPI 没有排序接口；批量 ADD 后的顺序因版本而异，
        因此写入后会回读核对，必要时按相反顺序再写一次。
        """

        ok, current_codes = self.read_group_codes(group_name)

        if not ok:
            return False, current_codes, False

        if current_codes == list(target_codes):
            return True, "名单与顺序已一致", False

        if current_codes:
            ret, message = self.ctx.modify_user_security(
                group_name,
                move_out_op,
                current_codes,
            )

            if ret != RET_OK:
                return False, f"移出旧名单失败：{message}", False

        if not target_codes:
            return True, "组已清空", True

        add_codes = list(target_codes)

        if self.futu_add_list_reversed:
            add_codes = list(reversed(add_codes))

        ret, message = self.ctx.modify_user_security(
            group_name,
            ModifyUserSecurityOp.ADD,
            add_codes,
        )

        if ret != RET_OK:
            return False, f"按序加回失败：{message}", True

        ok, written_codes = self.read_group_codes(group_name)

        if not ok:
            return False, written_codes, True

        if written_codes == list(target_codes):
            if self.futu_add_list_reversed is None:
                self.futu_add_list_reversed = False
            return True, "已按相对强度重排", True

        if written_codes == list(reversed(target_codes)):
            # 批量 ADD 后顺序颠倒：移出再反向加回。
            self.futu_add_list_reversed = True
            ret, message = self.ctx.modify_user_security(
                group_name,
                move_out_op,
                written_codes,
            )

            if ret != RET_OK:
                return False, f"纠正顺序时移出失败：{message}", True

            ret, message = self.ctx.modify_user_security(
                group_name,
                ModifyUserSecurityOp.ADD,
                list(reversed(target_codes)),
            )

            if ret != RET_OK:
                return False, f"纠正顺序时加回失败：{message}", True

            ok, fixed_codes = self.read_group_codes(group_name)

            if not ok:
                return False, fixed_codes, True

            if fixed_codes == list(target_codes):
                return True, "已按相对强度重排", True

            return (
                True,
                "组内股票已更新，但牛牛未按相对强度保留顺序",
                True,
            )

        return (
            True,
            "组内股票已更新，但牛牛显示顺序无法可靠控制",
            True,
        )

    def set_sync_status(self, text, error=False):
        """刷新同步按钮旁的状态文字。"""

        if not hasattr(self, "sync_status_label"):
            return

        self.sync_status_label.config(
            text=text,
            fg=self.ERROR_FG if error else self.TEXT_SECONDARY,
        )

    @staticmethod
    def is_custom_group_type(value):
        """兼容 SDK 返回字符串或枚举对象的自定义分组类型。"""

        return "CUSTOM" in str(value).upper()

    @staticmethod
    def truncate_reminder_value(value):
        """按富途规则把提醒值截断到小数点后 3 位。"""

        return float(
            Decimal(str(float(value))).quantize(
                Decimal("0.001"),
                rounding=ROUND_DOWN,
            )
        )

    @staticmethod
    def enum_name(value):
        """把 SDK 枚举或返回字符串统一成可比较的名称。"""

        return str(value).split(".")[-1].upper()

    @staticmethod
    def normalize_session_names(values):
        if values is None:
            return set()

        if isinstance(values, str):
            values = [values]

        try:
            return {
                App.enum_name(value)
                for value in values
            }
        except TypeError:
            return {App.enum_name(values)}

    @staticmethod
    def build_reminder_sessions(include_premarket):
        """兼容 SDK 枚举差异，构造提醒生效时段。"""

        names = ["OPEN"]

        if include_premarket:
            names.insert(0, "US_PRE")

        sessions = []

        for name in names:
            value = getattr(
                PriceReminderMarketStatus,
                name,
                None,
            )

            if value is not None:
                sessions.append(value)

        return sessions

    def build_desired_price_reminders(self, code):
        """返回某只 X 组股票当前应存在的提醒。"""

        desired = {}

        pm_high = self.locked_high.get(code)

        if pm_high is None:
            pm_high = self.pm_high.get(code)

        pm_low = self.locked_low.get(code)

        if pm_low is None:
            pm_low = self.pm_low.get(code)

        if pm_high is not None and pd.notna(pm_high) and float(pm_high) > 0:
            desired[REMINDER_NOTE_PM_HIGH] = {
                "type": PriceReminderType.PRICE_UP,
                "value": self.truncate_reminder_value(pm_high),
                "sessions": self.build_reminder_sessions(True),
            }

        if pm_low is not None and pd.notna(pm_low) and float(pm_low) > 0:
            desired[REMINDER_NOTE_PM_LOW] = {
                "type": PriceReminderType.PRICE_DOWN,
                "value": self.truncate_reminder_value(pm_low),
                "sessions": self.build_reminder_sessions(True),
            }

        return desired

    def delete_price_reminder(self, code, key):
        ret, message = self.ctx.set_price_reminder(
            code=code,
            op=SetPriceReminderOp.DEL,
            key=int(key),
        )

        if ret != RET_OK:
            raise RuntimeError(
                f"{code} 删除提醒失败，key={key}：{message}"
            )

    def sync_price_reminders_for_code(self, code, desired=None, managed=None):
        """
        精确同步 IGO盘前高、IGO盘前低两类提醒。
        旧版 IGO VWAP 提醒会被删除，其他提醒不会被触碰。
        """

        if desired is None:
            desired = self.build_desired_price_reminders(code)

        if managed is None:
            # 兼容单只股票直接调用；批量同步会在外层一次性读取整个美股市场，
            # 避免触发 get_price_reminder 每 30 秒最多 10 次的限制。
            ret, data = self.ctx.get_price_reminder(code=code)

            if ret != RET_OK:
                raise RuntimeError(
                    f"{code} 读取到价提醒失败：{data}"
                )

            if not isinstance(data, pd.DataFrame):
                data = pd.DataFrame()

            if data.empty or "note" not in data.columns:
                managed = pd.DataFrame()
            else:
                managed = data[
                    data["note"].astype(str).isin(
                        PROGRAM_REMINDER_NOTES
                    )
                ].copy()
        else:
            managed = managed.copy()

        added = 0
        modified = 0
        deleted = 0
        retained_keys = set()

        for note, spec in desired.items():
            if managed.empty:
                rows = pd.DataFrame()
            else:
                rows = managed[
                    managed["note"].astype(str) == note
                ].copy()

            primary = None

            if not rows.empty:
                primary = rows.iloc[0]
                retained_keys.add(int(primary["key"]))

                for _, duplicate in rows.iloc[1:].iterrows():
                    self.delete_price_reminder(
                        code,
                        duplicate["key"],
                    )
                    deleted += 1

            desired_type = self.enum_name(spec["type"])
            desired_value = float(spec["value"])
            desired_sessions = self.normalize_session_names(
                spec["sessions"]
            )

            if primary is None:
                ret, message = self.ctx.set_price_reminder(
                    code=code,
                    op=SetPriceReminderOp.ADD,
                    reminder_type=spec["type"],
                    reminder_freq=PriceReminderFreq.ALWAYS,
                    value=desired_value,
                    note=note,
                    reminder_session_list=spec["sessions"],
                )

                if ret != RET_OK:
                    raise RuntimeError(
                        f"{code} 新增提醒 {note} 失败：{message}"
                    )

                added += 1
                continue

            existing_type = self.enum_name(
                primary.get("reminder_type")
            )

            try:
                existing_value = float(primary.get("value"))
            except (TypeError, ValueError):
                existing_value = None

            existing_freq = self.enum_name(
                primary.get("reminder_freq")
            )
            existing_sessions = self.normalize_session_names(
                primary.get("reminder_session_list")
            )
            existing_enabled = bool(
                primary.get("enable", True)
            )

            need_modify = (
                existing_type != desired_type
                or existing_value is None
                or abs(existing_value - desired_value) > 0.0005
                or existing_freq
                != self.enum_name(PriceReminderFreq.ALWAYS)
                or existing_sessions != desired_sessions
            )

            if need_modify:
                ret, message = self.ctx.set_price_reminder(
                    code=code,
                    op=SetPriceReminderOp.MODIFY,
                    key=int(primary["key"]),
                    reminder_type=spec["type"],
                    reminder_freq=PriceReminderFreq.ALWAYS,
                    value=desired_value,
                    note=note,
                    reminder_session_list=spec["sessions"],
                )

                if ret != RET_OK:
                    raise RuntimeError(
                        f"{code} 更新提醒 {note} 失败：{message}"
                    )

                modified += 1

            if not existing_enabled:
                ret, message = self.ctx.set_price_reminder(
                    code=code,
                    op=SetPriceReminderOp.ENABLE,
                    key=int(primary["key"]),
                )

                if ret != RET_OK:
                    raise RuntimeError(
                        f"{code} 启用提醒 {note} 失败：{message}"
                    )

        # 删除不再需要或属于已移出 X 组的程序提醒。
        if not managed.empty:
            desired_notes = set(desired)

            for _, row in managed.iterrows():
                note = str(row.get("note", ""))
                key = int(row["key"])

                if note not in desired_notes:
                    self.delete_price_reminder(code, key)
                    deleted += 1

        return added, modified, deleted

    def sync_all_price_reminders(
        self,
        target_codes,
        removed_codes,
    ):
        """
        批量同步程序管理的提醒。

        关键优化：只调用一次 get_price_reminder(market=Market.US)，
        再在本地按股票筛选，避免原先每只股票调用一次而触发
        “30 秒最多 10 次”的接口限制。
        """

        target_codes = list(dict.fromkeys(target_codes))
        removed_codes = list(dict.fromkeys(removed_codes))
        all_codes = list(dict.fromkeys(target_codes + removed_codes))

        if not all_codes:
            return {
                "added": 0,
                "modified": 0,
                "deleted": 0,
            }

        ret, data = self.ctx.get_price_reminder(
            code=None,
            market=Market.US,
        )

        if ret != RET_OK:
            raise RuntimeError(
                f"批量读取美股到价提醒失败：{data}"
            )

        if not isinstance(data, pd.DataFrame):
            data = pd.DataFrame()

        if (
            data.empty
            or "code" not in data.columns
            or "note" not in data.columns
        ):
            managed_all = pd.DataFrame()
        else:
            managed_all = data[
                data["code"].astype(str).isin(all_codes)
                & data["note"].astype(str).isin(
                    PROGRAM_REMINDER_NOTES
                )
            ].copy()

        total_added = 0
        total_modified = 0
        total_deleted = 0

        for code in target_codes:
            desired = self.build_desired_price_reminders(code)

            if managed_all.empty:
                managed = pd.DataFrame()
            else:
                managed = managed_all[
                    managed_all["code"].astype(str) == code
                ].copy()

            added, modified, deleted = (
                self.sync_price_reminders_for_code(
                    code,
                    desired=desired,
                    managed=managed,
                )
            )

            total_added += added
            total_modified += modified
            total_deleted += deleted

        for code in removed_codes:
            if managed_all.empty:
                managed = pd.DataFrame()
            else:
                managed = managed_all[
                    managed_all["code"].astype(str) == code
                ].copy()

            added, modified, deleted = (
                self.sync_price_reminders_for_code(
                    code,
                    desired={},
                    managed=managed,
                )
            )

            total_added += added
            total_modified += modified
            total_deleted += deleted

        return {
            "added": total_added,
            "modified": total_modified,
            "deleted": total_deleted,
        }


    def schedule_auto_sync(self, reason):
        """防抖安排自动同步，把同一时刻的多只股票变化合并处理。"""

        if self.closed:
            return

        self.auto_sync_pending_reason = reason

        if self.auto_sync_job is not None:
            return

        self.auto_sync_job = self.root.after(
            AUTO_SYNC_DEBOUNCE_MS,
            self.run_scheduled_auto_sync,
        )

    def run_scheduled_auto_sync(self):
        """执行已经排队的自动同步；手动同步占用时稍后重试。"""

        self.auto_sync_job = None

        if self.closed:
            return

        reason = self.auto_sync_pending_reason or "自动检查"
        self.auto_sync_pending_reason = None

        if self.sync_in_progress:
            self.auto_sync_pending_reason = reason
            self.auto_sync_job = self.root.after(
                1000,
                self.run_scheduled_auto_sync,
            )
            return

        self.sync_lit_stocks_to_futu(
            automatic=True,
            reason=reason,
        )

    def check_five_minute_auto_sync(self):
        """
        常规盘每根完整 5 分钟 K 后检查目标名单。

        先等待所有股票读到当前边界；若个别代码迟迟没有更新，最多等待
        AUTO_SYNC_MAX_WAIT_SECONDS，避免一只异常股票阻塞整天的自动同步。
        真正访问富途前还会比较最近一次成功同步的名单，无变化则直接跳过。
        """

        now = eastern_now()

        if self.session_day != now.date():
            return

        now_naive = naive_eastern(now)
        first_boundary = datetime.combine(
            self.session_day,
            RTH_FIRST_5M_END,
        )
        session_close = datetime.combine(
            self.session_day,
            CLOSE_TIME,
        )

        if now_naive < first_boundary:
            return

        if now_naive > session_close + timedelta(
            seconds=AUTO_SYNC_FINAL_GRACE_SECONDS
        ):
            return

        expected_end = self.get_expected_completed_end(now)

        if (
            expected_end is None
            or expected_end < first_boundary
            or expected_end > session_close
        ):
            return

        if (
            self.last_auto_sync_boundary is not None
            and expected_end <= self.last_auto_sync_boundary
        ):
            return

        codes = self.get_s_stocks()
        not_ready = [
            code
            for code in codes
            if self.last_completed_end.get(code) is None
            or self.last_completed_end[code] < expected_end
        ]
        elapsed = (now_naive - expected_end).total_seconds()

        if not_ready and elapsed < AUTO_SYNC_MAX_WAIT_SECONDS:
            return

        self.last_auto_sync_boundary = expected_end

        if not_ready:
            print(
                f"自动同步等待超时：边界={expected_end:%H:%M} "
                f"尚未更新={','.join(not_ready)}"
            )

        self.schedule_auto_sync(
            f"完整5M {expected_end:%H:%M}"
        )

    def sync_lit_stocks_to_futu(self, automatic=False, reason="手动"):
        """把固定自选组 X 精确同步成当前有效信号股票。"""

        if self.closed:
            return

        target_codes = self.get_active_signal_codes()
        # 自动同步只关心进出集合，避免相对强度微抖就整组重写。
        membership_signature = frozenset(target_codes)

        if (
            automatic
            and self.last_successful_sync_target == membership_signature
        ):
            self.set_sync_status(
                f"自动检查完成（{reason}）：进出无变化，X组{len(target_codes)}只"
            )
            print(
                f"自动同步跳过：reason={reason} "
                f"target={target_codes} 原因=进出名单无变化"
            )
            return

        if self.sync_in_progress:
            return

        self.sync_in_progress = True

        if hasattr(self, "sync_button"):
            self.sync_button.config(
                state=tk.DISABLED,
                text=("自动同步中…" if automatic else "同步中…"),
                cursor="arrow",
            )

        self.set_sync_status(
            f"{'自动' if automatic else '手动'}同步中（{reason}）："
            f"{FUTU_SIGNAL_GROUP_NAME}"
        )
        self.root.update_idletasks()

        try:
            # OpenAPI 没有创建自选分组接口，所以先确认固定组已由用户创建，
            # 同时拒绝操作重名组，避免富途默认选择排序第一的同名分组。
            ret, groups = self.ctx.get_user_security_group()

            if ret != RET_OK:
                self.set_sync_status(
                    f"读取牛牛自选组失败：{groups}",
                    error=True,
                )
                return

            if (
                groups is None
                or not isinstance(groups, pd.DataFrame)
                or "group_name" not in groups.columns
                or "group_type" not in groups.columns
            ):
                self.set_sync_status(
                    "牛牛返回的自选组数据格式异常",
                    error=True,
                )
                return

            same_name = groups[
                groups["group_name"].astype(str)
                == FUTU_SIGNAL_GROUP_NAME
            ]
            custom_matches = same_name[
                same_name["group_type"].map(self.is_custom_group_type)
            ]

            if custom_matches.empty:
                self.set_sync_status(
                    f"请先在牛牛手动创建自定义组“{FUTU_SIGNAL_GROUP_NAME}”",
                    error=True,
                )
                return

            if len(custom_matches) > 1:
                self.set_sync_status(
                    f"检测到多个同名组“{FUTU_SIGNAL_GROUP_NAME}”，请只保留一个",
                    error=True,
                )
                return

            ret, current_data = self.ctx.get_user_security(
                FUTU_SIGNAL_GROUP_NAME
            )

            if ret != RET_OK:
                self.set_sync_status(
                    f"读取组内股票失败：{current_data}",
                    error=True,
                )
                return

            current_codes = self.extract_security_codes(current_data)
            current_set = set(current_codes)
            target_set = set(target_codes)
            to_add = [
                code for code in target_codes
                if code not in current_set
            ]
            to_remove = [
                code for code in current_codes
                if code not in target_set
            ]

            move_out_op = getattr(
                ModifyUserSecurityOp,
                "MOVE_OUT",
                None,
            )

            if (to_remove or (not automatic and current_codes)) and (
                move_out_op is None
            ):
                self.set_sync_status(
                    "当前 futu SDK 不支持 MOVE_OUT，请升级 SDK；未改动牛牛自选组",
                    error=True,
                )
                return

            reordered = False
            order_text = "未改顺序"

            if automatic:
                # 自动：只做进出增减，最多 0～2 次 modify，不整组重写。
                if not to_add and not to_remove:
                    order_text = "进出已对齐"
                else:
                    if to_add:
                        ret, message = self.ctx.modify_user_security(
                            FUTU_SIGNAL_GROUP_NAME,
                            ModifyUserSecurityOp.ADD,
                            to_add,
                        )

                        if ret != RET_OK:
                            self.set_sync_status(
                                f"新增信号股票失败：{message}",
                                error=True,
                            )
                            return

                    if to_remove:
                        ret, message = self.ctx.modify_user_security(
                            FUTU_SIGNAL_GROUP_NAME,
                            move_out_op,
                            to_remove,
                        )

                        if ret != RET_OK:
                            self.set_sync_status(
                                f"移出无有效信号股票失败：{message}",
                                error=True,
                            )
                            return

                    order_text = "仅进出"
            else:
                # 手动：整组按相对强度重排（API 较贵，只在点按钮时做）。
                need_rewrite = current_codes != list(target_codes)

                if need_rewrite:
                    ok, detail, reordered = self.rewrite_group_ordered(
                        FUTU_SIGNAL_GROUP_NAME,
                        target_codes,
                        move_out_op,
                    )

                    if not ok:
                        self.set_sync_status(str(detail), error=True)
                        return

                    order_text = (
                        "已重排"
                        if reordered and not to_add and not to_remove
                        else ("含重排" if reordered else "顺序已对齐")
                    )
                else:
                    order_text = "顺序已对齐"

            # 第一次同步或手动同步做完整提醒审计；之后自动同步只处理
            # 新增和移出的股票，避免每根 5M K 都重复核对整个 X 组。
            full_reminder_audit = (
                not automatic
                or self.last_successful_sync_target is None
            )
            reminder_target_codes = (
                target_codes if full_reminder_audit else to_add
            )

            reminder_result = self.sync_all_price_reminders(
                target_codes=reminder_target_codes,
                removed_codes=to_remove,
            )

            self.last_successful_sync_target = membership_signature

            self.set_sync_status(
                f"{'自动' if automatic else '手动'}完成（{reason}）："
                f"X组{len(target_codes)}只；"
                f"组新增{len(to_add)}、移出{len(to_remove)}；"
                f"{order_text}；"
                f"提醒新增{reminder_result['added']}、"
                f"更新{reminder_result['modified']}、"
                f"删除{reminder_result['deleted']}"
            )
            print(
                f"牛牛同步完成：mode={'auto' if automatic else 'manual'} "
                f"reason={reason} group={FUTU_SIGNAL_GROUP_NAME} "
                f"target={target_codes} added={to_add} removed={to_remove} "
                f"reordered={reordered} reminders={reminder_result}"
            )

        except Exception as error:
            self.set_sync_status(
                f"同步牛牛自选组异常：{error}",
                error=True,
            )
            print(f"同步牛牛自选组异常：{error}")

        finally:
            self.sync_in_progress = False

            if hasattr(self, "sync_button"):
                self.sync_button.config(
                    state=tk.NORMAL,
                    text="同步 X",
                    cursor="hand2",
                )

    # ========================================================
    # 初始化与定时器
    # ========================================================

    def initialize(self):
        if self.closed:
            return

        # 实时 K 线接口必须先订阅。ETH 包含常规盘和盘前盘后。
        stocks = self.get_all_stocks()
        self.ensure_5m_subscription(stocks)
        self.log_api_quota_status()
        self.load_initial_state()
        self.root.after(PM_REFRESH_MS, self.pm_timer)
        self.root.after(KLINE_CHECK_MS, self.kline_timer)
        self.root.after(1_000, self.market_breadth_timer)

    def load_initial_state(self):
        now = eastern_now()

        self.load_previous_closes()

        if now.time() < PRE_START:
            self.load_and_lock_pm(self.session_day)

        elif now.time() < PRE_LOCK_TIME:
            self.refresh_pm(self.session_day)

        else:
            self.load_and_lock_pm(self.session_day)

        # 启动时若已过 04:05，立即补齐最新完整 5 分钟 K（含 QQQ）。
        if now.time() >= FIRST_5M_END:
            self.load_latest_completed_bars(force=True)
            self.refresh_all_vs_qqq()

    def check_new_session(self):
        now = eastern_now()

        if now.time() < PRE_START:
            return False

        if self.session_day == now.date():
            return False

        print(
            f"美东 04:00 进入新监控日：{self.session_day} -> {now.date()}"
        )

        self.session_day = now.date()
        self.last_successful_sync_target = None
        self.last_auto_sync_boundary = None
        self.auto_sync_pending_reason = None

        if self.auto_sync_job is not None:
            try:
                self.root.after_cancel(self.auto_sync_job)
            except tk.TclError:
                pass
            self.auto_sync_job = None

        # 手动重点标签与盘前数据使用同一监控日周期，
        # 到美东 04:00 切换新监控日时统一清空。
        self.manual_highlighted_codes.clear()
        self.save_manual_highlights()

        for mapping in [
            self.pm_high,
            self.pm_low,
            self.locked_high,
            self.locked_low,
            self.previous_close,
            self.previous_high,
            self.previous_close_day,
            self.latest_close,
            self.breakout_state,
            self.last_completed_end,
            self.last_kline_request_at,
        ]:
            mapping.clear()

        for code in self.get_s_stocks():
            self.set_s_cell(code, "high", "-")
            self.set_s_cell(code, "previous", "-")
            self.set_s_cell(code, "close", "-")
            self.update_vs_qqq(code)
            self.set_breakout_signal(code, False)
            self.update_code_highlight(code)


        # 清除所有区域中由昨日手动点击留下的绿色代码背景。
        # 新监控日清除昨日手动重点标签，代码背景恢复默认。
        self.update_all_code_highlights()
        self.render_breakout_rows()

        # 新监控日立即读取前一交易日收盘价。
        self.load_previous_closes()

        return True

    def pm_timer(self):
        if self.closed:
            return

        try:
            self.check_new_session()
            now = eastern_now()

            if PRE_START <= now.time() < PRE_LOCK_TIME:
                self.refresh_pm(self.session_day)

            elif now.time() >= PRE_LOCK_TIME:
                self.load_and_lock_pm(self.session_day)

        except Exception as error:
            print(f"盘前定时器异常：{error}")

        finally:
            if not self.closed:
                self.root.after(PM_REFRESH_MS, self.pm_timer)


    def kline_timer(self):
        if self.closed:
            return

        try:
            self.check_new_session()
            self.load_latest_completed_bars(force=False)
            self.check_five_minute_auto_sync()

        except Exception as error:
            print(f"5 分钟 K 定时器异常：{error}")

        finally:
            if not self.closed:
                self.root.after(KLINE_CHECK_MS, self.kline_timer)

    # ========================================================
    # API 额度与市场广度
    # ========================================================

    def log_api_quota_status(self):
        """启动时只查询一次额度，便于确认实际占用，不参与循环轮询。"""

        try:
            ret, data = self.ctx.query_subscription()

            if ret == RET_OK and isinstance(data, dict):
                print(
                    "富途订阅额度："
                    f"本连接已用={data.get('own_used', '-')}，"
                    f"OpenD总已用={data.get('total_used', '-')}，"
                    f"剩余={data.get('remain', '-')}"
                )
            elif ret != RET_OK:
                print(f"查询订阅额度失败：{data}")

        except Exception as error:
            print(f"查询订阅额度异常：{error}")

        try:
            ret, data = self.ctx.get_history_kl_quota(get_detail=False)

            if ret == RET_OK:
                print(f"富途历史K线额度：{data}")
            else:
                print(f"查询历史K线额度失败：{data}")

        except Exception as error:
            print(f"查询历史K线额度异常：{error}")

    @staticmethod
    def parse_market_breadth(data):
        """
        把富途涨跌分布区间汇总为上涨、下跌、平盘家数。

        富途对正无穷区间可能返回 left=7/right=0，负无穷区间可能
        返回 left=0/right=-7，因此不能只按固定字段方向判断。
        """

        if not isinstance(data, dict):
            return None

        ranges = data.get("range_list")

        if not isinstance(ranges, list):
            return None

        up = 0
        down = 0
        flat = 0

        for item in ranges:
            if not isinstance(item, dict):
                continue

            try:
                count = int(item.get("stock_count", 0) or 0)
                left = float(item.get("left_border", 0) or 0)
                right = float(item.get("right_border", 0) or 0)
            except (TypeError, ValueError):
                continue

            range_type = str(item.get("type", "")).upper()
            low = min(left, right)
            high = max(left, right)

            if range_type == "NEGATIVE_INFINITY":
                down += count
            elif range_type == "POSITIVE_INFINITY":
                up += count
            elif low == 0 and high == 0:
                flat += count
            elif high <= 0 and low < 0:
                down += count
            elif low >= 0 and high > 0:
                up += count
            else:
                # 理论上分布区间不会跨越 0；若未来接口格式变化，
                # 使用区间中点做保守兼容，避免程序崩溃。
                midpoint = (left + right) / 2

                if midpoint > 0:
                    up += count
                elif midpoint < 0:
                    down += count
                else:
                    flat += count

        if up + down + flat <= 0:
            return None

        return up, down, flat

    def set_market_breadth_display(self, text, state="off"):
        """统一更新市场广度圆灯和文字。"""

        lamp_colors = {
            "bullish": self.SIGNAL_GREEN,
            "neutral": self.SIGNAL_YELLOW,
            "bearish": self.SIGNAL_RED,
            "off": self.SIGNAL_OFF,
            "error": self.SIGNAL_OFF,
        }
        text_colors = {
            "bullish": self.SIGNAL_GREEN,
            "neutral": self.TEXT_SECONDARY,
            "bearish": self.SIGNAL_RED,
            "off": self.TEXT_MUTED,
            "error": self.ERROR_FG,
        }

        lamp_color = lamp_colors.get(state, self.SIGNAL_OFF)
        text_color = text_colors.get(state, self.TEXT_MUTED)

        self.market_breadth_canvas.itemconfig(
            self.market_breadth_circle,
            fill=lamp_color,
            outline=lamp_color,
        )
        self.market_breadth_label.config(
            text=text,
            fg=text_color,
        )

    def refresh_market_breadth(self, force=False):
        """盘中按 5 分钟获取一次全美股市场广度。"""

        now = eastern_now()

        if self.session_day != now.date():
            return

        if now.time() < MARKET_BREADTH_START:
            self.set_market_breadth_display(
                "广度：待09:35",
                state="off",
            )
            return

        if now.time() > MARKET_BREADTH_END:
            return

        now_naive = naive_eastern(now)
        last_request = self.market_breadth_last_request_at

        if (
            not force
            and last_request is not None
            and (now_naive - last_request).total_seconds()
            < MARKET_BREADTH_REFRESH_MS / 1000
        ):
            return

        self.market_breadth_last_request_at = now_naive
        api = getattr(self.ctx, "get_rise_fall_distribution", None)

        if api is None:
            self.set_market_breadth_display(
                "广度：需升级",
                state="error",
            )
            return

        try:
            ret, data = api(market=Market.US)
        except Exception as error:
            print(f"获取美股市场广度异常：{error}")
            self.set_market_breadth_display(
                "广度：异常",
                state="error",
            )
            return

        if ret != RET_OK:
            print(f"获取美股市场广度失败：{data}")
            self.set_market_breadth_display(
                "广度：失败",
                state="error",
            )
            return

        parsed = self.parse_market_breadth(data)

        if parsed is None:
            print(f"美股市场广度数据格式异常：{data}")
            self.set_market_breadth_display(
                "广度：数据异常",
                state="error",
            )
            return

        up, down, flat = parsed
        self.market_breadth_up = up
        self.market_breadth_down = down
        self.market_breadth_flat = flat

        directional = up + down
        up_share = up / directional if directional > 0 else 0.5
        ratio_text = "∞" if down == 0 else f"{up / down:.2f}"

        if up_share >= MARKET_BREADTH_STRONG_SHARE:
            status = "偏多"
            breadth_state = "bullish"
        elif up_share <= MARKET_BREADTH_WEAK_SHARE:
            status = "偏空"
            breadth_state = "bearish"
        else:
            status = "中性"
            breadth_state = "neutral"

        self.set_market_breadth_display(
            (
                f"广度 {up_share:.0%} · A/D {ratio_text} · {status}"
            ),
            state=breadth_state,
        )

        print(
            f"美股市场广度：上涨={up} 下跌={down} 平盘={flat} "
            f"上涨占比={up_share:.2%} A/D={ratio_text} 状态={status}"
        )

    def market_breadth_timer(self):
        if self.closed:
            return

        try:
            self.refresh_market_breadth(force=False)
        except Exception as error:
            print(f"市场广度定时器异常：{error}")
        finally:
            if not self.closed:
                self.root.after(
                    MARKET_BREADTH_TIMER_MS,
                    self.market_breadth_timer,
                )

    # ========================================================
    # 昨日收盘价加载
    # ========================================================

    def store_previous_data(
        self,
        code,
        close,
        high,
        previous_day=None,
        source="",
    ):
        """保存并刷新某只股票的昨日收盘价和昨日最高价。"""

        try:
            close = float(close)
            high = float(high)
        except (TypeError, ValueError):
            return False

        if (
            not pd.notna(close)
            or not pd.notna(high)
            or close <= 0
            or high <= 0
        ):
            return False

        self.previous_close[code] = close
        self.previous_high[code] = high

        if previous_day is not None:
            self.previous_close_day[code] = previous_day

        if code == BENCHMARK_CODE:
            self.refresh_all_vs_qqq()
        elif code in self.get_s_stocks():
            self.set_s_cell(code, "previous", f"{close:.2f}")
            self.update_code_highlight(code)
            self.update_vs_qqq(code)
            latest = self.latest_close.get(code)

            if latest is not None:
                self.check_breakout(code, latest)

        if source:
            print(
                f"{code} 昨日行情：close={close} high={high} 来源={source}"
            )

        return True

    def load_previous_closes(self, codes=None, force=False):
        """
        加载上一交易日的不复权常规盘收盘价和最高价。

        昨收用于界面参考，以及个股/QQQ 相对昨收涨幅对比；
        不参与 S 线或突破信号判断。
        """

        if codes is None:
            codes = self.get_all_stocks()
        else:
            codes = list(dict.fromkeys(list(codes) + [BENCHMARK_CODE]))

        s_stock_set = set(self.get_s_stocks())

        for code in codes:
            if not self.needs_market_data(code):
                continue

            if (
                not force
                and code in self.previous_close
                and code in self.previous_high
            ):
                continue

            close, high, previous_day = get_previous_trading_close(
                self.ctx,
                code,
                self.session_day,
            )

            if close is None or high is None:
                self.previous_close.pop(code, None)
                self.previous_high.pop(code, None)
                self.previous_close_day.pop(code, None)

                if code in s_stock_set:
                    self.set_s_cell(code, "previous", "-")
                    self.update_vs_qqq(code)
                elif code == BENCHMARK_CODE:
                    self.refresh_all_vs_qqq()

                print(f"{code} 昨日行情读取失败，保留为空，避免错误信号")
                continue

            self.store_previous_data(
                code=code,
                close=close,
                high=high,
                previous_day=previous_day,
                source=f"不复权历史日K/RTH，交易日={previous_day}",
            )

    # ========================================================
    # 盘前刷新与锁定
    # ========================================================

    def refresh_pm(self, trading_day, codes=None):
        if codes is None:
            codes = self.get_s_stocks()

        for code in codes:
            if code not in self.get_s_stocks():
                continue

            high, low = get_pm_range(
                self.ctx,
                code,
                trading_day,
            )

            if high is None or low is None:
                continue

            self.pm_high[code] = high
            self.pm_low[code] = low

            self.set_s_cell(code, "high", f"{high:.2f}")
            self.update_code_highlight(code)
    def load_and_lock_pm(self, trading_day, codes=None):
        if codes is None:
            codes = self.get_s_stocks()

        for code in codes:
            if code not in self.get_s_stocks():
                continue

            if code in self.locked_high and code in self.locked_low:
                continue

            high, low = get_pm_range(
                self.ctx,
                code,
                trading_day,
            )

            if high is None or low is None:
                print(f"{code} 盘前锁定失败，下次继续重试")
                continue

            self.pm_high[code] = high
            self.pm_low[code] = low
            self.locked_high[code] = high
            self.locked_low[code] = low

            self.set_s_cell(code, "high", f"{high:.2f}")
            self.update_code_highlight(code)
            latest = self.latest_close.get(code)

            if latest is not None:
                self.check_breakout(code, latest)

            print(f"{code} 09:25盘前数据已锁定：high={high} low={low}")


    # ========================================================
    # 实时 5 分钟 K 订阅
    # ========================================================

    def ensure_5m_subscription(self, codes):
        """确保股票已订阅盘中以及盘前盘后的实时 5 分钟 K。"""

        pending = [
            code for code in dict.fromkeys(codes)
            if self.needs_market_data(code) and code not in self.subscribed_5m
        ]

        if not pending:
            return True

        try:
            ret, message = self.ctx.subscribe(
                pending,
                [SubType.K_5M],
                subscribe_push=False,
                session=Session.ETH,
            )
        except TypeError as error:
            # 旧版 SDK 没有 session 参数时尝试普通订阅；
            # 若无法取得盘前 K，后面的历史 K 回退仍可继续工作。
            print(f"实时K订阅不支持 session 参数，使用兼容模式：{error}")
            try:
                ret, message = self.ctx.subscribe(
                    pending,
                    [SubType.K_5M],
                    subscribe_push=False,
                )
            except Exception as inner_error:
                print(f"实时5分钟K订阅异常：{inner_error}")
                return False
        except Exception as error:
            print(f"实时5分钟K订阅异常：{error}")
            return False

        if ret != RET_OK:
            print(f"实时5分钟K订阅失败：{message}")
            return False

        self.subscribed_5m.update(pending)
        print("实时5分钟K订阅成功：" + ", ".join(pending))
        return True

    def get_5m_fetch_num(self, expected_end, now=None):
        """
        根据当前时间动态决定 get_cur_kline 需要返回多少根 5M K。

        常规盘内最少取 20 根；16:00 后随着盘后 K 增多，自动扩大返回
        数量，确保 16:00 目标 K 仍包含在结果中。只改变单次返回行数，
        不增加 API 调用次数。富途该接口最多支持 1000 根。
        """

        if now is None:
            now = eastern_now()

        elapsed_seconds = max(
            0.0,
            (
                naive_eastern(now)
                - expected_end
            ).total_seconds(),
        )
        elapsed_bars = math.ceil(
            elapsed_seconds / (5 * 60)
        )

        # 目标 K 本身 + 盘后已形成 K + 12 根缓冲。
        return min(
            1000,
            max(20, elapsed_bars + 13),
        )

    def get_5m_row_by_end_time(self, code, work, end_time, purpose):
        """
        按富途 5 分钟 K 的结束时间精确取行。

        例如：
        - 09:30-09:35 对应 time_key=09:35；
        - 15:55-16:00 对应 time_key=16:00。

        找不到目标时不拿更旧的 K 顶替，由定时器稍后重试。
        """

        if work is None or work.empty:
            return None

        target = pd.Timestamp(end_time)
        matched = work[
            work["_datetime"] == target
        ]

        if matched.empty:
            latest_keys = [
                value.strftime("%H:%M:%S")
                for value in work["_datetime"].tail(8)
            ]
            earliest_key = (
                work.iloc[0]["_datetime"].strftime("%H:%M:%S")
            )
            print(
                f"{code} {purpose}目标K不在当前返回范围："
                f"目标time_key={end_time:%H:%M:%S}，"
                f"最早={earliest_key}，"
                f"最近={latest_keys}；稍后扩大范围重试"
            )
            return None

        return matched.iloc[-1]

    # ========================================================
    # 最新应完成的 5 分钟 K
    # ========================================================

    def get_expected_completed_end(self, now):
        """
        返回已经确认完成的最近一个 5 分钟边界。

        在边界后等待 KLINE_CONFIRM_DELAY_SECONDS 秒，避免 OpenD 尚未把
        上一根 K 的最终 close 写入时，就把边界瞬间的临时值锁死。

        例如确认延迟为 3 秒：
        - 09:34:59：最近完成边界仍为 09:30；
        - 09:35:00-09:35:02：仍等待 09:30-09:35 最终值；
        - 09:35:03：确认边界为 09:35。
        """

        now_naive = naive_eastern(now)
        confirmed_now = now_naive - timedelta(
            seconds=KLINE_CONFIRM_DELAY_SECONDS
        )
        first_end = datetime.combine(self.session_day, FIRST_5M_END)
        session_close = datetime.combine(self.session_day, CLOSE_TIME)

        if self.session_day < now.date():
            return session_close

        if confirmed_now < first_end:
            return None

        boundary = floor_to_5_minutes(confirmed_now)

        if boundary > session_close:
            boundary = session_close

        if boundary < first_end:
            return None

        return boundary

    # ========================================================
    # 加载最新完整 5 分钟 K
    # ========================================================

    def load_latest_completed_bars(self, force=False, codes=None):
        now = eastern_now()

        if (
            self.session_day == now.date()
            and now.time() < FIRST_5M_END
        ):
            return

        expected_end = self.get_expected_completed_end(now)

        if expected_end is None:
            return

        now_naive = naive_eastern(now)

        if codes is None:
            codes = self.get_all_stocks()

        due_codes = []

        for code in codes:
            if not self.needs_market_data(code):
                continue

            last_end = self.last_completed_end.get(code)

            if (
                not force
                and last_end is not None
                and last_end >= expected_end
            ):
                continue

            last_request = self.last_kline_request_at.get(code)

            if (
                not force
                and last_request is not None
                and (now_naive - last_request).total_seconds()
                < KLINE_RETRY_SECONDS
            ):
                continue

            due_codes.append(code)

        if not due_codes:
            return

        for code in due_codes:
            self.last_kline_request_at[code] = now_naive
            self.read_latest_completed_bar(
                code=code,
                expected_end=expected_end,
                force=force,
            )

    def read_latest_completed_bar(
        self,
        code,
        expected_end,
        force=False,
    ):
        """
        读取最新完整 5 分钟 K 的收盘价。

        按富途 5 分钟 K 的结束时间，用 expected_end 精确取得对应完整 K。
        盘后会动态扩大返回根数；目标行尚未返回时保持原显示并重试，
        绝不拿更旧的 K 线收盘价代替。
        """

        self.ensure_5m_subscription([code])

        fetch_num = self.get_5m_fetch_num(
            expected_end=expected_end,
        )

        try:
            ret, data = self.ctx.get_cur_kline(
                code=code,
                num=fetch_num,
                ktype=SubType.K_5M,
                autype=PRICE_AUTYPE,
            )
        except Exception as error:
            print(f"{code} 读取实时5分钟K异常：{error}")
            return

        if ret != RET_OK:
            print(f"{code} 实时5分钟K读取失败：{data}")
            return

        work = prepare_kline_data(data)
        required_columns = {"close", "time_key"}

        if work.empty or not required_columns.issubset(work.columns):
            missing = sorted(required_columns - set(work.columns))
            print(f"{code} 实时5分钟K缺少字段：{missing}")
            return

        work = work[work["_datetime"].dt.date == self.session_day].copy()
        work["close"] = pd.to_numeric(work["close"], errors="coerce")
        work = work.dropna(subset=["close"])
        work = work.sort_values("_datetime").reset_index(drop=True)

        if work.empty:
            print(f"{code} 当天没有实时5分钟K")
            return

        target_row = self.get_5m_row_by_end_time(
            code=code,
            work=work,
            end_time=expected_end,
            purpose="最新完整5M",
        )

        if target_row is None:
            return

        try:
            close = float(target_row["close"])
        except (TypeError, ValueError):
            return

        if not pd.notna(close) or close <= 0:
            return

        bar_end = expected_end
        last_end = self.last_completed_end.get(code)

        if (
            not force
            and last_end is not None
            and bar_end <= last_end
        ):
            return

        self.last_completed_end[code] = bar_end
        self.latest_close[code] = close

        if code == BENCHMARK_CODE:
            self.refresh_all_vs_qqq()
            if hasattr(self, "kline_status_label"):
                qqq_pct = self.get_change_vs_prev_close_pct(BENCHMARK_CODE)
                qqq_text = (
                    f"{qqq_pct:+.2f}%"
                    if qqq_pct is not None
                    else "-"
                )
                self.kline_status_label.config(
                    text=(
                        f"5M收盘：{bar_end.strftime('%H:%M')} "
                        f"· QQQ {qqq_text} "
                        f"· 更新 {eastern_now():%H:%M:%S}"
                    ),
                    fg=self.ACCENT_BLUE,
                )
        elif code in self.get_s_stocks():
            self.set_s_cell(code, "close", f"{close:.2f}")
            self.check_breakout(code, close)
            self.update_vs_qqq(code)

            if hasattr(self, "kline_status_label"):
                self.kline_status_label.config(
                    text=(
                        f"5M收盘：{bar_end.strftime('%H:%M')} "
                        f"· 更新 {eastern_now():%H:%M:%S}"
                    ),
                    fg=self.ACCENT_BLUE,
                )

        tail_rows = work.tail(5)
        tail_parts = []

        for _, item in tail_rows.iterrows():
            part = f"key={str(item['time_key'])[11:19]}"

            if pd.notna(item.get("close")):
                part += f",close={float(item['close']):.6f}"

            tail_parts.append(part)

        print(
            f"{code} 最新完整5M：结束/time_key={bar_end:%H:%M} "
            f"close={close:.6f} 返回根数={fetch_num} "
            f"来源=time_key精确匹配"
        )
        print(
            f"{code} API最近5根5M原始值："
            + " | ".join(tail_parts)
        )

    # ========================================================
    # 信号判断
    # ========================================================

    def get_s_value(self, code):
        """S 线固定等于盘前高点，不再与昨日收盘价比较。"""

        high = self.locked_high.get(code)

        if high is None:
            high = self.pm_high.get(code)

        return high


    def check_breakout(self, code, close):
        s_value = self.get_s_value(code)

        if s_value is None:
            self.set_breakout_signal(code, False)
            print(f"{code} 缺少盘前高点，无法计算 S")
            return

        # 用户要求“在 S 之上”，采用严格大于，不包含等于。
        passed = close > s_value
        self.set_breakout_signal(code, passed)

        print(
            f"{code} 盘前高突破判断：close={close} 盘前高={s_value} "
            f"结果={'突破' if passed else '未突破'}"
        )


    # ========================================================
    # 5M收盘价柔和描边呼吸信号
    # ========================================================

    @staticmethod
    def blend_hex_color(start_color, end_color, amount):
        """在两种十六进制颜色之间平滑插值。"""

        amount = max(0.0, min(float(amount), 1.0))

        def parse(color):
            color = color.lstrip("#")
            return tuple(
                int(color[index:index + 2], 16)
                for index in (0, 2, 4)
            )

        start_rgb = parse(start_color)
        end_rgb = parse(end_color)
        result = tuple(
            round(start + (end - start) * amount)
            for start, end in zip(start_rgb, end_rgb)
        )

        return "#{:02X}{:02X}{:02X}".format(*result)

    def get_close_signal_state(self, code):
        """突破信号生效时返回 green，否则返回 None。"""

        if self.breakout_state.get(code, False):
            return "green"

        return None

    def apply_close_signal_style(self, code, intensity=None):
        """
        应用柔和呼吸样式。

        背景始终保持高饱和度绿色，在深色与亮色之间平滑变化；
        数字始终使用白色粗体，确保一眼可见。
        """

        state = self.get_close_signal_state(code)

        if intensity is None:
            # 信号刚触发时直接显示在中等亮度，避免等待动画下一帧。
            intensity = 0.55

        for row in self.iter_s_rows(code):
            label = row.get("close")

            if label is None:
                continue

            if state == "green":
                label.config(
                    bg=self.blend_hex_color(
                        self.CLOSE_GREEN_BG_LOW,
                        self.CLOSE_GREEN_BG_HIGH,
                        intensity,
                    ),
                    fg=self.blend_hex_color(
                        self.CLOSE_GREEN_FG_LOW,
                        self.CLOSE_GREEN_FG_HIGH,
                        intensity,
                    ),
                    highlightbackground=self.blend_hex_color(
                        self.CLOSE_GREEN_BORDER_LOW,
                        self.CLOSE_GREEN_BORDER_HIGH,
                        intensity,
                    ),
                    font=("Consolas", 10, "bold"),
                )

            else:
                label.config(
                    bg=self.NORMAL_BG,
                    fg=self.TEXT_PRIMARY,
                    highlightbackground=self.BORDER_BG,
                    font=("Consolas", 10, "normal"),
                )

    def animate_close_signals(self):
        """
        单一 Tkinter 定时器驱动全部有效信号。

        动画只修改 UI，不读取行情、不访问 OpenD，也不会增加任何
        富途 API 调用次数。
        """

        self.signal_breath_job = None

        if self.closed:
            return

        step_seconds = self.SIGNAL_BREATH_INTERVAL_MS / 1000.0
        phase_step = (
            2.0
            * math.pi
            * step_seconds
            / self.SIGNAL_BREATH_PERIOD_SECONDS
        )
        self.signal_breath_phase = (
            self.signal_breath_phase + phase_step
        ) % (2.0 * math.pi)

        # 余弦缓动：在两端自然减速，不会出现突然明暗跳变。
        wave = (
            1.0 - math.cos(self.signal_breath_phase)
        ) / 2.0

        # 在高饱和度深色和亮色之间完整呼吸。
        intensity = 0.05 + wave * 0.95

        for code in self.get_s_stocks():
            if self.get_close_signal_state(code) is not None:
                self.apply_close_signal_style(
                    code,
                    intensity=intensity,
                )

        self.signal_breath_job = self.root.after(
            self.SIGNAL_BREATH_INTERVAL_MS,
            self.animate_close_signals,
        )

    def set_breakout_signal(self, code, on):
        self.breakout_state[code] = bool(on)
        self.apply_close_signal_style(code)
        self.sync_breakout_page()

    # ========================================================
    # 关闭
    # ========================================================

    def on_close(self):
        if self.closed:
            return

        if self.signal_breath_job is not None:
            try:
                self.root.after_cancel(self.signal_breath_job)
            except tk.TclError:
                pass
            self.signal_breath_job = None

        if self.geometry_save_job is not None:
            try:
                self.root.after_cancel(self.geometry_save_job)
            except tk.TclError:
                pass
            self.geometry_save_job = None

        if self.auto_sync_job is not None:
            try:
                self.root.after_cancel(self.auto_sync_job)
            except tk.TclError:
                pass
            self.auto_sync_job = None

        self.save_pane_layout()
        self.save_window_geometry()
        self.closed = True

        try:
            self.ctx.close()
            print("富途连接已关闭")

        except Exception as error:
            print(f"关闭富途连接异常：{error}")

        self.root.destroy()


# ============================================================
# 启动
# ============================================================

if __name__ == "__main__":
    root = tk.Tk()
    app = App(root)
    root.mainloop()