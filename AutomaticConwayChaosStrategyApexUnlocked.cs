#region Using declarations
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Windows;
using System.Windows.Input;
using System.Windows.Media;
using System.Xml.Serialization;
using NinjaTrader.Cbi;
using NinjaTrader.Gui;
using NinjaTrader.Gui.Chart;
using NinjaTrader.Gui.SuperDom;
using NinjaTrader.Gui.Tools;
using NinjaTrader.Data;
using NinjaTrader.NinjaScript;
using NinjaTrader.Core.FloatingPoint;
using NinjaTrader.NinjaScript.Indicators;
using NinjaTrader.NinjaScript.DrawingTools;
using System.Speech.Synthesis;
#endregion

//This namespace holds Strategies in this folder and is required. Do not change it. 
namespace NinjaTrader.NinjaScript.Strategies
{
	[Gui.CategoryOrder("Parameters ", 1)]
	[Gui.CategoryOrder("Times ", 2)]
	[Gui.CategoryOrder("Chop Block ", 3)]
	[Gui.CategoryOrder("Buttons ", 4)]
	public class AutomaticConwayChaosStrategyApexUnlocked : Strategy
	{
		#region Variables

		private Dictionary<string,Order> Orders = new Dictionary<string,Order>();
		private object orderLock = new object();

		private const string strLong = "Long";
		private const string strShort = "Short";
		private const string strLong2 = "Long 2";
		private const string strShort2 = "Short 2";
		private const string strLongStop = "Long Stop";
		private const string strShortStop = "Short Stop";
		private const string strLongStop2 = "Long Stop 2";
		private const string strShortStop2 = "Short Stop 2";
		private const string strLongTarget1 = "Long Target";
		private const string strShortTarget1 = "Short Target";
		private const string strLongTarget2 = "Long Target 2";
		private const string strShortTarget2 = "Short Target 2";
		private const string strLongExit = "Long Exit";
		private const string strShortExit = "Short Exit";

		private LinReg slow, lr1, lr2;
		private EMA fast, sl1, sl2;

		private SUM ticksPerSecond;

		private int longHW = 0, shortHW = 0, trade1Dir;
		private Order trade1Order;
		private DateTime entryTime, exitTime;

		private System.Windows.Media.Brush stopBEBrush, statsFontBrush, statsBackgroundBrush, counterFontBrush, chopBlockDisabledBrush, chopBlockEnabledBrush, chopBlockFontBrush, emaFilterDisabledBrush, emaFilterEnabledBrush, emaFilterFontBrush, longBrush, shortBrush, longShortBrush, longFontBrush, shortFontBrush, longShortFontBrush, closeBrush, pauseBrush, targetBEBrush, chopBlockBrush, chopBlockOutlineBrush, barHeightBrush, longOnlyBrush, shortOnlyBrush, lsOnlyBackBrush;
		private System.Windows.Controls.Button btnRequireEMA, btnCounter, btnClose, btnLong, btnShort, btnLongShort, btnChopFilter, btnBreakEven, btnChopBlock, btnEMAFilter, btnStopBE;
		private bool paused = false;

		private Swing swing;
		private double chopBlockHigh = double.MinValue, chopBlockLow = double.MinValue;
		private double swingHigh = 0, swingLow = 0, entryPrice = 0;
		private Range range;
		private LinReg lrTrend, lrTrend2;
		private EMA slTrend, slTrend2;

		private Rectangle chopBlock;
		private int chopBlockOpacity = 20;

		private int longSignalBar = 0, shortSignalBar = 0;
		private int barsOutsideChopBlock = 0, trade2XBar;

		private double sodEquity = 0, barHigh, barLow;

		// ===== Trigger Lines (Trade #1) =====
		private double triggerLongPrice = 0.0;
		private double triggerShortPrice = 0.0;
		private bool triggerLinesActive = false;
		private bool triggerLongTouched = false;
		private bool triggerShortTouched = false;
		private DateTime triggerLinesCreatedTime = Core.Globals.MinDate;
		private string triggerLongTag = string.Empty;
		private string triggerShortTag = string.Empty;

		// ===== Stats Panel (from Chaos) =====
		private double dailyPnL = 0;
		private double lastTradeResult = 0;
		private string lastTradeDirection = "";
		private DateTime lastTradeTime = DateTime.MinValue;
		// Cache to avoid rebuilding stats text every tick
		private int statsCachedTradesCount = -1;
		private string statsCachedText = string.Empty;

		private SpeechSynthesizer _speaker;

		#endregion

		public AutomaticConwayChaosStrategyApexUnlocked()
		{
			//VendorLicense("EminiBuySellZones","ConwayControlledRiskEntryTradingSystem","http://conwaymarketdnadaytrading.com","jconway712@aol.com");
		}

		// ===== Helper: Is today in the holiday blackout window? =====
		private bool IsHolidayBlackout()
		{
			if (!UseHolidayFilter)
				return false;

			DateTime today = Time[0].Date;
			int month = today.Month;
			int day   = today.Day;

			// --- Thanksgiving week block ---
			if (BlockThanksgivingWeek)
			{
				// Thanksgiving is the 4th Thursday of November.
				// We block the entire Mon-Fri week that contains it.
				if (month == 11)
				{
					// Find the 4th Thursday of November this year
					DateTime nov1       = new DateTime(today.Year, 11, 1);
					int      thuOffset  = ((int)DayOfWeek.Thursday - (int)nov1.DayOfWeek + 7) % 7;
					DateTime firstThur  = nov1.AddDays(thuOffset);
					DateTime thanksgiv  = firstThur.AddDays(21); // 4th Thursday
					DateTime weekMon    = thanksgiv.AddDays(-(int)thanksgiv.DayOfWeek + 1);
					DateTime weekFri    = weekMon.AddDays(4);
					if (today >= weekMon && today <= weekFri)
						return true;
				}
			}

			// --- Holiday / rollover block (default Dec 15 - Jan 2) ---
			if (BlockHolidayRollover)
			{
				// Same year: start month/day through Dec 31
				if (month == HolidayBlockStartMonth && day >= HolidayBlockStartDay)
					return true;
				// Spill into next year: Jan 1 through end month/day
				if (month == HolidayBlockEndMonth && day <= HolidayBlockEndDay)
					return true;
				// Handle case where start and end are same month
				if (HolidayBlockStartMonth == HolidayBlockEndMonth
					&& month == HolidayBlockStartMonth
					&& day >= HolidayBlockStartDay && day <= HolidayBlockEndDay)
					return true;
			}

			return false;
		}

		// ===== Helper: Is current volume sufficient? =====
		private bool IsVolumeOK()
		{
			if (!UseVolumeFilter)
				return true;

			if (ticksPerSecond == null)
				return true;

			return ticksPerSecond[0] >= MinTicksPerSecond;
		}

		private bool IsWorking(string key)
		{
			if (!Orders.ContainsKey(key)) return false;
			Order o = Orders[key];
			return o != null && (o.OrderState == OrderState.Working || o.OrderState == OrderState.Accepted || o.OrderState == OrderState.PartFilled);
		}

		private void SendOrder(OrderAction action, OrderType type, int qty, double limitPrice, double stopPrice, string name)
		{
			Order o = SubmitOrderUnmanaged(0, action, type, qty, limitPrice, stopPrice, string.Empty, name);
			if (o != null)
				Orders[name] = o;
		}

		private void UpdatePanel()
		{
			// Panel update stub — extend as needed
		}

		protected override void OnStateChange()
		{
			if (State == State.SetDefaults)
			{
				Description							= @"Enter the description for your new custom Strategy here.";
				Name							= "AutomaticConwayChaosStrategyApexUnlocked";
				Calculate						= Calculate.OnBarClose;
				EntriesPerDirection				= 1;
				EntryHandling					= EntryHandling.AllEntries;
				IsExitOnSessionCloseStrategy		= true;
				ExitOnSessionCloseSeconds			= 30;
				IsFillLimitOnTouch				= false;
				MaximumBarsLookBack				= MaximumBarsLookBack.TwoHundredFiftySix;
				OrderFillResolution				= OrderFillResolution.Standard;
				Slippage						= 0;
				StartBehavior					= StartBehavior.WaitUntilFlat;
				TimeInForce						= TimeInForce.Gtc;
				TraceOrders						= false;
				RealtimeErrorHandling				= RealtimeErrorHandling.IgnoreAllErrors;
				StopTargetHandling				= StopTargetHandling.PerEntryExecution;
				BarsRequiredToTrade				= 20;
				IsUnmanaged						= true;
				IsInstantiatedOnEachOptimizationIteration	= true;

				StopTicks = 30;
				Target1Contracts = 1;
				Target1Ticks = 60;
				StopGoesBreakEven = false;
				ProfitTarget1 = 20;
				StopGoesBreakEvenPlusMinusTicks1 = 2;
				ProfitTarget2 = 30;
				StopGoesBreakEvenPlusMinusTicks2 = 20;

				ProfitTarget3 = 40;
				StopGoesBreakEvenPlusMinusTicks3 = 30;

				CloseBrush = Brushes.Black;
				PauseBrush = Brushes.Lime;
				TargetBEBrush = Brushes.Lime;
				StopBEBrush = Brushes.Lime;

				PriceBarTime = new TimeSpan(9, 29, 50);
				AboveBelowTicks = 1;
				PlotTriggerLines = true;
				TriggerLineStroke = new Stroke(Brushes.Goldenrod, DashStyleHelper.Solid, 2);

				Trade2Reversal = false;
				Trade2Stop = 50;
				Trade2Contracts = 1;
				Trade2Target = 60;
				ProfitTargetTrade2 = true;
				ProfitTarget1Trade2 = 60;
				ProfitTarget1StopTicksTrade2 = 40;
				ProfitTarget2Trade2 = 0;
				ProfitTarget2StopTicksTrade2 = 0;
				ProfitTarget3Trade2 = 0;
				ProfitTarget3StopTicksTrade2 = 0;

				MarketOrderReversal = true;
				StopOrderReversal = false;
				StopOrderReversalEntry_ticks = 12;
				CancelStopOrderAfter_Bars = 1;
				CancelTrade2 = false;
				CancelTrade2Minutes = 15;

				AudioAlert = true;

				StopLineStroke = new Stroke(Brushes.Red);

				// ===== Stats Panel (from Chaos) =====
				StatsFontSize = 14;
				StatsFontBrush = Brushes.White;
				StatsBackgroundBrush = Brushes.Black;

				// ===== Seasonal Filters =====
				UseHolidayFilter         = true;
				BlockThanksgivingWeek    = true;
				BlockHolidayRollover     = true;
				HolidayBlockStartMonth   = 12;
				HolidayBlockStartDay     = 15;
				HolidayBlockEndMonth     = 1;
				HolidayBlockEndDay       = 2;

				// ===== Volume Filter =====
				UseVolumeFilter    = true;
				MinTicksPerSecond  = 50;
			}
			else if (State == State.Configure)
			{
				AddDataSeries(BarsPeriodType.Second, 1);
			}
			else if (State == State.DataLoaded)
			{
				ticksPerSecond = SUM(Volumes[1], 30);

				_speaker = new SpeechSynthesizer();
				_speaker.SelectVoiceByHints(VoiceGender.Male, VoiceAge.Adult);

				swing = Swing(1);

				range = Range(BarsArray[BarsArray.Length - 1]);
			}
			else if (State == State.Transition)
			{
				List<string> keys = Orders.Keys.ToList();
				foreach (string o in keys)
					if (IsWorking(o))
						GetRealtimeOrder(Orders[o]);
			}
			else if (State == State.Historical)
				AddButtonToToolbar();
			else if (State == State.Terminated)
				RemoveButtonFromToolbar();
		}

		protected override void OnBarUpdate()
		{
			try
			{
				for (int x = 0; x < BarsArray.Length; x++)
					if (CurrentBars[x] < 1)
						return;

				if (BarsInProgress != 0)
				{
					if (barHigh == 0 || Close[0] > barHigh)
						barHigh = Close[0];
					if (barLow == 0 || Close[0] < barLow)
						barLow = Close[0];

					if (IsWorking(strLong2) && CurrentBars[0] > trade2XBar + CancelStopOrderAfter_Bars)
						if (Orders.ContainsKey(strLong2) && Orders[strLong2] != null) CancelOrder(Orders[strLong2]);
					if (IsWorking(strShort2) && CurrentBars[0] > trade2XBar + CancelStopOrderAfter_Bars)
						if (Orders.ContainsKey(strShort2) && Orders[strShort2] != null) CancelOrder(Orders[strShort2]);

					bool pastTime = Time[0].TimeOfDay.CompareTo(PriceBarTime) >= 0;
					bool firstBar = Time[1].TimeOfDay.CompareTo(PriceBarTime) < 0;

					// Create Trigger Lines at the same prices where the old OCO stop orders used to be placed
					if (pastTime && firstBar)
					{
						// ===== SEASONAL FILTER CHECK =====
						if (IsHolidayBlackout())
						{
							Draw.TextFixed(this, "FilterMsg", "TRADING BLOCKED: Holiday / Rollover Period", TextPosition.TopRight, Brushes.Orange, new SimpleFont("Arial", 12), Brushes.Black, Brushes.Black, 10);
							return;
						}

						// ===== VOLUME FILTER CHECK =====
						if (!IsVolumeOK())
						{
							Draw.TextFixed(this, "FilterMsg", "TRADING BLOCKED: Volume Too Low (" + (ticksPerSecond != null ? ticksPerSecond[0].ToString("F0") : "?") + " ticks/sec, min=" + MinTicksPerSecond + ")", TextPosition.TopRight, Brushes.Yellow, new SimpleFont("Arial", 12), Brushes.Black, Brushes.Black, 10);
							return;
						}

						// Clear any filter message if we are trading today
						Draw.TextFixed(this, "FilterMsg", "", TextPosition.TopRight, Brushes.Transparent, new SimpleFont("Arial", 12), Brushes.Transparent, Brushes.Transparent, 10);

						triggerLongPrice  = barHigh + AboveBelowTicks * TickSize;
						triggerShortPrice = barLow  - AboveBelowTicks * TickSize;

						triggerLinesActive = true;
						triggerLongTouched = false;
						triggerShortTouched = false;
						triggerLinesCreatedTime = Time[0];

						// remove prior day's trigger lines (if any)
						if (!string.IsNullOrEmpty(triggerLongTag))
							RemoveDrawObject(triggerLongTag);
						if (!string.IsNullOrEmpty(triggerShortTag))
							RemoveDrawObject(triggerShortTag);

						triggerLongTag  = "TriggerLineLong_"  + Time[0].ToString("yyyyMMdd_HHmmss");
						triggerShortTag = "TriggerLineShort_" + Time[0].ToString("yyyyMMdd_HHmmss");

						if (PlotTriggerLines)
						{
							Draw.Line(this, triggerLongTag,  IsAutoScale, 0, triggerLongPrice,  -1, triggerLongPrice,  TriggerLineStroke.Brush, TriggerLineStroke.DashStyleHelper, (int)TriggerLineStroke.Width);
							Draw.Line(this, triggerShortTag, IsAutoScale, 0, triggerShortPrice, -1, triggerShortPrice, TriggerLineStroke.Brush, TriggerLineStroke.DashStyleHelper, (int)TriggerLineStroke.Width);
						}
					}

					// Trigger logic (Apex-friendly / directional):
					// Enter on the FIRST touch of the trigger level (no 2x confirmation).
					// IMPORTANT: We still do NOT place resting entry orders on both sides (no straddle).
					// If both sides are breached on the same bar (possible with Calculate.OnBarClose),
					// pick a single direction to remain directional.
					if (triggerLinesActive && Position.MarketPosition == MarketPosition.Flat && !IsWorking(strLong) && !IsWorking(strShort))
					{
						bool longHit  = High[0] >= triggerLongPrice;
						bool shortHit = Low[0]  <= triggerShortPrice;

						if (longHit && !shortHit)
						{
							SendOrder(OrderAction.Buy, OrderType.Market, Target1Contracts, 0, 0, strLong);
							triggerLinesActive = false;
						}
						else if (shortHit && !longHit)
						{
							SendOrder(OrderAction.SellShort, OrderType.Market, Target1Contracts, 0, 0, strShort);
							triggerLinesActive = false;
						}
						else if (longHit && shortHit)
						{
							// Same bar hit both levels: choose ONE side based on bar direction.
							if (Close[0] >= Open[0])
								SendOrder(OrderAction.Buy, OrderType.Market, Target1Contracts, 0, 0, strLong);
							else
								SendOrder(OrderAction.SellShort, OrderType.Market, Target1Contracts, 0, 0, strShort);

							triggerLinesActive = false;
						}
					}

					if (trade1Dir != 0)
					{
						if (Position.MarketPosition == MarketPosition.Long)
						{
							int profitTicks = (int)Position.GetUnrealizedProfitLoss(PerformanceUnit.Ticks, High[0]);
							if (profitTicks > longHW)
								longHW = profitTicks;

							double stop = 0;
							if (StopGoesBreakEven)
							{
								if (longHW >= ProfitTarget3 && ProfitTarget3 > 0)
									stop = Position.AveragePrice + StopGoesBreakEvenPlusMinusTicks3 * TickSize;
								else if (longHW >= ProfitTarget2 && ProfitTarget2 > 0)
									stop = Position.AveragePrice + StopGoesBreakEvenPlusMinusTicks2 * TickSize;
								else if (longHW >= ProfitTarget1 && ProfitTarget1 > 0)
									stop = Position.AveragePrice + StopGoesBreakEvenPlusMinusTicks1 * TickSize;
							}

							Draw.TextFixed(this, "text", stop.ToString(), TextPosition.BottomRight);
							if (stop != 0)
								SendOrder(OrderAction.Sell, OrderType.StopMarket, Position.Quantity, 0, stop, strLongStop);
						}
						else if (Position.MarketPosition == MarketPosition.Short)
						{
							int profitTicks = (int)Position.GetUnrealizedProfitLoss(PerformanceUnit.Ticks, Low[0]);
							if (profitTicks > shortHW)
								shortHW = profitTicks;

							double stop = double.MaxValue;
							if (StopGoesBreakEven)
							{
								if (shortHW >= ProfitTarget3 && ProfitTarget3 > 0)
									stop = Position.AveragePrice - StopGoesBreakEvenPlusMinusTicks3 * TickSize;
								else if (shortHW >= ProfitTarget2 && ProfitTarget2 > 0)
									stop = Position.AveragePrice - StopGoesBreakEvenPlusMinusTicks2 * TickSize;
								else if (shortHW >= ProfitTarget1 && ProfitTarget1 > 0)
									stop = Position.AveragePrice - StopGoesBreakEvenPlusMinusTicks1 * TickSize;
							}

							if (stop != double.MaxValue)
								SendOrder(OrderAction.BuyToCover, OrderType.StopMarket, Position.Quantity, 0, stop, strShortStop);
						}
					}
					else
					{
						if (Position.MarketPosition == MarketPosition.Long)
						{
							if (High[0] > swingHigh)
								swingHigh = High[0];

							int profitTicks = (int)Position.GetUnrealizedProfitLoss(PerformanceUnit.Ticks, High[0]);
							if (profitTicks > longHW)
								longHW = profitTicks;

							if (trade1Dir != 0)
							{
								double stop = 0;
								if (StopGoesBreakEven)
								{
									if (longHW >= ProfitTarget2 && ProfitTarget2 > 0)
										stop = Position.AveragePrice + StopGoesBreakEvenPlusMinusTicks1 * TickSize;
									else if (longHW >= ProfitTarget1 && ProfitTarget1 > 0)
										stop = Position.AveragePrice + StopGoesBreakEvenPlusMinusTicks2 * TickSize;
								}

								Draw.TextFixed(this, "text", stop.ToString(), TextPosition.BottomRight);
								if (stop != 0)
									SendOrder(OrderAction.Sell, OrderType.StopMarket, Position.Quantity, 0, stop, strLongStop);
							}
							else if (ProfitTargetTrade2)
							{
								double stop = 0;
								if (longHW >= ProfitTarget3Trade2 && ProfitTarget3Trade2 > 0)
									stop = Position.AveragePrice + ProfitTarget3StopTicksTrade2 * TickSize;
								else if (longHW >= ProfitTarget2Trade2 && ProfitTarget2Trade2 > 0)
									stop = Position.AveragePrice + ProfitTarget2StopTicksTrade2 * TickSize;
								else if (longHW >= ProfitTarget1Trade2 && ProfitTarget1Trade2 > 0)
									stop = Position.AveragePrice + ProfitTarget1StopTicksTrade2 * TickSize;

								Draw.TextFixed(this, "text", stop.ToString(), TextPosition.BottomRight);
								if (stop != 0)
									SendOrder(OrderAction.Sell, OrderType.StopMarket, Position.Quantity, 0, stop, strLongStop);
						}
						}
						else if (Position.MarketPosition == MarketPosition.Short)
						{
							if (Low[0] < swingLow)
								swingLow = Low[0];

							int profitTicks = (int)Position.GetUnrealizedProfitLoss(PerformanceUnit.Ticks, Low[0]);
							if (profitTicks > shortHW)
								shortHW = profitTicks;

							if (trade1Dir != 0)
							{
								double stop = double.MaxValue;
								if (StopGoesBreakEven)
								{
									if (shortHW >= ProfitTarget2 && ProfitTarget2 > 0)
										stop = Position.AveragePrice - StopGoesBreakEvenPlusMinusTicks1 * TickSize;
									else if (shortHW >= ProfitTarget1 && ProfitTarget1 > 0)
										stop = Position.AveragePrice - StopGoesBreakEvenPlusMinusTicks2 * TickSize;
								}

								if (stop != double.MaxValue)
									SendOrder(OrderAction.BuyToCover, OrderType.StopMarket, Position.Quantity, 0, stop, strShortStop);
						}
						}
					}

					return;
				}

				barHigh = barLow = 0;
				bool rangeOK = true;
				bool tslLong = true, tslShort = true;
				bool emaLong = true, emaShort = true;

				bool timeOK = true;

				UpdatePanel();
			}
			catch (Exception ex)
			{
				Log(ex.ToString(), LogLevel.Error);
				return;
			}
		}

		protected override void OnOrderUpdate(Cbi.Order o, double limitPrice, double stopPrice, int quantity, int filled, double averageFillPrice, Cbi.OrderState orderState, DateTime time, Cbi.ErrorCode error, string comment)
		{
			if (Orders.ContainsKey(o.Name))
				Orders[o.Name] = o;
		}

		protected override void OnExecutionUpdate(Execution e, string executionId, double price, int quantity, MarketPosition marketPosition, string orderId, DateTime time)
		{
			if (e.Name == strLong)
			{
				swingHigh = swing.SwingHigh[0];
				swingLow = swing.SwingLow[0];
				entryPrice = e.Order.AverageFillPrice;

				longHW = 0;

				double stop = entryPrice - StopTicks * TickSize;
				double target1 = entryPrice + Target1Ticks * TickSize;

				int qty1 = Math.Min(Target1Contracts, e.Order.Filled);
				int qty2 = e.Order.Filled - qty1;

				if (qty1 > 0 && Target1Ticks > 0)
					SendOrder(OrderAction.Sell, OrderType.Limit, qty1, target1, 0, strLongTarget1);
				if (StopTicks > 0)
					SendOrder(OrderAction.Sell, OrderType.StopMarket, e.Order.Filled, 0, stop, strLongStop);

				trade1Dir = 1;
				trade1Order = e.Order;
				entryTime = Time[0];
			}
			else if (e.Name == strShort)
			{
				swingHigh = swing.SwingHigh[0];
				swingLow = swing.SwingLow[0];
				entryPrice = e.Order.AverageFillPrice;

				shortHW = 0;

				double stop = entryPrice + StopTicks * TickSize;
				double target1 = entryPrice - Target1Ticks * TickSize;

				int qty1 = Math.Min(Target1Contracts, e.Order.Filled);
				int qty2 = e.Order.Filled - qty1;

				if (qty1 > 0 && Target1Ticks > 0)
					SendOrder(OrderAction.BuyToCover, OrderType.Limit, qty1, target1, 0, strShortTarget1);
				if (StopTicks > 0)
					SendOrder(OrderAction.BuyToCover, OrderType.StopMarket, e.Order.Filled, 0, stop, strShortStop);

				trade1Dir = -1;
				trade1Order = e.Order;
				entryTime = Time[0];
			}
			else if (e.Name == strLong2)
			{
				if (AudioAlert)
					Say("Go long");

				longHW = 0;
				entryPrice = e.Order.AverageFillPrice;

				double stop = entryPrice - Trade2Stop * TickSize;
				double target1 = entryPrice + Trade2Target * TickSize;

				if (Trade2Target > 0)
					SendOrder(OrderAction.Sell, OrderType.Limit, e.Order.Filled, target1, 0, strLongTarget2);
				if (Trade2Stop > 0)
					SendOrder(OrderAction.Sell, OrderType.StopMarket, e.Order.Filled, 0, stop, strLongStop2);

				trade1Dir = 0;
			}
			else if (e.Name == strShort2)
			{
				if (AudioAlert)
					Say("Go short");

				shortHW = 0;
				entryPrice = e.Order.AverageFillPrice;

				double stop = entryPrice + Trade2Stop * TickSize;
				double target1 = entryPrice - Trade2Target * TickSize;

				if (Trade2Target > 0)
					SendOrder(OrderAction.BuyToCover, OrderType.Limit, e.Order.Filled, target1, 0, strShortTarget2);
				if (Trade2Stop > 0)
					SendOrder(OrderAction.BuyToCover, OrderType.StopMarket, e.Order.Filled, 0, stop, strShortStop2);

				trade1Dir = 0;
			}
			else if (e.Order.OrderAction == OrderAction.Sell)
			{
				double exitPrice = e.Order.AverageFillPrice;
				if (exitPrice > entryPrice)
					Say("Exit long with win");
				else if (exitPrice < entryPrice)
					Say("Exit long with loss");
				else
					Say("Exit long with breakeven");

				if (e.Name == strLongStop || e.Name == strLongStop2 || e.Name == strLongExit)
				{
					if (IsWorking(strLongTarget1))
						if (Orders.ContainsKey(strLongTarget1) && Orders[strLongTarget1] != null) CancelOrder(Orders[strLongTarget1]);
					if (IsWorking(strLongTarget2))
						if (Orders.ContainsKey(strLongTarget2) && Orders[strLongTarget2] != null) CancelOrder(Orders[strLongTarget2]);
					if (IsWorking(strLongStop2))
						if (Orders.ContainsKey(strLongStop2) && Orders[strLongStop2] != null) CancelOrder(Orders[strLongStop2]);

					if (e.Name == strLongStop)
					{
						if (IsWorking(strLongExit))
							if (Orders.ContainsKey(strLongExit) && Orders[strLongExit] != null) CancelOrder(Orders[strLongExit]);
					}
					else
					{
						if (IsWorking(strLongStop))
							if (Orders.ContainsKey(strLongStop) && Orders[strLongStop] != null) CancelOrder(Orders[strLongStop]);
					}
				}
				else if (e.Name == strLongTarget1 || e.Name == strLongTarget2)
				{
					if (Position.MarketPosition == MarketPosition.Flat)
					{
						if (IsWorking(strLongStop))
							if (Orders.ContainsKey(strLongStop) && Orders[strLongStop] != null) CancelOrder(Orders[strLongStop]);
						if (IsWorking(strLongStop2))
							if (Orders.ContainsKey(strLongStop2) && Orders[strLongStop2] != null) CancelOrder(Orders[strLongStop2]);
						if (IsWorking(strLongExit))
							if (Orders.ContainsKey(strLongExit) && Orders[strLongExit] != null) CancelOrder(Orders[strLongExit]);
					}
					else
					{
						if (IsWorking(strLongStop))
						{
							Order o = Orders[strLongStop];
							SendOrder(o.OrderAction, o.OrderType, Position.Quantity, o.LimitPrice, o.StopPrice, o.Name);
						}

						if (IsWorking(strLongExit))
						{
							Order o = Orders[strLongExit];
							SendOrder(o.OrderAction, o.OrderType, Position.Quantity, o.LimitPrice, o.StopPrice, o.Name);
						}
					}
				}

				if (Trade2Reversal && e.Name == strLongStop && exitPrice < entryPrice)
				{
					if (!CancelTrade2 || Time[0].Subtract(entryTime).TotalMinutes < CancelTrade2Minutes)
					{
						if (MarketOrderReversal)
							SendOrder(OrderAction.SellShort, OrderType.Market, Trade2Contracts, 0, 0, strShort2);
						else
						{
							trade2XBar = CurrentBars[0];
							var stopPrice = exitPrice - StopOrderReversalEntry_ticks * TickSize;
							if (StopLine)
								Draw.Line(this, trade2XBar.ToString(), IsAutoScale, 0, stopPrice, -1, stopPrice, StopLineStroke.Brush, StopLineStroke.DashStyleHelper, (int)StopLineStroke.Width);
							SendOrder(OrderAction.SellShort, OrderType.StopMarket, Trade2Contracts, 0, stopPrice, strShort2);
						}
					}
				}
			}
			else if (e.Order.OrderAction == OrderAction.BuyToCover)
			{
				double exitPrice = e.Order.AverageFillPrice;
				if (exitPrice < entryPrice)
					Say("Exit short with win");
				else if (exitPrice > entryPrice)
					Say("Exit short with loss");
				else
					Say("Exit short with breakeven");

				if (e.Name == strShortStop || e.Name == strShortStop2 || e.Name == strShortExit)
				{
					if (IsWorking(strShortTarget1))
						if (Orders.ContainsKey(strShortTarget1) && Orders[strShortTarget1] != null) CancelOrder(Orders[strShortTarget1]);
					if (IsWorking(strShortTarget2))
						if (Orders.ContainsKey(strShortTarget2) && Orders[strShortTarget2] != null) CancelOrder(Orders[strShortTarget2]);
					if (IsWorking(strShortStop2))
						if (Orders.ContainsKey(strShortStop2) && Orders[strShortStop2] != null) CancelOrder(Orders[strShortStop2]);

					if (e.Name == strShortStop)
					{
						if (IsWorking(strShortExit))
							if (Orders.ContainsKey(strShortExit) && Orders[strShortExit] != null) CancelOrder(Orders[strShortExit]);
					}
					else
					{
						if (IsWorking(strShortStop))
							if (Orders.ContainsKey(strShortStop) && Orders[strShortStop] != null) CancelOrder(Orders[strShortStop]);
					}
				}
				else if (e.Name == strShortTarget1 || e.Name == strShortTarget2)
				{
					if (Position.MarketPosition == MarketPosition.Flat)
					{
						if (IsWorking(strShortStop))
							if (Orders.ContainsKey(strShortStop) && Orders[strShortStop] != null) CancelOrder(Orders[strShortStop]);
						if (IsWorking(strShortStop2))
							if (Orders.ContainsKey(strShortStop2) && Orders[strShortStop2] != null) CancelOrder(Orders[strShortStop2]);
						if (IsWorking(strShortExit))
							if (Orders.ContainsKey(strShortExit) && Orders[strShortExit] != null) CancelOrder(Orders[strShortExit]);
					}
					else
					{
						if (IsWorking(strShortStop))
						{
							Order o = Orders[strShortStop];
							SendOrder(o.OrderAction, o.OrderType, Position.Quantity, o.LimitPrice, o.StopPrice, o.Name);
						}

						if (IsWorking(strShortExit))
						{
							Order o = Orders[strShortExit];
							SendOrder(o.OrderAction, o.OrderType, Position.Quantity, o.LimitPrice, o.StopPrice, o.Name);
						}
					}
				}

				UpdatePanel();
			}
		}

		private Chart chartWindow;
		private bool buttonAdded = false;
		private void AddButtonToToolbar()
		{
			if (ChartControl == null || buttonAdded)
				return;

			ChartControl.Dispatcher.InvokeAsync((Action)(() =>
			{
				chartWindow = Window.GetWindow(ChartControl.Parent) as Chart;
				if (chartWindow == null)
					return;

				Style s = new Style();
				s.TargetType = typeof(System.Windows.Controls.Button);
				s.Setters.Add(new Setter(System.Windows.Controls.Button.BackgroundProperty, Brushes.Cyan));
				s.Setters.Add(new Setter(System.Windows.Controls.Button.ForegroundProperty, closeBrush));
				s.Setters.Add(new Setter(System.Windows.Controls.Button.ContentProperty, "StrategyClose"));

				btnClose = new System.Windows.Controls.Button();
				btnClose.Style = s;
				btnClose.Click += btnClose_Click;

				s = new Style();
				s.TargetType = typeof(System.Windows.Controls.Button);
				s.Setters.Add(new Setter(System.Windows.Controls.Button.BackgroundProperty, targetBEBrush));
				s.Setters.Add(new Setter(System.Windows.Controls.Button.ForegroundProperty, closeBrush));
				s.Setters.Add(new Setter(System.Windows.Controls.Button.ContentProperty, "TargetBE"));

				btnBreakEven = new System.Windows.Controls.Button();
				btnBreakEven.Style = s;
				btnBreakEven.Click += btnBreakEven_Click;

				s = new Style();
				s.TargetType = typeof(System.Windows.Controls.Button);
				s.Setters.Add(new Setter(System.Windows.Controls.Button.BackgroundProperty, stopBEBrush));
				s.Setters.Add(new Setter(System.Windows.Controls.Button.ForegroundProperty, closeBrush));
				s.Setters.Add(new Setter(System.Windows.Controls.Button.ContentProperty, "StopBE"));

				btnStopBE = new System.Windows.Controls.Button();
				btnStopBE.Style = s;
				btnStopBE.Click += btnStopBE_Click;

				chartWindow.MainMenu.Add(btnClose);
				chartWindow.MainMenu.Add(btnBreakEven);
				chartWindow.MainMenu.Add(btnStopBE);

			}));

			buttonAdded = true;
		}

		private void RemoveButtonFromToolbar()
		{
			if (chartWindow != null)
			{
				ChartControl.Dispatcher.InvokeAsync((Action)(() =>
				{
					if (btnClose != null)
						chartWindow.MainMenu.Remove(btnClose);
					if (btnLong != null)
						chartWindow.MainMenu.Remove(btnLong);
					if (btnShort != null)
						chartWindow.MainMenu.Remove(btnShort);
					if (btnLongShort != null)
						chartWindow.MainMenu.Remove(btnLongShort);
					if (btnChopFilter != null)
						chartWindow.MainMenu.Remove(btnChopFilter);
					if (btnBreakEven != null)
						chartWindow.MainMenu.Remove(btnBreakEven);
					if (btnChopBlock != null)
						chartWindow.MainMenu.Remove(btnChopBlock);
					if (btnEMAFilter != null)
						chartWindow.MainMenu.Remove(btnEMAFilter);
					if (btnStopBE != null)
						chartWindow.MainMenu.Remove(btnStopBE);
					if (btnRequireEMA != null)
						chartWindow.MainMenu.Remove(btnRequireEMA);
				}));
			}
		}

		private void btnStopBE_Click(object sender, RoutedEventArgs e)
		{
			if (Position.MarketPosition == MarketPosition.Long)
			{
				SendOrder(OrderAction.Sell, OrderType.StopMarket, Position.Quantity, 0, Position.AveragePrice, strLongStop);
			}

			if (Position.MarketPosition == MarketPosition.Short)
			{
				SendOrder(OrderAction.BuyToCover, OrderType.StopMarket, Position.Quantity, 0, Position.AveragePrice, strShortStop);
			}
		}

		private void btnClose_Click(object sender, RoutedEventArgs e)
		{
			if (Position.MarketPosition == MarketPosition.Long)
				SendOrder(OrderAction.Sell, OrderType.Market, Position.Quantity, 0, 0, strLongExit);
			if (Position.MarketPosition == MarketPosition.Short)
				SendOrder(OrderAction.BuyToCover, OrderType.Market, Position.Quantity, 0, 0, strShortExit);
		}

		private void btnBreakEven_Click(object sender, RoutedEventArgs e)
		{
			if (Position.MarketPosition == MarketPosition.Long)
			{
				SendOrder(OrderAction.Sell, OrderType.Limit, Position.Quantity, Position.AveragePrice, 0, strLongTarget1);
			}

			if (Position.MarketPosition == MarketPosition.Short)
			{
				SendOrder(OrderAction.BuyToCover, OrderType.Limit, Position.Quantity, Position.AveragePrice, 0, strShortTarget1);
			}
		}

		private void Say(string speechstring)
		{
			if (!AudioAlert || State == State.Historical || _speaker == null)
				return;

			_speaker.SpeakAsync(speechstring);
		}

		#region Properties

		[NinjaScriptProperty]
		[Display(Name = "StopTicks", Order = 6, GroupName = "One-Bar Breakout Trade #1")]
		public int StopTicks
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Trade #1 Contracts", Order = 7, GroupName = "One-Bar Breakout Trade #1")]
		public int Target1Contracts
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Target1Ticks", Order = 8, GroupName = "One-Bar Breakout Trade #1")]
		public int Target1Ticks
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Profit Target", Order = 12, GroupName = "One-Bar Breakout Trade #1")]
		public bool StopGoesBreakEven
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "ProfitTarget1", Order = 13, GroupName = "One-Bar Breakout Trade #1")]
		public int ProfitTarget1
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Profit Target1 Stop_ticks", Order = 14, GroupName = "One-Bar Breakout Trade #1")]
		public int StopGoesBreakEvenPlusMinusTicks1
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "ProfitTarget2", Order = 15, GroupName = "One-Bar Breakout Trade #1")]
		public int ProfitTarget2
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Profit Target2 Stop_ticks", Order = 16, GroupName = "One-Bar Breakout Trade #1")]
		public int StopGoesBreakEvenPlusMinusTicks2
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "ProfitTarget3", Order = 17, GroupName = "One-Bar Breakout Trade #1")]
		public int ProfitTarget3
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Profit Target3 Stop_ticks", Order = 18, GroupName = "One-Bar Breakout Trade #1")]
		public int StopGoesBreakEvenPlusMinusTicks3
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "AboveBelow_Ticks", Order = 3, GroupName = "One-Bar Breakout Trade #1")]
		public int AboveBelowTicks
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Plot Trigger Lines", Order = 3, GroupName = "One-Bar Breakout Trade #1")]
		public bool PlotTriggerLines
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "TriggerLineStroke", Order = 3, GroupName = "One-Bar Breakout Trade #1")]
		public Stroke TriggerLineStroke
		{ get; set; }

		private TimeSpan priceBarTime = new TimeSpan(9, 29, 50);

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "PriceBarTime", Order = 4, GroupName = "One-Bar Breakout Trade #1")]
		public TimeSpan PriceBarTime
		{
			get { return priceBarTime; }
			set { priceBarTime = value; }
		}

		[Browsable(false)]
		public string PriceBarTimeS
		{
			get { return priceBarTime.ToString(); }
			set { priceBarTime = TimeSpan.Parse(value); }
		}

		// ===== Trade #2 =====

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Trade #2 Reversal", Order = 0, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public bool Trade2Reversal
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Trade #2 Stop", Order = 8, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public int Trade2Stop
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Trade #2 Contracts", Order = 9, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public int Trade2Contracts
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Trade #2 Target", Order = 10, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public int Trade2Target
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Profit Target Trade #2", Order = 11, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public bool ProfitTargetTrade2
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Profit Target1 Trade #2", Order = 12, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public int ProfitTarget1Trade2
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Profit Target1 Stop Ticks Trade #2", Order = 13, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public int ProfitTarget1StopTicksTrade2
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Profit Target2 Trade #2", Order = 14, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public int ProfitTarget2Trade2
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Profit Target2 Stop Ticks Trade #2", Order = 15, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public int ProfitTarget2StopTicksTrade2
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Profit Target3 Trade #2", Order = 16, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public int ProfitTarget3Trade2
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Profit Target3 Stop Ticks Trade #2", Order = 17, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public int ProfitTarget3StopTicksTrade2
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Market Order Reversal", Order = 18, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public bool MarketOrderReversal
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Stop Order Reversal", Order = 19, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public bool StopOrderReversal
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "StopOrderReversalEntry_ticks", Order = 20, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public int StopOrderReversalEntry_ticks
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "CancelStopOrderAfter_Bars", Order = 21, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public int CancelStopOrderAfter_Bars
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Cancel_Trade#2 if Trade#1 is protracted", Order = 22, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public bool CancelTrade2
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Cancel_Trade#2_Minutes", Order = 23, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public int CancelTrade2Minutes
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "AudioAlert", Order = 24, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public bool AudioAlert
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "StopLine", Order = 25, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public bool StopLine
		{ get; set; }

		[NinjaScriptProperty]
		[Display(ResourceType = typeof(Custom.Resource), Name = "StopLineStroke", Order = 26, GroupName = "One-Bar Breakout Trade #2 - Reversal")]
		public Stroke StopLineStroke
		{ get; set; }

		#region Stats Panel

		[NinjaScriptProperty]
		[Display(Name = "Stats Font Size", Order = 1, GroupName = "Stats Panel")]
		public int StatsFontSize
		{ get; set; }

		[XmlIgnore]
		[Display(Name = "Stats Font Color", Order = 2, GroupName = "Stats Panel")]
		public Brush StatsFontBrush
		{
			get { return statsFontBrush; }
			set
			{
				statsFontBrush = value;
				if (statsFontBrush != null)
				{
					if (statsFontBrush.IsFrozen)
						statsFontBrush = statsFontBrush.Clone();
					statsFontBrush.Freeze();
				}
			}
		}

		[Browsable(false)]
		public string StatsFontBrushS
		{
			get { return Serialize.BrushToString(StatsFontBrush); }
			set { StatsFontBrush = Serialize.StringToBrush(value); }
		}

		[XmlIgnore]
		[Display(Name = "Stats Background Color", Order = 3, GroupName = "Stats Panel")]
		public Brush StatsBackgroundBrush
		{
			get { return statsBackgroundBrush; }
			set
			{
				statsBackgroundBrush = value;
				if (statsBackgroundBrush != null)
				{
					if (statsBackgroundBrush.IsFrozen)
						statsBackgroundBrush = statsBackgroundBrush.Clone();
					statsBackgroundBrush.Freeze();
				}
			}
		}

		[Browsable(false)]
		public string StatsBackgroundBrushS
		{
			get { return Serialize.BrushToString(StatsBackgroundBrush); }
			set { StatsBackgroundBrush = Serialize.StringToBrush(value); }
		}

		#endregion

		#region Seasonal Filters

		[NinjaScriptProperty]
		[Display(Name = "Use Holiday Filter", Order = 1, GroupName = "Seasonal Filters")]
		public bool UseHolidayFilter
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Block Thanksgiving Week", Order = 2, GroupName = "Seasonal Filters")]
		public bool BlockThanksgivingWeek
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Block Holiday/Rollover Period", Order = 3, GroupName = "Seasonal Filters")]
		public bool BlockHolidayRollover
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Holiday Block Start Month", Order = 4, GroupName = "Seasonal Filters")]
		public int HolidayBlockStartMonth
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Holiday Block Start Day", Order = 5, GroupName = "Seasonal Filters")]
		public int HolidayBlockStartDay
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Holiday Block End Month", Order = 6, GroupName = "Seasonal Filters")]
		public int HolidayBlockEndMonth
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Holiday Block End Day", Order = 7, GroupName = "Seasonal Filters")]
		public int HolidayBlockEndDay
		{ get; set; }

		#endregion

		#region Volume Filter

		[NinjaScriptProperty]
		[Display(Name = "Use Volume Filter", Order = 1, GroupName = "Volume Filter")]
		public bool UseVolumeFilter
		{ get; set; }

		[NinjaScriptProperty]
		[Display(Name = "Min Ticks Per Second", Order = 2, GroupName = "Volume Filter")]
		public int MinTicksPerSecond
		{ get; set; }

		#endregion

		#region Buttons

		[XmlIgnore]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Close Font Color", Order = 4, GroupName = "Buttons")]
		public System.Windows.Media.Brush CloseBrush
		{
			get { return closeBrush; }
			set
			{
				closeBrush = value;
				if (closeBrush != null)
				{
					if (closeBrush.IsFrozen)
						closeBrush = closeBrush.Clone();
					closeBrush.Freeze();
				}
			}
		}

		[Browsable(false)]
		public string CloseBrushS
		{
			get { return Serialize.BrushToString(CloseBrush); }
			set { CloseBrush = Serialize.StringToBrush(value); }
		}

		[XmlIgnore]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Pause Button Color", Order = 5, GroupName = "Buttons")]
		public System.Windows.Media.Brush PauseBrush
		{
			get { return pauseBrush; }
			set
			{
				pauseBrush = value;
				if (pauseBrush != null)
				{
					if (pauseBrush.IsFrozen)
						pauseBrush = pauseBrush.Clone();
					pauseBrush.Freeze();
				}
			}
		}

		[Browsable(false)]
		public string PauseBrushS
		{
			get { return Serialize.BrushToString(PauseBrush); }
			set { PauseBrush = Serialize.StringToBrush(value); }
		}

		[XmlIgnore]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Target BE Button Color", Order = 6, GroupName = "Buttons")]
		public System.Windows.Media.Brush TargetBEBrush
		{
			get { return targetBEBrush; }
			set
			{
				targetBEBrush = value;
				if (targetBEBrush != null)
				{
					if (targetBEBrush.IsFrozen)
						targetBEBrush = targetBEBrush.Clone();
					targetBEBrush.Freeze();
				}
			}
		}

		[Browsable(false)]
		public string ChopBrushS
		{
			get { return Serialize.BrushToString(TargetBEBrush); }
			set { TargetBEBrush = Serialize.StringToBrush(value); }
		}

		[XmlIgnore]
		[Display(ResourceType = typeof(Custom.Resource), Name = "Stop BE Button Color", Order = 7, GroupName = "Buttons")]
		public System.Windows.Media.Brush StopBEBrush
		{
			get { return stopBEBrush; }
			set
			{
				stopBEBrush = value;
				if (stopBEBrush != null)
				{
					if (stopBEBrush.IsFrozen)
						stopBEBrush = stopBEBrush.Clone();
					stopBEBrush.Freeze();
				}
			}
		}

		[Browsable(false)]
		public string StopBEBrushS
		{
			get { return Serialize.BrushToString(StopBEBrush); }
			set { StopBEBrush = Serialize.StringToBrush(value); }
		}

		#endregion

		#endregion
	} 
}