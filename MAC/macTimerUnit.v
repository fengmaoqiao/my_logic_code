//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author: $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: $
// $Date: $
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : Top level of macTimerUnit module
//                    
// Simulation Notes : 
//    For simulation, two defines are available
//
//    RW_SIMU_ON    : which creates string signals to display the FSM states on  
//                 the waveform viewer.
//
//    RW_ASSERT_ON  : which enables System Verilog Assertions.
//
// Synthesis Notes  :
// Application Note :                                                       
// Simulator        :                                                       
//     For simulation with RW_ASSERT_ON, the simulator must support System 
//     Verilog Assertions
//
// Parameters       :                                                       
// Terms & concepts :                                                       
// Bugs             :                                                       
// Open issues and future enhancements :                                    
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"
module macTimerUnit( 
            ///////////////////////////////////////////////
            //$port_g Clock and reset
            ///////////////////////////////////////////////
            input wire         macCoreClk,              // MAC Core Clock
            input wire         macLPClk,                // MAC LP Clock

            input wire         macLPClkSwitch,          // MAC LP Clock frequency = 32KHz when active
                        
            input wire         macCoreClkHardRst_n,     // Hard Reset of the MAC Core Clock domain active low

            input wire         macCoreClkSoftRst_n,     // Soft Reset of the MAC Core Clock domain
            
            ///////////////////////////////////////////////
            //$port_g TX Controller
            ///////////////////////////////////////////////
            input wire         sentCFEND,               // Indicates that the transmitted frame is a CF-END
            input wire         txDone_p,                // Indicates the completion of the transmission

            output wire        sec20ChannelIdleFlag,      // Secondary 20MHz channel idle for PIFS flag
            output wire        sec40ChannelIdleFlag,      // Secondary 40MHz channel idle for PIFS flag
            output wire        sec80ChannelIdleFlag,      // Secondary 80MHz channel idle for PIFS flag

            output reg [7:0]   dtimCnt,                 // DTIM counter
            output reg [7:0]   cfpCnt,                  // CFP counter

            ///////////////////////////////////////////////
            //$port_g RX Controller
            ///////////////////////////////////////////////
            input wire         dtimUpdate_p,            // Update DTIM element
            input wire [7:0]   rxDtimCnt,               // DTIM counter received
            
            input wire         cfpUpdate_p,             // Update CFP element
            input wire [7:0]   rxCfpCnt,                // CFP counter received
            
                                                        // has been received
            input wire         tsfUpdate_p,             // Update TSF
            input wire         tsfOffsetUpdate_p,       // Update TSF Offset
            input wire [63:0]  timeStamp,               // Timestamp
            
            input wire         cfEndRcved_p,            // CF-End received
            input wire         rxTrig_p,                // RX Trigger
            input wire         olbcUpdate_p,            // Update OLBC counter
            input wire         lastRxWrong,             // Last received packet wrong
            
            input wire         quietElement1InValid,    // Indicates that the Quiet Element 1 are valid
            input wire         quietElement2InValid,    // Indicates that the Quiet Element 2 are valid

            ///////////////////////////////////////////////
            //$port_g MAC-PHY interface
            ///////////////////////////////////////////////
            input wire         macPhyIfRxEndForTiming_p,// Rx end for timing from MAC-PHY if. resynchronized
            input wire         macPhyIfRxCca,           // CCA Primary trigger resynchronized
            input wire         macPhyIfRxCcaSec20,      // CCA Secondary 20 MHz trigger resynchronized
            input wire         macPhyIfRxCcaSec40,      // CCA Secondary 40 MHz trigger resynchronized
            input wire         macPhyIfRxCcaSec80,      // CCA Secondary 80 MHz trigger resynchronized
            input wire         mpIfTxEn,                // Indicates that TX is in progress

            ///////////////////////////////////////////////
            //$port_g NAV
            ///////////////////////////////////////////////
            input wire         channelToIdle_p,         // Channel move to idle pulse
            input wire         channelBusy,             // Channel busy indicator

            output reg         cfpOn,                   // CFP is in progress
            output wire        rxDot11a,                // Last received packet is 802.11a
            
            output reg         navCfpMaxDurUpdate_p,    // Update NAV with CFP Max duration
            
            output reg         loadQuietDuration_p,     // load quiet duration
            output reg  [15:0] quietDuration,           // quiet duration value

            ///////////////////////////////////////////////
            //$port_g A-MPDU Deaggregator
            ///////////////////////////////////////////////
            input wire  [3:0]  rxLegRate,               // Legacy rate
            input wire  [2:0]  rxFormatMod,             // Format and modulation
            input wire         rxDataStart_p,           // Start of data flow

            ///////////////////////////////////////////////
            //$port_g MAC Controller
            ///////////////////////////////////////////////
            input wire [15:0]  frmDurWithoutMH,         // Indicates the duration if the Beacon or Probe Response from the end of the MAC header
            
            input wire         resetCommonCnt_p,        // Reset common count counter
            input wire         moveToActive_p,          // Core should now move to ACTIVE state
            input wire         moveToIdle_p,            // Core should now move to IDLE state

            input wire         respTO_p,                // ACK / CTS response timeout
            
            output reg  [15:0] impQICnt,                // Quiet interval counter in 32 us
            output wire [15:0] nextTBTTCnt,             // Next TBTT counter in 32 us

            output wire        tickDMAEarlyTBTT_p,      // Pulse prior of tickEarlyTBTT_p
            output wire        tickEarlyTBTT_p,         // Pulse prior of tickTBTT_p
            
            output reg [7:0]   sifsRemaining,           // Value of sift remaining in us before tickSift_p

            ///////////////////////////////////////////////
            //$port_g Control and Status Register
            ///////////////////////////////////////////////
            input wire         hwFSMReset,                   // HW FSM Reset
            
            input wire [3:0]   currentState,                 // Current state of the core
            
            input wire [15:0]  listenInterval,               // Listen interval
            input wire         wakeupDTIM,                   // Wakeup DTIM interval
            input wire [14:0]  atimWAutoWakeUpTO,            // ATIM Window / Auto Wake Up Time Out
            
            input wire         bssType,                      // BSS Type
            input wire         ap,                           // Access Point
            input wire [2:0]   abgnMode,                     // Indicate current operating mode
            input wire         cfpAware,                     // CFP Aware
            input wire         rxRIFSEn,                     // Enable RIFS in RX    

            input wire [15:0]  beaconInt,                    // Beacon interval
            input wire [6:0]   impTBTTPeriod,                // Impending TBTT Period
            input wire         impTBTTIn128Us,               // Impending TBTT Interrupt Period in 128us
            input wire [7:0]   noBcnTxTime,                  // No Beacon Transmit Time in 16us

            input wire [7:0]   dtimPeriod,                   // DTIM Period
            input wire [7:0]   cfpPeriod,                    // CFP period
            input wire         dtimUpdatedBySW,              // sw programming dtimCfpPeriod register

            input wire [31:0]  tsfTimerHigh,                 // TSF[63:32] register
            input wire [31:0]  tsfTimerLow,                  // TSF[31:0] register
            input wire         tsfUpdatedBySW,               // sw programming tsfTimerLow register

            input wire [15:0]  olbcTimer,                    // OLBC Timer
            input wire [7:0]   ofdmCount,                    // OFDM Count
            input wire [7:0]   dsssCount,                    // DSSS/CCK Count

            input wire [7:0]   macCoreClkFreq,               // MAC Core Clock Frequency
            input wire [9:0]   txRFDelayInMACClk,            // Transmit RF Delay in MAC Clocks
            input wire [9:0]   txChainDelayInMACClk,         // Transmit Chain Delay in MAC Clocks

            input wire [7:0]   slotTime,                     // Slot time in us
            input wire [15:0]  slotTimeInMACClk,             // Slot time in MAC Clocks

            input wire [9:0]   macProcDelayInMACClk,         // MAC Processing Delay in MAC Clocks
            input wire [9:0]   txDelayRFOnInMACClk,          // Transmit Delay with RF On in MAC Clocks
            input wire [9:0]   rxRFDelayInMACClk,            // Receive RF Delay in MAC Clocks
            input wire [3:0]   rxCCADelay,                   // CCA Delay in us

            input wire [9:0]   radioWakeUpTime,              // RF wakeup time in 32us resolution

            input wire [15:0]  sifsBInMACClk,                // SIFS Duration for 802.11b in MAC Clocks
            input wire [15:0]  sifsAInMACClk,                // SIFS Duration for 802.11a in MAC Clocks

            input wire [7:0]   sifsB,                        // SIFS Duration for 802.11b
            input wire [7:0]   sifsA,                        // SIFS Duration for 802.11a

            input wire [9:0]   txDMAProcDlyInMACClk,         // Transmit DMA Processing Delay in MAC Clocks
            input wire [9:0]   rifsInMACClk,                 // RIFS Duration in MAC Clocks
            input wire [9:0]   rifsTOInMACClk,               // RIFS Timeout Duration in MAC Clocks

            input wire [7:0]   txAbsoluteTimeout,            // Transmission Absolute Timeout
            input wire [7:0]   txPacketTimeout,              // Transmission Packet Timeout

            input wire [7:0]   rxAbsoluteTimeout,            // Reception Absolute Timeout
            input wire [7:0]   rxPacketTimeout,              // Reception Packet Timeout

            input wire [3:0]   aifsn0,                       // AIFSN for AC 0
            input wire [3:0]   aifsn1,                       // AIFSN for AC 1
            input wire [3:0]   aifsn2,                       // AIFSN for AC 2
            input wire [3:0]   aifsn3,                       // AIFSN for AC 3

            input wire [31:0]  ccaBusyDur,                   // CCA Busy Duration from CSReg
            input wire [31:0]  ccaBusyDurSec20,              // CCA Busy Duration on Secondary 20MHz from CSReg
            input wire [31:0]  ccaBusyDurSec40,              // CCA Busy Duration on Secondary 40MHz  from CSReg
            input wire [31:0]  ccaBusyDurSec80,              // CCA Busy Duration on Secondary 80MHz  from CSReg

            input wire [7:0]   quietCount1,                  // Quiet Count 1
            input wire [7:0]   quietPeriod1,                 // Quiet Period 1
            input wire [15:0]  quietDuration1,               // Quiet Duration 1
            input wire [15:0]  quietOffset1,                 // Quiet Offset 1

            input wire [7:0]   quietCount2,                  // Quiet Count 2
            input wire [7:0]   quietPeriod2,                 // Quiet Period 2
            input wire [15:0]  quietDuration2,               // Quiet Duration 2
            input wire [15:0]  quietOffset2,                 // Quiet Offset 2

            input wire  [31:0] absTimerValue0,               // Absolute timer 0 value
            input wire  [31:0] absTimerValue1,               // Absolute timer 1 value
            input wire  [31:0] absTimerValue2,               // Absolute timer 2 value
            input wire  [31:0] absTimerValue3,               // Absolute timer 3 value
            input wire  [31:0] absTimerValue4,               // Absolute timer 4 value
            input wire  [31:0] absTimerValue5,               // Absolute timer 5 value
            input wire  [31:0] absTimerValue6,               // Absolute timer 6 value
            input wire  [31:0] absTimerValue7,               // Absolute timer 7 value
            input wire  [31:0] absTimerValue8,               // Absolute timer 8 value
            input wire  [31:0] absTimerValue9,               // Absolute timer 9 value

            output reg  [31:0] monotonicCounter1,            // Monotonic counter 1 in clk cc
            output wire [31:0] monotonicCounterLow2,         // Monotonic counter 2 [31:0] in us
            output wire [15:0] monotonicCounterHigh2,        // Monotonic counter 2 [47:32] in us
          
            output reg  [31:0] ccaBusyDurIn,                 // CCA Busy Duration
            output wire        ccaBusyDurInValid,            // Indicates that the ccaBusyDur register has to be updated with ccaBusyDurIn

            output reg  [31:0] ccaBusyDurSec20In,            // CCA Busy Duration on Secondary 20MHz
            output wire        ccaBusyDurSec20InValid,       // Indicates that the ccaBusyDurSec20 register has to be updated with ccaBusyDurIn

            output reg  [31:0] ccaBusyDurSec40In,            // CCA Busy Duration on Secondary 40MHz
            output wire        ccaBusyDurSec40InValid,       // Indicates that the ccaBusyDurSec40 register has to be updated with ccaBusyDurIn

            output reg  [31:0] ccaBusyDurSec80In,            // CCA Busy Duration on Secondary 40MHz
            output wire        ccaBusyDurSec80InValid,       // Indicates that the ccaBusyDurSec40 register has to be updated with ccaBusyDurIn

            output wire        dtimUpdatedBySWIn,            // Clear Software update request
            output reg         dtimUpdatedBySWInValid,       // Indicates that the dtimUpdatedBySW register has to be updated with dtimUpdatedBySWIn
            
            output wire [63:0] tsfTimer,                     // TSF timer 64-bit
            output wire        tsfUpdatedBySWIn,             // Clear Software update request
            output wire        tsfUpdatedBySWInValid,        // Indicates that the tsfUpdatedBySW register has to be updated with tsfUpdatedBySWIn

            ///////////////////////////////////////////////
            //$port_g Interrupt Controller
            ///////////////////////////////////////////////
            output reg         olbcOFDM,                // OFDM OLBC
            output reg         olbcDSSS,                // DSSS OLBC
            output reg         impPriTBTT,              // Impending Primary TBTT
            output reg         impSecTBTT,              // Impending Secondary TBTT
            output reg         impPriDTIM,              // Impending Primary DTIM
            output reg         impSecDTIM,              // Impending Secondary DTIM
            output reg         timerTxTrigger,          // Tx trigger
            output reg         timerRxTrigger,          // Rx trigger
            output reg  [9:0]  absTimers,               // absTimers interruptions

            ///////////////////////////////////////////////
            //$port_g Backoff Engine
            ///////////////////////////////////////////////
            output wire        noBeaconTxPeriod,        // Indicates that scheduled TX beacon will be suppressed

            output wire        tickDMAEarlySlot_p,      // Pulse prior of tickEarlySlot_p
            output wire        tickEarlySlot_p,         // Pulse prior of tickSlot_p
            output wire        tickSlot_p,              // Pulse every slot

            output reg [7:0]   slotCnt,                 // Slot counter

            output wire        tickRIFS_p,              // Pulse when RIFS over
            output wire        tickSIFS_p,              // Pulse when SIFS over
            output wire        tickPIFS_p,              // Pulse when SIFS over
            output wire        rifsTO_p,                // Pulse when RIFS timeout occurs
            
            output reg [11:0]  aifsCnt0,                // AIFS0 counter in us
            output reg [11:0]  aifsCnt1,                // AIFS1 counter in us
            output reg [11:0]  aifsCnt2,                // AIFS2 counter in us
            output reg [11:0]  aifsCnt3,                // AIFS3 counter in us

            output wire        aifsFlag0,               // Flag when AIFS0 over
            output wire        aifsFlag1,               // Flag when AIFS1 over
            output wire        aifsFlag2,               // Flag when AIFS2 over
            output wire        aifsFlag3,               // Flag when AIFS3 over

            output wire        eifsFlag0,               // Flag when EIFS0 over
            output wire        eifsFlag1,               // Flag when EIFS1 over
            output wire        eifsFlag2,               // Flag when EIFS2 over
            output wire        eifsFlag3,               // Flag when EIFS3 over
            
            output wire        tickTBTT_p,              // Pulse every TBTTs

            output wire        tickSlot1us_p,           // Pulse every microseconds aligned on slotCnt

            ///////////////////////////////////////////////
            //$port_g Doze Controller
            ///////////////////////////////////////////////
            input wire         moveToDoze_p,            // Core should now move to DOZE state
            
            output wire        wakeupListenInterval_p,  // Wakeup core at listen interval
            output wire        wakeupDTIM_p,            // Wakeup core at DTIM count null
            output wire        atimWindowOver_p,        // ATIM window over

            ///////////////////////////////////////////////
            //$port_g General tick
            ///////////////////////////////////////////////
            output wire        tick1us_p,               // Pulse every microseconds
            output wire        tick1tu_p,               // Pulse every TUs

            ///////////////////////////////////////////////
            //$port_g Debug ports
            ///////////////////////////////////////////////
            output wire [15:0] debugPortMACTimerUnit,   // Debug port for validation
            output wire [15:0] debugPortMACTimerUnit2,  // Debug port for validation
            output wire [15:0] debugPortMACTimerUnit3   // Debug port for validation
            );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

// Core current state
localparam 
    IDLE_STATE  =  4'h0, // idle state
    DOZE_STATE  =  4'h2, // doze state
  ACTIVE_STATE  =  4'h3; // active state

localparam
    AIFS0_INIT  =  3'h7,
    AIFS1_INIT  =  3'h3,
    AIFS2_INIT  =  3'h2,
    AIFS3_INIT  =  3'h2;

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
// Microsecond counter for tick1us_p generation
reg [7:0]    microSecCnt;

// 32 Microseconds counter for tick32us_p generation
reg [4:0]    timeoutCnt;
wire         tick32us_p;

// Microsecond counter for tickSlot1us_p generation
reg [7:0]    microSecSlotCnt;

// Beacon interval counter in us
reg [25:0]   beaconIntCnt;

// TSF sync signals
wire [25:0]  modulo;
wire         updateBeaconIntCnt_p;
wire         adjustLPInc;

// Impending TBTT period in us
wire [14:0]  impTBTTPeriodConv;
wire [25:0]  impSecOffset;
// Flag indicating that the TBTT has been delayed due to an on-going transmission or reception
reg          tbttDelayed;

// Common counter used for Listen interval and ATIM window
reg [15:0]   commonCnt;

// Time unit counter for tick1tu_p generation
wire [9:0]   tuCnt;

// RIFS counter
reg [9:0]    rifsCnt;
// RIFS Timeout counter
reg [9:0]    rifsTOCnt;

// SIFS & Slot counter
wire         trigSIFS_p;
reg          sifsFlag;
reg  [15:0]  sifsSlotCnt;
wire [15:0]  sifsInMACClk;
wire         tickNullSlot_p;
wire         tickNullSIFS_p;
wire [15:0]  sifsDiffInMACClk;

// AIFS Counters
wire [11:0] txChainMacDMADelayCntMinus1;
wire [11:0] txChainMacDMADelayCntPlus1;

wire [11:0] sifsMinusTxChainMacDMA;
wire [11:0] sifsMinusTxChainMacDMAAndCCA;
wire [11:0] aifs0SlotDuration;
wire [11:0] aifs1SlotDuration;
wire [11:0] aifs2SlotDuration;
wire [11:0] aifs3SlotDuration;

// EIFS counters
reg [14:0]   eifsCnt0;
reg [14:0]   eifsCnt1;
reg [14:0]   eifsCnt2;
reg [14:0]   eifsCnt3;

// EIFS flag reset
reg          eifsFlag0_ff1;
reg          eifsFlag1_ff1;
reg          eifsFlag2_ff1;
reg          eifsFlag3_ff1;
wire         eifsFlag0Rst_p;
wire         eifsFlag1Rst_p;
wire         eifsFlag2Rst_p;
wire         eifsFlag3Rst_p;
reg          eifsMask;

// PIFS counter
reg [15:0]   sec20PIFSCnt;
reg [15:0]   sec40PIFSCnt;
reg [15:0]   sec80PIFSCnt;
reg [15:0]   pifsCnt;

// CCA
reg          macPhyIfRxCcaSec20_ff1;
reg          macPhyIfRxCcaSec40_ff1;
reg          macPhyIfRxCcaSec80_ff1;

// Absolute counters
reg [7:0]    txAbsoluteTimeoutCnt;
reg [7:0]    rxAbsoluteTimeoutCnt;

// Packet counters
reg [7:0]    txPacketTimeoutCnt;
reg [7:0]    rxPacketTimeoutCnt;

// OLBC timer
reg [15:0]   olbcTimerCnt;

// OLBC counters
reg [7:0]    olbcOFDMCnt;
reg [7:0]    olbcDSSSCnt;

// OLBC interrupt generation
reg          olbcOFDMCntDone;
reg          olbcOFDMCntDone_ff1;
reg          olbcDSSSCntDone;
reg          olbcDSSSCntDone_ff1;

// Delays addition in MAC clk
wire [9:0]   txChainMacDelayInMACClk;

// Delays addition in us
wire [4:0]   txChainMacDMADelayCnt;

// Microsecond counter for txChainMacDelayInMACClk conversion in us
reg          txChainMacDelayCntEn;
reg          txChainMacDelayCntDone;
reg [3:0]    txChainMacDelayCnt;

// Early wake-up delay
wire [25:0]  earlyWakeupDelay;

// Microsecond counter for txDMAProcDlyInMACClk conversion in us
reg          txDMADelayCntEn;
reg          txDMADelayCntDone;
reg [3:0]    txDMADelayCnt;

// Quiet interval counters
reg [25:0]   priQICnt;
reg [25:0]   secQICnt;
wire [25:0]  selectQICnt;
reg          quietElement1InValid_ff1;
reg          quietElement2InValid_ff1;

// Monotonic counter 2
reg [47:0]   monotonicCounter2;
reg          absTimerInterruptMask;
reg          macLPClkSwitchDly;
wire         absTimers0MSBMatch; // indicate that the MSB of monotonicCounterLow2 match with the MSB of absTimerValue0
wire         absTimers1MSBMatch; // indicate that the MSB of monotonicCounterLow2 match with the MSB of absTimerValue1
wire         absTimers2MSBMatch; // indicate that the MSB of monotonicCounterLow2 match with the MSB of absTimerValue2
wire         absTimers3MSBMatch; // indicate that the MSB of monotonicCounterLow2 match with the MSB of absTimerValue3
wire         absTimers4MSBMatch; // indicate that the MSB of monotonicCounterLow2 match with the MSB of absTimerValue4
wire         absTimers5MSBMatch; // indicate that the MSB of monotonicCounterLow2 match with the MSB of absTimerValue5
wire         absTimers6MSBMatch; // indicate that the MSB of monotonicCounterLow2 match with the MSB of absTimerValue6
wire         absTimers7MSBMatch; // indicate that the MSB of monotonicCounterLow2 match with the MSB of absTimerValue7
wire         absTimers8MSBMatch; // indicate that the MSB of monotonicCounterLow2 match with the MSB of absTimerValue8
wire         absTimers9MSBMatch; // indicate that the MSB of monotonicCounterLow2 match with the MSB of absTimerValue9

// SIFS re-calculation for short packet
reg          rxDot11a_ff1;
wire         sifsSlotCntUpdate_p;

// us calculation for sifs remaining
reg [7:0]    txDelayInUs;
reg [7:0]    rxRFDelayInUs;
reg [9:0]    delayTxRxCnt;
wire         txDelayInUsDone;
wire         rxRFDelayInUsDone;

// internal wire
wire         olbcOFDMInt;                // OFDM OLBC
wire         olbcDSSSInt;                // DSSS OLBC
wire         impPriTBTTInt;              // Impending Primary TBTT
wire         impSecTBTTInt;              // Impending Secondary TBTT
wire         impPriDTIMInt;              // Impending Primary DTIM
wire         impSecDTIMInt;              // Impending Secondary DTIM
wire         timerTxTriggerInt;          // Tx trigger
wire         timerRxTriggerInt;          // Rx trigger
wire [9:0]   absTimersInt;               // absTimers interruptions

wire [7:0]   sifs;                       // SIFS Duration for 802.11a

wire         macCoreIsIdle;              // Indicate that the MAC Core is in IDLE State
wire         macCoreIsInDoze;            // Indicate that the MAC Core is in DOZE State
wire         macCoreIsActive;            // Indicate that the MAC Core is in ACTIVE State

wire  [15:0] pifsInMACClk;               // PIFS duration in MACCoreClk

wire         earlyWakeup_p;              // Wakeup core from DOZE

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// Flags indicating the MAC Core State
assign macCoreIsIdle   = (currentState == IDLE_STATE) ? 1'b1 : 1'b0;
assign macCoreIsInDoze = (currentState == DOZE_STATE) ? 1'b1 : 1'b0;
assign macCoreIsActive = (currentState == ACTIVE_STATE) ? 1'b1 : 1'b0;

// Delays calculation for logic reduction
//////////////////////////////////////////////////////////////////////////////

// TX Chain MAC delay = txChainDelayInMACClk + macProcDelayInMACClk
assign txChainMacDelayInMACClk = (txChainDelayInMACClk + macProcDelayInMACClk);


// Delays conversion from MAC Clock definition into us
//////////////////////////////////////////////////////////////////////////////

// txChainMacDelayCnt counter for txChainMacDelayInMACClk conversion in us
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)             // Asynchronous Reset
  begin
    txChainMacDelayCntEn   <= 1'b0;
    txChainMacDelayCntDone <= 1'b0;
    txChainMacDelayCnt     <= 4'h5;
  end
  else if (!macCoreClkSoftRst_n || moveToActive_p) // Synchronous Reset
  begin
    txChainMacDelayCntEn   <= 1'b0;
    txChainMacDelayCntDone <= 1'b0;
    txChainMacDelayCnt     <= 4'h5;
  end
  else
  begin
    // Enable counter on tickEarlySlot_p
    if (tickEarlySlot_p && !txChainMacDelayCntDone)
      txChainMacDelayCntEn <= 1'b1;
    // Disable counter on tickNullSlot_p
    else if (tickNullSlot_p)
      txChainMacDelayCntEn <= 1'b0;
    
    // Delay done
    if (txChainMacDelayCntEn && tickNullSlot_p)
      txChainMacDelayCntDone <= 1'b1;
    
    // Clear counter on tickEarlySlot_p
    if (tickEarlySlot_p && !txChainMacDelayCntDone)
      txChainMacDelayCnt <= 4'h0;
    // Increment counter on tick1us_p
    else if (txChainMacDelayCntEn && tick1us_p && !txChainMacDelayCntDone)
      txChainMacDelayCnt <= txChainMacDelayCnt + 4'h1;
  end
end

// txDMADelayCnt counter for txDMAProcDlyInMACClk conversion in us
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)             // Asynchronous Reset
  begin
    txDMADelayCntEn   <= 1'b0;
    txDMADelayCntDone <= 1'b0;
    txDMADelayCnt     <= 4'h3;
  end
  else  if (!macCoreClkSoftRst_n || moveToActive_p) // Synchronous Reset
  begin
    txDMADelayCntEn   <= 1'b0;
    txDMADelayCntDone <= 1'b0;
    txDMADelayCnt     <= 4'h3;
  end
  else
  begin
    // Enable counter on tickDMAEarlySlot_p
    if (tickDMAEarlySlot_p && !txDMADelayCntDone)
      txDMADelayCntEn <= 1'b1;
    // Disable counter on tickEarlySlot_p
    else if (tickEarlySlot_p)
      txDMADelayCntEn <= 1'b0;
    
    // Delay done
    if (txDMADelayCntEn && tickEarlySlot_p)
      txDMADelayCntDone <= 1'b1;
    
    // Clear counter on tickEarlySlot_p
    if (tickDMAEarlySlot_p && !txDMADelayCntDone)
      txDMADelayCnt <= 4'h0;
    // Increment counter on tick1us_p
    else if (txDMADelayCntEn && tick1us_p && !txDMADelayCntDone)
      txDMADelayCnt <= txDMADelayCnt + 4'h1;
  end
end

// txChainMacDMADelayCnt counter for txDMAProcDlyInMACClk + txChainMacDelayInMACClk conversion in us
assign txChainMacDMADelayCnt = {1'b0, txDMADelayCnt} + {1'b0, txChainMacDelayCnt};


// Microsecond counter
//////////////////////////////////////////////////////////////////////////////

// microSecCnt counter for generating tick1us_p pulse
always @ (posedge macLPClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)   // Asynchronous Reset
    microSecCnt <= 8'd`MAC_FREQ - 8'h1;
  else if (!macCoreClkSoftRst_n || (microSecCnt == 8'h0))
    microSecCnt <= macCoreClkFreq - 8'h1;
  else if (!macLPClkSwitch)
    microSecCnt <= microSecCnt - 8'h1;
end

// pulse generated every microsecond
assign tick1us_p = !macLPClkSwitch && (microSecCnt == 8'h0);


// rxdot11a muxing
//////////////////////////////////////////////////////////////////////////////
assign rxDot11a = (abgnMode != 3'b0) ? 1'b1 : 1'b0;

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)   // Asynchronous Reset
    rxDot11a_ff1 <= 1'b0;
  else
    rxDot11a_ff1 <= rxDot11a;
end

assign sifsSlotCntUpdate_p = (rxDot11a && !rxDot11a_ff1) ||
                             (!rxDot11a && rxDot11a_ff1);


// Instanciation of tsfSync
//////////////////////////////////////////////////////////////////////////////
tsfSync U_tsfSync (
    // Clock and reset
		.macCoreClk             (macCoreClk),
		.macLPClk               (macLPClk),
		.macLPClkSwitch         (macLPClkSwitch),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
    // RX Controller
		.tsfUpdate_p            (tsfUpdate_p),
		.tsfOffsetUpdate_p      (tsfOffsetUpdate_p),
		.timeStamp              (timeStamp),
    // MAC-PHY Interface
		.macPhyIfRxEndForTiming_p (macPhyIfRxEndForTiming_p),
    // MAC Controller
		.moveToActive_p         (moveToActive_p),
		.frmDurWithoutMH        (frmDurWithoutMH),
    // Control and Status Register
		.bssType                (bssType),
		.ap                     (ap),
		.beaconInt              (beaconInt),
		.tsfTimerHigh           (tsfTimerHigh),
		.tsfTimerLow            (tsfTimerLow),
		.tsfUpdatedBySW         (tsfUpdatedBySW),
		.tsfTimer               (tsfTimer),
		.tsfUpdatedBySWIn       (tsfUpdatedBySWIn),
		.tsfUpdatedBySWInValid  (tsfUpdatedBySWInValid),
    // MAC Timer Unit
		.tick1us_p              (tick1us_p),
		.modulo                 (modulo),
		.updateBeaconIntCnt_p   (updateBeaconIntCnt_p),
		.adjustLPInc            (adjustLPInc)
		);


// Beacon Interval counter
//////////////////////////////////////////////////////////////////////////////
    
// beaconIntCnt counts the time between beacon Intervals. 
// Update of this count is done only if the modulo value is less
// than the beacon interval.
// It is maintained in microseconds.
always @ (posedge macLPClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    beaconIntCnt <= 26'h0;
  else if (!macCoreClkSoftRst_n)    // Synchronous Reset
    beaconIntCnt <= 26'h0;
  else if (updateBeaconIntCnt_p  && (modulo < ({beaconInt, 10'b0})))
    beaconIntCnt <= {beaconInt, 10'b0} - modulo;
  else if (macLPClkSwitch)
  begin
    if (beaconInt == 16'h0)
      beaconIntCnt <= 26'h0;
    else if (beaconIntCnt < 26'd32)
      beaconIntCnt <= {beaconInt, 10'b0} - 26'h1;
    else
      beaconIntCnt <= beaconIntCnt - 26'd32 + {25'b0, adjustLPInc};
  end
  else if (tick1us_p)
  begin
    if (beaconInt == 16'h0)
      beaconIntCnt <= 26'h0;
    else if (beaconIntCnt == 26'h0)
      beaconIntCnt <= {beaconInt, 10'b0} - 26'h1;
    else 
      beaconIntCnt <= beaconIntCnt - 26'h1;
  end
end

// Next TBTT counter in 32 us for MAC Controller
assign nextTBTTCnt = (beaconIntCnt[25:20] > 6'h1) ? 16'hffff : beaconIntCnt[20:5];

// Time unit counter
//////////////////////////////////////////////////////////////////////////////

// the tuCnt is the lower 10 bits of the beaconIntCnt 
assign tuCnt = beaconIntCnt[9:0];
    
// pulse generated every TU (1024 us) 
assign tick1tu_p = (tuCnt == {6'd0,txChainMacDelayCnt}) && tick1us_p;


// TBTT pulses
//////////////////////////////////////////////////////////////////////////////

// impPriTBTT is generated as an indication to software to program the primary beacon
// before the TBTT into the beacon FIFO when the core is not in IDLE
// Consider dtimCnt != 1 instead of 0 because the  impPriTBTT is generated before changing the dtimCnt value
assign impPriTBTTInt = (beaconIntCnt == {11'b0, impTBTTPeriodConv}) && 
                       tick1us_p && (dtimCnt != 8'h1); 

// impSecTBTT is generated as an indication to software to program the secondary beacon
// before the half TBTT into the beacon FIFO when the core is not in IDLE
assign impSecTBTTInt = (beaconIntCnt == impSecOffset) && 
                       tick1us_p && (dtimCnt != 8'h0);

// impPriDTIM is generated as an indication to software to program the primary DTIM
// before the TBTT into the beacon FIFO when the core is not in IDLE
// Consider dtimCnt != 1 instead of 0 because the  impPriTBTT is generated before changin the dtimCnt value
assign impPriDTIMInt = (beaconIntCnt == {11'b0, impTBTTPeriodConv}) && 
                       tick1us_p && (dtimCnt == 8'h1);

// impSecDTIM is generated as an indication to software to program the secondary DTIM
// before the half TBTT into the beacon FIFO when the core is not in IDLE
assign impSecDTIMInt = (beaconIntCnt == impSecOffset) && 
                       tick1us_p && (dtimCnt == 8'h0);

// pulse generated txChainMacDelayCnt + txDMADelayCnt before TBTT, to inform the 
// backoff that TBTT is about to occur and a beacon needs to be scheduled 
assign tickDMAEarlyTBTT_p = tbttDelayed ? tickDMAEarlySlot_p : 
                                          (beaconIntCnt == {21'd0,txChainMacDMADelayCnt}) && tick1us_p && !macCoreIsIdle && !(macPhyIfRxCca || mpIfTxEn);
                       
// pulse generated macProcDelay + txDelaySlot before TBTT, to inform the 
// core that TBTT is about to occur and a beacon needs to be scheduled 
assign tickEarlyTBTT_p = (macLPClkSwitch) ? (tickTBTT_p) :
                                            tbttDelayed ? tickEarlySlot_p : 
                                                          (beaconIntCnt == {22'd0,txChainMacDelayCnt}) && tick1us_p && !macCoreIsIdle;

// Generate the tbttDelayed indicating that the TBBT has been delayed due to a transmission (mpIfTxEn)
// or a reception (macPhyIfRxCca)
always @ (posedge macLPClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    tbttDelayed <= 1'b0;
  else if (!macCoreClkSoftRst_n || hwFSMReset)    // Synchronous Reset   
    tbttDelayed <= 1'b0;
  else if ((beaconIntCnt == {21'd0,txChainMacDMADelayCnt}) && tick1us_p && !macCoreIsIdle)
  begin
    if (macPhyIfRxCca || mpIfTxEn)
      tbttDelayed <= 1'b1;
    else
      tbttDelayed <= 1'b0;
  end
  else if (tbttDelayed && tickEarlyTBTT_p)
    tbttDelayed <= 1'b0;
end    
      


// pulse generated every TBTT
assign tickTBTT_p = (macLPClkSwitch) ? ((beaconIntCnt < 26'd32)) : 
                                       ((beaconIntCnt == 26'h0) && tick1us_p &&
                                        !macCoreIsIdle);

// impTBTTPeriod conversion in us from impTBTTIn128Us register
assign impTBTTPeriodConv = (impTBTTIn128Us) ? {1'b0,impTBTTPeriod, 7'h0} : {8'h0, impTBTTPeriod};

// impSecOffset = impTBTTPeriodConv + {beaconInt, 9'b0}
assign impSecOffset = {11'b0, impTBTTPeriodConv} + {1'b0, beaconInt, 9'b0};


// Listen Interval & ATIM counter
//////////////////////////////////////////////////////////////////////////////
    
// The commonCnt counter is reused for the listen Interval & ATIM Window.
// It counts the listen interval when in DOZE, and this is a STA in an BSS.
// It counts the ATIM window when the core is in ACTIVE and this is a STA in an IBSS.
always @ (posedge macLPClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    commonCnt <= 16'h0;
  else if (!macCoreClkSoftRst_n || hwFSMReset)    // Synchronous Reset   
    commonCnt <= 16'h0;
  // the counter is loaded with the listenInterval (from macCSreg) when the 
  // moveToDoze_p is asserted (for STA in a BSS)
  else if (moveToDoze_p && bssType)
    commonCnt <= listenInterval;
  // start the ATIM window counter at every TBTT if the core is part of an 
  // IBSS and when the state of the core is ACTIVE
  else if (tickTBTT_p && !bssType && !macCoreIsActive)
    commonCnt <= {1'b0, atimWAutoWakeUpTO};
  // reset the common counter when the core state changes
  else if (resetCommonCnt_p)
    commonCnt <= 16'h0;
  // if the count is zero, hold it at zero
  else if (commonCnt == 16'h0) 
    commonCnt <= 16'h0;
  // decrement the count every TBTT when the core is in DOZE, because the counter
  // is counting the listen interval
  else if (tickTBTT_p && bssType && macCoreIsInDoze) 
    commonCnt <= commonCnt - 16'b1;
  // decrement the count every TU when the core is in ACTIVE, because the
  // counter is counting the ATIM window in IBSS
  else if (tick1tu_p && !bssType && macCoreIsActive) 
    commonCnt <= commonCnt - 16'b1;
end


// ATIM window
//////////////////////////////////////////////////////////////////////////////

// generates the ATIM window over pulse if the STA is part of IBSS and is in ACTIVE
assign atimWindowOver_p = !bssType && macCoreIsActive &&
                          (commonCnt == 16'h1) && (tuCnt == {6'd0,txChainMacDelayCnt}) && tick1tu_p;


// Wake Up pulse
//////////////////////////////////////////////////////////////////////////////

// earlyWakeup_p is generated unconditionally and can be used to 
// wake up cores if they are in DOZE and the core is almost at the end of the
// DOZE state. It is generated in advance to allow the radio to be turned on.
assign earlyWakeup_p = (macLPClkSwitch) ? 
                      ((beaconIntCnt < earlyWakeupDelay) && macCoreIsInDoze) :
                      ((beaconIntCnt == ({22'd0,txChainMacDelayCnt} + {11'b0, radioWakeUpTime, 5'b0})) &&
                        tick1us_p && macCoreIsInDoze);

// wakeupDTIM_p is generated when the the dtimCnt is 1 or the dtimPeriod itself 
// is 1 AND the wakeupDTIM is set. The wakeupDTIM is not checked when the
// DTIM condition occurs when the CFP is about to start.
assign wakeupDTIM_p = earlyWakeup_p && ((dtimCnt == 8'd1) ||
                      (dtimPeriod == 8'h1)) && 
                      ((((cfpCnt == 8'h1) || (cfpPeriod == 8'h1)) && cfpAware)
                      || wakeupDTIM);
 
// wakeupListenInterval_p is generated when the core is in doze, and it is a part of a BSS.
assign wakeupListenInterval_p = earlyWakeup_p && bssType && (commonCnt == 16'h1);

// Early wake-up delay
assign earlyWakeupDelay = (({22'd0,txChainMacDelayCnt} + {11'b0, radioWakeUpTime, 5'b0}) > 26'd32) ?
                           ({22'd0,txChainMacDelayCnt} + {11'b0, radioWakeUpTime, 5'b0}) : (26'd33);


// Backoff Engine Flag
//////////////////////////////////////////////////////////////////////////////

// noBeaconTxPeriod is used to mask the beacon transmission if it
// is likely to overlap with the impending TBTT due to the delay in starting a
// beacon transmission.
assign noBeaconTxPeriod = ((beaconIntCnt < {14'b0, noBcnTxTime,4'b0}) &&
                           (beaconIntCnt > {21'd0,txChainMacDMADelayCnt}))    &&
                         !((beaconIntCnt == {21'd0,txChainMacDMADelayCnt})    &&
                           (microSecCnt == 8'h0));


// RIFS counter
//////////////////////////////////////////////////////////////////////////////

// rifsCnt counter for generating tickRifs_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    rifsCnt <= 10'h0;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p) 
    rifsCnt <= 10'h0;
  else if (txDone_p)
    rifsCnt <= (rifsInMACClk + txRFDelayInMACClk - txDelayRFOnInMACClk - 10'h1);
  else if (rifsCnt != 10'h0)
    rifsCnt <= rifsCnt - 10'h1;
end

// tickRIFS_p indicates that RIFS time has expired
assign tickRIFS_p = (rifsCnt == 10'h1);


// RIFS Timeout counter
//////////////////////////////////////////////////////////////////////////////

// rifsTOCnt counter for generating rifsTO_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    rifsTOCnt <= 10'h0;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p) 
    rifsTOCnt <= 10'h0;
  else if (rxRIFSEn)
  begin
    if (macPhyIfRxEndForTiming_p)
      rifsTOCnt <= rifsTOInMACClk;
    else if (rifsTOCnt != 10'h0)
      rifsTOCnt <= rifsTOCnt - 10'h1;
  end    
end

// rifsTO_p indicates that RIFS timeout has expired
assign rifsTO_p = rxRIFSEn && (rifsTOCnt == 10'h1);


// SIFS & Slot counter
//////////////////////////////////////////////////////////////////////////////

// The SIFS will get triggered when channelToIdle_p occurs (which is a
// pulse generated when NAV count becomes zero),respTO_p occurs (which is
// a pulse that is generated when ACK/CTS timeout occurs in CP Period,
// or when txDone_p occurs (which indicates that the transmission on air is over).
assign trigSIFS_p = (!sifsFlag && channelToIdle_p && !macPhyIfRxCca) || txDone_p || respTO_p;

// The sifs flag signal switchs the sifs slot counter between the sifs and 
// slot. When the flag is high, the sifsSlotCnt counter counts SIFS, after
// which it counts SLOTS
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    sifsFlag <= 1'b1;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p) 
    sifsFlag <= 1'b1;
  else if (trigSIFS_p || macPhyIfRxEndForTiming_p)
    sifsFlag <= 1'b1;
  else if ((sifsSlotCnt == 16'h0) || mpIfTxEn)
    sifsFlag <= 1'b0;
end

// SIFS mux
assign sifsInMACClk = (rxDot11a) ? sifsAInMACClk : sifsBInMACClk;

// SIFS difference
assign sifsDiffInMACClk = sifsAInMACClk - sifsBInMACClk;

// sifsSlotCnt is reused between the SIFS and SLOT calculation.
// When trigSIFS_p is asserted, the counter start counting down for SIFS. If
// this is a dot11a environment, then a SIFS of 10us should be counted for, else
// a SIFS of 16us should be counted for. This is done on the basic of the dot11a
// bit from CSREG. Thus for dot11g, a SIFS time of 10us will be counted for.
// If cca is asserted when the SIFS period is being counted, the SIFS counter
// should not stop, because the ACK has to be sent irrespective of any other
// transmission on the channel. Also if cca is high after the SIFS period, the
// counter should be loaded with the SIFS counts and frozen to prevent
// earlySlot_p being generated. The value that is loaded is dependent on the
// last packet rxed (and not on the environment); so if the last pkt rxed was
// a OFDM packet, a SIFS time of 16us will be counted for, else a SIFS time of
// 10us will be counted for.
// Every time the counter goes to zero, it counts down for SLOT. 
// When a eifsFlag is issued, the sifsSlotCnt is loaded with 
// macProcDelayInMACClk + txChainDelayInMACClk.
// This is done do so that the next SLOT can be counted after the EIFS actually
// gets over in air (because the eifsFlag is actually asserted
// at EIFS - macProcDelayInMACClk - txChainDelayInMACClk.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    sifsSlotCnt <= 16'd`SIFS_TIME_DOT11B * 16'd`MAC_FREQ;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p)
    sifsSlotCnt <= 16'd`SIFS_TIME_DOT11B * 16'd`MAC_FREQ;
  else if (macCoreIsActive)
  begin
    if (macPhyIfRxEndForTiming_p)
      sifsSlotCnt <= (sifsInMACClk - {6'd0,rxRFDelayInMACClk} - 16'h1);
    else if (trigSIFS_p || (macPhyIfRxCca && !sifsFlag) || mpIfTxEn)
      sifsSlotCnt <= sifsInMACClk - 16'h1;
    else if (sifsSlotCnt == 16'h0)
      sifsSlotCnt <= slotTimeInMACClk - 16'h1;
    else if (eifsFlag0Rst_p || eifsFlag1Rst_p || eifsFlag2Rst_p || eifsFlag3Rst_p)
      sifsSlotCnt <= ({6'b0, txChainMacDelayInMACClk} - {8'd0,macCoreClkFreq});
    else if (sifsSlotCntUpdate_p && sifsFlag)
    begin
      if (rxDot11a)
        sifsSlotCnt <= sifsSlotCnt + sifsDiffInMACClk - 16'h1;
      else
        sifsSlotCnt <= sifsSlotCnt - sifsDiffInMACClk - 16'h1;
    end
    else
      sifsSlotCnt <= sifsSlotCnt - 16'h1;
  end
end

// slotCnt in us for Backoff Engine
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    slotCnt <= 8'd`SLOT_TIME_DOT11B;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p)
    slotCnt <= 8'd`SLOT_TIME_DOT11B;
  else if (macCoreIsActive)
  begin
    if (tickNullSIFS_p || mpIfTxEn || macPhyIfRxCca || channelBusy || respTO_p)
      slotCnt <= slotTime - 8'h1;
    else if (!sifsFlag && (slotCnt == 8'h0) && tickSlot1us_p)
      slotCnt <= slotTime - 8'h1;
    else if (tickSlot1us_p && !sifsFlag)
      slotCnt <= slotCnt - 8'h1;
  end    
end

// microSecSlotCnt counter for generating tickSlot1us_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)   // Asynchronous Reset
    microSecSlotCnt <= 8'd`MAC_FREQ - 8'h1;
  else if (!macCoreClkSoftRst_n || (microSecSlotCnt == 8'h0) || tickNullSIFS_p || moveToIdle_p)
    microSecSlotCnt <= macCoreClkFreq - 8'h1;
  else if (macCoreIsActive)
    microSecSlotCnt <= microSecSlotCnt - 8'h1;
end

// pulse generated every microsecond at tickSlot1us_p boundary
assign tickSlot1us_p = (microSecSlotCnt == 8'h0);


// Calculation for sifs remaining in us for duration computation in tx controller when sending mpdu
assign txDelayInUsDone   = (delayTxRxCnt >= txChainDelayInMACClk);
assign rxRFDelayInUsDone = (delayTxRxCnt >= rxRFDelayInMACClk);

// Calculation of tx and rxrf delay in us 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)   // Asynchronous Reset
  begin
    txDelayInUs   <=  8'h0;
    rxRFDelayInUs <=  8'h0;
    delayTxRxCnt  <= 10'h0; 
  end
  else if(macCoreClkSoftRst_n == 1'b0 || moveToIdle_p)
  begin
    txDelayInUs   <=  8'h0;
    rxRFDelayInUs <=  8'h0;
    delayTxRxCnt  <= 10'h0;
  end
  else
  begin
    if(macCoreIsActive && ((txDelayInUsDone == 1'b0) || (rxRFDelayInUsDone == 1'b0)))
    begin
      if(tick1us_p)
      begin
        delayTxRxCnt  <=  delayTxRxCnt + {2'h0,macCoreClkFreq};
        
        if(txDelayInUsDone == 1'b0)
          txDelayInUs   <=  txDelayInUs  + 8'h1;
          
        if(rxRFDelayInUsDone == 1'b0)
          rxRFDelayInUs <=  rxRFDelayInUs+ 8'h1;
      end
    end
    else if(!macCoreIsActive && ((txDelayInUsDone == 1'b1) || (rxRFDelayInUsDone == 1'b1)) && (delayTxRxCnt != 10'h0))
    begin
      txDelayInUs   <= 8'h0;
      rxRFDelayInUs <= 8'h0;
      delayTxRxCnt  <= 10'h0;
    end
  end
end

// Calculation of sifs remaining for mac comtroller tx
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)   // Asynchronous Reset
    sifsRemaining <= 8'h0;
  else if (macCoreClkSoftRst_n == 1'b0 || moveToIdle_p)
    sifsRemaining <= 8'h0;
  else
  begin
    if (trigSIFS_p || (macPhyIfRxCca && !sifsFlag) || mpIfTxEn)
    begin
      if(rxDot11a)
        sifsRemaining <= sifsA - txDelayInUs;
      else
        sifsRemaining <= sifsB - txDelayInUs;
    end
    else if (macPhyIfRxEndForTiming_p)
    begin
      if(rxDot11a)
        sifsRemaining <= sifsA - txDelayInUs - rxRFDelayInUs;
      else
        sifsRemaining <= sifsB - txDelayInUs - rxRFDelayInUs;
    end
    else if((sifsRemaining != 8'h0) && sifsFlag && tick1us_p)
      sifsRemaining <= sifsRemaining - 8'h1;
  end
end

// SIFS & Slot pulses
//////////////////////////////////////////////////////////////////////////////

// tickDMAEarlySlot_p is used to start the DMA processing early, so as to finally
// meet the SLOT boundary in air
assign tickDMAEarlySlot_p = (sifsSlotCnt == ({6'd0,txChainMacDelayInMACClk} + {6'd0,txDMAProcDlyInMACClk})) &&
                            !sifsFlag && (!channelBusy || cfpOn);

// tickEarlySlot_p is used to start the MAC processing early, so as to finally
// meet the SLOT boundary in air
assign tickEarlySlot_p = (sifsSlotCnt == {6'd0,txChainMacDelayInMACClk}) && !sifsFlag &&
                         (!channelBusy || cfpOn);

// tickSlot_p is used by the MAC to start the MAC processing early, so as to
// finally meet the SLOT boundary in air
assign tickSlot_p = (sifsSlotCnt == {6'd0,txChainDelayInMACClk}) && !sifsFlag;

// tickNullSlot_p is used for txChainMacDelayInMACClk conversion in us
assign tickNullSlot_p = (sifsSlotCnt == 16'h0) && !sifsFlag;

// tickSIFS_p is used by the MAC to start the core processing early, so as to
// finally meet the SIFS boundary in air
assign tickSIFS_p = (sifsSlotCnt == {6'd0,txChainDelayInMACClk}) && sifsFlag;

// tickNullSIFS_p is used for slotCnt set
assign tickNullSIFS_p = (sifsSlotCnt == 16'h0) && sifsFlag;


// PIFS counters
//////////////////////////////////////////////////////////////////////////////

// Delayed macPhyIfRxCcaSec20 for sec20PIFSCnt counter
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    macPhyIfRxCcaSec20_ff1 <= 1'b0;
  else
    macPhyIfRxCcaSec20_ff1 <= macPhyIfRxCcaSec20;
end

assign pifsInMACClk = sifsInMACClk + slotTimeInMACClk - {6'd0,txChainMacDelayInMACClk};
  
// sec20PIFSCnt counter for generating sec20ChannelIdleFlag flag
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    sec20PIFSCnt <= (16'd`SIFS_TIME_DOT11B + 16'd`SLOT_TIME_DOT11B) * 16'd`MAC_FREQ;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p) 
    sec20PIFSCnt <= (16'd`SIFS_TIME_DOT11B + 16'd`SLOT_TIME_DOT11B) * 16'd`MAC_FREQ;
  else if (!macPhyIfRxCcaSec20 && macPhyIfRxCcaSec20_ff1)
    sec20PIFSCnt <= pifsInMACClk;
  else if ((sec20PIFSCnt != 16'h0) && !macPhyIfRxCcaSec20)
    sec20PIFSCnt <= sec20PIFSCnt - 16'h1;
end

// sec20ChannelIdleFlag indicates that the secondary 20MHz channel was IDLE for more than PIFS time
assign sec20ChannelIdleFlag = !macPhyIfRxCcaSec20_ff1 && (sec20PIFSCnt == 16'h0);

// Delayed macPhyIfRxCcaSec40 for sec40PIFSCnt counter
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    macPhyIfRxCcaSec40_ff1 <= 1'b0;
  else
    macPhyIfRxCcaSec40_ff1 <= macPhyIfRxCcaSec40;
end

// sec40PIFSCnt counter for generating sec40ChannelIdleFlag flag
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    sec40PIFSCnt <= (16'd`SIFS_TIME_DOT11B + 16'd`SLOT_TIME_DOT11B) * 16'd`MAC_FREQ;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p) 
    sec40PIFSCnt <= (16'd`SIFS_TIME_DOT11B + 16'd`SLOT_TIME_DOT11B) * 16'd`MAC_FREQ;
  else if (!macPhyIfRxCcaSec40 && macPhyIfRxCcaSec40_ff1)
    sec40PIFSCnt <= pifsInMACClk;
  else if ((sec40PIFSCnt != 16'h0) && !macPhyIfRxCcaSec40)
    sec40PIFSCnt <= sec40PIFSCnt - 16'h1;
end

// sec40ChannelIdleFlag indicates that the secondary 40MHz channel was IDLE for more than PIFS time
assign sec40ChannelIdleFlag = !macPhyIfRxCcaSec40_ff1 && (sec40PIFSCnt == 16'h0);

// Delayed macPhyIfRxCcaSec80 for sec80PIFSCnt counter
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    macPhyIfRxCcaSec80_ff1 <= 1'b0;
  else
    macPhyIfRxCcaSec80_ff1 <= macPhyIfRxCcaSec80;
end

// sec80PIFSCnt counter for generating sec80ChannelIdleFlag flag
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    sec80PIFSCnt <= (16'd`SIFS_TIME_DOT11B + 16'd`SLOT_TIME_DOT11B) * 16'd`MAC_FREQ;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p) 
    sec80PIFSCnt <= (16'd`SIFS_TIME_DOT11B + 16'd`SLOT_TIME_DOT11B) * 16'd`MAC_FREQ;
  else if (!macPhyIfRxCcaSec80 && macPhyIfRxCcaSec80_ff1)
    sec80PIFSCnt <= pifsInMACClk;
  else if ((sec80PIFSCnt != 16'h0) && !macPhyIfRxCcaSec80)
    sec80PIFSCnt <= sec80PIFSCnt - 16'h1;
end

// sec80ChannelIdleFlag indicates that the secondary 80MHz channel was IDLE for more than PIFS time
assign sec80ChannelIdleFlag = !macPhyIfRxCcaSec80_ff1 && (sec80PIFSCnt == 16'h0);

// pifsCnt counter for generating tickPIFS_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    pifsCnt <= (16'd`SIFS_TIME_DOT11B + 16'd`SLOT_TIME_DOT11B) * 16'd`MAC_FREQ;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p) 
    pifsCnt <= (16'd`SIFS_TIME_DOT11B + 16'd`SLOT_TIME_DOT11B) * 16'd`MAC_FREQ;
  else if (trigSIFS_p || (macPhyIfRxCca && !sifsFlag) || mpIfTxEn)
    pifsCnt <= sifsInMACClk + slotTimeInMACClk - {6'd0,txChainDelayInMACClk};
  else if (macPhyIfRxEndForTiming_p)
    pifsCnt <= pifsInMACClk;
  else if (pifsCnt == 16'h0)
    pifsCnt <= pifsCnt;
  else
    pifsCnt <= pifsCnt - 16'h1;
end

// tickPIFS_p is used by the MAC to start the core processing early, so as to
// finally meet the PIFS boundary in air
assign tickPIFS_p = (pifsCnt == 15'd0);


// AIFS counters
//////////////////////////////////////////////////////////////////////////////
//abgnMode
//3'b000: 802.11b
//3'b001: 802.11a
//3'b010: 802.11g
//3'b011: 802.11n @ 2.4 GHz
//3'b100: 802.11n @ 5 GHz
//3'b110: 802.11ac @5 GHz
assign sifs = ((abgnMode == 3'b000) || (abgnMode == 3'b010) || (abgnMode == 3'b011)) ? sifsB : sifsA;

assign txChainMacDMADelayCntMinus1 = {7'd0,txChainMacDMADelayCnt} - 12'h1;
assign txChainMacDMADelayCntPlus1 = {7'd0,txChainMacDMADelayCnt} + 12'h1;
assign sifsMinusTxChainMacDMA = {4'b0,sifs} - txChainMacDMADelayCntMinus1;
assign sifsMinusTxChainMacDMAAndCCA = sifsMinusTxChainMacDMA - {8'd0,rxCCADelay};

// AIFS 0 
assign aifs0SlotDuration = {8'd0,aifsn0} * {4'd0,slotTime};

// aifsCnt0 counter for generating aifsFlag0 flag
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    aifsCnt0 <= AIFS0_INIT * 12'd`SLOT_TIME_DOT11B;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p)
    aifsCnt0 <= AIFS0_INIT * 12'd`SLOT_TIME_DOT11B;
  else if (tickNullSIFS_p)
    aifsCnt0 <= aifs0SlotDuration - txChainMacDMADelayCntPlus1;
  else if (mpIfTxEn || channelBusy || respTO_p)
    aifsCnt0 <= aifs0SlotDuration + sifsMinusTxChainMacDMA;
  else if (macPhyIfRxCca)
    aifsCnt0 <= aifs0SlotDuration + sifsMinusTxChainMacDMAAndCCA;
  else if (aifsCnt0 == 12'h0)
    aifsCnt0 <= aifsCnt0;
  else if (tickSlot1us_p && !sifsFlag)
    aifsCnt0 <= aifsCnt0 - 12'h1;
end

// aifsFlag0 indicates that the channel was IDLE for more than a AIFS time
assign aifsFlag0 = (aifsCnt0 == 12'h0) && !eifsMask;


// AIFS 1 
assign aifs1SlotDuration = {8'd0,aifsn1} * {4'd0,slotTime};

// aifsCnt1 counter for generating aifsFlag1 flag
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    aifsCnt1 <= AIFS1_INIT * 12'd`SLOT_TIME_DOT11B;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p)
    aifsCnt1 <= AIFS1_INIT * 12'd`SLOT_TIME_DOT11B;
  else if (tickNullSIFS_p)
    aifsCnt1 <= aifs1SlotDuration - txChainMacDMADelayCntPlus1;
  else if (mpIfTxEn || channelBusy || respTO_p)
    aifsCnt1 <= aifs1SlotDuration + sifsMinusTxChainMacDMA;
  else if (macPhyIfRxCca)
    aifsCnt1 <= aifs1SlotDuration + sifsMinusTxChainMacDMAAndCCA;
  else if (aifsCnt1 == 12'h0)
    aifsCnt1 <= aifsCnt1;
  else if (tickSlot1us_p && !sifsFlag)
    aifsCnt1 <= aifsCnt1 - 12'h1;
end

// aifsFlag1 indicates that the channel was IDLE for more than a AIFS time
assign aifsFlag1 = (aifsCnt1 == 12'h0) && !eifsMask;


// AIFS 2 
assign aifs2SlotDuration = {8'd0,aifsn2} * {4'd0,slotTime};

// aifsCnt2 counter for generating aifsFlag2 flag
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    aifsCnt2 <= AIFS2_INIT * 12'd`SLOT_TIME_DOT11B;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p)
    aifsCnt2 <= AIFS2_INIT * 12'd`SLOT_TIME_DOT11B;
  else if (tickNullSIFS_p)
    aifsCnt2 <= aifs2SlotDuration - txChainMacDMADelayCntPlus1;
  else if (mpIfTxEn || channelBusy || respTO_p)
    aifsCnt2 <= aifs2SlotDuration + sifsMinusTxChainMacDMA;
  else if (macPhyIfRxCca)
    aifsCnt2 <= aifs2SlotDuration + sifsMinusTxChainMacDMAAndCCA;
  else if (aifsCnt2 == 12'h0)
    aifsCnt2 <= aifsCnt2;
  else if (tickSlot1us_p && !sifsFlag)
    aifsCnt2 <= aifsCnt2 - 12'h1;
end

// aifsFlag2 indicates that the channel was IDLE for more than a AIFS time
assign aifsFlag2 = (aifsCnt2 == 12'h0) && !eifsMask;

// AIFS 3 
assign aifs3SlotDuration = {8'd0,aifsn3} * {4'd0,slotTime};

// aifsCnt3 counter for generating aifsFlag3 flag
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    aifsCnt3 <= AIFS3_INIT * 12'd`SLOT_TIME_DOT11B;
  else if (!macCoreClkSoftRst_n || hwFSMReset || moveToIdle_p)
    aifsCnt3 <= AIFS3_INIT * 12'd`SLOT_TIME_DOT11B;
  else if (tickNullSIFS_p)
    aifsCnt3 <= aifs3SlotDuration - txChainMacDMADelayCntPlus1;
  else if (mpIfTxEn || channelBusy || respTO_p)
    aifsCnt3 <= aifs3SlotDuration + sifsMinusTxChainMacDMA;
  else if (macPhyIfRxCca)
    aifsCnt3 <= aifs3SlotDuration + sifsMinusTxChainMacDMAAndCCA;
  else if (aifsCnt3 == 12'h0)
    aifsCnt3 <= aifsCnt3;
  else if (tickSlot1us_p && !sifsFlag)
    aifsCnt3 <= aifsCnt3 - 12'h1;
end

// aifsFlag3 indicates that the channel was IDLE for more than a AIFS time
assign aifsFlag3 = (aifsCnt3 == 12'h0) && !eifsMask;


// EIFS counters
//////////////////////////////////////////////////////////////////////////////

// Trigger the EIFS counter after the AIFS period has reached.
// The counter is reset when the packet reception or transmission is in progress
// or when the channel is BUSY as indicated by the physical/virtual carrier 
// sense mechanisms.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    eifsCnt0 <= 15'h0;
  else if (!eifsMask)
    eifsCnt0 <= 15'h0;
  else if (((rxDot11a && (eifsCnt0 != (15'd`EIFS_MINUS_DIFS_DOT11A + 15'h1)))  ||
           (!rxDot11a && (eifsCnt0 != (15'd`EIFS_MINUS_DIFS_DOT11B + 15'h1)))) &&
           (aifsCnt0 == 12'h0) && tickSlot1us_p && eifsMask)
    eifsCnt0 <= eifsCnt0 + 15'h1;
end

// eifsFlag0 indicates that the channel was idle for more than an CP0 EIFS time.
assign eifsFlag0 = rxDot11a ? (eifsCnt0 == (15'd`EIFS_MINUS_DIFS_DOT11A + 15'h1))
                            : (eifsCnt0 == (15'd`EIFS_MINUS_DIFS_DOT11B + 15'h1));


// same as eifsCnt0, using AC1 parameters
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    eifsCnt1 <= 15'h0;
  else if (!eifsMask)
    eifsCnt1 <= 15'h0;
  else if (((rxDot11a && (eifsCnt1 != (15'd`EIFS_MINUS_DIFS_DOT11A + 15'h1)))  ||
           (!rxDot11a && (eifsCnt1 != (15'd`EIFS_MINUS_DIFS_DOT11B + 15'h1)))) &&
           (aifsCnt1 == 12'h0) && tickSlot1us_p && eifsMask)
    eifsCnt1 <= eifsCnt1 + 15'h1;
end

// eifsFlag1 indicates that the channel was idle for more than an CP1 EIFS time.
assign eifsFlag1 = rxDot11a ? (eifsCnt1 == (15'd`EIFS_MINUS_DIFS_DOT11A + 15'h1))
                            : (eifsCnt1 == (15'd`EIFS_MINUS_DIFS_DOT11B + 15'h1));


// same as eifsCnt0, using AC2 parameters
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    eifsCnt2 <= 15'h0;
  else if (!eifsMask)
    eifsCnt2 <= 15'h0;
  else if (((rxDot11a && (eifsCnt2 != (15'd`EIFS_MINUS_DIFS_DOT11A + 15'h1)))  ||
           (!rxDot11a && (eifsCnt2 != (15'd`EIFS_MINUS_DIFS_DOT11B + 15'h1)))) &&
           (aifsCnt2 == 12'h0) && tickSlot1us_p && eifsMask)
    eifsCnt2 <= eifsCnt2 + 15'h1;
end

// eifsFlag2 indicates that the channel was idle for more than an CP2 EIFS time.
assign eifsFlag2 = rxDot11a ? (eifsCnt2 == (15'd`EIFS_MINUS_DIFS_DOT11A + 15'h1))
                            : (eifsCnt2 == (15'd`EIFS_MINUS_DIFS_DOT11B + 15'h1));


// same as eifsCnt0, using AC3 parameters
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    eifsCnt3 <= 15'h0;
  else if (!eifsMask)
    eifsCnt3 <= 15'h0;
  else if (((rxDot11a && (eifsCnt3 != (15'd`EIFS_MINUS_DIFS_DOT11A + 15'h1)))  ||
           (!rxDot11a && (eifsCnt3 != (15'd`EIFS_MINUS_DIFS_DOT11B + 15'h1)))) &&
           (aifsCnt3 == 12'h0) && tickSlot1us_p && eifsMask)
    eifsCnt3 <= eifsCnt3 + 15'h1;
end

// eifsFlag3 indicates that the channel was idle for more than an CP3 EIFS time.
assign eifsFlag3 = rxDot11a ? (eifsCnt3 == (15'd`EIFS_MINUS_DIFS_DOT11A + 15'h1))
                            : (eifsCnt3 == (15'd`EIFS_MINUS_DIFS_DOT11B + 15'h1));

// Delayed EIFS flags for EIFS flag reset and EIFS mask generation
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
  begin
    eifsFlag0_ff1 <= 1'b0;
    eifsFlag1_ff1 <= 1'b0;
    eifsFlag2_ff1 <= 1'b0;
    eifsFlag3_ff1 <= 1'b0;
    eifsMask      <= 1'b0;
  end
  else if (!macCoreClkSoftRst_n || moveToIdle_p)
  begin
    eifsFlag0_ff1 <= 1'b0;
    eifsFlag1_ff1 <= 1'b0;
    eifsFlag2_ff1 <= 1'b0;
    eifsFlag3_ff1 <= 1'b0;
    eifsMask      <= 1'b0;
  end
  else
  begin
    eifsFlag0_ff1 <= eifsFlag0;
    eifsFlag1_ff1 <= eifsFlag1;
    eifsFlag2_ff1 <= eifsFlag2;
    eifsFlag3_ff1 <= eifsFlag3;
    // EIFS mask generation
    if (mpIfTxEn || macPhyIfRxCca || channelBusy || respTO_p)
      eifsMask <= 1'b0;
    else if (lastRxWrong)
      eifsMask <= 1'b1;
  end
end

// generating EIFS flag reset for sifsSlotCnt counter reset
assign eifsFlag0Rst_p = eifsFlag0 && !eifsFlag0_ff1;
assign eifsFlag1Rst_p = eifsFlag1 && !eifsFlag1_ff1;
assign eifsFlag2Rst_p = eifsFlag2 && !eifsFlag2_ff1;
assign eifsFlag3Rst_p = eifsFlag3 && !eifsFlag3_ff1;


// DTIM counter
//////////////////////////////////////////////////////////////////////////////

// generating the DTIM count update in STA and AP.
always @ (posedge macLPClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    dtimCnt <= 8'h0;
  else if (!macCoreClkSoftRst_n)
     dtimCnt <= 8'h0;
  else if (dtimUpdatedBySW && ap)
    dtimCnt <= 8'h1;
  else if (macCoreIsActive && dtimUpdate_p)
    dtimCnt <= rxDtimCnt;
  else if ((beaconIntCnt == {21'd0,txChainMacDMADelayCnt}) && tick1us_p)
  begin
      if (dtimCnt == 8'h0)
      dtimCnt <= dtimPeriod - 8'h1;
    else
      dtimCnt <= dtimCnt - 8'h1;
  end
end


// generate dtimUpdatedBySWInValid in order to clear dtimUpdatedBySW bit
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    dtimUpdatedBySWInValid <= 1'b0;
  else
    dtimUpdatedBySWInValid <= dtimUpdatedBySW;
end

assign dtimUpdatedBySWIn = 1'b0;


// CFP counter
//////////////////////////////////////////////////////////////////////////////

// generating the CFP count update in STA and AP.
always @ (posedge macLPClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    cfpCnt <= 8'h0;
  else if (!macCoreClkSoftRst_n)
     cfpCnt <= 8'h0;
  else if (dtimUpdatedBySW && ap)
    cfpCnt <= 8'h1;
  else if (macCoreIsActive && cfpUpdate_p)
    cfpCnt <= rxCfpCnt;
  else if ((beaconIntCnt == {21'd0,txChainMacDMADelayCnt}) && tick1us_p && (dtimCnt == 8'h0))
  begin
    if (cfpCnt == 8'h0)
      cfpCnt <= cfpPeriod - 8'h1;
    else
      cfpCnt <= cfpCnt - 8'h1;
  end
end


// CFP active period
//////////////////////////////////////////////////////////////////////////////

// cfpOn indicates that the CF period is active. It gets set when
// the NAV is updated with the CFP max duration.
// The clearing of the flag at AP is performed when the navCounter expires or
// a cfEnd frame is received or transmitted.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    cfpOn <= 1'h0;
  else if (!macCoreClkSoftRst_n || hwFSMReset)
    cfpOn <= 1'h0;
  else if (navCfpMaxDurUpdate_p)
    cfpOn <= 1'b1;
  else if (channelToIdle_p || cfEndRcved_p || sentCFEND)
    cfpOn <= 1'b0;
end

// The cfPeriod begins when the dtimCnt and cfpCnt are both equal to zero and 
// the core is cfpAware and TBTT occurs, else it should be done at every TBTT
// if the cfpPeriod and dtimPeriod is 0. 
// at this point the NAV counter should be loaded with cfpMaxDuration.
//assign navCfpMaxDurUpdate_p = (cfpCnt == 8'h0) && (dtimCnt == 8'h0) && bssType &&
//                              cfpAware && tickTBTT_p;

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    navCfpMaxDurUpdate_p <= 1'd0;
  else if ((cfpCnt == 8'h0) && (dtimCnt == 8'h0) && bssType && cfpAware && tickTBTT_p)
    navCfpMaxDurUpdate_p <= 1'b1;
  else
    navCfpMaxDurUpdate_p <= 1'b0;
end

// Absolute counters
//////////////////////////////////////////////////////////////////////////////

// fourMicroSecCnt counter for generating tick32us_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    timeoutCnt <= 5'h1f;
  else if (!macCoreClkSoftRst_n || ((timeoutCnt == 5'h00) && tick1us_p))
    timeoutCnt <= 5'h1f;
  else if (tick1us_p)
    timeoutCnt <= timeoutCnt - 5'h1;
end

// pulse generated every 32 microseconds
assign tick32us_p = (timeoutCnt == 5'h0) && tick1us_p;

// TX absolute counter for generating timerTxTrigger
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    txAbsoluteTimeoutCnt <= 8'h0;
  else if (!macCoreClkSoftRst_n || timerTxTriggerInt)
    txAbsoluteTimeoutCnt <= 8'h0;
  else if ((txAbsoluteTimeoutCnt == 8'h0) && txDone_p && 
    (txAbsoluteTimeout != 8'h0))
    txAbsoluteTimeoutCnt <= txAbsoluteTimeout;
  else if ((txAbsoluteTimeoutCnt != 8'h0) && tick32us_p)
    txAbsoluteTimeoutCnt <= txAbsoluteTimeoutCnt - 8'h1;
end

// RX absolute counter for generating timerRxTrigger
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    rxAbsoluteTimeoutCnt <= 8'h0;
  else if (!macCoreClkSoftRst_n || timerRxTriggerInt)
    rxAbsoluteTimeoutCnt <= 8'h0;
  else if ((rxAbsoluteTimeoutCnt == 8'h0) && rxTrig_p && 
    (rxAbsoluteTimeout != 8'h0))
    rxAbsoluteTimeoutCnt <= rxAbsoluteTimeout;
  else if ((rxAbsoluteTimeoutCnt != 8'h0) && tick32us_p)
    rxAbsoluteTimeoutCnt <= rxAbsoluteTimeoutCnt - 8'h1;
end


// Packet counters
//////////////////////////////////////////////////////////////////////////////

// TX packet counter for generating timerTxTrigger
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    txPacketTimeoutCnt <= 8'h0;
  else if (!macCoreClkSoftRst_n || timerTxTriggerInt)
    txPacketTimeoutCnt <= 8'h0;
  else if (txDone_p && (txPacketTimeout != 8'h0))
    txPacketTimeoutCnt <= txPacketTimeout;
  else if ((txPacketTimeoutCnt != 8'h0) && tick32us_p)
    txPacketTimeoutCnt <= txPacketTimeoutCnt - 8'h1;
end

// RX packet counter for generating timerRxTrigger
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    rxPacketTimeoutCnt <= 8'h0;
  else if (!macCoreClkSoftRst_n || timerRxTriggerInt)
    rxPacketTimeoutCnt <= 8'h0;
  else if (rxTrig_p && (rxPacketTimeout != 8'h0))
    rxPacketTimeoutCnt <= rxPacketTimeout;
  else if ((rxPacketTimeoutCnt != 8'h0) && tick32us_p)
    rxPacketTimeoutCnt <= rxPacketTimeoutCnt - 8'h1;
end


// TX & RX Triggers
//////////////////////////////////////////////////////////////////////////////

// TX Trigger
assign timerTxTriggerInt = tick32us_p &&
                        ((txAbsoluteTimeoutCnt == 8'h1) || 
                        (txPacketTimeoutCnt == 8'h1));

// RX Trigger
assign timerRxTriggerInt = tick32us_p &&
                        ((rxAbsoluteTimeoutCnt == 8'h1) ||
                        (rxPacketTimeoutCnt == 8'h1));


// CCA busy duration
//////////////////////////////////////////////////////////////////////////////

// generate ccaBusyDurIn
always @*
begin
  if (!macCoreClkSoftRst_n)
    ccaBusyDurIn = 32'b0;
  // CCA busy duration incrementation every microseconds
  else if (tick1us_p && (channelBusy || macPhyIfRxCca))
    ccaBusyDurIn = ccaBusyDur + 32'b1;
  else
    ccaBusyDurIn = ccaBusyDur;
end

assign ccaBusyDurInValid = ((tick1us_p && (channelBusy || macPhyIfRxCca)) 
                           || !macCoreClkSoftRst_n);

// generate ccaBusyDurSec20In
always @*
begin
  if (!macCoreClkSoftRst_n)
    ccaBusyDurSec20In = 32'b0;
  // CCA busy duration incrementation every microseconds
  else if (tick1us_p && macPhyIfRxCcaSec20)
    ccaBusyDurSec20In = ccaBusyDurSec20 + 32'b1;
  else
    ccaBusyDurSec20In = ccaBusyDurSec20;
end

assign ccaBusyDurSec20InValid = ((tick1us_p && macPhyIfRxCcaSec20) || !macCoreClkSoftRst_n);

// generate ccaBusyDurSec40In
always @*
begin
  if (!macCoreClkSoftRst_n)
    ccaBusyDurSec40In = 32'b0;
  // CCA busy duration incrementation every microseconds
  else if (tick1us_p && macPhyIfRxCcaSec40)
    ccaBusyDurSec40In = ccaBusyDurSec40 + 32'b1;
  else
    ccaBusyDurSec40In = ccaBusyDurSec40;
end

assign ccaBusyDurSec40InValid = ((tick1us_p && macPhyIfRxCcaSec40) || !macCoreClkSoftRst_n);

// generate ccaBusyDurSec80In
always @*
begin
  if (!macCoreClkSoftRst_n)
    ccaBusyDurSec80In = 32'b0;
  // CCA busy duration incrementation every microseconds
  else if (tick1us_p && macPhyIfRxCcaSec80)
    ccaBusyDurSec80In = ccaBusyDurSec80 + 32'b1;
  else
    ccaBusyDurSec80In = ccaBusyDurSec80;
end

assign ccaBusyDurSec80InValid = ((tick1us_p && macPhyIfRxCcaSec80) || !macCoreClkSoftRst_n);


// OLBC counters
//////////////////////////////////////////////////////////////////////////////

// generate OLBC timer and counters
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
  begin
    olbcTimerCnt <= 16'h0;
    olbcOFDMCnt  <= 8'h0;
    olbcDSSSCnt  <= 8'h0;
  end
  // Clear timer and counters when olbcTimer register is null
  else if (olbcTimer == 16'h0)
  begin
    olbcTimerCnt <= 16'h0;
    olbcOFDMCnt  <= 8'h0;
    olbcDSSSCnt  <= 8'h0;
  end
  else
  begin
    // OLBC Timer set
    if ((olbcTimerCnt == 16'h0) && tick1us_p)
      olbcTimerCnt <= olbcTimer;
    // OLBC Timer increment
    else if (tick1us_p)
      olbcTimerCnt <= olbcTimerCnt - 16'h1;
    
    // OLBC counters clear
    if (olbcTimerCnt == 16'h0)
    begin
      olbcOFDMCnt <= 8'h0;
      olbcDSSSCnt <= 8'h0;
    end
    // OLBC Counters increment
    else if (olbcUpdate_p)
    begin
      if ((rxLegRate[3] == 1'b0) && (rxFormatMod == 3'b0))
      begin
        if (olbcDSSSCnt < dsssCount)
          // DSSS counter increment
          olbcDSSSCnt <= olbcDSSSCnt + 8'h1;
      end
      else
      begin
        if (olbcOFDMCnt < ofdmCount)
          // OFDM counter increment
          olbcOFDMCnt <= olbcOFDMCnt + 8'h1;
      end
    end
  end
end

// generate OLBC flag for interrupt generation
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
  begin
    olbcOFDMCntDone     <= 1'b0;
    olbcOFDMCntDone_ff1 <= 1'b0;
    olbcDSSSCntDone     <= 1'b0;
    olbcDSSSCntDone_ff1 <= 1'b0;
  end
  // Clear flags
  else if ((olbcTimer == 16'h0) || (olbcTimerCnt == 16'h0))
  begin
    olbcOFDMCntDone     <= 1'b0;
    olbcOFDMCntDone_ff1 <= 1'b0;
    olbcDSSSCntDone     <= 1'b0;
    olbcDSSSCntDone_ff1 <= 1'b0;
  end
  else
  begin
    // Delayed signal for pulse generation
    olbcOFDMCntDone_ff1 <= olbcOFDMCntDone;
    olbcDSSSCntDone_ff1 <= olbcDSSSCntDone;
  
    // OLBC flags
    if ((olbcOFDMCnt == ofdmCount) && (ofdmCount != 8'd0))
      olbcOFDMCntDone <= 1'b1;
    if ((olbcDSSSCnt == dsssCount) && (dsssCount != 8'd0))
      olbcDSSSCntDone <= 1'b1;
  end
end

// olbcOFDM indicates that OFDM frames received with incorrect BSS have reached ofdmCount register
assign olbcOFDMInt = olbcOFDMCntDone && !olbcOFDMCntDone_ff1;

// olbcDSSS indicates that DSSS frames received with incorrect BSS have reached dsssCount register
assign olbcDSSSInt = olbcDSSSCntDone && !olbcDSSSCntDone_ff1;


// Quiet intervals
//////////////////////////////////////////////////////////////////////////////

// Delayed updateBeaconIntCnt_p for priQICnt and secQICnt update
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
  begin
    quietElement1InValid_ff1 <= 1'b0;
    quietElement2InValid_ff1 <= 1'b0;
  end
  else
  begin
    quietElement1InValid_ff1 <= quietElement1InValid;
    quietElement2InValid_ff1 <= quietElement2InValid;
  end
end

// generate priQICnt counter
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                           // Asynchronous Reset
    priQICnt <= 26'h3ff_ffff;
  else if (!macCoreClkSoftRst_n || (quietPeriod1 == 8'h0) || // Synchronous Reset
    (quietCount1 == 8'h0))
    priQICnt <= 26'h3ff_ffff;
  else if ((bssType && !ap) || !bssType)
  begin
    if ((quietCount1 == 8'h2) && quietElement1InValid_ff1)
      priQICnt <= {quietOffset1, 10'b0} + {beaconInt, 10'b0};
    else if ((quietCount1 == 8'h1) && quietElement1InValid_ff1)
      priQICnt <= {quietOffset1, 10'b0};
    else if (tick1us_p && (priQICnt != 26'h3ff_ffff))
      priQICnt <= priQICnt - 26'h1;
  end
  else
    priQICnt <= 26'h3ff_ffff;
end

// generate secQICnt counter
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                           // Asynchronous Reset
    secQICnt <= 26'h3ff_ffff;
  else if (!macCoreClkSoftRst_n || (quietPeriod2 == 8'h0) || // Synchronous Reset
    (quietCount2 == 8'h0))
    secQICnt <= 26'h3ff_ffff;
  else if ((bssType && !ap) || !bssType)
  begin
    if ((quietCount2 == 8'h2) && quietElement2InValid_ff1)
      secQICnt <= {quietOffset2, 10'b0} + {beaconInt, 10'b0};
    else if ((quietCount2 == 8'h1) && quietElement2InValid_ff1)
      secQICnt <= {quietOffset2, 10'b0};
    else if (tick1us_p && (secQICnt != 26'h3ff_ffff))
      secQICnt <= secQICnt - 26'h1;
  end
  else
    secQICnt <= 26'h3ff_ffff;
end

// NAV counter is loaded with quiet duration when Quiet counter register is null.
//assign loadQuietDuration_p = ((priQICnt == 26'h0) || (secQICnt == 26'h0)) && tick1us_p;

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    loadQuietDuration_p <= 1'b0;
  else if ((priQICnt == 26'h0) || (secQICnt == 26'h0))
    loadQuietDuration_p <= tick1us_p;
  else 
    loadQuietDuration_p <= 1'b0;  
end

// Provide quiet duration to NAV
//assign quietDuration = (priQICnt == 26'h0) ? quietDuration1 : quietDuration2;
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    quietDuration <= 16'b0;
  else if (priQICnt == 26'h0)
    quietDuration <= quietDuration1;
  else 
    quietDuration <= quietDuration2;  
end

// Provide shortest impending Quiet interval to MAC Controller for TXOP calculation
assign selectQICnt = (priQICnt < secQICnt) ? priQICnt : secQICnt;
//assign impQICnt = (selectQICnt[25:20] > 6'h1) ? 16'hffff : selectQICnt[20:5];
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    impQICnt <= 16'b0;
  else if (selectQICnt[25:20] > 6'h1)
    impQICnt <= 16'hffff;
  else 
    impQICnt <= selectQICnt[20:5];  
end


// Monotonic counters
//////////////////////////////////////////////////////////////////////////////

// Monotonic counter 1
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    monotonicCounter1 <= 32'b0;
  else if (macCoreClkSoftRst_n == 1'b0)           // Synchronous Reset
    monotonicCounter1 <= 32'b0;
  else
    monotonicCounter1 <= monotonicCounter1 + 32'h1;
end

// Monotonic counter 2
always @ (posedge macLPClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    monotonicCounter2 <= 48'b0;
  else if (macCoreClkSoftRst_n == 1'b0)           // Synchronous Reset
    monotonicCounter2 <= 48'b0;
  else if (macLPClkSwitch)
    monotonicCounter2 <= monotonicCounter2 + 48'd31 + {48'b0, adjustLPInc};
  else if (tick1us_p)
    monotonicCounter2 <= monotonicCounter2 + 48'h1;
end

// Absolute timer interrupt mask. It avoids the generation of absTimer Interrupt after the reset. 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    absTimerInterruptMask <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)           // Synchronous Reset
    absTimerInterruptMask <= 1'b0;
  else if (tick1us_p)
    absTimerInterruptMask <= 1'b1;
end


always @ (posedge macLPClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                // Asynchronous Reset
    macLPClkSwitchDly <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)           // Synchronous Reset
    macLPClkSwitchDly <= 1'b0;
  else
    macLPClkSwitchDly <= macLPClkSwitch;
end

assign monotonicCounterLow2  = monotonicCounter2[31:0];
assign monotonicCounterHigh2 = monotonicCounter2[47:32];


// Absolute timer interrupt
// Foreach timer, the corresponding absTimiersInt (indicating a matching between the current monotonicCounter value and the programmed value)
// is generated based on three conditions :
// 1- When running on LowPower clock (32kHz), the comparaison is done masking the 5 LSB which corresponds to a matching with 32us accuracy.  
// 2- When running on Fast clock, the comparaison is done considering a complet matching between monotonic and programmed absTimer values and 
//    this comparaison is done once every 1us (tick1us_p).
// 3- A corner case must be handled when the switch from LowPower Clock and Fast clock. In this specifc case, on the first clock cycle of 
//    Fast clock (indicated by macLPClkSwitchDly && !macLPClkSwitch), 
//    the comparison is done as in case 1 but only if the 5 LSB of the monotonic timer is greater or equal to the five LSB of programmed absTimer.   


// Absolute Timer 0
assign absTimers0MSBMatch = (monotonicCounterLow2[31:5] == absTimerValue0[31:5]);
assign absTimersInt[0] = absTimers0MSBMatch && (macLPClkSwitch ||
                                                (macLPClkSwitchDly && (monotonicCounterLow2[4:0] >= absTimerValue0[4:0])) ||
                                                (monotonicCounterLow2[4:0] == absTimerValue0[4:0]));



// Absolute Timer 1
assign absTimers1MSBMatch = (monotonicCounterLow2[31:5] == absTimerValue1[31:5]);
assign absTimersInt[1] = absTimers1MSBMatch && (macLPClkSwitch ||
                                                (macLPClkSwitchDly && (monotonicCounterLow2[4:0] >= absTimerValue1[4:0])) ||
                                                (monotonicCounterLow2[4:0] == absTimerValue1[4:0]));

// Absolute Timer 2
assign absTimers2MSBMatch = (monotonicCounterLow2[31:5] == absTimerValue2[31:5]);
assign absTimersInt[2] = absTimers2MSBMatch && (macLPClkSwitch ||
                                                (macLPClkSwitchDly && (monotonicCounterLow2[4:0] >= absTimerValue2[4:0])) ||
                                                (monotonicCounterLow2[4:0] == absTimerValue2[4:0]));

// Absolute Timer 3
assign absTimers3MSBMatch = (monotonicCounterLow2[31:5] == absTimerValue3[31:5]);
assign absTimersInt[3] = absTimers3MSBMatch && (macLPClkSwitch ||
                                                (macLPClkSwitchDly && (monotonicCounterLow2[4:0] >= absTimerValue3[4:0])) ||
                                                (monotonicCounterLow2[4:0] == absTimerValue3[4:0]));


// Absolute Timer 4
assign absTimers4MSBMatch = (monotonicCounterLow2[31:5] == absTimerValue4[31:5]);
assign absTimersInt[4] = absTimers4MSBMatch && (macLPClkSwitch ||
                                                (macLPClkSwitchDly && (monotonicCounterLow2[4:0] >= absTimerValue4[4:0])) ||
                                                (monotonicCounterLow2[4:0] == absTimerValue4[4:0]));


// Absolute Timer 5
assign absTimers5MSBMatch = (monotonicCounterLow2[31:5] == absTimerValue5[31:5]);
assign absTimersInt[5] = absTimers5MSBMatch && (macLPClkSwitch ||
                                                (macLPClkSwitchDly && (monotonicCounterLow2[4:0] >= absTimerValue5[4:0])) ||
                                                (monotonicCounterLow2[4:0] == absTimerValue5[4:0]));

// Absolute Timer 6
assign absTimers6MSBMatch = (monotonicCounterLow2[31:5] == absTimerValue6[31:5]);
assign absTimersInt[6] = absTimers6MSBMatch && (macLPClkSwitch ||
                                                (macLPClkSwitchDly && (monotonicCounterLow2[4:0] >= absTimerValue6[4:0])) ||
                                                (monotonicCounterLow2[4:0] == absTimerValue6[4:0]));


// Absolute Timer 7
assign absTimers7MSBMatch = (monotonicCounterLow2[31:5] == absTimerValue7[31:5]);
assign absTimersInt[7] = absTimers7MSBMatch && (macLPClkSwitch ||
                                                (macLPClkSwitchDly && (monotonicCounterLow2[4:0] >= absTimerValue7[4:0])) ||
                                                (monotonicCounterLow2[4:0] == absTimerValue7[4:0]));


// Absolute Timer 8
assign absTimers8MSBMatch = (monotonicCounterLow2[31:5] == absTimerValue8[31:5]);
assign absTimersInt[8] = absTimers8MSBMatch && (macLPClkSwitch ||
                                                (macLPClkSwitchDly && (monotonicCounterLow2[4:0] >= absTimerValue8[4:0])) ||
                                                (monotonicCounterLow2[4:0] == absTimerValue8[4:0]));


// Absolute Timer 9
assign absTimers9MSBMatch = (monotonicCounterLow2[31:5] == absTimerValue9[31:5]);
assign absTimersInt[9] = absTimers9MSBMatch && (macLPClkSwitch ||
                                                (macLPClkSwitchDly && (monotonicCounterLow2[4:0] >= absTimerValue9[4:0])) ||
                                                (monotonicCounterLow2[4:0] == absTimerValue9[4:0]));

// FF logic for resync in inctrl
always @ (posedge macLPClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    impPriTBTT <= 1'b0;
    impSecTBTT <= 1'b0;
    impPriDTIM <= 1'b0;
    impSecDTIM <= 1'b0;
  end
  else if (macCoreClkSoftRst_n == 1'b0)    // Synchronous Reset
  begin
    impPriTBTT <= 1'b0;
    impSecTBTT <= 1'b0;
    impPriDTIM <= 1'b0;
    impSecDTIM <= 1'b0;
  end
  else
  begin
    impPriTBTT <= impPriTBTTInt;
    impSecTBTT <= impSecTBTTInt;
    impPriDTIM <= impPriDTIMInt;
    impSecDTIM <= impSecDTIMInt;
  end
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    olbcOFDM       <= 1'b0;
    olbcDSSS       <= 1'b0;
    timerTxTrigger <= 1'b0;
    timerRxTrigger <= 1'b0;
  end
  else if (macCoreClkSoftRst_n == 1'b0)    // Synchronous Reset
  begin
    olbcOFDM       <= 1'b0;
    olbcDSSS       <= 1'b0;
    timerTxTrigger <= 1'b0;
    timerRxTrigger <= 1'b0;
  end
  else
  begin
    olbcOFDM       <= olbcOFDMInt;
    olbcDSSS       <= olbcDSSSInt;
    timerTxTrigger <= timerTxTriggerInt;
    timerRxTrigger <= timerRxTriggerInt;
  end
end

always @ (posedge macLPClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    absTimers      <= 10'd0;
  else if (macCoreClkSoftRst_n == 1'b0 || !absTimerInterruptMask)    // Synchronous Reset
    absTimers      <= 10'd0;
  else if (tick1us_p || macLPClkSwitch || macLPClkSwitchDly)
    absTimers      <= absTimersInt;
  else
    absTimers      <= 10'd0;
end

// Debug port
//////////////////////////////////////////////////////////////////////////////
assign debugPortMACTimerUnit = {wakeupListenInterval_p,
                                earlyWakeup_p,
                                channelBusy,
                                navCfpMaxDurUpdate_p || loadQuietDuration_p,
                                moveToActive_p,
                                tickDMAEarlySlot_p,
                                tickEarlySlot_p,
                                tickSlot_p,
                                tickPIFS_p,
                                tickRIFS_p,
                                tickNullSIFS_p,
                                tickSIFS_p,
                                tickDMAEarlyTBTT_p,
                                tickEarlyTBTT_p,
                                tickTBTT_p,
                                tick1us_p
                                };

assign debugPortMACTimerUnit2 = {wakeupListenInterval_p,
                                 wakeupDTIM_p,
                                 earlyWakeup_p,
                                 moveToActive_p,
                                 moveToDoze_p,
                                 impPriTBTTInt,
                                 impPriDTIMInt,
                                 dtimCnt[2],
                                 dtimCnt[1],
                                 dtimCnt[0],
                                 dtimUpdate_p,
                                 dtimUpdatedBySW,
                                 1'b0,
                                 updateBeaconIntCnt_p,
                                 cfpUpdate_p,
                                 navCfpMaxDurUpdate_p
                                };

assign debugPortMACTimerUnit3 = {beaconIntCnt[15:7],
                                 updateBeaconIntCnt_p,
                                 dtimCnt[2:0],
                                 tickTBTT_p,
                                 impPriTBTTInt | impPriDTIMInt,
                                 dtimUpdate_p};


///////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////
// System Verilog Assertions
///////////////////////////////////////
`ifdef RW_ASSERT_ON
default clocking cb @(posedge macCoreClk); endclocking

//$rw_sva Checks DMA delay for tickDMAEarlySlot_p generation
property dmaDelayError_prop;
@(posedge macCoreClk)
  (macCoreIsActive) |-> ((txDMAProcDlyInMACClk + txChainMacDelayInMACClk) < (slotTimeInMACClk - 16'h1));
endproperty
dmaDelayError: assert property (disable iff (!macCoreClkHardRst_n) dmaDelayError_prop);

//$rw_sva Checks MAC delay for tickEarlySlot_p generation
property macDelayError_prop;
@(posedge macCoreClk)
  (macCoreIsActive) |-> (txChainMacDelayInMACClk < (slotTimeInMACClk - 16'h1));
endproperty
macDelayError: assert property (disable iff (!macCoreClkHardRst_n) macDelayError_prop);

//$rw_sva Checks PHY delay for tickSlot_p generation
property phySlotDelayError_prop;
@(posedge macCoreClk)
  (macCoreIsActive) |-> (txChainDelayInMACClk < (slotTimeInMACClk - 16'h1));
endproperty
phySlotDelayError: assert property (disable iff (!macCoreClkHardRst_n) phySlotDelayError_prop);

//$rw_sva Checks PHY delay for tickSIFS_p generation
property phySIFSDelayError_prop;
@(posedge macCoreClk)
  (macCoreIsActive) |-> (txChainDelayInMACClk < (sifsInMACClk - 16'h1));
endproperty
phySIFSDelayError: assert property (disable iff (!macCoreClkHardRst_n) phySIFSDelayError_prop);

`endif // RW_ASSERT_ON


endmodule