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
// Description      : Top level of backoff module
//                    
// Simulation Notes : 
// Synthesis Notes  :
// Application Note :                                                       
// Simulator        :                                                       
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

`default_nettype wire
module backoff( 
            //$port_g Clock and Reset
            input  wire            macCoreClk,              // MAC core clock      
            input  wire            macCoreClkHardRst_n,     // MAC core clock hard reset
            
            input  wire            macCoreClkSoftRst_n,     // MAC core clock soft reset
            
            //$port_g MacController Module interface
            input  wire  [15:0]    acMOT,                   // Current AC Medium Occupancy timer
            input  wire            retryType,               // Indicates the type of retry
                                                            // 0 : Short Retry Limit
                                                            // 1 : Long Retry Limit
            input  wire            retry_p,                 // Indicates that the current frame has to be retried
            input  wire            txSuccessful_p,          // Tx Success
            input  wire            retryLTReached_p,        // Indicates that the retry limit has been reached
            input  wire            txInProgress,            // Tx is ongoing

            output wire  [ 3:0]    txDmaState,              // DMA state for the active channel.
            output wire  [15:0]    txOpLimit,               // TXOP Limit of the active channel.
            output wire            backOffDone_p,           // Indicates when a backOff has expired
            output wire            startTxFrameExGated,     // Start Transmission from register gated (set only when the startTxAC won the medium) 
            
            //$port_g RxController Module interface
            input  wire            bcnRcved_p,              // Beacon received

            //$port_g dmaEngine Interface
            output wire            trigTxAC0,               // Backoff done
            output wire            trigTxAC1,               // Backoff done
            output wire            trigTxAC2,               // Backoff done
            output wire            trigTxAC3,               // Backoff done
            output wire            trigTxBcn,               // Backoff done  
   
            //$port_g interrupt controller Interface
            output wire            ac3ProtTrigger,           // protocol trigger interruption
            output wire            ac2ProtTrigger,           // protocol trigger interruption
            output wire            ac1ProtTrigger,           // protocol trigger interruption
            output wire            ac0ProtTrigger,           // protocol trigger interruption

            //$port_g macCSReg Interface
            input  wire            ap,                      // indicate the CORE is setup as an AP
            input  wire  [ 3:0]    currentState,            // core current state
            input  wire  [ 3:0]    cwMax0,                  // min Contention Window
            input  wire  [ 3:0]    cwMin0,                  // max Contention Window
            input  wire  [ 3:0]    cwMax1,                  // min Contention Window
            input  wire  [ 3:0]    cwMin1,                  // max Contention Window
            input  wire  [ 3:0]    cwMax2,                  // min Contention Window
            input  wire  [ 3:0]    cwMin2,                  // max Contention Window
            input  wire  [ 3:0]    cwMax3,                  // min Contention Window
            input  wire  [ 3:0]    cwMin3,                  // max Contention Window
            input  wire  [ 3:0]    txAC3State,              // AC3 state
            input  wire  [ 3:0]    txAC2State,              // AC2 state 
            input  wire  [ 3:0]    txAC1State,              // AC1 state 
            input  wire  [ 3:0]    txAC0State,              // AC0 state 
            input  wire  [ 3:0]    txBcnState,              // Beacon state 
            input  wire            startTxFrameEx,          // Start Tx frame
            input  wire  [ 1:0]    startTxAC,               // Start Tx AC
            input  wire            bssType,                 // bsstype
            input  wire  [ 7:0]    edcaTriggerTimer,        // HCCA trigger Timer 
            input  wire  [ 7:0]    slotTime,                // Slot time
            input  wire  [15:0]    txOpLimit0,              // Txop registers       
            input  wire  [15:0]    txOpLimit1,              // Txop registers       
            input  wire  [15:0]    txOpLimit2,              // Txop registers       
            input  wire  [15:0]    txOpLimit3,              // Txop registers       
            input  wire            setac3HasData,           // set ac3 has data
            input  wire            setac2HasData,           // set ac2 has data
            input  wire            setac1HasData,           // set ac1 has data
            input  wire            setac0HasData,           // set ac0 has data
            input  wire            clearac3HasData,         // clear ac3 has data
            input  wire            clearac2HasData,         // clear ac2 has data
            input  wire            clearac1HasData,         // clear ac1 has data
            input  wire            clearac0HasData,         // clear ac0 has data
            
            output wire            statussetac3HasData,     // ac3 has data status
            output wire            statussetac2HasData,     // ac2 has data status
            output wire            statussetac1HasData,     // ac1 has data status
            output wire            statussetac0HasData,     // ac0 has data status
            input  wire  [ 1:0]    backoffOffset,           // backoff offset
            output wire  [ 3:0]    currentCW0,              // current Contetion window value
            output wire  [ 3:0]    currentCW1,              // current Contetion window value 
            output wire  [ 3:0]    currentCW2,              // current Contetion window value
            output wire  [ 3:0]    currentCW3,              // current Contetion window value
            output wire  [15:0]    ac1MOT,                  // medium occupancy timer of AC0
            output wire  [15:0]    ac0MOT,                  // medium occupancy timer of AC1
            output wire  [15:0]    ac3MOT,                  // medium occupancy timer of AC2
            output wire  [15:0]    ac2MOT,                  // medium occupancy timer of AC3
            output wire  [ 7:0]    ac3QSRC,                 // short retry count on AC0
            output wire  [ 7:0]    ac2QSRC,                 // short retry count on AC1
            output wire  [ 7:0]    ac1QSRC,                 // short retry count on AC2
            output wire  [ 7:0]    ac0QSRC,                 // short retry count on AC3
            output wire  [ 7:0]    ac3QLRC,                 // long retry count on AC0
            output wire  [ 7:0]    ac2QLRC,                 // long retry count on AC1
            output wire  [ 7:0]    ac1QLRC,                 // long retry count on AC2
            output wire  [ 7:0]    ac0QLRC,                 // long retry count on AC3
            output wire  [ 2:0]    activeAC,                // Indicates which AC is currently selected.
            output wire  [ 7:0]    hccaTriggerTimer,        // EDCA trigger Timer 
    
            //$port_g macPhyIf Interface
            input  wire            macPhyIfRxCca,           // CCA

            //$port_g NAV Interface
            input  wire            channelBusy,             // Channel Busy
            
            //$port_g Coex interface
          `ifdef RW_WLAN_COEX_EN
            input                  coexWlanTxAbort,         // Requests from external arbiter abort all on-going transmission
          `endif // RW_WLAN_COEX_EN

            //$port_g Timer Interface
            input  wire            noBeaconTxPeriod,        // Period during which the BEACON will not be transmitted
            input  wire [ 7:0]     slotCnt,                 // Slot counter
            input  wire            tickDMAEarlySlot_p,      // Pulse prior of tickDMAEarlySlot_p
            input  wire            tickEarlySlot_p,         // Pulse prior of tickSlot_p
            input  wire            aifsFlag0,               // Flag when AIFS0 over
            input  wire            aifsFlag1,               // Flag when AIFS1 over
            input  wire            aifsFlag2,               // Flag when AIFS2 over
            input  wire            aifsFlag3,               // Flag when AIFS3 over
            input  wire            eifsFlag0,               // Flag when EIFS0 over
            input  wire            eifsFlag1,               // Flag when EIFS1 over
            input  wire            eifsFlag2,               // Flag when EIFS2 over
            input  wire            eifsFlag3,               // Flag when EIFS3 over
            input  wire [11:0]     aifsCnt0,                // AIFS0 counter
            input  wire [11:0]     aifsCnt1,                // AIFS1 counter
            input  wire [11:0]     aifsCnt2,                // AIFS2 counter
            input  wire [11:0]     aifsCnt3,                // AIFS3 counter
            input  wire            tickEarlyTBTT_p,         // Pulse every TBTTs
            input  wire            tickDMAEarlyTBTT_p,      // Pulse prior of tickEarlyTBTT_p
            input  wire            tickSlot1us_p,           // microsecond tick aligned on slotcnt
            input  wire            tickSlot_p,              // slot indicator      
            
            //$port_g Debug interface
            output wire [15:0]     debugPortBackoff,        // debug port 
            output wire [15:0]     debugPortBackoff2,
            output wire [15:0]     debugPortBackoff3

            
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
wire            backoffEnable;           // Block Enable 


wire [18:0]     pseudoRandomNumber;      // Generated pseudo random number

wire            backoffCntLoad0;         // Load backoff counter
wire            backoffCntLoad1;         // Load backoff counter
wire            backoffCntLoad2;         // Load backoff counter
wire            backoffCntLoad3;         // Load backoff counter

wire [15:0]     backoffCnt0;             // backoff counter
wire [15:0]     backoffCnt1;             // backoff counter
wire [15:0]     backoffCnt2;             // backoff counter
wire [15:0]     backoffCnt3;             // backoff counter

wire            backoffCntEnable0;       // Enable backoff counter
wire            backoffCntEnable1;       // Enable backoff counter
wire            backoffCntEnable2;       // Enable backoff counter
wire            backoffCntEnable3;       // Enable backoff counter

wire            backoffDone0;            // Enable backoff done indicator
wire            backoffDone1;            // Enable backoff done indicator
wire            backoffDone2;            // Enable backoff done indicator
wire            backoffDone3;            // Enable backoff done indicator

wire            InternalColl0_p;         // Internal Collision Indicator
wire            InternalColl1_p;         // Internal Collision Indicator
wire            InternalColl2_p;         // Internal Collision Indicator
wire            InternalColl3_p;         // Internal Collision Indicator

wire            txFailed0_p;             // Tx Failed
wire            txFailed1_p;             // Tx Failed
wire            txFailed2_p;             // Tx Failed
wire            txFailed3_p;             // Tx Failed

wire            txSuccessful0_p;         // Tx Success
wire            txSuccessful1_p;         // Tx Success
wire            txSuccessful2_p;         // Tx Success
wire            txSuccessful3_p;         // Tx Success

wire            retryLtReached0;         // retry limit over
wire            retryLtReached1;         // retry limit over
wire            retryLtReached2;         // retry limit over
wire            retryLtReached3;         // retry limit over

wire            ac3ProtTriggerFlagReset; // ac3 protocol trigger reset
wire            ac2ProtTriggerFlagReset; // ac2 protocol trigger reset
wire            ac1ProtTriggerFlagReset; // ac1 protocol trigger reset
wire            ac0ProtTriggerFlagReset; // ac0 protocol trigger reset


wire            aifsQueue1;              // AIFS tick for queue 1
wire            macPhyIfRxCcaGated;      // asserted in IBSS when Beacon queue is programmed
wire            TBTTFlag;                // asserted in IBSS when Beacon queue is programmed

reg  [ 3:0]     currentStateSaved;       // save slotCnt
wire            currentStateEvent;       // save slotCnt1

wire  [3:0]     txMuxedState;

wire            resetBackoffACSel;       // Reset backoffACSel module

wire  [2:0]     backoffCtrl0Cs;          // backoffCtrl0 FSM Current State
wire  [2:0]     backoffCtrl1Cs;          // backoffCtrl1 FSM Current State
wire  [2:0]     backoffCtrl2Cs;          // backoffCtrl2 FSM Current State
wire  [2:0]     backoffCtrl3Cs;          // backoffCtrl3 FSM Current State


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


// debug port
assign debugPortBackoff[1:0] = activeAC[1:0];
assign debugPortBackoff[2]   = trigTxAC0;
assign debugPortBackoff[3]   = trigTxAC1;
assign debugPortBackoff[4]   = trigTxAC2;
assign debugPortBackoff[5]   = trigTxAC3;
assign debugPortBackoff[6]   = trigTxBcn;
assign debugPortBackoff[7]   = ac0ProtTrigger;
assign debugPortBackoff[8]   = ac1ProtTrigger;
assign debugPortBackoff[9]   = ac2ProtTrigger;
assign debugPortBackoff[10]  = ac3ProtTrigger;
assign debugPortBackoff[11]  = InternalColl0_p;
assign debugPortBackoff[12]  = InternalColl1_p;
assign debugPortBackoff[13]  = InternalColl2_p;
assign debugPortBackoff[14]  = backOffDone_p;
assign debugPortBackoff[15]  = TBTTFlag;


// Assign startTxFrameEx to startTxFrameExGated only when the AC defined in startTxAC won the medium
assign startTxFrameExGated = (startTxAC == activeAC[1:0]) ? startTxFrameEx : 1'b0;

// Enable when the MAC is active
assign backoffEnable = (currentState == 4'b0011) ? 1'b1 : 1'b0;

// Muxing queue 1 input depending on the BSS type
assign aifsQueue1            = (bssType) ? aifsFlag1  : tickEarlyTBTT_p;

assign currentStateEvent     = ((currentStateSaved == 4'b0) && (currentState == 4'h1  || currentState == 4'h3)) ? 1'b1 : 1'b0;

// a pulse when the core move to active event
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
  begin
    currentStateSaved <= 4'b0;
  end
  else if (!macCoreClkSoftRst_n)
  begin
    currentStateSaved <= 4'b0;
  end
  else
  begin
    currentStateSaved <=  currentState;
  end
end


assign txMuxedState = ((bssType == 1'b0) && (txBcnState != 4'b0001)) ? txBcnState : txAC1State;


assign resetBackoffACSel = macCoreClkSoftRst_n && backoffEnable;

// Instanciation of backoffACSel
// Name of the instance : U_backoffACSel
// Name of the file containing this module : backoffACSel.v
backoffACSel U_backoffACSel (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (resetBackoffACSel),
		.bcnRcved_p             (bcnRcved_p),
		.acMOT                  (acMOT),
		.retryType              (retryType),
		.retry_p                (retry_p),
		.txSuccessful_p         (txSuccessful_p),
		.retryLTReached_p       (retryLTReached_p),
		.txInProgress           (txInProgress),
		.txDmaState             (txDmaState),
		.txOpLimit              (txOpLimit),
		.backOffDone_p          (backOffDone_p),
		.noBeaconTxPeriod       (noBeaconTxPeriod),
		.tickDMAEarlySlot_p     (tickDMAEarlySlot_p),
		.tickEarlySlot_p        (tickEarlySlot_p),
		.tickEarlyTBTT_p        (tickEarlyTBTT_p),
		.tickDMAEarlyTBTT_p     (tickDMAEarlyTBTT_p),
		.tickSlot_p             (tickSlot_p),
		.macPhyIfRxCca          (macPhyIfRxCca),
		.channelBusy            (channelBusy),
  `ifdef RW_WLAN_COEX_EN
		.coexWlanTxAbort        (coexWlanTxAbort),
  `endif // RW_WLAN_COEX_EN
		.txOpLimit0             (txOpLimit0),
		.txOpLimit1             (txOpLimit1),
		.txOpLimit2             (txOpLimit2),
		.txOpLimit3             (txOpLimit3),
		.ac0MOT                 (ac0MOT),
		.ac1MOT                 (ac1MOT),
		.ac3MOT                 (ac3MOT),
		.ac2MOT                 (ac2MOT),
		.ac3QSRC                (ac3QSRC),
		.ac2QSRC                (ac2QSRC),
		.ac1QSRC                (ac1QSRC),
		.ac0QSRC                (ac0QSRC),
		.ac3QLRC                (ac3QLRC),
		.ac2QLRC                (ac2QLRC),
		.ac1QLRC                (ac1QLRC),
		.ac0QLRC                (ac0QLRC),
		.activeAC               (activeAC),
		.ap                     (ap),
		.txAC3State             (txAC3State),
		.txAC2State             (txAC2State),
		.txAC1State             (txAC1State),
		.txAC0State             (txAC0State),
		.txBcnState             (txBcnState),
		.startTxFrameEx         (startTxFrameEx),
		.startTxAC              (startTxAC),
		.bssType                (bssType),
		.trigTxAC0              (trigTxAC0),
		.trigTxAC1              (trigTxAC1),
		.trigTxAC2              (trigTxAC2),
		.trigTxAC3              (trigTxAC3),
		.trigTxBcn              (trigTxBcn),
		.backoffDone0           (backoffDone0),
		.backoffDone1           (backoffDone1),
		.backoffDone2           (backoffDone2),
		.backoffDone3           (backoffDone3),
		.retryLtReached0        (retryLtReached0),
		.retryLtReached1        (retryLtReached1),
		.retryLtReached2        (retryLtReached2),
		.retryLtReached3        (retryLtReached3),
		.txFailed0_p            (txFailed0_p),
		.txFailed1_p            (txFailed1_p),
		.txFailed2_p            (txFailed2_p),
		.txFailed3_p            (txFailed3_p),
		.txSuccessful0_p        (txSuccessful0_p),
		.txSuccessful1_p        (txSuccessful1_p),
		.txSuccessful2_p        (txSuccessful2_p),
		.txSuccessful3_p        (txSuccessful3_p),
		.InternalColl0_p        (InternalColl0_p),
		.InternalColl1_p        (InternalColl1_p),
		.InternalColl2_p        (InternalColl2_p),
		.InternalColl3_p        (InternalColl3_p),
		.macPhyIfRxCcaGated     (macPhyIfRxCcaGated),
		.TBTTFlag               (TBTTFlag)
		);







// Instanciation of backoffProtTrig
// Name of the instance : U_backoffProtTrig
// Name of the file containing this module : backoffProtTrig.v
backoffProtTrig U_backoffProtTrig (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
		.backoffEnable          (backoffEnable),
		.currentStateEvent      (currentStateEvent),
		.txInProgress           (txInProgress),
		.txAC3State             (txAC3State),
		.txAC2State             (txAC2State),
		.txAC1State             (txAC1State),
		.txAC0State             (txAC0State),
		.backoffCnt0            (backoffCnt0),
		.backoffCnt1            (backoffCnt1),
		.backoffCnt2            (backoffCnt2),
		.backoffCnt3            (backoffCnt3),
		.aifsCnt0               (aifsCnt0),
		.aifsCnt1               (aifsCnt1),
		.aifsCnt2               (aifsCnt2),
		.aifsCnt3               (aifsCnt3),
		.slotCnt                (slotCnt),
		.tickSlot1us_p          (tickSlot1us_p),
		.hccaTriggerTimer       (hccaTriggerTimer),
		.edcaTriggerTimer       (edcaTriggerTimer),
		.slotTime               (slotTime),
		.setac3HasData          (setac3HasData),
		.setac2HasData          (setac2HasData),
		.setac1HasData          (setac1HasData),
		.setac0HasData          (setac0HasData),
		.clearac3HasData        (clearac3HasData),
		.clearac2HasData        (clearac2HasData),
		.clearac1HasData        (clearac1HasData),
		.clearac0HasData        (clearac0HasData),
		.statussetac3HasData    (statussetac3HasData),
		.statussetac2HasData    (statussetac2HasData),
		.statussetac1HasData    (statussetac1HasData),
		.statussetac0HasData    (statussetac0HasData),
		.ac3ProtTriggerFlagReset(ac3ProtTriggerFlagReset),
		.ac2ProtTriggerFlagReset(ac2ProtTriggerFlagReset),
		.ac1ProtTriggerFlagReset(ac1ProtTriggerFlagReset),
		.ac0ProtTriggerFlagReset(ac0ProtTriggerFlagReset),
		.ac3ProtTrigger         (ac3ProtTrigger),
		.ac2ProtTrigger         (ac2ProtTrigger),
		.ac1ProtTrigger         (ac1ProtTrigger),
		.ac0ProtTrigger         (ac0ProtTrigger)
		);




// Instanciation of backoffPRNG
// Name of the instance : U_backoffPRNG
// Name of the file containing this module : backoffPRNG.v
backoffPRNG U_backoffPRNG (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
		.backOffDone_p          (backOffDone_p),
		.pseudoRandomNumber     (pseudoRandomNumber)
		);



// Instanciation of backoffCnt
// Name of the instance : U_backoffCnt
// Name of the file containing this module : backoffCnt.v
backoffCnt #(.BACKOFFOFF(0),.CWRESET(4)) U_backoffCnt0 (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
		.pseudoRandomNumber     (pseudoRandomNumber),
		.backoffCntLoad         (backoffCntLoad0),
		.backoffCntEnable       (backoffCntEnable0),
		.retryLtReached         (retryLtReached0),
		.InternalColl           (InternalColl0_p),
		.backoffCntValue        (backoffCnt0),
		.txFailed_p             (txFailed0_p),
		.currentStateEvent      (currentStateEvent),
		.txSuccessful_p         (txSuccessful0_p),
		.tickSlot_p             (tickSlot_p),
		.cwMin                  (cwMin0),
		.cwMax                  (cwMax0),
		.backoffOffset          (backoffOffset),
		.currentCW              (currentCW0)
		);

// Instanciation of backoffCtrl
// Name of the instance : U_backoffCtrl
// Name of the file containing this module : backoffCtrl.v
backoffCtrl U_backoffCtrl0 (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
		.backoffEnable          (backoffEnable),
		.txInProgress           (txInProgress),
		.txACState              (txAC0State),
		.acHasData              (statussetac0HasData),
		.macPhyIfRxCca          (macPhyIfRxCcaGated),
		.channelBusy            (channelBusy),
		.backoffCnt             (backoffCnt0),
		.txFailed_p             (txFailed0_p),
		.txSuccessful_p         (txSuccessful0_p),
		.retryLTReached_p       (retryLTReached_p),
		.aifsFlag               (aifsFlag0),
		.eifsFlag               (eifsFlag0),
		.tickDMAEarlySlot_p     (tickDMAEarlySlot_p),
		.backOffDone_p          (backOffDone_p),
		.backoffDone            (backoffDone0),
		.acProtTriggerFlagReset (ac0ProtTriggerFlagReset),
  `ifdef RW_WLAN_COEX_EN
		.coexWlanTxAbort        (coexWlanTxAbort),
  `endif // RW_WLAN_COEX_EN
		.backoffCntLoad         (backoffCntLoad0),
		.backoffCntEnable       (backoffCntEnable0),
		.backoffCtrlCs          (backoffCtrl0Cs)
		);


// Instanciation of backoffCnt
// Name of the instance : U_backoffCnt
// Name of the file containing this module : backoffCnt.v
backoffCnt #(.BACKOFFOFF(1),.CWRESET(4)) U_backoffCnt1 (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
		.pseudoRandomNumber     (pseudoRandomNumber),
		.backoffCntLoad         (backoffCntLoad1),
		.backoffCntEnable       (backoffCntEnable1),
		.retryLtReached         (retryLtReached1),
		.InternalColl           (InternalColl1_p),
		.backoffCntValue        (backoffCnt1),
		.txFailed_p             (txFailed1_p),
		.currentStateEvent      (currentStateEvent),
		.txSuccessful_p         (txSuccessful1_p),
		.tickSlot_p             (tickSlot_p),
		.cwMin                  (cwMin1),
		.cwMax                  (cwMax1),
		.backoffOffset          (backoffOffset),
		.currentCW              (currentCW1)

		);

// Instanciation of backoffCtrl
// Name of the instance : U_backoffCtrl
// Name of the file containing this module : backoffCtrl.v
backoffCtrl U_backoffCtrl1 (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
		.backoffEnable          (backoffEnable),
		.txInProgress           (txInProgress),
		.txACState              (txMuxedState),
		.acHasData              (statussetac1HasData),
		.macPhyIfRxCca          (macPhyIfRxCca),
		.channelBusy            (channelBusy),
		.backoffCnt             (backoffCnt1),
		.txFailed_p             (txFailed1_p),
		.txSuccessful_p         (txSuccessful1_p),
		.retryLTReached_p       (retryLTReached_p),
		.aifsFlag               (aifsQueue1),
		.eifsFlag               (eifsFlag1),
		.tickDMAEarlySlot_p     (tickDMAEarlySlot_p),
		.backOffDone_p          (backOffDone_p),
		.backoffDone            (backoffDone1),
		.acProtTriggerFlagReset (ac1ProtTriggerFlagReset),
  `ifdef RW_WLAN_COEX_EN
		.coexWlanTxAbort        (coexWlanTxAbort),
  `endif // RW_WLAN_COEX_EN
		.backoffCntLoad         (backoffCntLoad1),
		.backoffCntEnable       (backoffCntEnable1),
		.backoffCtrlCs          (backoffCtrl1Cs)
		);

// Instanciation of backoffCnt
// Name of the instance : U_backoffCnt
// Name of the file containing this module : backoffCnt.v
backoffCnt #(.BACKOFFOFF(2),.CWRESET(3)) U_backoffCnt2 (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
		.pseudoRandomNumber     (pseudoRandomNumber),
		.backoffCntLoad         (backoffCntLoad2),
		.backoffCntEnable       (backoffCntEnable2),
		.retryLtReached         (retryLtReached2),
		.InternalColl           (InternalColl2_p),
		.backoffCntValue        (backoffCnt2),
		.txFailed_p             (txFailed2_p),
		.currentStateEvent      (currentStateEvent),
		.txSuccessful_p         (txSuccessful2_p),
		.tickSlot_p             (tickSlot_p),
		.cwMin                  (cwMin2),
		.cwMax                  (cwMax2),
		.backoffOffset          (backoffOffset),
		.currentCW              (currentCW2)
		);

// Instanciation of backoffCtrl
// Name of the instance : U_backoffCtrl
// Name of the file containing this module : backoffCtrl.v
backoffCtrl U_backoffCtrl2 (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
		.backoffEnable          (backoffEnable),
		.txInProgress           (txInProgress),
		.txACState              (txAC2State),
		.acHasData              (statussetac2HasData),
		.macPhyIfRxCca          (macPhyIfRxCca),
		.channelBusy            (channelBusy),
		.backoffCnt             (backoffCnt2),
		.txFailed_p             (txFailed2_p),
		.txSuccessful_p         (txSuccessful2_p),
		.retryLTReached_p       (retryLTReached_p),
		.aifsFlag               (aifsFlag2),
		.eifsFlag               (eifsFlag2),
		.tickDMAEarlySlot_p     (tickDMAEarlySlot_p),
		.backOffDone_p          (backOffDone_p),
		.backoffDone            (backoffDone2),
		.acProtTriggerFlagReset (ac2ProtTriggerFlagReset),
  `ifdef RW_WLAN_COEX_EN
		.coexWlanTxAbort        (coexWlanTxAbort),
  `endif // RW_WLAN_COEX_EN
		.backoffCntLoad         (backoffCntLoad2),
		.backoffCntEnable       (backoffCntEnable2),
		.backoffCtrlCs          (backoffCtrl2Cs)
		);
    
// Instanciation of backoffCnt
// Name of the instance : U_backoffCnt
// Name of the file containing this module : backoffCnt.v
backoffCnt #(.BACKOFFOFF(3),.CWRESET(2)) U_backoffCnt3 (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
		.pseudoRandomNumber     (pseudoRandomNumber),
		.backoffCntLoad         (backoffCntLoad3),
		.backoffCntEnable       (backoffCntEnable3),
		.retryLtReached         (retryLtReached3),
		.InternalColl           (InternalColl3_p),
		.backoffCntValue        (backoffCnt3),
		.txFailed_p             (txFailed3_p),
		.currentStateEvent      (currentStateEvent),
		.txSuccessful_p         (txSuccessful3_p),
		.tickSlot_p             (tickSlot_p),
		.cwMin                  (cwMin3),
		.cwMax                  (cwMax3),
		.backoffOffset          (backoffOffset),
		.currentCW              (currentCW3)
		);

// Instanciation of backoffCtrl
// Name of the instance : U_backoffCtrl
// Name of the file containing this module : backoffCtrl.v
backoffCtrl U_backoffCtrl3 (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
		.backoffEnable          (backoffEnable),
		.txInProgress           (txInProgress),
		.txACState              (txAC3State),
		.acHasData              (statussetac3HasData),
		.macPhyIfRxCca          (macPhyIfRxCca),
		.channelBusy            (channelBusy),
		.backoffCnt             (backoffCnt3),
		.txFailed_p             (txFailed3_p),
		.txSuccessful_p         (txSuccessful3_p),
		.retryLTReached_p       (retryLTReached_p),
		.aifsFlag               (aifsFlag3),
		.eifsFlag               (eifsFlag3),
		.tickDMAEarlySlot_p     (tickDMAEarlySlot_p),
		.backOffDone_p          (backOffDone_p),
		.backoffDone            (backoffDone3),
		.acProtTriggerFlagReset (ac3ProtTriggerFlagReset),
  `ifdef RW_WLAN_COEX_EN
		.coexWlanTxAbort        (coexWlanTxAbort),
  `endif // RW_WLAN_COEX_EN
		.backoffCntLoad         (backoffCntLoad3),
		.backoffCntEnable       (backoffCntEnable3),
 		.backoffCtrlCs          (backoffCtrl3Cs)
		);

assign debugPortBackoff3 = {backoffEnable,
                            (txAC3State != 4'b0010),
                            statussetac3HasData,
                            backoffCtrl3Cs,
                            backoffCnt3[2:0],
                            aifsFlag3,
                            tickDMAEarlySlot_p,
                            tickSlot_p,
                            backOffDone_p,
                            backoffDone3,
                            backoffCntLoad3,
                            backoffCntEnable3}; 

assign debugPortBackoff2 = {backoffEnable,
                            (txAC2State != 4'b0010),
                            statussetac2HasData,
                            backoffCtrl2Cs,
                            backoffCnt2[2:0],
                            aifsFlag2,
                            tickDMAEarlySlot_p,
                            tickSlot_p,
                            backOffDone_p,
                            backoffDone2,
                            backoffCntLoad2,
                            backoffCntEnable2}; 


///////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////
// System Verilog Assertions
///////////////////////////////////////


`ifdef RW_ASSERT_ON
//$rw_sva Check for BackoffDone are mutuallly exclusive
property backoffDone_exclusive0_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  trigTxAC0 |->!(trigTxAC1 | trigTxAC2 | trigTxAC3);
endproperty

backoffDone_exclusive0: assert property (backoffDone_exclusive0_prop); 

//$rw_sva Check for BackoffDone are mutuallly exclusive
property backoffDone_exclusive1_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  trigTxAC1 |->!(trigTxAC0 | trigTxAC2 | trigTxAC3);
endproperty

backoffDone_exclusive1: assert property (backoffDone_exclusive1_prop); 

//$rw_sva Check for BackoffDone are mutuallly exclusive
property backoffDone_exclusive2_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  trigTxAC2 |->!(trigTxAC0 | trigTxAC1 | trigTxAC3);
endproperty

backoffDone_exclusive2: assert property (backoffDone_exclusive2_prop); 

//$rw_sva Check for BackoffDone are mutuallly exclusive
property backoffDone_exclusive3_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  trigTxAC3 |->!(trigTxAC0 | trigTxAC1 | trigTxAC2);
endproperty

backoffDone_exclusive3: assert property (backoffDone_exclusive3_prop); 

//$rw_sva Check for a collision match at least one backoff done
property collision_means_trigTxAC0rop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  InternalColl0_p |=> (trigTxAC1 | trigTxAC2 | trigTxAC3 | trigTxBcn);
endproperty

collision_means_backoffDone0: assert property (collision_means_trigTxAC0rop); 

//$rw_sva Check for a collision match at least one backoff done
property collision_means_trigTxAC1_interalrop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  InternalColl1_p |=> (trigTxAC0 | trigTxAC2 | trigTxAC3 | trigTxBcn);
endproperty

collision_means_backoffDone1: assert property (collision_means_trigTxAC1_interalrop); 

//$rw_sva Check for a collision match at least one backoff done
property collision_means_trigTxAC2rop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  InternalColl2_p |=> (trigTxAC0 | trigTxAC1 | trigTxAC3 | trigTxBcn);
endproperty

collision_means_backoffDone2: assert property (collision_means_trigTxAC2rop); 

//$rw_sva Check for a collision match at least one backoff done
property collision_means_trigTxAC3rop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  InternalColl3_p |=> (trigTxAC0 | trigTxAC1 | trigTxAC2 | trigTxBcn);
endproperty

collision_means_backoffDone3: assert property (collision_means_trigTxAC3rop); 

//$rw_sva Check there is a single retrylt at a time
property retryLT_exclusive0_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  retryLtReached0 |-> !(retryLtReached1 | retryLtReached2 | retryLtReached3);
endproperty

retryLT_exclusive0: assert property (retryLT_exclusive0_prop); 

//$rw_sva Check there is a single retrylt at a time
property retryLT_exclusive1_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  retryLtReached1 |-> !(retryLtReached0 | retryLtReached2 | retryLtReached3);
endproperty

retryLT_exclusive1: assert property (retryLT_exclusive1_prop); 

//$rw_sva Check there is a single retrylt at a time
property retryLT_exclusive2_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  retryLtReached2 |-> !(retryLtReached0 | retryLtReached1 | retryLtReached3);
endproperty

retryLT_exclusive2: assert property (retryLT_exclusive2_prop); 


//$rw_sva Check there is a single retrylt at a time
property retryLT_exclusive3_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  retryLtReached3 |-> !(retryLtReached0 | retryLtReached1 | retryLtReached2);
endproperty

retryLT_exclusive3: assert property (retryLT_exclusive3_prop); 


//$rw_sva Check ac0ProtTrigger is a pulse
property ac0ProtTrigger_pulse_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  ac0ProtTrigger |=> !ac0ProtTrigger;
endproperty

ac0ProtTrigger_pulse: assert property (ac0ProtTrigger_pulse_prop); 

//$rw_sva Check ac1ProtTrigger is a pulse
property ac1ProtTrigger_pulse_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  ac1ProtTrigger |=> !ac1ProtTrigger;
endproperty

ac1ProtTrigger_pulse: assert property (ac1ProtTrigger_pulse_prop); 

//$rw_sva Check ac2ProtTrigger is a pulse
property ac2ProtTrigger_pulse_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  ac2ProtTrigger |=> !ac2ProtTrigger;
endproperty

ac2ProtTrigger_pulse: assert property (ac2ProtTrigger_pulse_prop); 

//$rw_sva Check ac3ProtTrigger is a pulse
property ac3ProtTrigger_pulse_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  ac3ProtTrigger |=> !ac3ProtTrigger;
endproperty

ac3ProtTrigger_pulse: assert property (ac3ProtTrigger_pulse_prop); 

//$rw_sva Check ac0ProtTrigger is triggered only when the queue has data
property ac0ProtTriggerWhenHasData_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  ac0ProtTrigger |-> statussetac0HasData;
endproperty

ac0ProtTriggerWhenHasData: assert property (ac0ProtTriggerWhenHasData_prop); 

//$rw_sva Check ac0ProtTrigger is triggered only when the queue has data
property ac1ProtTriggerWhenHasData_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  ac1ProtTrigger |-> statussetac1HasData;
endproperty

ac1ProtTriggerWhenHasData: assert property (ac1ProtTriggerWhenHasData_prop); 

//$rw_sva Check ac0ProtTrigger is triggered only when the queue has data
property ac2ProtTriggerWhenHasData_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  ac2ProtTrigger |-> statussetac2HasData;
endproperty

ac2ProtTriggerWhenHasData: assert property (ac2ProtTriggerWhenHasData_prop); 

//$rw_sva Check ac0ProtTrigger is triggered only when the queue has data
property ac3ProtTriggerWhenHasData_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  ac3ProtTrigger |-> statussetac3HasData;
endproperty

ac3ProtTriggerWhenHasData: assert property (ac3ProtTriggerWhenHasData_prop); 

`endif // RW_ASSERT_ON


endmodule
