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
// Description      : 
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

module backoffCtrl( 
            //$port_g Clock and Reset
            input  wire            macCoreClk,              // mac core clock      
            input  wire            macCoreClkHardRst_n,     // mac core clock reset

            input  wire            macCoreClkSoftRst_n,     // MAC core clock soft reset
            
            //$port_g macController Interface
            input  wire            backoffEnable,           // Block Enable 
            input  wire            txInProgress,            // Tx is ongoing
            
            input  wire            acHasData,
            input  wire [3:0]      txACState,
            
            //$port_g macPhyIf Interface
            input wire             macPhyIfRxCca,           // CCA

            //$port_g NAV Interface
            input wire             channelBusy,             // Channel Busy
            
            //$port_g macController Interface
            input  wire [15:0]     backoffCnt,              // backoff counter
            input  wire            txFailed_p,              // Tx failed
            input  wire            txSuccessful_p,          // Tx Success
            input  wire            retryLTReached_p,        // Indicates that the retry limit has been reached
            
            //$port_g Timer Interface
            input  wire            aifsFlag,                // AiFS start
            input  wire            eifsFlag,                // EiFS start
            input  wire            tickDMAEarlySlot_p,      // early slot
            
            //$port_g ac sel Interface
            input wire             backOffDone_p,
            output wire            backoffDone,             // BackOff count load
            
            //$port_g protocol trigger Interface
            output reg             acProtTriggerFlagReset,  // Reset the protocol trigger generation mechanism after a backoff reload
            
            //$port_g Coex interface
          `ifdef RW_WLAN_COEX_EN
            input  wire            coexWlanTxAbort,         // Requests from external arbiter abort all on-going transmission
          `endif // RW_WLAN_COEX_EN
          
            //$port_g backoff counter
            output wire            backoffCntLoad,          // BackOff count load
            output wire            backoffCntEnable,        // BackOff count Enable

            output  reg      [2:0] backoffCtrlCs            // backoffCtrl FSM Current State

                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// backoffCtrl FSM states definition
//$fsm_sd backoffCtrl
localparam
                 IDLE  =  3'd0,  //
         LD_BKOFF_CNT  =  3'd1,  //
           CHK_MEDIUM  =  3'd2,  //
            WAIT_AIFS  =  3'd3,  //
       DEC_BCKOFF_CNT  =  3'd4,  //
          BCKOFF_DONE  =  3'd5;  //



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
// backoffCtrl FSM signals definition
reg [2:0] backoffCtrlNs;  // backoffCtrl FSM Next State
`ifdef RW_SIMU_ON
  // String definition to display backoffCtrl current state
  reg [14*8:0] backoffCtrlCs_str;
`endif // RW_SIMU_ON

reg  txInProgressDelayed;   // sampling TxInprogress
wire txInProgressFalling_p; // pulse indicating falling edge of txInprogress

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

assign txInProgressFalling_p = (txInProgressDelayed == 1'b1 && txInProgress == 1'b0) ? 1'b1 : 1'b0;

assign backoffCntEnable = (backoffCtrlCs == DEC_BCKOFF_CNT) ? 1'b1 : 1'b0;
assign backoffCntLoad   = (backoffCtrlCs == LD_BKOFF_CNT)   ? 1'b1 : 1'b0;

assign backoffDone      = (backoffCtrlCs == BCKOFF_DONE)   ? 1'b1 : 1'b0;

// backoffCtrl FSM Current State Logic
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    backoffCtrlCs <= IDLE;
  else if (macCoreClkSoftRst_n == 1'b0 || !backoffEnable)  // Synchronous Reset
    backoffCtrlCs <= IDLE;
  else
    backoffCtrlCs <= backoffCtrlNs;
end


// backoffCtrl FSM Next State Logic.
always @*
begin
  case(backoffCtrlCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits for the macController trigger
      if (backoffEnable == 1'b1)
        //$fsm_t When backoffEnable is received, the state machine goes to LD_BKOFF_CNT state.
        backoffCtrlNs = LD_BKOFF_CNT;
      else
        //$fsm_t While backoffEnable is not received, the state machine stays in IDLE state.
        backoffCtrlNs = IDLE;

    LD_BKOFF_CNT:
    //$fsm_s In LD_BKOFF_CNT state, the state machine goes to check medium

      //$fsm_t In LD_BKOFF_CNT state, the state machine goes to CHK_MEDIUM
      backoffCtrlNs = CHK_MEDIUM;

    CHK_MEDIUM:
      //$fsm_s In CHK_MEDIUM state, the state machine waits for the channel to be free before
      // starting to decount the backoff
      if (macPhyIfRxCca || channelBusy || txInProgress || (!acHasData && (txACState != 4'b0010))) 
        //$fsm_t While the medium is busy, the state machine stays in CHK_MEDIUM state.
        backoffCtrlNs = CHK_MEDIUM;
      else
        //$fsm_t When the medium is free, the state machine goes to WAIT_AIFS state.
        backoffCtrlNs = WAIT_AIFS;

    WAIT_AIFS:
      //$fsm_s In WAIT_AIFS state, wait for AIFS indicator to move the DEC_BACKOFF_CNT
      if (macPhyIfRxCca || channelBusy || txInProgress) 
        //$fsm_t When the medium is busy, the state machine goes to CHK_MEDIUM state.
        backoffCtrlNs = CHK_MEDIUM;
      else if (aifsFlag  || eifsFlag)
        //$fsm_t When aifsFlag is received, the state machine goes to DEC_BCKOFF_CNT state.
        backoffCtrlNs = DEC_BCKOFF_CNT;
      else
        //$fsm_t While nothing is received, the state machine stays in WAIT_AIFS state.
        backoffCtrlNs = WAIT_AIFS;

    DEC_BCKOFF_CNT:
      //$fsm_s In DEC_BCKOFF_CNT state, the state machine waits for the end of the count 
      //$fsm_s In WAIT_EIFS state, the state machine waits fow the eifstick
      if (macPhyIfRxCca || channelBusy || txInProgress)
        //$fsm_t When the medium is busy, the state machine goes to CHK_MEDIUM state.
        backoffCtrlNs = CHK_MEDIUM;
    `ifdef RW_WLAN_COEX_EN
      else if (tickDMAEarlySlot_p == 1'b1 && backoffCnt == 16'd0 && !coexWlanTxAbort)
    `else // RW_WLAN_COEX_EN
      else if (tickDMAEarlySlot_p == 1'b1 && backoffCnt == 16'd0)
    `endif // RW_WLAN_COEX_EN
        //$fsm_t When backoffDone_p is received, the state machine goes to BCKOFF_DONE state.
        backoffCtrlNs = BCKOFF_DONE;
      else
        //$fsm_t While backoffDone_p is not received, the state machine stays in DEC_BCKOFF_CNT state.
        backoffCtrlNs = DEC_BCKOFF_CNT;

    BCKOFF_DONE:
    //$fsm_s In BCKOFF_DONE state, the state machine reload the backoff counter
      if (((macPhyIfRxCca || channelBusy) && !txInProgress) || txFailed_p || txSuccessful_p || retryLTReached_p || backOffDone_p)
        //$fsm_t when channel goes busy or the Tx is finished, the state machine goes to LD_BKOFF_CNT.
        backoffCtrlNs = LD_BKOFF_CNT;
      else if (txInProgressFalling_p == 1'b1)
        //$fsm_t when TXOP is finished, the state machine goes to WAIT_AIFS.
        backoffCtrlNs = WAIT_AIFS;
      else 
        //$fsm_t While transmission is not complete or channel is idle the state machine stays in BCKOFF_DONE state.
        backoffCtrlNs = BCKOFF_DONE;
      
    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off
     default:
        backoffCtrlNs = IDLE;
    // pragma coverage block = on
  endcase
end

// generate a pulse to reset the protocol trigger mechanism 
// once the backoff is reloaded
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    acProtTriggerFlagReset <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    acProtTriggerFlagReset <= 1'b0;
  else
    acProtTriggerFlagReset <= backoffCntLoad;

end

// sample the txInprogress
// once the backoff is reloaded
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    txInProgressDelayed <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    txInProgressDelayed <= 1'b0;
  else
    txInProgressDelayed <= txInProgress;

end

`ifdef RW_SIMU_ON
// backoffCtrl FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (backoffCtrlCs)
                 IDLE  :  backoffCtrlCs_str = {"IDLE"};
         LD_BKOFF_CNT  :  backoffCtrlCs_str = {"LD_BKOFF_CNT"};
           CHK_MEDIUM  :  backoffCtrlCs_str = {"CHK_MEDIUM"};
            WAIT_AIFS  :  backoffCtrlCs_str = {"WAIT_AIFS"};
       DEC_BCKOFF_CNT  :  backoffCtrlCs_str = {"DEC_BCKOFF_CNT"};
          BCKOFF_DONE  :  backoffCtrlCs_str = {"BCKOFF_DONE"};
              default  :  backoffCtrlCs_str = {"XXX"};
   endcase
end
`endif // RW_SIMU_ON

endmodule
                 
