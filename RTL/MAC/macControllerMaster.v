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
//    For simulation, two defines are available
//
//    RW_SIMU_ON   : which creates string signals to display the FSM states on  
//                the waveform viewers
//
//    RW_ASSERT_ON : which enables System Verilog Assertions.
//
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


module macControllerMaster( 
          //$port_g Clock and Reset interface
          input  wire        macCoreClk,               // MAC Core Clock
          input  wire        macCoreClkHardRst_n,      // Hard Reset of the MAC Core Clock domain 
                                                       // active low
          input  wire        macCoreClkSoftRst_n,      // Soft Reset of the MAC Core Clock domain 

          //$port_g MAC-PHY interface
          input  wire        mpIfTxErr_p,              // Tx error from MAC-PHY if. resynchronized
          input  wire        macPhyIfRxCca,            // CCA trigger                   
          input  wire        macPhyIfRxErr_p,          // Rx error from MAC-PHY if. resynchronized
          input  wire        macPhyIfRxEnd_p,          // Indicate the macPhy if is idle
          output wire        mpifKeepRFonMaster,       // Keep the RF ON
          output reg         startRxMaster_p,          // Start the RX
          input  wire        rxVector1Start_p,         // Indicate that the first byte of RX Vector has been received
          output wire        stopRxMaster_p,           // Stop the RX
          input  wire        trigTxBackoff,         // Indicate that the backoff won the medium

          //$port_g BackOff Module interface
          
          input  wire        backOffDone_p,            // Indicates when a backOff has expired
          
          //$port_g RX Control State Machine interface
          input  wire        rxExchangeCompleted_p,    // When the completion of a RX frame exchange
          output wire        rxExchangeEnabled,        // Enables the RX frame exchange

          //$port_g TX Control State Machine interface
          input  wire        txExchangeCompleted_p,    // When the completion of a TX frame exchange
          output wire        txExchangeEnabled,        // Enables the TX frame exchange

          //$port_g MAC Timer Unit Module interface
          output wire        resetCommonCnt_p,         // Reset common count counter
          output wire        moveToActive_p,           // Core should now move to ACTIVE state
          output wire        moveToIdle_p,             // Indicates that the macControllerMasterFSM moves to IDLE state
          output reg         idleInterrupt,            // Indicates that the Core has moved to IDLE state

          //$port_g Doze Module interface
          input  wire        dozeWakeUp_p,             // Wake up the Mac Controller 
          output wire        moveToDoze_p,             // Move to Doze request
 
          //$port_g HW Error detected
          input  wire        hwErr,                    // HW error detected

          
          //$port_g CSReg interface
          output reg   [2:0] macControllerMasterFSMCs, // State of the MAC Controller Master FSM     
          output reg   [3:0] currentState,             // Indicates the current state of the Core. The state encoding is as follows:
                                                       // 0000 - IDLE state. This is the default state.
                                                       // 0010 - DOZE state
                                                       // 0011 - ACTIVE state
                                                       // 0100 to 1111  - reserved
          input  wire  [3:0] nextState,                // Indicates the next state of the Core
          output reg   [3:0] nextStateIn,              // When the current state goes back to IDLE, the nextState is also set to IDLE
          output wire        nextStateInValid          // Indicates that the nextStateIn value can be capture.
          
          
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

// macControllerMasterFSM FSM states definition
//$fsm_sd macControllerMasterFSM
localparam
                 IDLE  =  3'd0,  // 
             PHYERROR  =  3'd1,  // 
       WAIT_TXRX_TRIG  =  3'd2,  // 
            ACTIVE_RX  =  3'd3,  // 
            ACTIVE_TX  =  3'd4,  // 
                 DOZE  =  3'd5;  // 



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
// macControllerMasterFSM FSM signals definition

reg [2:0] macControllerMasterFSMNs;  // macControllerMasterFSM FSM Next State

reg [2:0] macControllerMasterFSMPs;  // macControllerMasterFSM FSM Previous State
 
reg macPhyIfRxEnd;    // Captured version of macPhyIfRxEnd_p

reg  startRxInt_p;    // Internal request to start the RX
reg  startRxIntDly_p; // Internal request delayed of 1 cc to start the RX
reg  backOffDone;
`ifdef RW_SIMU_ON
// String definition to display macControllerMasterFSM current state
reg [14*8:0] macControllerMasterFSMCs_str;
`endif // RW_SIMU_ON



//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////



// macControllerMasterFSM FSM Current State Logic 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macControllerMasterFSMCs <= IDLE; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macControllerMasterFSMCs <= IDLE; 
  else
    macControllerMasterFSMCs <= macControllerMasterFSMNs; 
end

// macControllerMasterFSM FSM Previous State Logic 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macControllerMasterFSMPs <= IDLE; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macControllerMasterFSMPs <= IDLE; 
  else
    macControllerMasterFSMPs <= macControllerMasterFSMCs; 
end


// macControllerMasterFSM FSM Next State Logic.
always @* 
begin
  case(macControllerMasterFSMCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits for Software to program the stateCntlrReg.nextState 
      //register to ACTIVE states or till trigger is received from DOZE state machine to move out 
      //of IDLE
      begin        
        if (nextState != currentState)
        begin
        case (nextState)
          4'b0010 :
            //$fsm_t When the MAC HW Current state is DOZE, the state machine goes to DOZE state.
            macControllerMasterFSMNs = DOZE; 
          4'b0011 :
            //$fsm_t When the MAC HW Current state is ACTIVE, the state machine goes to WAIT_TXRX_TRIG state.
            macControllerMasterFSMNs = WAIT_TXRX_TRIG; 
          default : 
            //$fsm_t Else, the state machine stays in IDLE state.
            macControllerMasterFSMNs = IDLE;
          endcase
        end
        else
          macControllerMasterFSMNs = IDLE;
      end
      
    WAIT_TXRX_TRIG:
      //$fsm_s In WAIT_TXRX_TRIG state, the state machine waits for backOffDone_p indication from Backoff 
      //block, a tickEarlyTbtt_p from the Timers Unit or CCA indication from MAC-PHY Interface
      if (macPhyIfRxErr_p)
        //$fsm_t If a PHY RX Error is reported, the state machine moves in PHYERROR state.
        macControllerMasterFSMNs = PHYERROR;
      else if (rxVector1Start_p) 
        //$fsm_t When CCA indication is received, the state machine goes to ACTIVE_RX state.
        macControllerMasterFSMNs = ACTIVE_RX; 
      else
      begin
        if (backOffDone  && !macPhyIfRxCca)
          //$fsm_t When backOffDone_p is received, the state machine moves in ACTIVE_TX state.
          macControllerMasterFSMNs = ACTIVE_TX;
        else
        begin  
          if (nextState == 4'b0000)
            //$fsm_t If neither cca indication nor backOffDone_p is received but the SW requested to 
            // move to IDLE, the state machine moves in IDLE state.
            macControllerMasterFSMNs = IDLE;
          else
            //$fsm_t While neither cca indication nor backOffDone_p is received and the SW did not request to 
            // move to IDLE, the state machine stays in WAIT_TXRX_TRIG state.
            macControllerMasterFSMNs = WAIT_TXRX_TRIG;
        end    
      end
      
    ACTIVE_RX:
      //$fsm_s In ACTIVE_RX state, the state machine waits till current reception and applicable response 
      //frame transmission is completed. 
      if (macPhyIfRxErr_p)
        //$fsm_t If a PHY RX Error is reported, the state machine moves in PHYERROR state.
        macControllerMasterFSMNs = PHYERROR;
      else if (rxExchangeCompleted_p) 
        //$fsm_t When rxExchangeCompleted_p is received, the state machine goes to WAIT_TXRX_TRIG state.
        macControllerMasterFSMNs = WAIT_TXRX_TRIG; 
      else
        //$fsm_t While rxExchangeCompleted_p is not received, the state machine stays in ACTIVE_RX state.
        macControllerMasterFSMNs = ACTIVE_RX;

    ACTIVE_TX:
      //$fsm_s In ACTIVE_TX state, the state machine waits till current TXOP is completed.
      //  - Transmission of the protection frame if required
      //  - Reception of the protection frame response if any
      //  - Transmission of the data
      //  - Reception of the frame response if any
      //  - TXOPLimit verification
      //  - CF-END transmission if required.
      if (txExchangeCompleted_p) 
        //$fsm_t When txExchangeCompleted_p is received indicatating the completion of the TXOP, 
        //the state machine goes back to WAIT_TXRX_TRIG state.
        macControllerMasterFSMNs = WAIT_TXRX_TRIG; 
      else
        //$fsm_t While txExchangeCompleted_p is not received, the state machine stays in ACTIVE_TX state.
        macControllerMasterFSMNs = ACTIVE_TX;

    PHYERROR:
      //$fsm_s In PHYERROR state, the state machine waits for the recovery of the PHY.
      if (macPhyIfRxEnd)
        //$fsm_t If macPhyIfRxEnd is set indicating the complete recovery of the PHY and MAC-PHY IF, 
        // the state machine moves to WAIT_TXRX_TRIG state.
        macControllerMasterFSMNs = WAIT_TXRX_TRIG;
      else
        //$fsm_t While macPhyIfRxErr_p is set, the state machine stays in PHYERROR state.
        macControllerMasterFSMNs = PHYERROR;
        
    DOZE:
      //$fsm_s In DOZE state, the state machine is in doze and waits for a wake up
      if (dozeWakeUp_p)
        //$fsm_t If dozeWakeUp_p is received indicating a wake up, 
        // the state machine moves to IDLE state.
        macControllerMasterFSMNs = IDLE;
          
      else
        //$fsm_t While dozeWakeUp_p is not received, the state machine stays in DOZE state.
        macControllerMasterFSMNs = DOZE;
        

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
    default:   
        macControllerMasterFSMNs = IDLE; 
    // pragma coverage block = on 
  endcase
end

// When the macControllerMaster FSM moves to WAIT_TXRX_TRIG, the startRxInt_p indication is generated
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    backOffDone <= 1'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    backOffDone <= 1'b0; 
  else
  begin
    if (backOffDone_p)
      backOffDone <= 1'b1;
    else if (macControllerMasterFSMCs == ACTIVE_TX)
      backOffDone <= 1'b0;
  end    
end




// Indicates that a RX Frame Exchange is on-going
assign rxExchangeEnabled = (macControllerMasterFSMCs == ACTIVE_RX) ? 1'b1 : 1'b0;

// Indicates that a TX Frame Exchange is on-going
assign txExchangeEnabled = (macControllerMasterFSMCs == ACTIVE_TX) ? 1'b1 : 1'b0;

// Forced the RF On in case of RIFS.
assign mpifKeepRFonMaster = 1'b0; //$todo in case of RIFS.

// When the macControllerMaster FSM moves to WAIT_TXRX_TRIG, the startRxInt_p indication is generated
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    startRxInt_p <= 1'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    startRxInt_p <= 1'b0; 
  else
  begin
    if (stopRxMaster_p)
      startRxInt_p <= 1'b0;
    else if (macControllerMasterFSMCs == WAIT_TXRX_TRIG && !trigTxBackoff)
      startRxInt_p <= 1'b1;
    else
      startRxInt_p <= 1'b0;
  end    
end

// Generation of startRxIntDly_p which is startRxInt_p delayed of one clock cycle.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    startRxIntDly_p <= 1'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    startRxIntDly_p <= 1'b0; 
  else
    if (stopRxMaster_p)
      startRxIntDly_p <= 1'b0;
    else 
      startRxIntDly_p <= startRxInt_p;
end

// Generation of startRxMaster_p which is startRxInt_p delayed of two clock cycles.
// This is to guaranty that stopRx_p generated from macControllerRx and macControllerTx will never occur at the same time
// than the startRxMaster_p
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    startRxMaster_p <= 1'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    startRxMaster_p <= 1'b0; 
  else
    if (stopRxMaster_p | trigTxBackoff)
      startRxMaster_p <= 1'b0;
    else
      startRxMaster_p <= startRxIntDly_p;
end

// When the FSM moves to PHYERROR or IDLE, the stopRxMaster_p pulse is generated to stop the PHY RX
assign stopRxMaster_p  = ((macControllerMasterFSMCs == PHYERROR) || ((macControllerMasterFSMCs == IDLE) && (macControllerMasterFSMPs == IDLE)) || (macControllerMasterFSMCs == DOZE) ||  ((macControllerMasterFSMCs == WAIT_TXRX_TRIG) && trigTxBackoff)) ? 1'b1 : 1'b0;

// Generate an interrupt when the FSM moves to IDLE state.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    idleInterrupt <= 1'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    idleInterrupt <= 1'b0; 
  else if ((macControllerMasterFSMCs != IDLE) && (macControllerMasterFSMNs == IDLE))
    idleInterrupt <= 1'b1;
  else if ((macControllerMasterFSMCs == IDLE) && (macControllerMasterFSMNs != IDLE))
    idleInterrupt <= 1'b0;
end

// macControllerMasterFSM FSM Current State Logic 
//always @ * 
//begin
//  if (macControllerMasterFSMCs == IDLE)
//    currentState = 4'b0000;
//  else if (macControllerMasterFSMCs == DOZE)
//    currentState = 4'b0010;
//  else
//    currentState = 4'b0011;
//end
//
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    currentState <= 4'b0000;
  else if (macCoreClkSoftRst_n == 1'b0)
    currentState <= 4'b0000;
  else if (moveToIdle_p)
    currentState <= 4'b0000;
  else if (moveToDoze_p)
    currentState <= 4'b0010;
  else if (moveToActive_p)
    currentState <= 4'b0011;
end


// MAC Next State Valid signal generation
assign nextStateInValid =  (macControllerMasterFSMCs != macControllerMasterFSMPs) && 
                            ((macControllerMasterFSMCs == IDLE) || (macControllerMasterFSMCs == DOZE)) || 
                           !macCoreClkSoftRst_n ? 1'b1 : 1'b0;

// Assignment of nextStateIn based on the next state
always @*
begin
  case (macControllerMasterFSMCs)
       IDLE : nextStateIn = 4'b0000;
       DOZE : nextStateIn = 4'b0010;
    default : nextStateIn = 4'b0000;
  endcase  
end

// When the FSM moves from IDLE or to IDLE, the resetCommontCnt_p for MAC Timer Unit
assign resetCommonCnt_p =  moveToIdle_p ||  moveToActive_p || moveToDoze_p;

// When the FSM moves to WAIT_TXRX_TRIG, the moveToIdle_p is generated
assign moveToIdle_p = ((macControllerMasterFSMCs == IDLE) && (macControllerMasterFSMPs != IDLE));

// When the FSM moves to WAIT_TXRX_TRIG, the moveToActive_p is generated for MAC Timer Unit
assign moveToActive_p = ((macControllerMasterFSMCs == WAIT_TXRX_TRIG) && (macControllerMasterFSMPs == IDLE));

// When the FSM moves to DOZE, the moveToDoze_p is generated for Doze and MAC Timer Module.
assign moveToDoze_p = ((macControllerMasterFSMCs == DOZE) && (macControllerMasterFSMPs != DOZE));



// Capture macPhyIfRxEnd_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPhyIfRxEnd <= 1'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macPhyIfRxEnd <= 1'b0; 
  else
  begin
    if (macPhyIfRxEnd_p)
      macPhyIfRxEnd <= 1'b1;
    else if (macPhyIfRxEnd && (macControllerMasterFSMCs != PHYERROR))
      macPhyIfRxEnd <= 1'b0;
  end    
end

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
// Disable coverage on the default state because it cannot be reached.
// pragma coverage block = off 
// macControllerMasterFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (macControllerMasterFSMCs)
                 IDLE  :  macControllerMasterFSMCs_str = {"IDLE"};
       WAIT_TXRX_TRIG  :  macControllerMasterFSMCs_str = {"WAIT_TXRX_TRIG"};
            ACTIVE_RX  :  macControllerMasterFSMCs_str = {"ACTIVE_RX"};
            ACTIVE_TX  :  macControllerMasterFSMCs_str = {"ACTIVE_TX"};
             PHYERROR  :  macControllerMasterFSMCs_str = {"PHYERROR"};
                 DOZE  :  macControllerMasterFSMCs_str = {"DOZE"};
              default  :  macControllerMasterFSMCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

`ifdef RW_ASSERT_ON

// Cover Points Definitions
///////////////////////////

//$rw_sva This cover point checks if a request to move to IDLE has been received while transmitting
countIdleRequestWhenTx: cover property (@(posedge macCoreClk) (txExchangeEnabled && $rose(nextState == 0)));

//$rw_sva This cover point checks if a request to move to IDLE has been received while receiving
countIdleRequestWhenRx: cover property (@(posedge macCoreClk) (rxExchangeEnabled && $rose(nextState == 0)));


`endif // RW_ASSERT_ON

endmodule
                 
