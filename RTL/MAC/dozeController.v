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
// Description      : Top level of dozeController module
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

`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"
module dozeController( 
          //$port_g Clock and Reset interface
          input  wire        macLPClk,               // MAC LowPower Clock
          input  wire        macCoreClk,             // MAC Core Clock
          input  wire        macCoreClkHardRst_n,    // Hard Reset of the MAC Core Clock domain 
          input  wire        macCoreClkSoftRst_n,    // Soft Reset of the MAC Core Clock domain 

          //$port_g MAC Controller interface
          input  wire        moveToDoze_p,           // Move to Doze request
          output wire        dozeWakeUp_p,           // Wake up the Mac Controller 

          //$port_g Timers interface
          input  wire        wakeupListenInterval_p, // Wakeup core at listen interval
          input  wire        wakeupDTIM_p,           // Wakeup core at DTIM count null
          input  wire        atimWindowOver_p,       // ATIM window over
          input  wire        absGenTimersInt,        // Absolute Timer Interrupt
          
          //$port_g Clock Controller interface
          output reg         macPriClkEn,            // Clock Enable for macPriClk Clocks
          output reg         macSecClkEn,            // Clock Enable for macPriClk Clocks
          output wire        platformWakeUp,         // Wake Up platform
          output wire        macLPClkSwitch,         // Switch MAC Lower Clock.

          //$port_g Registers interface
          input  wire  [3:0] nextState,              // Indicates the next state of the Core
          input  wire        enableLPClkSwitch,      // Enable the switch to LP clock in DOZE
          input  wire        wakeUpFromDoze,         // Wake Up From Doze
          input  wire        wakeUpSW,               // Wake Up SW
          input  wire        activeClkGating,        // Active Clock Gating This bit is set by SW to turn on 
                                                     // active clock gating in HW. When reset, the HW does not 
                                                     // perform active clock gating, i.e. does not turn off 
                                                     // clocks to save power in ACTIVE state.
          output wire [15:0] debugPortDozeController // Debug port for validation
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// dozeControllerFSM FSM states definition
//$fsm_sd dozeControllerFSM
localparam
                 IDLE  =  3'd0,  // 
          SWITCHTO32K  =  3'd1,  // 
         SWITCHOFFCLK  =  3'd2,  // 
                 DOZE  =  3'd3,  // 
            WAITSWREQ  =  3'd4,  // 
      SWITCHTOFASTCLK  =  3'd5,  // 
          SWITCHONCLK  =  3'd6;  // 


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
// dozeControllerFSM FSM signals definition
reg [2:0] dozeControllerFSMCs;  // dozeControllerFSM FSM Current State
reg [2:0] dozeControllerFSMNs;  // dozeControllerFSM FSM Next State
  
reg [(`DOZECOUNTERSIZE-1):0] counter;
reg fastClkReady;

wire wakeUp;
wire counterDone_p;

`ifdef RW_SIMU_ON
// String definition to display dozeControllerFSM current state
reg [15*8-1:0] dozeControllerFSMCs_str;
`endif // RW_SIMU_ON

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////



// dozeControllerFSM FSM Current State Logic 
always @ (posedge macLPClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    dozeControllerFSMCs <= IDLE;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    dozeControllerFSMCs <= IDLE;
  else
    dozeControllerFSMCs <= dozeControllerFSMNs; 
end


// dozeControllerFSM FSM Next State Logic.
always @* 
begin
  case(dozeControllerFSMCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits for a moveToDoze request from the SW 
      if (moveToDoze_p) 
        //$fsm_t When moveToDoze_p is received, the state machine goes to SWITCHOFFCLK state.
        dozeControllerFSMNs = SWITCHTO32K; 
      else
        //$fsm_t While moveToDoze_p is not received, the state machine stays in IDLE state.
        dozeControllerFSMNs = IDLE;

    SWITCHTO32K:
      //$fsm_s In SWITCHTO32K state, the state machine waits for counterDone_p indicating that the
      //time required to switch to 32kHz is completed (`SWITCHTO32K_DURATION in fast clock cycle)
      if (counterDone_p) 
        //$fsm_t When counterDone_p is received, the state machine goes to SWITCHOFFCLK state.
        dozeControllerFSMNs = SWITCHOFFCLK; 
      else
        //$fsm_t While counterDone_p is not received, the state machine stays in SWITCHTO32K state.
        dozeControllerFSMNs = SWITCHTO32K;

    SWITCHOFFCLK:
      //$fsm_s In SWITCHOFFCLK state, the state machine switches the Primar Clocks Off

      //$fsm_t One clock cycle after, the state machine stays in SWITCHOFFCLK state.
      dozeControllerFSMNs = DOZE;

    DOZE:
      //$fsm_s In DOZE state, the state machine waits for a Wake Up indication either from the Timer Unit or 
      //from the SW
      if (wakeUpSW && wakeUp) 
        //$fsm_t When wakeUp is received and wakeUpSW is set, the state machine goes to WAITSWREQ state.
        dozeControllerFSMNs = WAITSWREQ;
      else if ((!wakeUpSW && wakeUp) || (nextState == 4'b0))
        //$fsm_t When wakeUp is received and wakeUpSW is not set, the state machine goes to SWITCHTOFASTCLK state.
        dozeControllerFSMNs = SWITCHTOFASTCLK; 
      else
        //$fsm_t While wakeUp is not received and SW changed nextState to IDLE, the state machine stays in DOZE state.
        dozeControllerFSMNs = DOZE;

    WAITSWREQ:
      //$fsm_s In WAITSWREQ state, the state machine waits until the SW moves the state to IDLE.
      if (nextState == 4'b0) 
        //$fsm_t When SW changes nextState to IDLE, the state machine goes to SWITCHTOFASTCLK state.
        dozeControllerFSMNs = SWITCHTOFASTCLK; 
      else
        //$fsm_t While wakeUp is not received and SW changed nextState to IDLE, the state machine stays in WAITSWREQ state.
        dozeControllerFSMNs = WAITSWREQ;

    SWITCHTOFASTCLK:
      //$fsm_s In SWITCHTOFASTCLK state, the state machine waits for the counterDone_p indicating that the
      //time required to switch to fast clocks is completed (`SWITCHTOFASTCLK_DURATION in LP clock cycle)
      if (counterDone_p) 
        //$fsm_t When counterDone_p is received, the state machine goes to SWITCHONCLK state.
        dozeControllerFSMNs = SWITCHONCLK; 
      else
        //$fsm_t While counterDone_p is not received, the state machine stays in SWITCHTOFASTCLK state.
        dozeControllerFSMNs = SWITCHTOFASTCLK;

    SWITCHONCLK:
      //$fsm_s In SWITCHONCLK state, the state machine switches the Primary Clocks On 
      if (fastClkReady) 
        //$fsm_t When fastClkReady is received, the state machine moves to IDLE state.
        dozeControllerFSMNs = IDLE;
      else
        //$fsm_t While fastClkReady is not set, the state machine stays in SWITCHONCLK state.
        dozeControllerFSMNs = SWITCHONCLK;

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
     default:   
        dozeControllerFSMNs = IDLE; 
    // pragma coverage block = on 
  endcase
end


// counter process
always @ (posedge macLPClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    counter    <= `DOZECOUNTERSIZE'd0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    counter    <= `DOZECOUNTERSIZE'd0;
  else
  begin
    if (dozeControllerFSMCs == DOZE)
      counter    <= `DOZECOUNTERSIZE'd`SWITCHTOFASTCLK_DURATION;
    else if (dozeControllerFSMCs == IDLE)
      counter    <= `DOZECOUNTERSIZE'd`SWITCHTO32K_DURATION;
    else if ((dozeControllerFSMCs == SWITCHTO32K) || (dozeControllerFSMCs == SWITCHTOFASTCLK))
      counter    <= counter - `DOZECOUNTERSIZE'd1;
  end 
end

// fastClkReady flag
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    fastClkReady    <= 1'b1;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    fastClkReady    <= 1'b1;
  else
  begin
    if (dozeControllerFSMCs == SWITCHTO32K)
      fastClkReady    <= 1'b0;
    else if (dozeControllerFSMCs == SWITCHONCLK)
      fastClkReady    <= 1'b1;
  end  
end

assign counterDone_p  = (counter == {`DOZECOUNTERSIZE{1'b0}}) ? 1'b1 : 1'b0;

assign wakeUp         = wakeupListenInterval_p || wakeupDTIM_p || atimWindowOver_p || absGenTimersInt || wakeUpFromDoze;

assign macLPClkSwitch = ((dozeControllerFSMCs == SWITCHTO32K) || (dozeControllerFSMCs == SWITCHOFFCLK) || (dozeControllerFSMCs == DOZE)) ? enableLPClkSwitch : 1'b0;

assign platformWakeUp = ((dozeControllerFSMCs == DOZE) || (dozeControllerFSMCs == SWITCHOFFCLK)) ? 1'b0 : 1'b1;

assign dozeWakeUp_p   = ((dozeControllerFSMCs == SWITCHONCLK) && (dozeControllerFSMNs == IDLE)) ? 1'b1 : 1'b0;




always @ (posedge macLPClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPriClkEn    <= 1'd1;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macPriClkEn    <= 1'd1;
  else if (activeClkGating)
  begin 
    if (!wakeUpFromDoze && ((dozeControllerFSMCs == SWITCHOFFCLK) || (dozeControllerFSMCs == DOZE) || (dozeControllerFSMCs == WAITSWREQ)))
      macPriClkEn    <= 1'd0;
    else
      macPriClkEn    <= 1'd1;
  end  
  else
    macPriClkEn    <= 1'd1;
end

always @ (posedge macLPClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macSecClkEn    <= 1'd1;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macSecClkEn    <= 1'd1;
  else if (activeClkGating)
  begin 
    if ((dozeControllerFSMCs == SWITCHTO32K) || (dozeControllerFSMCs == SWITCHOFFCLK))
      macSecClkEn    <= 1'd0;
    else
      macSecClkEn    <= macPriClkEn;
  end  
  else
    macSecClkEn    <= 1'd1;
end


// Debug port
//////////////////////////////////////////////////////////////////////////////
assign debugPortDozeController  = {activeClkGating,
                                   platformWakeUp,
                                   counterDone_p,
                                   macLPClkSwitch,
                                   fastClkReady,
                                   moveToDoze_p,
                                   dozeWakeUp_p,
                                   wakeUpSW,
                                   wakeupListenInterval_p,
                                   macSecClkEn,
                                   wakeupDTIM_p,
                                   atimWindowOver_p,
                                   macPriClkEn,
                                   dozeControllerFSMCs};

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
// dozeControllerFSM FSM states displayed in a string to easy simulation and debug
// Disable coverage on the default state because it cannot be reached.
// pragma coverage block = off 

always @*
begin
  case (dozeControllerFSMCs)
                 IDLE  :  dozeControllerFSMCs_str = {"IDLE"};
         SWITCHOFFCLK  :  dozeControllerFSMCs_str = {"SWITCHOFFCLK"};
          SWITCHTO32K  :  dozeControllerFSMCs_str = {"SWITCHTO32K"};
                 DOZE  :  dozeControllerFSMCs_str = {"DOZE"};
            WAITSWREQ  :  dozeControllerFSMCs_str = {"WAITSWREQ"};
      SWITCHTOFASTCLK  :  dozeControllerFSMCs_str = {"SWITCHTOFASTCLK"};
          SWITCHONCLK  :  dozeControllerFSMCs_str = {"SWITCHONCLK"};
              default  :  dozeControllerFSMCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

endmodule
