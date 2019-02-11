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
// Description      : Top level of deaggregator module
//
// Simulation Notes : 
//    For simulation, two defines are available
//
//    RW_SIMU_ON       : which creates string signals to display the FSM states
//                    on the waveform viewer.
//
//    RW_ASSERT_ON     : which enables System Verilog Assertions.
//
// Synthesis Notes  :
//
// Application Note : 
//
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


module tsfSync( 
            ///////////////////////////////////////////////
            //$port_g Clock and reset
            ///////////////////////////////////////////////
            input wire         macCoreClk,              // MAC Core Clock
            input wire         macLPClk,                // MAC LP Clock

            input wire         macLPClkSwitch,          // MAC LP Clock frequency = 32KHz when active
            
            input wire         macCoreClkHardRst_n,     // Hard Reset of the MAC Core Clock domain active low

            input wire         macCoreClkSoftRst_n,     // Soft Reset of the MAC Core Clock domain
            
            ///////////////////////////////////////////////
            //$port_g RX Controller
            ///////////////////////////////////////////////
            input wire         tsfUpdate_p,             // Update TSF
            input wire         tsfOffsetUpdate_p,       // Update TSF Offset
            input wire [63:0]  timeStamp,               // Timestamp

            ///////////////////////////////////////////////
            //$port_g MAC-PHY interface
            ///////////////////////////////////////////////
            input wire         macPhyIfRxEndForTiming_p,// Rx end for timing from MAC-PHY if. resynchronized
                                                        // has been received
            
            ///////////////////////////////////////////////
            //$port_g MAC Controller
            ///////////////////////////////////////////////
            input wire         moveToActive_p,          // Core should now move to ACTIVE state
            input wire [15:0]  frmDurWithoutMH,         // Indicates the duration if the Beacon or Probe Response from the end of the MAC header
            
            ///////////////////////////////////////////////
            //$port_g Control and Status Register
            ///////////////////////////////////////////////
            input wire         bssType,                 // BSS Type
            input wire         ap,                      // Access Point

            input wire [15:0]  beaconInt,               // Beacon interval

            input wire [31:0]  tsfTimerHigh,            // TSF[63:32] register
            input wire [31:0]  tsfTimerLow,             // TSF[31:0] register
            input wire         tsfUpdatedBySW,          // sw programming tsfTimerLow register

            output reg [63:0]  tsfTimer,                // TSF timer 64-bit

            output wire        tsfUpdatedBySWIn,        // Clear Software update request
            output reg         tsfUpdatedBySWInValid,   // Indicates that the tsfUpdatedBySW register has to be updated with tsfUpdatedBySWIn

            ///////////////////////////////////////////////
            //$port_g MAC Timer Unit
            ///////////////////////////////////////////////
            input wire         tick1us_p,               // Pulse every microseconds
            
            output wire [25:0] modulo,                  // Modulo output
            output wire        updateBeaconIntCnt_p,    // Update beacon interval counter
            
            output wire        adjustLPInc              // Adjust 32K counters running on macLPClk
            );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

// tsfSync FSM states definition
//$fsm_sd tsfSync
localparam 
                  IDLE  =  3'd0, // idle state
     CHK_TSF_TO_UPDATE  =  3'd1, // update TSF unconditionally if BSS or if current < new in IBSS
            UPDATE_TSF  =  3'd2, // generate signal to update TSF
          TRIG_DIVIDER  =  3'd3, // this trigers calulation of modulo
        WAIT_MOD_VALID  =  3'd4, // wait for valid indication from divider
    WAIT_ANOTHER_CLOCK  =  3'd5, // wait for one more clock
    UPDATE_BCNINTV_CNT  =  3'd6; // update Beacon Interval counter


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// tsfSync FSM signals definition
reg [2:0] tsfSyncCs;    // tsfSync FSM Current State
reg [2:0] tsfSyncNs;    // tsfSync FSM Next State

`ifdef RW_SIMU_ON
  // String definition to dislpay deaggregator current state
  reg [19*8:0] tsfSyncCs_str;
`endif // RW_SIMU_ON

// TSF offset
reg [63:0]  tsfOffset;

// Adjust counter in macLPClk
reg [1:0]  adjustLPCnt;

// Modulo computation
reg [16:0]  moduloInterm;
reg [5:0]   moduloCnt;
wire [16:0] moduloDiff;

// TSF comparison control
reg         tsfLocalLesser;
reg         tsfOffsetUpdate_ff1_p;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

                
// tsfSync FSM Current State Logic 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    tsfSyncCs <= IDLE; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    tsfSyncCs <= IDLE; 
  else if (moveToActive_p)
    tsfSyncCs <= TRIG_DIVIDER;
  else
    tsfSyncCs <= tsfSyncNs; 
end

// tsfSync FSM Next State Logic.
always @* 
begin
  case(tsfSyncCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits trigger from RX Controller
      if (tsfUpdate_p) 
        //$fsm_t When tsfUpdate_p is received, the state machine goes to CHK_TSF_TO_UPDATE state.
        tsfSyncNs = CHK_TSF_TO_UPDATE; 
      else
        //$fsm_t While tsfUpdate_p is not received, the state machine stays in IDLE state.
        tsfSyncNs = IDLE;

    CHK_TSF_TO_UPDATE:
      //$fsm_s In CHK_TSF_TO_UPDATE state, the state machine checks TSF updating condition:
      // The conditions for updating the tsf in infrastructure BSS and IBSS
      // depends on the following conditions.
      // (a) bssType == 1 and not(ap) indicates that the module is an STA in 
      // infrastructure BSS update the TSF unconditionally
      // (b) bssType == 0 indicates that the module is a member of IBBS
      // in this case, update the TSF Timer if the sender's TSF is ahead
      // of the receiver TSF by maximum of MAX_TSFOFFSET
      if ((bssType && !ap) || (tsfLocalLesser && !bssType))
        //$fsm_t When condition is received, the state machine goes to UPDATE_TSF state.
        tsfSyncNs = UPDATE_TSF;
      else
        //$fsm_t While condition is not reached, the state machine returns in IDLE state.
        tsfSyncNs = IDLE;

    UPDATE_TSF:
      //$fsm_s In UPDATE_TSF state, the state machine waits one clock cycle
      // update the TSF timer with the offset + local TSF Timer value

        //$fsm_t After one clock cycle, the state machine goes to TRIG_DIVIDER state.
        tsfSyncNs = TRIG_DIVIDER;

    TRIG_DIVIDER:
      //$fsm_s In TRIG_DIVIDER state, the state machine waits one clock cycle
      // after updating the TSF, the divider is triggered to compute the value of (TSF) mod (beacon Interval)

        //$fsm_t After one clock cycle, the state machine goes to WAIT_MOD_VALID state.
        tsfSyncNs = WAIT_MOD_VALID;

    WAIT_MOD_VALID:
      //$fsm_s In WAIT_MOD_VALID state, the state machine waits end of modulo calculation
      if (moduloCnt == 6'd53) 
        //$fsm_t When Modulo counter reaches 53, the state machine goes to WAIT_ANOTHER_CLOCK state.
        // we get 54 bits (because we consider TSF in TU(1024us) for modulo computation.
        tsfSyncNs = WAIT_ANOTHER_CLOCK;
      else
        //$fsm_t While Modulo counter is not 53, the state machine stays in WAIT_MOD_VALID state.
        tsfSyncNs = WAIT_MOD_VALID;

    WAIT_ANOTHER_CLOCK:
      //$fsm_s In WAIT_ANOTHER_CLOCK state, the state machine waits one clock cycle for the output to be stable after the moduloCnt=54

        //$fsm_t After one clock cycle, the state machine goes to UPDATE_BCNINTV_CNT state.
        tsfSyncNs = UPDATE_BCNINTV_CNT;

    UPDATE_BCNINTV_CNT:
      //$fsm_s In UPDATE_BCNINTV_CNT state, the state machine waits one clock cycle
      // The computed modulo value is used to update the beacon Interval counter 

        //$fsm_t After one clock cycle, the state machine goes to IDLE state.
        tsfSyncNs = IDLE;

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
     default:   
        tsfSyncNs = IDLE; 
    // pragma coverage block = on 
  endcase
end


// tsfOffset is used to maintain the TSF offset between a received 
// Beacon/Probe Resp and the local TSF.
// When firstMHByteRcved_p is asserted, the local TSF contents are written into 
// the register. The PHY-RXSTART int is asserted when the 1st nibble of the
// RX-VECTOR is passed to the MAC. The Rx chain delay on this nibble is
// expected to be kept constant by the PHY. This is the reference time.
// When all the bytes of the TSF are received (it does not matter how long
// it takes for the bytes to be rxed or when they are received), the offset
// between the received TSF and the local TSF is calculated and stored.
// The value of the local TSF is calculated from the TSF reference, by
// subtracting the Rx chain delay and adding to it the calculated time for
// the 24 bytes before the TSF field in the Bcn to be received from the
// PHY-RXSTART int.
// The offset is finally added to the tsfTimer register.
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
    tsfOffset <= 64'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    tsfOffset <= 64'b0;
  else if (macPhyIfRxEndForTiming_p)
    tsfOffset <= (timeStamp + {48'd0,frmDurWithoutMH}) - tsfTimer;
  else if (tsfSyncCs == TRIG_DIVIDER)
    tsfOffset <= tsfTimer;
  else if (tsfSyncCs == WAIT_MOD_VALID)
    tsfOffset <= {tsfOffset[62:0] ,1'b0};
end

// tsfLocalLesser is used to indicate whether the received time-stamp is greater than
// the local TSF, this is used to update the TSF in an IBSS.
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)       // Asynchronous Reset
  begin
    tsfLocalLesser        <= 1'b0;
    tsfOffsetUpdate_ff1_p <= 1'b0;
  end
  else
  begin
    // tsfLocalLesser comparison
    if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    begin
      tsfLocalLesser        <= 1'b0;
      tsfOffsetUpdate_ff1_p <= 1'b0;
    end
    else if (tsfOffsetUpdate_ff1_p)
    begin
      if ((tsfTimer + tsfOffset) > tsfTimer)
        tsfLocalLesser <= 1'b1;
      else
        tsfLocalLesser <= 1'b0; 
    end 
  
    // tsfOffsetUpdate_p delayed by one cc
    tsfOffsetUpdate_ff1_p <= tsfOffsetUpdate_p;
  end
end


// generate TSF timer on 64-bit maintained in microseconds.
always @(posedge macLPClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    tsfTimer <= 64'b0;
  else if (!macCoreClkSoftRst_n)    // Synchronous reset
    tsfTimer <= 64'b0;
  else if (tsfSyncCs == UPDATE_TSF) // TSF update after offset calculation
    tsfTimer <= tsfTimer + tsfOffset;
  else if (tsfUpdatedBySW)          // SW programming tsfTimerLow register
  begin
    tsfTimer[63:32] <= tsfTimerHigh;
    tsfTimer[31:0]  <= tsfTimerLow;
  end
  else if (macLPClkSwitch)          // TSF incrementation every 32 KHz in Doze
    tsfTimer <= tsfTimer + 64'd31 + {63'b0, adjustLPInc};
  else if (tick1us_p)               // TSF incrementation every microseconds
    tsfTimer <= tsfTimer + 64'b1;
end

// generate tsfUpdatedBySWInValid in order to clear tsfUpdatedBySW bit
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                     // Asynchronous Reset
    tsfUpdatedBySWInValid <= 1'b0;
  else
    tsfUpdatedBySWInValid <= tsfUpdatedBySW;
end

assign tsfUpdatedBySWIn = 1'b0;

// generate TSF adjust for tsfTimer incrementation in macLPClk (32Khz=31.25us)
// every 4 clock cycle increment by 2
always @(posedge macLPClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)                     // Asynchronous Reset
    adjustLPCnt <= 2'b0;
  else if (!macCoreClkSoftRst_n || !macLPClkSwitch)    // Synchronous reset
    adjustLPCnt <= 2'b0;
  else                                                 // LP clock active
    adjustLPCnt <= adjustLPCnt + 2'b1;
end

// Adjust 32K counters running on macLPClk
assign adjustLPInc = (adjustLPCnt == 2'h3) ? 1'b1 : 1'b0;


// moduloInterm is used for performing modulo computation for TSF 
// Synchronization. This is done if FSM is in WAIT_MOD_VALID state.
// a counter (moduloCnt) is used to count the number of bits of the
// timestamp which has been shifted into divider module. in this case 54 bits
// has to be left shifted..
//           x---------------x        FINAL RESULT = {mod,lower10 bits of TSF}
//           |Trigger Divider|                    TT
//           x-------|-------x                    || 
//                   |            x------------------------------------x
//                   |            |cnt = (64-10) && dividend > BI      | 
//  cnt == 0         |            |then mod = diff else mod == dividend|
//  dividend= 0      |            x-----------------------^------------x
//                   |   x------------------x             |
// x-------------v-------v-----------x      |_____________x cnt == 55
// |pad LSB with tsfOffsetValue[63]  |      |
// |if (dividend > BI)               |      |
// |dividend =                       |      |
// | diff(dividend-BI),MSB(TSFOFFREG)|------x cnt <= 54
// |else                             |
// |(shift dividend left by one &    |
// |pad LSB with MSB(TSFOFFREG))     |
// x---------------------------------x
//                         
// NOTE : TSF is counted in microseconds... and Beacon Intervals in TUs(1024 us)
// by selecting the upper 54 bits of TSFTimer we are expressing TSF also in TUs
// and operating in TU terms. Finally conversion back to microseconds is
// achieved by concatinating the modulo value with the LSBs of the TSF Timer 
// which was chosen for division.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)           // Asynchronous Reset
  begin
    moduloCnt    <= 6'h00;
    moduloInterm <= 17'h0;
  end
  else if ((macCoreClkSoftRst_n == 1'b0) ||  // Synchronous Reset
           (tsfSyncCs == TRIG_DIVIDER))
  begin
    moduloCnt    <= 6'h00;
    moduloInterm <= 17'h00000; 
  end
  // End of Modulo calculation
  else if ((moduloCnt == 6'd54) && (moduloInterm >= {1'd0,beaconInt}))
    moduloInterm <= {1'b0, moduloDiff[15:0]};
  // Modulo loop
  else if (tsfSyncCs == WAIT_MOD_VALID)
  begin
    // Increment counter
    moduloCnt <= moduloCnt + 6'h01;
    
    // Modulo calculation
    if (moduloInterm >= {1'd0,beaconInt}) 
      moduloInterm <= {moduloDiff[15:0], tsfOffset[63]}; 
    else 
      moduloInterm <= {moduloInterm[15:0], tsfOffset[63]}; 
  end
end

// Difference between modulo and Beacon interval
assign moduloDiff = moduloInterm - {1'b0, beaconInt}; 

// Final modulo value
assign modulo = {moduloInterm[15:0], tsfOffset[63:54]};

// Send pulse to update beacon Interval counter after calculation
// of the (TSF) mod (beacon Interval)
assign updateBeaconIntCnt_p = (tsfSyncCs == UPDATE_BCNINTV_CNT);


///////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
///////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////
// Display FSM State in string for RTL simulation waveform
//////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
// tsfSync FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (tsfSyncCs)
                 IDLE  :  tsfSyncCs_str = {"IDLE"};
    CHK_TSF_TO_UPDATE  :  tsfSyncCs_str = {"CHK_TSF_TO_UPDATE"};
           UPDATE_TSF  :  tsfSyncCs_str = {"UPDATE_TSF"};
         TRIG_DIVIDER  :  tsfSyncCs_str = {"TRIG_DIVIDER"};
       WAIT_MOD_VALID  :  tsfSyncCs_str = {"WAIT_MOD_VALID"};
   WAIT_ANOTHER_CLOCK  :  tsfSyncCs_str = {"WAIT_ANOTHER_CLOCK"};
   UPDATE_BCNINTV_CNT  :  tsfSyncCs_str = {"UPDATE_BCNINTV_CNT"};
              default  :  tsfSyncCs_str = {"XXX"};
   endcase
end
`endif // RW_SIMU_ON

endmodule
