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
// Description      : Top level of nav module
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


module nav( 
            //$port_g Clock and Reset
            input  wire        macCoreClk,                    // mac core clock      
            input  wire        macCoreClkHardRst_n,           // mac core clock reset
            input wire         macCoreClkSoftRst_n,           // Soft Reset of the MAC Core Clock domain
                                                              // active low
            //$port_g MAC Controller Module interface
            input  wire [15:0] ctsDuration,                   // Indicates the duration of a CTS frame response of the received RTS
            input  wire        ctsDurationValid_p,            // Indicates that the ctsDuration is valid
            input  wire [15:0] ackDuration,                   // Indicates the duration of a ACK frame response of the received PS-POLL
            input  wire        ackDurationValid_p,            // Indicates that the ackDuration is valid
            input  wire  [7:0] phyRxStartDelay,               // Receive Start Delay of the PHY
            input  wire        moveToActive_p,                // Core should now move to ACTIVE state
            input  wire        stopRx_p,                      // Stop Rx
            
            //$port_g Rx controller interface
            input  wire        navClear_p,                    // Clear NAV
            input  wire        navUpdate_p,                   // Update NAV with frame duration
            input  wire [15:0] rxFrameDuration,               // Frame duration
            input  wire        navCfpDurRemUpdate_p,          // Update NAV with CFP duration remaining
            input  wire [15:0] cfpDurRemaining,               // CFP duration remaining
            input  wire        navLsigUpdate_p,               // Update NAV with LSIG
            input  wire [15:0] navLsigDuration,               // Update NAV LSIG duration
            input  wire        notMinePsPollRcved_p,          // indicate reception of a pspoll
            input  wire        incorrectRcved_p,              // Frame not received correctly for PS-POLL case
            input  wire        correctRcved_p,                // Frame received correctly
            input  wire        notMineRtsRcved_p,             // indicate the reception of an RTS
                         
            //$port_g macPhyIf interface
            input  wire        macPhyIfRxEndForTiming_p,      // end of transmission (antenna) 
            input  wire        macPhyIfRxEnd_p,               // end of transmission
            input  wire        macPhyIfRxErr_p,               // Rx error from MAC-PHY if. resynchronized
            input  wire        macPhyIfRxStart_p,             // Start of reception pulse
 
            //$port_g MAC Timer Unit interface
            input  wire        tick1us_p,                     // 1 us pulse
            input  wire        rxDot11a,                      // Last received packet is 802.11a
            input  wire        navCfpMaxDurUpdate_p,          // Update NAV with CFP Max duration
            input  wire        loadQuietDuration_p,           // load quiet duration
            input  wire [15:0] quietDuration,                 // quiet duration value
            output wire        channelToIdle_p,               // NAV will go idle

            //$port_g Registers If
            input  wire [ 7:0] sifsB,                         // SIFS Duration for 802.11b in us
            input  wire [ 7:0] sifsA,                         // SIFS Duration for 802.11a in us
            input  wire [ 7:0] slotTime,                      // slot time for timeout
            input  wire [ 2:0] abgnMode,                      // Indicate the current operating mode
            input  wire [15:0] cfpMaxDuration,                // CFP Max duration
            input  wire [15:0] probeDelay,                    // Probe delay during active scan
            input  wire [25:0] navCounter,                    // counter value from registers
            output wire [25:0] navCounterIn,                  // counter value to registers
            output reg         navCounterInValid,             // counter value to registers
            
            //$port_g Status
            output wire        channelBusy,                   // Channel busy indicator
            output wire        channelIdle,                   // channel idle indicator
            
            //$port_g Debug
            output wire [15:0] debugPortNAV                   // Debug Port NAV
            );

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
reg         rtsRcvdSampled;        // keep in memory the RTS received indicator
reg         notMineRtsRcved;       // Capture version of notMineRtsRcved_p

reg         navCounterEnable;      // counter enable
reg  [25:0] navCounterEnd;         // counter end of count value
reg  [15:0] int_ctsDuration;       // For time out counter
reg  [ 7:0] int_phyRxStartDelay;   // For time out counter
reg         navCounterHoldsQuiet;  // hold quiet duration
reg         navCounterHoldsProbe;  // hold probe delay

reg         endForceInc;           // indicate end of received frame

reg         navRestart_p;          // indicate NAV has to restart count
reg  [ 7:0] navRestartOffset;      // NAV offset in case of restart
reg         navRestartOffsetEn;    // Enable NAV offset calculation

wire [15:0] timeoutVal;            // value for the timeout
reg         timeout_p;             // indicate a timeout occured
reg  [15:0] timeoutCount;          // time out counter
reg         psPollReceived;        // a pspoll has been received
wire [15:0] pspollAckprotection;   // a pspollprotection length

wire [ 7:0] sifsMux;               // SIFS mux

wire [25:0] navCounterRemaining;   // counter remaining
reg  [25:0] navCounterInt;   // counter remaining

reg  [15:0] rxFrameDurationSigExt; // Frame duration with signal extension
wire        needSigExt;            // Signal extension needed
reg         rxErrDetected;         // Flag indicating that the rxErr_p has been received 
reg         correctRcved;          // Flag indicating that the correctRcved_p has been received 
reg         incorrectRcved;        // Flag indicating that the incorrectRcved_p has been received 

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// SIFS mux
assign sifsMux = (rxDot11a) ? sifsA : sifsB;

// rxFrameDuration with Signal extension
// In 2.4GHz, when HW receives an OFDM PPDU, it subtracts 6us during NAV update
assign needSigExt = rxDot11a && ((abgnMode == 3'h2) || (abgnMode == 3'h3));

// Remove the signal extension from the rxFrameDuration when needed
always @ *
begin
  if (needSigExt)
  begin
    if (rxFrameDuration > 16'h6)
      rxFrameDurationSigExt = rxFrameDuration - 16'h6; 
    else 
      rxFrameDurationSigExt = 16'h0; 
  end
  else    
    rxFrameDurationSigExt = rxFrameDuration; 
end

// ctsDuration sampling
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    int_ctsDuration <= 16'h0000;
  else if(macCoreClkSoftRst_n == 1'b0)
    int_ctsDuration <= 16'h0000;
  else if (ctsDurationValid_p)
    int_ctsDuration <= ctsDuration;
end

// phyRxStartDelay sampling
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    int_phyRxStartDelay <= 8'h0;
  else if(macCoreClkSoftRst_n == 1'b0)
    int_phyRxStartDelay <= 8'h0;
  else if (ctsDurationValid_p)
    int_phyRxStartDelay <= phyRxStartDelay;
end

// macPhyIfRxErr_p sampling
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxErrDetected <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxErrDetected <= 1'b0;
  else if (macPhyIfRxErr_p)
    rxErrDetected <= 1'b1;
  else if (macPhyIfRxEnd_p || macPhyIfRxStart_p)
    rxErrDetected <= 1'b0;
end

// correctRcved_p sampling
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    correctRcved <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    correctRcved <= 1'b0;
  else if (correctRcved_p)
    correctRcved <= 1'b1;
  else if (macPhyIfRxEnd_p || macPhyIfRxStart_p)
    correctRcved <= 1'b0;
end

// incorrectRcved_p sampling
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    incorrectRcved <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    incorrectRcved <= 1'b0;
  else if (incorrectRcved_p)
    incorrectRcved <= 1'b1;
  else if (macPhyIfRxEnd_p || macPhyIfRxStart_p)
    incorrectRcved <= 1'b0;
end

assign pspollAckprotection  = ackDuration + {8'b0, sifsMux};

assign channelIdle = !navCounterEnable;
assign channelBusy = navCounterEnable;

// to be refined
//assign timeoutVal = 2*{8'b0, sifsMux} + 2*{8'b0, slotTime} + {8'b0, int_phyRxStartDelay} + int_ctsDuration;
assign timeoutVal = {7'b0, sifsMux,1'b0} + {7'b0, slotTime,1'b0} + {8'b0, int_phyRxStartDelay} + int_ctsDuration;

// channelToIdle_p generation 1 cc before channel goes to idle for SIFS boundary
assign channelToIdle_p = (navClear_p || 
                         (macPhyIfRxStart_p && navCounterHoldsProbe) ||
                         (timeout_p && !navCounterHoldsQuiet) ||
                         ((navCounterInt >= (navCounterEnd - 26'h1)) && 
                         tick1us_p && !navCounterHoldsQuiet));

// nav counter control
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    navCounterInt     <= 26'h0000;
    navCounterEnable  <= 1'b0;
    navCounterInValid <= 1'b1;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    navCounterInt     <= 26'h0000;
    navCounterEnable  <= 1'b0;
    navCounterInValid <= 1'b1;
  end
  else
  begin
    if (((macPhyIfRxEndForTiming_p && !macPhyIfRxEnd_p &&  !rxErrDetected) || navCfpMaxDurUpdate_p ||
         loadQuietDuration_p || moveToActive_p || navLsigUpdate_p) &&
        (navCounter == 26'h0000))
    begin
      navCounterEnable  <= 1'b1;
      navCounterInt     <= 26'h0000;
      navCounterInValid <= 1'b1;
    end
    // reset the NAV in case of external clear or timeout
    else if (navClear_p || (timeout_p && !navCounterHoldsQuiet) ||
      (endForceInc && (navCounterEnd == 26'h0000)) ||
      (navCounterHoldsProbe && macPhyIfRxStart_p))
    begin
      navCounterEnable  <= 1'b0;
      navCounterInt     <= 26'h0000;
      navCounterInValid <= 1'b1;
    end
    // restart the NAV count
    else if (navRestart_p)
    begin
      navCounterInt     <= {18'h0000, navRestartOffset};
      navCounterInValid <= 1'b1;
    end
    else if (navCounterEnable && tick1us_p)
    begin
      navCounterInValid  <= 1'b1;
      if (!endForceInc)
        navCounterInt     <= navCounterInt + 26'd1;
      else if (navCounterInt >= (navCounterEnd - 26'd1))
      begin
        navCounterEnable <= 1'b0;
        navCounterInt     <= 26'h0000;
      end
      else
        navCounterInt     <= navCounterInt + 26'd1;
    end
    else
      navCounterInValid  <= 1'b0;
  end     
end

// nav counter remaining
assign navCounterRemaining = (navCounterEnable) ? navCounterEnd - navCounterInt : 26'd0;
assign navCounterIn        = navCounterRemaining;

// nav counterEnd control
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    navCounterEnd <= 26'h0000;
    navRestart_p  <= 1'b0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    navCounterEnd <= 26'h0000;
    navRestart_p  <= 1'b0;
  end
  else
  begin
    // navRestart_p pulse generation
    navRestart_p  <= 1'b0;
    
    // update remaining duration
    if (navCfpDurRemUpdate_p)
    begin
      if ({10'h0,cfpDurRemaining} > navCounterEnd)
        navCounterEnd <= {10'h0,cfpDurRemaining};
      if ({10'h0,cfpDurRemaining} > navCounterRemaining)
      begin
        navRestart_p  <= 1'b1;
        navCounterEnd <= {10'h0,cfpDurRemaining};
      end
    end
    // update max duration
    else if (navCfpMaxDurUpdate_p)
    begin
      if ({10'h0,cfpMaxDuration} > navCounterEnd)
        navCounterEnd <= {10'h0,cfpMaxDuration}; 
      if ({10'h0,cfpMaxDuration} > navCounterRemaining)
      begin
        navRestart_p  <= 1'b1;
        navCounterEnd <= {10'h0,cfpMaxDuration}; 
      end
    end
    // pspoll received
    else if (psPollReceived && navUpdate_p)
    begin 
      if (ackDurationValid_p)
      begin
        if  ({10'h0,pspollAckprotection} >  navCounterEnd)
          navCounterEnd <= {10'h0,pspollAckprotection};
        if ({10'h0,pspollAckprotection} > navCounterRemaining)
        begin
          navRestart_p  <= 1'b1;
          navCounterEnd <= {10'h0,pspollAckprotection};
        end
      end
    end
    // update frame duration
    else if (navUpdate_p && !rxFrameDuration[15])
    begin
      if ({10'h0,rxFrameDurationSigExt} >  navCounterEnd)
        navCounterEnd <= {10'h0,rxFrameDurationSigExt};
      if ({10'h0,rxFrameDurationSigExt} > navCounterRemaining)
      begin
        navRestart_p  <= 1'b1;
        navCounterEnd <= {10'h0,rxFrameDurationSigExt};
      end
    end
    // update L-SIG duration (No check on current NAV needed)
    else if (navLsigUpdate_p)
    begin
      if ({10'h0,navLsigDuration} >  navCounterEnd)
       navCounterEnd <= {10'h0,navLsigDuration}; 
      if ({10'h0,navLsigDuration} > navCounterRemaining)
      begin
        navRestart_p  <= 1'b1;
        navCounterEnd <= {10'h0,navLsigDuration};
      end   
    end 
    // update probe delay (No check on current NAV needed)
    else if (moveToActive_p)
       navCounterEnd <= {10'b0,probeDelay}; 
    // update quiet duration (No check on current NAV needed)
    else if (loadQuietDuration_p)
       navCounterEnd <= {quietDuration,10'b0}; 
    // reset the NAV in case of external clear or timeout or NAV disable
    else if (navClear_p || (timeout_p && !navCounterHoldsQuiet) || !navCounterEnable)
       navCounterEnd <= 26'h0000;
  end
end

// nav timeout control
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    timeoutCount    <= 16'h0000;
    timeout_p       <= 1'b0;
    rtsRcvdSampled  <= 1'b0;
    notMineRtsRcved <= 1'b0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    timeoutCount    <= 16'h0000;
    timeout_p       <= 1'b0;
    rtsRcvdSampled  <= 1'b0;
    notMineRtsRcved <= 1'b0;
  end
  else
  begin
    if (notMineRtsRcved_p && !rxFrameDuration[15])
      notMineRtsRcved <= 1'b1;
    else if (macPhyIfRxEnd_p || timeout_p || macPhyIfRxStart_p || incorrectRcved_p)
      notMineRtsRcved <= 1'b0;

    if (timeout_p || macPhyIfRxStart_p || incorrectRcved_p)
      rtsRcvdSampled <= 1'b0;
    else if (notMineRtsRcved && macPhyIfRxEnd_p)
      rtsRcvdSampled <= 1'b1;
     
    // reset the nav timeout when packet is received 
    // or when channel is idle
    if ((navCounter == 26'h0000) || macPhyIfRxStart_p)
    begin
      timeoutCount   <= 16'h0000;
      timeout_p      <= 1'b0;
    end
    else if (tick1us_p)
    begin
      // timeout reached, assert timeout pulse
      if ((timeoutCount  == (timeoutVal - 16'd1)) && rtsRcvdSampled)
      begin
        timeoutCount   <= 16'h0000;
        timeout_p      <= 1'b1;
      end
      // stop the count when hold duration is enabled
      else if (!navCounterHoldsQuiet  && rtsRcvdSampled)
      begin
        timeoutCount <= timeoutCount + 16'd1;
        timeout_p    <= 1'b0;
      end
      else
      begin
        timeoutCount <= timeoutCount;
        timeout_p    <= 1'b0;
      end
    end
    else
    begin
      timeoutCount <= timeoutCount;
      timeout_p    <= 1'b0;
    end
  end
end

// input pulse latch
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    psPollReceived       <= 1'b0;
    navCounterHoldsQuiet <= 1'b0;
    navCounterHoldsProbe <= 1'b0;
    endForceInc          <= 1'b0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    psPollReceived       <= 1'b0;
    navCounterHoldsQuiet <= 1'b0;
    navCounterHoldsProbe <= 1'b0;
    endForceInc          <= 1'b0;
  end
  else
  begin
    // PS-POLL received
    if (notMinePsPollRcved_p)
      psPollReceived <= 1'b1;
    else if (navUpdate_p || incorrectRcved_p)
      psPollReceived <= 1'b0;
    
    // end of NAV incrementation force for time between macPhyIfRxEndForTiming_p
    // and end of frame
    if (incorrectRcved || correctRcved || navCfpMaxDurUpdate_p ||
      loadQuietDuration_p || moveToActive_p || rxErrDetected || stopRx_p)
      endForceInc <= 1'b1;
    else if (!navCounterEnable)
      endForceInc <= 1'b0;
    
    // start quiet duration
    if (loadQuietDuration_p) 
      navCounterHoldsQuiet <= 1'b1;
    // end quiet duration
    else if (!navCounterEnable)
      navCounterHoldsQuiet <= 1'b0;

    // start probe delay
    if (moveToActive_p) 
      navCounterHoldsProbe <= 1'b1;
    // end probe delay
    else if (!navCounterEnable)
      navCounterHoldsProbe <= 1'b0;
  end
end

// navRestartOffset computation
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    navRestartOffset   <= 8'b0;
    navRestartOffsetEn <= 1'b0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    navRestartOffset   <= 8'b0;
    navRestartOffsetEn <= 1'b0;
  end
  else
  begin
    // NAV restart offset enable
    if (navCounterEnable && macPhyIfRxEndForTiming_p)
      navRestartOffsetEn <= 1'b1;
    else if (!navCounterEnable || navRestart_p || incorrectRcved || correctRcved)
      navRestartOffsetEn <= 1'b0;
      
    // NAV restart offset calculation
    if (navRestartOffsetEn && tick1us_p)
      navRestartOffset <= navRestartOffset + 8'd1;
    else if (!navRestartOffsetEn)
      navRestartOffset <= 8'b0;
  end
end

// Debug Port assigment
assign debugPortNAV = {channelBusy,
                       navClear_p,
                       navUpdate_p,
                       macPhyIfRxEnd_p,
                       psPollReceived,
                       endForceInc,
                       notMineRtsRcved,
                       incorrectRcved_p,
                       correctRcved_p,
                       navLsigUpdate_p,
                       macPhyIfRxEndForTiming_p,
                       timeout_p,
                       navCounterEnable,
                       navRestart_p,
                       stopRx_p,
                       macPhyIfRxErr_p};
                       
                        
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_ASSERT_ON


//$rw_sva Check the nav update and cfpDurRemaing are not upated at the same time
property not_navUpdate_p_while_cfpDurRemaining_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  navCfpDurRemUpdate_p|->!navUpdate_p;
endproperty
not_navUpdate_p_while_cfpDurRemaining: assert property (not_navUpdate_p_while_cfpDurRemaining_prop); 

//$rw_sva Check the nav update and cfpDurRemaing are not upated at the same time
property not_cfpDurRemaining_while_navUpdate_p_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  navUpdate_p|->!navCfpDurRemUpdate_p;
endproperty
not_cfpDurRemaining_while_navUpdate_p: assert property (not_cfpDurRemaining_while_navUpdate_p_prop); 


//$rw_sva Check check no idle while busy
property not_channelbusy_while_idle_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  channelBusy|->!channelIdle;
endproperty
not_channelbusy_while_idle: assert property (not_channelbusy_while_idle_prop); 

//$rw_sva Check check no busy while idle
property not_channelidle_while_busy_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  channelIdle|->!channelBusy;
endproperty
not_channelidle_while_busy: assert property (not_channelidle_while_busy_prop); 

//$rw_sva Check timeout_p is a pulse
property timeout_p_pulse_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  timeout_p|=>!timeout_p;
endproperty
timeout_p_pulse: assert property (timeout_p_pulse_prop); 

//$rw_sva Check channelToIdle_p is a pulse
property channelToIdle_p_pulse_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  channelToIdle_p|=>!channelToIdle_p;
endproperty
channelToIdle_p_pulse: assert property (channelToIdle_p_pulse_prop); 

//$rw_sva Check channelToIdle_p comes before channel idle
property channelToIdle_p_before_idle_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  $rose(channelToIdle_p) |=> channelIdle;
endproperty
channelToIdle_p_before_idle: assert property (channelToIdle_p_before_idle_prop); 


`endif // RW_ASSERT_ON

endmodule
