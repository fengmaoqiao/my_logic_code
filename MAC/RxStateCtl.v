//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author          : $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: $
// $Date: $
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : Controls the Rx part of the Phy interface
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

module RxStateCtl( 
            //$port_g clock and Reset
            input  wire    mpIFClk,                   // PHY clock
            input  wire    mpIFClkHardRst_n,          // PHY clock hard reset
            input  wire    mpIFClkSoftRst_n,         // PHY clock soft reset
            input  wire    macCoreRxClk,              // mac core Rx clock                  
            input  wire    macCoreClkHardRst_n,       // mac core Rx clock hard reset            
            
            //$port_g control
            input  wire   startRx,                    // Start Rx trigger
            input  wire   stopRx_p,                   // Stop Rx trigger
            
            //$port_g PHY IF
            input  wire   rxErr_p,                    // Rx error
            input  wire   rxEnd_p,                    // Rx end
            input  wire   phyRdy,                     // data valid signal                  
            input  wire   rxEndForTiming_p,           // end of transmission (antenna) 
            //
            output reg    rxReq,                      // Rx request
            
            //$port_g FIFO control
            input  wire   mpIfRxFifoFull,             // Rx Fifo full
            output wire   fifoWriteEn,                // Rx fifo write enable
            //
            output wire   rxFifoRdClkFlush,           // flush FIFO on macCoreRxClk domain

            //$port_g Rx controller
            output wire   macPhyIfRxErr_p,            // Rx error 
            output reg    macPhyIfRxEnd_p,            // Rx end
            output wire   macPhyIfRxEndForTiming_p,   // end of reception at the antenna                  

            output reg    forceCCAPrimary,            // Force the CCA Primary high between the first byte
                                                      // of the rxVector1 and the rxEndForTiming_p

            //$port_g Mac Controller If                                                            
            output wire   macPhyIfRxStart_p,          // Start of reception pulse

            //$port_g CSReg
            input  wire   macPHYIFFIFOReset,          // Flush the FIFO
            input  wire   rxReqForceDeassertion,      // Force deassertion of rxReq after each rxEnd_p
            
            //$port_g Interrupt controller
            output  reg   mpifOverflow,               // RX Overflow
            
            //$port_g Keep RF
            input  wire   mackeepRFOn,                // input Keep RF
            //
            output reg    RxkeepRFOn,                  // output Keep RF

            //$port_g Diag Port
            output wire [15:0] debugPortMACPhyIf2
            );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
//$fsm_sd rxstate
localparam
                 IDLE  =  3'd0,  // 
             RXVECTOR  =  3'd1,  // 
               RXDATA  =  3'd2,  // 
                RXEND  =  3'd3,  // 
              RXERROR  =  3'd4;  // 



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
  // String definition to dislpay rxstate current state
  reg [8*8:0] rxstateCs_str;
`endif // RW_SIMU_ON


// rxstate FSM signals definition
reg [2:0] rxstateCs;              // rxstate FSM Current State
reg [2:0] rxstatePs;              // rxstate FSM Previous State
reg [2:0] rxstateNs;              // rxstate FSM Next State

reg [4:0] rx_vector_cnt;          // Rx vector counter

wire      fifo_reset;             // fifo reset from registers

reg       modemIsStarted;         // indicate the modem started to trannsmit data

wire      phyRxStart_p;           // Start of reception pulse

reg       rxEndForTimingInt_p;    // Internal version of rxEndForTiming_p
reg       rxEndForTimingRcved;    // Indicates that the pulse rxEndForTiming_p has been received during RXVECTOR state

wire      macPhyIfRxEndInt_p;            // Rx end

wire      rxFifoWrClkFlush;           // flush FIFO

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

assign fifoWriteEn = rxReq && phyRdy;


pulse2PulseSynchro U_macPhyIfRxErrInt_p_synchro (
                .srcclk (mpIFClk),
                .srcresetn (mpIFClkHardRst_n),
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (rxErr_p),
                .dstdata (macPhyIfRxErr_p)
                );

pulse2PulseSynchro U_macPhyIfRxEnd_p_synchro (
                .srcclk (mpIFClk),
                .srcresetn (mpIFClkHardRst_n),
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (rxEnd_p),
                .dstdata (macPhyIfRxEndInt_p)
                );
                
// Delayed macPhyIfRxEnd_p of 1cc
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPhyIfRxEnd_p <= 1'b0; 
  else
    macPhyIfRxEnd_p <= macPhyIfRxEndInt_p; 
end

pulse2PulseSynchro U_fifoflush_synchro (
                .srcclk (mpIFClk),
                .srcresetn (mpIFClkHardRst_n),
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (rxFifoWrClkFlush),
                .dstdata (rxFifoRdClkFlush)
                );

pulse2PulseSynchro U_fiforeset_synchro (
                .srcclk (macCoreRxClk),
                .srcresetn (macCoreClkHardRst_n),
                .dstclk (mpIFClk),
                .dstresetn (mpIFClkHardRst_n),
                .srcdata (macPHYIFFIFOReset),
                .dstdata (fifo_reset)
                );

pulse2PulseSynchro U_macPhyIfRxStart_p_synchro (
                .srcclk (mpIFClk),
                .srcresetn (mpIFClkHardRst_n),
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (phyRxStart_p),
                .dstdata (macPhyIfRxStart_p)
                );

pulse2PulseSynchro U_macPhyIfRxEndForTiming_p_synchro (
                .srcclk (mpIFClk),
                .srcresetn (mpIFClkHardRst_n),
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (rxEndForTimingInt_p),
                .dstdata (macPhyIfRxEndForTiming_p)
                );


// flush mechanism
assign rxFifoWrClkFlush = (fifo_reset || ((rxstateCs == IDLE) && (rxstatePs == RXERROR)) || ((rxstateCs == RXEND) && (rxstatePs != RXEND))) ? 1'b1 : 1'b0;

// rxstate FSM Current State Logic 
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxstateCs <= IDLE; 
  else if (mpIFClkSoftRst_n == 1'b0)  // Synchronous Reset
    rxstateCs <= IDLE; 
  else
    rxstateCs <= rxstateNs; 
end

// rxstate FSM Previous State Logic 
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxstatePs <= IDLE; 
  else if (mpIFClkSoftRst_n == 1'b0)  // Synchronous Reset
    rxstatePs <= IDLE; 
  else
    rxstatePs <= rxstateCs; 
end

// rxstate FSM Next State Logic.
always @* 
begin
  case(rxstateCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits for the Mac controller trigger.
      if (stopRx_p) 
        //$fsm_t When stopRx_p is true, the state machine goes to RXEND state to flush the MAC PHY RX FIFO
        rxstateNs = RXEND; 
      else if (startRx) 
        //$fsm_t When startRx is true, the state machine goes to RXVECTOR state
        rxstateNs = RXVECTOR; 
      else
        rxstateNs = rxstateCs; 

    RXVECTOR:
      //$fsm_s In RXVECTOR state, the state machine to have transmitted all the Tx vector
      if (rxErr_p)
        //$fsm_t When rx error is asserted by the phy or the Mac controller
        // stop the Reception
        rxstateNs = RXERROR;
      else if (rx_vector_cnt == 5'd15) 
        //$fsm_t When rx_vector_cnt is over go to rx_data
        rxstateNs = RXDATA; 
      else if (stopRx_p)
        //$fsm_t When rx error is asserted by the phy or the Mac controller
        // stop the Reception
        rxstateNs = RXEND;
      else
        rxstateNs = rxstateCs; 

    RXDATA:
      //$fsm_s In RXDATA state, the state machine waits the end of the Reception
      // the Phy asserts Rxend when all the data have been sent ot the MAC
      if (rxErr_p)
        //$fsm_t When rx error is asserted by the phy or the Mac controller
        // stop the Reception
        rxstateNs = RXERROR;
      else if (rxEnd_p) 
        //$fsm_t When rxend is true, the state machine goes to IDLE state
        rxstateNs = IDLE; 
      else if (stopRx_p || mpifOverflow)
        //$fsm_t When Rx Error is true, the state machine goes to RXEND state
        rxstateNs = RXEND;
      else
        rxstateNs = rxstateCs; 

    RXEND:
      //$fsm_s In RXEND state, the state machine waits for Rxend to happens 
      // This is to make sure the PHY is idle before any other transaction
      if (modemIsStarted)
      begin
        if (rxEnd_p) 
          //$fsm_t When rxEnd_p is true, the state machine goes to IDLE state
          rxstateNs = IDLE; 
        else
          rxstateNs = rxstateCs; 
      end
      else
        //$fsm_t modem is not started move unconditionnaly to IDLE
        rxstateNs = IDLE; 

    RXERROR:
      //$fsm_s In RXDATA state, the state machine waits the end of the Reception
      // the Phy asserts Rxend when all the data have been sent ot the MAC
      if (stopRx_p)
        //$fsm_t When rx error is asserted by the phy or the Mac controller
        // stop the Reception
        rxstateNs = IDLE;
      else
        rxstateNs = rxstateCs; 

        
    // Disable coverage on the default state because it cannot be reached.
    default:   
       rxstateNs = IDLE; 
  endcase
end

// rx vector counter
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    rx_vector_cnt <= 5'b0000; 
  else if (mpIFClkSoftRst_n == 1'b0)  // Synchronous Reset
    rx_vector_cnt <= 5'b0000; 
  // increment vector count each time a vector is sampled 
  // byt the rx FIFO
  else if ( rxstateCs == RXVECTOR ) 
  begin
    if (phyRdy)
      rx_vector_cnt <= rx_vector_cnt + 5'd1; 
  end
  else
     rx_vector_cnt <= 5'b0000; 
end

assign phyRxStart_p = (rx_vector_cnt == 5'h1);

// control interface
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxReq             <= 1'b0; 
  else if (mpIFClkSoftRst_n == 1'b0)  // Synchronous Reset
    rxReq             <= 1'b0; 
  else 
  begin
    if (rxReqForceDeassertion)
    begin
      if (rxEnd_p || stopRx_p || (rxstateCs == IDLE) || (rxstateCs == RXERROR))
        rxReq            <= 1'b0;
      else if (startRx)
        rxReq            <= 1'b1;
    end
    else
    begin    
      if (startRx &&  (rxstateCs != RXERROR))
        rxReq            <= 1'b1;
      else
        rxReq            <= 1'b0;
    end    
  end
end

// rxEndForTiming_p 
// To avoid the generation of rxEndForTiming_p pulse to the macCore 
// before the providing macPhyIfRxStart_p, the rxEndForTiming_p is latched 
// when the FSM is in RXVECTOR and generated only when the FSM is in RXDATA
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    rxEndForTimingRcved <= 1'b0; 
    rxEndForTimingInt_p <= 1'b0;
  end  
  else if (rxstateCs == IDLE)
  begin
    rxEndForTimingRcved <= 1'b0; 
    rxEndForTimingInt_p <= 1'b0;
  end  
  else
  begin
    rxEndForTimingInt_p <= 1'b0;
    if (rxEndForTiming_p)
    begin
      if ((rxstateCs == RXVECTOR) && (rx_vector_cnt <= 5'd6))
        // When the rxEndForTiming_p pulse is received during RXVECTOR state,
        // the flag rxEndForTimingRcved is set
        rxEndForTimingRcved <= 1'b1; 
      else
        // When the rxEndForTiming_p pulse is received outside RXVECTOR side,
        // the pulse rxEndForTimingInt_p is generated
        rxEndForTimingInt_p <= 1'b1;
    end     
    if (rxEndForTimingRcved && ((rxstateCs != RXVECTOR) || (rx_vector_cnt > 5'd6)))
    begin
      // When the flag rxEndForTimingRcved was set and the FSM leaves RXVECTOR state,
      // the pulse rxEndForTimingInt_p is generated
      rxEndForTimingRcved <= 1'b0; 
      rxEndForTimingInt_p <= 1'b1;
    end  
  end
end

always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    forceCCAPrimary <= 1'b0; 
  else if (rxstateCs == IDLE)
    forceCCAPrimary <= 1'b0; 
  else
  begin
    if ((rxstateCs == RXVECTOR) && (rx_vector_cnt == 5'd1))
      forceCCAPrimary <= 1'b1; 
    if (rxEndForTimingInt_p || rxEnd_p)
      forceCCAPrimary <= 1'b0; 
  end
end




// Keep RF On
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    RxkeepRFOn      <= 1'b0; 
  else if (mpIFClkSoftRst_n == 1'b0)  // Synchronous Reset
    RxkeepRFOn      <= 1'b0; 
  else 
  begin
    if (rxReq && !rxEndForTimingRcved)
      RxkeepRFOn   <= mackeepRFOn; 
  end
end

// control interface
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    mpifOverflow <= 1'b0; 
  else if (rxstateCs == IDLE)
    mpifOverflow <= 1'b0; 
  else
  begin
    mpifOverflow <= 1'b0;
    // Violation if the FIFO handling
    // assert overflow
    if (mpIfRxFifoFull && fifoWriteEn)
      mpifOverflow <= 1'b1; 
  end
end

// detect modem started to transmit
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    modemIsStarted      <= 1'b0; 
  else if (mpIFClkSoftRst_n == 1'b0)  // Synchronous Reset
    modemIsStarted      <= 1'b0; 
  else 
  begin
    if (((rxstateCs == RXVECTOR)  ||
         (rxstateCs == RXDATA  )) &&
         phyRdy)
      modemIsStarted   <= 1'b1; 
    else if (rxstateCs == IDLE)
      modemIsStarted   <= 1'b0; 
  end
end


assign debugPortMACPhyIf2 = {modemIsStarted,
                             mpifOverflow,
                             mpIfRxFifoFull,
                             rxReqForceDeassertion,
                             startRx,
                             mpIFClkSoftRst_n,
                             stopRx_p,
                             rx_vector_cnt,
                             rxReq,
                             rxstateCs};


// rxstate FSM states definition
`ifdef RW_SIMU_ON
// rxstate FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (rxstateCs)
                 IDLE  :  rxstateCs_str = {"IDLE"};
             RXVECTOR  :  rxstateCs_str = {"RXVECTOR"};
               RXDATA  :  rxstateCs_str = {"RXDATA"};
                RXEND  :  rxstateCs_str = {"RXEND"};
              RXERROR  :  rxstateCs_str = {"RXERROR"};
   endcase
end
`endif // RW_SIMU_ON
endmodule
                 
