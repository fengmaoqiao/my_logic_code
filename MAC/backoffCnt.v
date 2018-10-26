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

module backoffCnt #(parameter BACKOFFOFF= 0, CWRESET= 0)( 
            //$port_g Clock and Reset
            input  wire            macCoreClk,              // mac core clock      
            input  wire            macCoreClkHardRst_n,     // mac core clock reset
            
            input  wire            macCoreClkSoftRst_n,     // MAC core clock soft reset

            //$port_g backoffPRNG interface
            input  wire [18:0]     pseudoRandomNumber,      // pseudo random number
            
            //$port_g backoffCtrl interface
            input  wire            backoffCntLoad,          // pseudo random number
            input  wire            backoffCntEnable,        // pseudo random number
            input  wire            retryLtReached,          // pseudo random number
            
            //$port_g backoffACSel interface
            input  wire            InternalColl,            // pseudo random number
            output reg  [15:0]     backoffCntValue,         // current backoff status

            //$port_g macController interface
            input  wire            txFailed_p,              // Tx failed
            input  wire            txSuccessful_p,          // Tx Success
            
            //$port_g current state event
            input  wire            currentStateEvent,       // core state event
            
            //$port_g Timer interface
            input  wire            tickSlot_p,              // Indidcate the slot information
            
            //$port_g Registers interface
            input  wire [3:0]      cwMin,                   // minimum contention window
            input  wire [3:0]      cwMax,                   // maximum contention window
            input  wire [1:0]      backoffOffset,           // backoff offset
            
            output wire [3:0]      currentCW                // Current Contention Window size
            
        
            
);


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
//wire [31:0]              nullVector;                       // vector conatining on zero. Used for concatenation
//
reg  [ 3:0]              windowWidth;                      // size of the contention window
reg  [15:0]              randomCntValue;                   // resized to window width random value

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// Null Vector
//assign nullVector  = 32'b0;

assign currentCW = windowWidth;

always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
    // Window Width reset at 4'h5 
    windowWidth <= CWRESET[3:0];
  else if (!macCoreClkSoftRst_n)
    // Window Width reset at 4'h5 
    windowWidth <= CWRESET[3:0];
  else 
  begin
    if (currentStateEvent == 1'b1)
      windowWidth <= cwMin;
    else if (txSuccessful_p || retryLtReached)
      windowWidth <= cwMin;
    else if(txFailed_p || InternalColl)
      if(windowWidth == cwMax) 
        windowWidth <= windowWidth;
      else
        windowWidth <= windowWidth + 4'd1; 
    else
      windowWidth <= windowWidth; 
     
  end
end


// mapping the appropriate number of bits from the pseudo Random counter
// to the output port
always @ (windowWidth or pseudoRandomNumber)
begin
   case (windowWidth)
      4'h0    : randomCntValue = {16'b0};
      4'h1    : randomCntValue = {15'b0,pseudoRandomNumber[     BACKOFFOFF:BACKOFFOFF]};
      4'h2    : randomCntValue = {14'b0,pseudoRandomNumber[ 1 + BACKOFFOFF:BACKOFFOFF]};
      4'h3    : randomCntValue = {13'b0,pseudoRandomNumber[ 2 + BACKOFFOFF:BACKOFFOFF]};
      4'h4    : randomCntValue = {12'b0,pseudoRandomNumber[ 3 + BACKOFFOFF:BACKOFFOFF]};
      4'h5    : randomCntValue = {11'b0,pseudoRandomNumber[ 4 + BACKOFFOFF:BACKOFFOFF]};
      4'h6    : randomCntValue = {10'b0,pseudoRandomNumber[ 5 + BACKOFFOFF:BACKOFFOFF]};
      4'h7    : randomCntValue = { 9'b0,pseudoRandomNumber[ 6 + BACKOFFOFF:BACKOFFOFF]};
      4'h8    : randomCntValue = { 8'b0,pseudoRandomNumber[ 7 + BACKOFFOFF:BACKOFFOFF]};
      4'h9    : randomCntValue = { 7'b0,pseudoRandomNumber[ 8 + BACKOFFOFF:BACKOFFOFF]};
      4'hA    : randomCntValue = { 6'b0,pseudoRandomNumber[ 9 + BACKOFFOFF:BACKOFFOFF]};
      4'hB    : randomCntValue = { 5'b0,pseudoRandomNumber[10 + BACKOFFOFF:BACKOFFOFF]};
      4'hC    : randomCntValue = { 4'b0,pseudoRandomNumber[11 + BACKOFFOFF:BACKOFFOFF]};
      4'hD    : randomCntValue = { 3'b0,pseudoRandomNumber[12 + BACKOFFOFF:BACKOFFOFF]};
      4'hE    : randomCntValue = { 2'b0,pseudoRandomNumber[13 + BACKOFFOFF:BACKOFFOFF]};
      4'hF    : randomCntValue = { 1'b0,pseudoRandomNumber[14 + BACKOFFOFF:BACKOFFOFF]};
   endcase
end

// backOffCounter
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
    backoffCntValue     <= 16'h0;
  else if (!macCoreClkSoftRst_n)
    backoffCntValue     <= 16'h0;
  else 
  begin
    // laod the backoff counter with pseudo random value
    if (backoffCntLoad == 1'b1)
    begin
      backoffCntValue    <= randomCntValue + {14'd0,backoffOffset};
    end
    else
    begin
      // start to count when the back is enabled
      if (backoffCntEnable == 1'b1)
      begin
        // tickslot decrement the backoff counter
        if (tickSlot_p == 1'b1 && backoffCntValue != 16'd0 )
          backoffCntValue    <= backoffCntValue - 16'd1;
      end
      else
      begin
        backoffCntValue    <= backoffCntValue;
      end
    end
  end
end







endmodule
                 
