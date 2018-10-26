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
//   This block is output buffer which conbverts 128 bit o/p of aes block into the
//   streams of 8 bits
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

module ccmpOutReg (

  //$port_g Inputs
  input  wire         pClk,            // baseband clock signal
  input  wire         nPRst,           // reset signal from hardware
  input  wire         nSRst,           // reset signal from software
  input  wire         rxCsIsIdle,      // Indicates Encrypt/Decrypt
  input  wire         rxError_p,       // Indicates Rx Error
  input  wire         tcTxErrorP,      // Indicates Tx Error
  input  wire         payloadEnd_p,    // Indicates that pay load End
  input  wire [3:0]   payloadLen,      // length of pay load
  input  wire         micValid_p,      // Indicates that MIC is valid
  input  wire [63:0]  mic,             // MIC output
  input  wire [127:0] ccmOutData,      // CCM output data to output reg
  input  wire         ccmOutValid_p,   // Indicates that CCM data is valid
  input  wire         txRxBufferFull,  // Indicates that Tx buffer is full

  //$port_g Outputs
  output wire [7:0]   ccmpOutData,     // Indicates that ccmp data is valid
  output reg          ccmpOutValid,    // 8 bit output data
  output wire         ccmpOutLast_p    // Last data from CCMP
  );

// ------------------------ Register Declarations ------------------
  reg  [127:0] outReg;
  reg  [127:0] nextoutReg;
  reg  [3:0]   regPtr;
  reg  [3:0]   nextregPtr;
  reg          nextccmpOutValid;
  reg          nextlastBlock;
  reg          lastBlock;
  reg          micValid;
  reg          nextmicValid;
  reg          micValidReg;

// ------------------------ Wire Declarations ---------------------
  wire [3:0]   newpayloadLen;

//--------------Logic Begins---------------------------------------
// Data register and pointer logic
  always @*
  begin
    nextregPtr = regPtr;
    nextoutReg = outReg;
    if (tcTxErrorP || rxError_p)
      nextregPtr = 4'h0;
    else if (ccmpOutValid == 1'b0)
    begin
      nextregPtr = 4'h0;
      if (micValid && (lastBlock == 1'b0))
        nextoutReg = {64'h0000_0000_0000_0000,mic}; 
      else
        nextoutReg = ccmOutData;
    end
    else if (txRxBufferFull == 1'b0)
    begin
      nextregPtr = regPtr + 4'h1; 
      nextoutReg = {8'h00,outReg[127:8]};
    end
  end

// ccmOutValid generation
  always @*
  begin
    if (tcTxErrorP || rxError_p)
      nextccmpOutValid = 1'b0;
    else if ((regPtr == 4'hF || (regPtr == newpayloadLen  && lastBlock) || (regPtr == 4'h7 && micValid && ~lastBlock)) && ~(txRxBufferFull))
      nextccmpOutValid = 1'b0;
    else if(ccmOutValid_p || (micValid && (lastBlock == 1'b0)))
      nextccmpOutValid = 1'b1;
    else
      nextccmpOutValid = ccmpOutValid;
  end

// Last block signal generation
  always @*
  begin
    if((regPtr == newpayloadLen  && lastBlock &&  ~(txRxBufferFull)) || tcTxErrorP || rxError_p)
      nextlastBlock = 1'b0;
    else if(payloadEnd_p)
      nextlastBlock = 1'b1;
    else
      nextlastBlock = lastBlock;
  end

// Final Mic valid  signal generation
  always @*
  begin
    if(micValid_p && rxCsIsIdle) 
      nextmicValid = 1'b1;
    else if((regPtr == 4'h7 && (micValidReg == 1'b0) && (txRxBufferFull == 1'b0)) || tcTxErrorP || rxError_p)
      nextmicValid = 1'b0;
    else 
      nextmicValid = micValid;
  end

// sequential logic 
  always@(posedge pClk or negedge nPRst) 
  begin
    if(nPRst == 1'b0)
      micValidReg   <= 1'b0;
    else if (nSRst == 1'b0)
      micValidReg   <= 1'b0;
    else 
    begin
      if(micValid_p == 1'b1) 
        micValidReg <= 1'b1;
      else if(lastBlock == 1'b0) 
        micValidReg <= 1'b0;
      else 
        micValidReg <= micValidReg;
    end // End of else 
  end // End of always 

// sequential logic 
  always@(posedge pClk or negedge nPRst)
  begin
    if (nPRst == 1'b0)
    begin
      regPtr        <= 4'h0;
      ccmpOutValid  <= 1'b0; 
      micValid      <= 1'b0; 
      lastBlock     <= 1'b0; 
    end
    else if (nSRst == 1'b0)
    begin
      regPtr        <= 4'h0;
      ccmpOutValid  <= 1'b0; 
      micValid      <= 1'b0; 
      lastBlock     <= 1'b0; 
    end
    else
    begin
      regPtr        <= nextregPtr;
      ccmpOutValid  <= nextccmpOutValid; 
      micValid      <= nextmicValid ; 
      lastBlock     <= nextlastBlock ; 
    end
  end

  always@(posedge pClk or negedge nPRst) 
  begin
    if(nPRst == 1'b0) 
      outReg <= 128'h0;
    else if (nSRst == 1'b0)
      outReg <= 128'h0;
    else  
      outReg  <=  nextoutReg;
  end

// Reduce the original payload by one logic
  assign newpayloadLen  =  payloadLen - 4'h1;

//ccmpOutData
  assign ccmpOutData    = outReg[7:0];

//ccmpOutLast_p
  assign ccmpOutLast_p  = lastBlock && !nextlastBlock;

endmodule

//------------------- END OF FILE ----------------//
