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
//   This block is input buffer which converts 8 bit stream to 128 bit data 
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

module ccmpInReg (

  //$port_g Inputs
  input  wire          pClk,                 // baseband clock signal
  input  wire          nPRst,                // reset signal from hardware
  input  wire          nSRst,                // reset signal from software
  input  wire          rxCsIsIdle,           // Encrypt/Decrypt flag
  input  wire          txCsIsIdle,           // Encrypt/Decrypt flag
  input  wire          rxError_p,            // rx Error flag
  input  wire          tcTxErrorP,           // tx Error flag
  input  wire          wrCCMPEn_p,           // Write signal to the buffer
  input  wire          address4Pres,         // Indicates that address4 field Exists
  input  wire          payloadEnd_p,         // indicates last byte of payload
  input  wire          micEnd,               // indicate mic end
  input  wire [7:0]    dataFromBuffer,       // data to be decrypted
  input  wire [7:0]    plainText,            // data to be encrypted
  input  wire          loadMsg_p,            // Read pulse from CCM block
  input  wire          loadAAD2_p,           // AAD read signal from CCM block
  input  wire          rxMICPending,         // Indicates that receive MIC calculation is pending
  input  wire          popDataOutBuffer_p,   // Indicate ccmpInReg is read

  //$port_g Outputs
  output wire [127:0]  ccmInData,            // Input data to CCM block.
  output reg  [127:0]  maskReg,              // mask Register
  output wire          stopPopFromBuffer,    // Buffer full signal.
  output reg           ccmInValid,           // Indicate the ccmp in bufffer is valid
  output reg           aadValid,             // Indicates that AAD is present
  output wire          payloadEndOut_p,      // Indicates the end of payload 
  output wire          micEndOut,            // Indicate buffer is shifting mic
  output wire          ccmpRegFull,          // CCMP buffer empty signal
  output wire          nextccmpRegFull,      // CCMP buffer empty signal
  output reg           aadReady              // Indicate buffer hold ADD for ccmp init
  );


  // ------------------------ Register Declarations ------------------------------
  reg [127:0] nextinReg;  
  reg [127:0] inReg;  
  reg [127:0] nextmaskReg;  
  reg [3:0]   lenCtr;  
  reg [3:0]   nextlenCtr;  
  reg         nextendAAD;  
  reg         lastBlock;  
  reg         nextlastBlock;  
  reg         micStart;  
  reg         nextmicStart;  
  reg         shiftZeroes;  
  reg         nextshiftZeroes;  
  reg         ccmpInRegFull;  
  reg         nextccmpInRegFull;  
  reg         delccmpInRegFull;  
  reg         nextccmInValid;  
  reg         nextaadValid;  
  reg         delrxCsIsIdle;
  reg         ccmpInEn1;   
  reg         ccmpInEn2;   
  reg         endAAD;
  // ------------------------ Wire Declarations ----------------------------------
  wire [7:0]  regInData;            
  wire        endRx_p;
  wire        ccmpInEnPulse;

  //--------------Logic Begins----------------------------------------

  // Mux b/w recieve and transmit data
  assign  regInData = !rxCsIsIdle ? dataFromBuffer : plainText;

  // Buffer pointer generation logic
  always @*
  begin
    nextinReg     = inReg;
    nextmaskReg   = maskReg;
    if (loadMsg_p || tcTxErrorP || rxError_p || endRx_p || loadAAD2_p || (rxCsIsIdle && txCsIsIdle))
    begin
      nextlenCtr    = 4'h0;
      nextmaskReg   = 128'hFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF;
    end
    else if ((wrCCMPEn_p || shiftZeroes) && (aadValid == 1'b0) && 
      (ccmInValid == 1'b0))
    begin
      if (shiftZeroes)
      begin
        nextinReg  = {8'h00,inReg[127:8]} ;
        nextmaskReg= {8'h00,maskReg[127:8]};
      end
      else
        nextinReg  = {regInData,inReg[127:8]} ;
      nextlenCtr    = lenCtr + 4'h1;
    end
    else
      nextlenCtr    = lenCtr;
  end

  // aadReady generation.
  always @(posedge pClk or negedge nPRst) 
  begin
    if(nPRst == 1'b0)
      aadReady <= 1'b0;
    else if(nSRst == 1'b0)
      aadReady <= 1'b0;
    else 
    begin
      if((loadAAD2_p == 1'b1) || (micStart == 1'b1) || (tcTxErrorP == 1'b1) || (rxError_p == 1'b1) || ((rxCsIsIdle == 1'b1) && (txCsIsIdle == 1'b1))) 
        aadReady <= 1'b0;
      else if((lenCtr[3:0] == 4'hF) && ((wrCCMPEn_p == 1'b1) || (shiftZeroes == 1'b1)) && (endAAD == 1'b0))
        aadReady <= 1'b1;
      else 
        aadReady <= aadReady;
    end 
  end

  // endAAD signal generation 
  always @*
  begin 
    if(payloadEndOut_p || tcTxErrorP || rxError_p || (rxCsIsIdle && txCsIsIdle))
      nextendAAD = 1'b0;
    else if(loadAAD2_p)
      nextendAAD = 1'b1;
    else
      nextendAAD = endAAD;
  end

  // ccmpRegFull generation
  always @*
  begin
    if (loadMsg_p || loadAAD2_p || tcTxErrorP || rxError_p || endRx_p || (rxCsIsIdle && txCsIsIdle)) 
      nextccmpInRegFull = 1'b0;
    else if (lenCtr[3:0] == 4'hf  && ((wrCCMPEn_p && (rxCsIsIdle || popDataOutBuffer_p)) || shiftZeroes))
      nextccmpInRegFull = 1'b1;
    else if (lenCtr[3:0] == 4'hf  && (wrCCMPEn_p || shiftZeroes))
      nextccmpInRegFull = 1'b1;
    else
      nextccmpInRegFull = ccmpInRegFull;
  end

  always@(posedge pClk or negedge nPRst) 
  begin
    if (nPRst == 1'b0)
      ccmpInEn1 <= 1'b0;
    else if(nSRst == 1'b0)
      ccmpInEn1 <= 1'b0;
    else if((tcTxErrorP == 1'b1) || (rxError_p == 1'b1))
      ccmpInEn1 <= 1'b0;
    else if((lenCtr[3:0] == 4'h0) && ccmpInRegFull && (shiftZeroes == 1'b0) && (rxCsIsIdle == 1'b0))
      ccmpInEn1 <= 1'b1;
    else
      ccmpInEn1 <= 1'b0;
  end

  always@(posedge pClk or negedge nPRst) 
  begin
    if (nPRst == 1'b0)
      ccmpInEn2 <= 1'b0;
    else if (nSRst == 1'b0)
      ccmpInEn2 <= 1'b0;
    else if((tcTxErrorP == 1'b1) || (rxError_p == 1'b1))
      ccmpInEn2 <= 1'b0;
    else 
      ccmpInEn2 <= ccmpInEn1;  
  end

  //ccmpInEnPulse
  assign ccmpInEnPulse = (ccmpInEn1 & !ccmpInEn2);

  //stopPopFromBuffer
  assign stopPopFromBuffer = ((lenCtr[3:0]        == 4'hf) &&
                              (shiftZeroes        == 1'b0) &&
                              (popDataOutBuffer_p == 1'b1) &&
                              (rxCsIsIdle         == 1'b0) &&
                              (nextccmpInRegFull  == 1'b0)    );

  // ccmInValid signal generation 
  always @*
  begin
    if ((nextccmpInRegFull == 1'b0)  || loadMsg_p || tcTxErrorP || rxError_p)
      nextccmInValid =  1'b0;
    else if (wrCCMPEn_p || shiftZeroes  || ccmpInEnPulse || (nextccmpInRegFull && wrCCMPEn_p))
      nextccmInValid =  endAAD;
    else 
      nextccmInValid = ccmInValid;
  end

  // aadInValid signal generation 
  always @*
  begin
    if (((ccmpInRegFull == 1'b0) || tcTxErrorP || rxError_p || rxMICPending) && (lenCtr[3:0] != 4'hf))
      nextaadValid   =  1'b0;
    else if ((wrCCMPEn_p || shiftZeroes || ccmpInEnPulse) && ~(rxMICPending))
      nextaadValid   = !endAAD;
    else if (nextccmpInRegFull == 1'b0)
      nextaadValid   =  1'b0;
    else
      nextaadValid   = aadValid;
  end


  // lastBlock signal generation 
  always @*
  begin
    if(loadMsg_p || tcTxErrorP || rxError_p || payloadEndOut_p || ((rxCsIsIdle == 1'b1) && (txCsIsIdle == 1'b1)))
      nextlastBlock   = 1'b0;
    else if(payloadEnd_p)
      nextlastBlock   = 1'b1;
    else
      nextlastBlock   = lastBlock;
  end

  //assign payloadEndOut_p = lastBlock && loadMsg_p ; 
  assign payloadEndOut_p = lastBlock && loadMsg_p;

  // ShiftZero signal generation 
  always @*
  begin
    if ((lenCtr[3:0] == 4'hf && (wrCCMPEn_p || shiftZeroes)) || tcTxErrorP || rxError_p || ((rxCsIsIdle == 1'b1) && (txCsIsIdle == 1'b1)))
      nextshiftZeroes = 1'b0;
    else if ((!address4Pres && lenCtr[3:0] == 4'h9 && !endAAD && wrCCMPEn_p) || (micStart && lenCtr[3:0] == 4'h7 && wrCCMPEn_p) || payloadEnd_p) 
      nextshiftZeroes= 1'b1;
    else
      nextshiftZeroes = shiftZeroes;
  end

  // MicStart signal generation 
  always @*
  begin
    if((loadMsg_p && (lastBlock == 1'b0)) || tcTxErrorP || rxError_p || endRx_p)
      nextmicStart = 1'b0;
    else if (payloadEndOut_p && (rxCsIsIdle == 1'b0))
      nextmicStart = 1'b1;
    else
      nextmicStart = micStart;
  end

  // Buffer Full signal generation to the outside World
  assign  nextccmpRegFull = nextccmpInRegFull || nextshiftZeroes;
  //ccmpRegFull
  assign  ccmpRegFull = ccmpInRegFull || shiftZeroes;
  // ccmInData
  assign  ccmInData   = inReg;

  // Detect end of reception
  assign endRx_p = rxCsIsIdle && ~(delrxCsIsIdle);

  // Logic for micEndOut;
  assign micEndOut = micEnd && delccmpInRegFull;


  // Sequential logic
  always@(posedge pClk or negedge nPRst)
  begin
    if (nPRst == 1'b0)
    begin
      inReg            <= 128'h0;
      lenCtr           <= 4'h0;
      endAAD           <= 1'b0;
      ccmpInRegFull    <= 1'b0;
      delccmpInRegFull <= 1'b0;
      micStart         <= 1'b0;
      shiftZeroes      <= 1'b0;
      lastBlock        <= 1'b0;
      maskReg          <= 128'hFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF;
      ccmInValid       <= 1'b0;
      aadValid         <= 1'b0;
      delrxCsIsIdle    <= 1'b0;
    end
    else if (nSRst == 1'b0)
    begin
      inReg            <= 128'h0;
      lenCtr           <= 4'h0;
      endAAD           <= 1'b0;
      ccmpInRegFull    <= 1'b0;
      delccmpInRegFull <= 1'b0;
      micStart         <= 1'b0;
      shiftZeroes      <= 1'b0;
      lastBlock        <= 1'b0;
      maskReg          <= 128'hFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF;
      ccmInValid       <= 1'b0;
      aadValid         <= 1'b0;
      delrxCsIsIdle    <= 1'b0;
    end
    else
    begin
      inReg            <= nextinReg;
      lenCtr           <= nextlenCtr;
      endAAD           <= nextendAAD;
      ccmpInRegFull    <= nextccmpInRegFull;
      delccmpInRegFull <= ccmpInRegFull;
      micStart         <= nextmicStart;
      shiftZeroes      <= nextshiftZeroes;
      lastBlock        <= nextlastBlock;
      maskReg          <= nextmaskReg;
      ccmInValid       <= nextccmInValid;
      aadValid         <= nextaadValid;
      delrxCsIsIdle    <= rxCsIsIdle;
    end
  end

endmodule       
//------------------- END OF FILE ----------------//
