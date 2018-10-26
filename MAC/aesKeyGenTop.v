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
//   This module is responsible for generating the Key for each round
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

module aesKeyGenTop (  

  //$port_g Clock and reset
  input  wire          pClk,          //baseband clock signal 
  input  wire          nPRst,         //baseband reset signal 
  input  wire          nSRst,         //baseband soft reset
  input  wire          enable,

  //$port_g aesCore
  input  wire [127:0]  aesKey,        //Input Key from  Key Register
  input  wire   [3:0]  roundCount,    //Rcon values used for Key generation
  input  wire          loadKey,       //Signal to mux the input kay

  output wire [127:0]  roundKey       //Key for each Round 
  );

// ------------------------ Register Declarations ------------------------------

  reg    [7:0]    rounCon;
  reg    [127:0]  muxedKey;

// ------------------------ Wire Declarations ----------------------------------

  wire   [31:0]   sBoxRegInst;
  wire   [31:0]   sBoxData;
  wire   [31:0]   nexttempKeyReg2;
  wire   [31:0]   nexttempKeyReg1;
  wire   [31:0]   nexttempKeyReg0;

  wire   [31:0]   tempKeyReg3;
  wire   [31:0]   tempKeyReg2;
  wire   [31:0]   tempKeyReg1;
  wire   [31:0]   tempKeyReg0;

  /******************************************************************************
    Main Code Start
  ******************************************************************************/

//-----------------------------------------------------------------------------
// Combinational logic for Rcon Generation  used for Key Generation process for
// both  Encryption
//-----------------------------------------------------------------------------

  always@(roundCount)
  begin
    case(roundCount)
      4'h0:rounCon = 8'h01;
      4'h1:rounCon = 8'h02;
      4'h2:rounCon = 8'h04;
      4'h3:rounCon = 8'h08;
      4'h4:rounCon = 8'h10;
      4'h5:rounCon = 8'h20;
      4'h6:rounCon = 8'h40;
      4'h7:rounCon = 8'h80;
      4'h8:rounCon = 8'h1b;
      4'h9:rounCon = 8'h36;
      default:rounCon = 8'h00;
    endcase
  end

//-----------------------------------------------------------------------------
// Following Instannce includes the 8-Bit logic for key generation and 32 bit 
// registers
//-----------------------------------------------------------------------------
  aesKeyInst uaesKeyInst3(.pClk(pClk),
  .nPRst(nPRst),
  .nSRst(nSRst),
  .enable(enable),

  .muxedKey(muxedKey[127:96]),
  .xorIn(nexttempKeyReg2),

  .nexttempKeyReg(), // Lint warning but this is the last of aeskey chaining
  .tempKeyReg(tempKeyReg3)
  );

  aesKeyInst uaesKeyInst2(.pClk(pClk),
  .nPRst(nPRst),
  .nSRst(nSRst),
  .enable(enable),

  .muxedKey(muxedKey[95:64]),
  .xorIn(nexttempKeyReg1),

  .nexttempKeyReg(nexttempKeyReg2),
  .tempKeyReg(tempKeyReg2)
  );

  aesKeyInst uaesKeyInst1(.pClk(pClk),
  .nPRst(nPRst),
  .nSRst(nSRst),
  .enable(enable),

  .muxedKey(muxedKey[63:32]),
  .xorIn(nexttempKeyReg0),

  .nexttempKeyReg(nexttempKeyReg1),
  .tempKeyReg(tempKeyReg1)
  );

  aesKeyInst uaesKeyInst0(.pClk(pClk),
  .nPRst(nPRst),
  .nSRst(nSRst),
  .enable(enable),

  .muxedKey(muxedKey[31:0]),
  .xorIn(sBoxRegInst),

  .nexttempKeyReg(nexttempKeyReg0),
  .tempKeyReg(tempKeyReg0)
  );
//sBoxRegInst
  assign  sBoxRegInst = {sBoxData[7:0],sBoxData[31:8]}^{24'h000000,rounCon};

//----------------------------------------------------------------------------
//Input Mux B/W Input Key and FeedBack Key
//----------------------------------------------------------------------------

  always@(aesKey or loadKey or tempKeyReg0 or tempKeyReg1 or tempKeyReg2 or 
    tempKeyReg3) 
  begin
    if(loadKey)
      muxedKey = aesKey;
    else
      muxedKey = {tempKeyReg3,tempKeyReg2,tempKeyReg1,tempKeyReg0};
  end

//-----------------------------------------------------------------------------
// Substituaion box 
//-----------------------------------------------------------------------------

  aesSBox uSubBox0 (.inData (muxedKey[103:96]),
  .outData(sBoxData[7:0])
  );

//-----------------------------------------------------------------------------
// Substituaion box
//-----------------------------------------------------------------------------

  aesSBox uSubBox1 (.inData (muxedKey[111:104]),
  .outData(sBoxData[15:8])
  );

//-----------------------------------------------------------------------------
// Substituaion box
//-----------------------------------------------------------------------------

  aesSBox uSubBox2 (.inData (muxedKey[119:112]),
  .outData(sBoxData[23:16])
  );

//-----------------------------------------------------------------------------
// Substituaion box
//-----------------------------------------------------------------------------

  aesSBox uSubBox3 (.inData (muxedKey[127:120]),
  .outData(sBoxData[31:24])
  );

//-----------------------------------------------------------------------------
// Output Signal Gneration 
//-----------------------------------------------------------------------------
  assign roundKey   = {tempKeyReg3,tempKeyReg2,tempKeyReg1,tempKeyReg0};

endmodule

//-------------------------End of file------------------------------------------
