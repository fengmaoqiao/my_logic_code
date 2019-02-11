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
//   This block is the top level module for aes implementation
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

module aesCore (

  //$port_g Clocks and Resets
  input  wire           pClk,           // baseband clock signal
  input  wire           nPRst,          // reset signal from hardware
  input  wire           nSRst,          // reset signal from software

  //$port_g ccmCntl
  input  wire           rxError_p,      // Indicates Rx Error
  input  wire           tcTxErrorP,     // Indicates Tx Error
  input  wire           aesInValid,     // Indicates Tx FIFO is not Empty
  input  wire  [127:0]  aesKey,         // Input Key from  Key Register
  input  wire  [127:0]  aesInData,      // Input Data from TransmitFifo
  input  wire           loadFlag,       // Input Data from TransmitFifo

  `ifdef RW_AES_AC
  output reg   [127:0]  aesOutData,     // Encrypted Data
  output reg            aesOutValid_p   // To Rx Fifo when OutData is valid
  `else
  output wire  [127:0]  aesOutData,     // Encrypted Data
  output wire           aesOutValid_p   // To Rx Fifo when OutData is valid
  `endif

 );


// ------------------ Register Declarations ----------
  reg [31:0]  tempDataReg3;
  reg [31:0]  tempDataReg2;
  reg [31:0]  tempDataReg1;
  reg [31:0]  tempDataReg0;
  reg [31:0]  nexttempDataReg3;
  reg [31:0]  nexttempDataReg2;
  reg [31:0]  nexttempDataReg1;
  reg [31:0]  nexttempDataReg0;
  reg [31:0]  encryptWord3;
  reg [31:0]  encryptWord2;
  reg [31:0]  encryptWord1;
  reg [31:0]  encryptWord0;
  reg         start;

// ------------------- Wire Declarations --------------
  wire [127:0] inARKeyData;
  wire [127:0] roundKey;
  wire [63:0]  inARKeyDataSh;
  wire [31:0]  roundWord3;
  wire [31:0]  roundWord2;
  wire [31:0]  roundWord1;
  wire [31:0]  roundWord0;
  wire [31:0]  shiftedWord3;
  wire [31:0]  shiftedWord2;
  wire [31:0]  shiftedWord1;
  wire [31:0]  shiftedWord0;
  wire [31:0]  intOutData3;
  wire [31:0]  intOutData2;
  wire [31:0]  intOutData1;
  wire [31:0]  intOutData0;
  wire [31:0]  encShiftedWord3;
  wire [31:0]  encShiftedWord2;
  wire [31:0]  encShiftedWord1;
  wire [31:0]  encShiftedWord0;
  wire [31:0]  aesSBox3; 
  wire [31:0]  aesSBox2; 
  wire [31:0]  aesSBox1; 
  wire [31:0]  aesSBox0; 
  wire [31:0]  mixData3; 
  wire [31:0]  mixData2; 
  wire [31:0]  mixData1; 
  wire [31:0]  mixData0; 
  wire [3:0]   roundCount;
  wire         aesReadData_p;
  wire         enable;

  `ifdef RW_AES_AC
  wire         aesOutValid_int_p;
  `endif

// -------------------- Logic Begins --------------------

// Control FSM for Controlling Encryption/Deccryption and other Muxing

aesControl U_aesControl ( 
// Inputs
  .pClk(pClk),
  .nPRst(nPRst),
  .nSRst(nSRst),
  .rxError_p(rxError_p),
  .tcTxErrorP(tcTxErrorP),
  .aesInValid(aesInValid),
  .loadFlag(loadFlag),

// Outputs
  `ifdef RW_AES_AC
  .aesOutValid_p(aesOutValid_int_p),
  `else
  .aesOutValid_p(aesOutValid_p),
  `endif
  .aesReadData_p(aesReadData_p),
  .roundCount(roundCount)
 );

//Key Generation Module Which generates the keys required for each round on the 
//fly

aesKeyGenTop U_aesKeyGenTop (
// Inputs
  .pClk(pClk),
  .nPRst(nPRst),
  .nSRst(nSRst),
  .enable(enable),
  .aesKey(aesKey),
  .roundCount(roundCount),
  .loadKey(aesReadData_p),

// Outputs
  .roundKey(roundKey)
 );

// Initial AddroundKey
assign inARKeyData = aesKey ^ aesInData;

// Rearranging of incoming data for shift operation 
assign inARKeyDataSh[7:0]   = inARKeyData[95:88];
//inARKeyDataSh[15:8]
assign inARKeyDataSh[15:8]  = inARKeyData[15:8];
//inARKeyDataSh[23:16]
assign inARKeyDataSh[23:16] = inARKeyData[63:56];
//inARKeyDataSh[31:24]
assign inARKeyDataSh[31:24] = inARKeyData[111:104];
//inARKeyDataSh[39:32]
assign inARKeyDataSh[39:32] = inARKeyData[31:24];
//inARKeyDataSh[47:40]
assign inARKeyDataSh[47:40] = inARKeyData[79:72];
//inARKeyDataSh[55:48]
assign inARKeyDataSh[55:48] = inARKeyData[127:120];
//inARKeyDataSh[63:56]
assign inARKeyDataSh[63:56] = inARKeyData[47:40];

//shiftedWord3
assign shiftedWord3 =  {inARKeyDataSh[7:0],inARKeyData[55:48],
                        inARKeyDataSh[15:8],inARKeyData[103:96]};
//shiftedWord2                          
assign shiftedWord2 =  {inARKeyDataSh[23:16],inARKeyData[23:16],
                        inARKeyDataSh[31:24],inARKeyData[71:64]};
//shiftedWord1
assign shiftedWord1 =  {inARKeyDataSh[39:32],inARKeyData[119:112],
                        inARKeyDataSh[47:40],inARKeyData[39:32]};
//shiftedWord0
assign shiftedWord0 =  {inARKeyDataSh[55:48],inARKeyData[87:80],
                        inARKeyDataSh[63:56],inARKeyData[7:0]};

assign enable       =  (aesInValid == 1'b1) || (start == 1'b1);

// Following Combinational logic forms the mux at the input 
// i.e Before temorary register 
always@(shiftedWord0 or shiftedWord1 or shiftedWord2 or shiftedWord3 or
        roundWord0 or roundWord1 or roundWord2 or roundWord3 or aesReadData_p)
begin
  if (aesReadData_p)
  begin
    nexttempDataReg3 = shiftedWord3;
    nexttempDataReg2 = shiftedWord2;
    nexttempDataReg1 = shiftedWord1;
    nexttempDataReg0 = shiftedWord0;
  end
  else
  begin
    nexttempDataReg3 = roundWord3;
    nexttempDataReg2 = roundWord2;
    nexttempDataReg1 = roundWord1;
    nexttempDataReg0 = roundWord0;
  end
end

//Sequential logic for tempDataReg
always@(posedge pClk or negedge nPRst)
  if(nPRst == 1'b0)
  begin
    tempDataReg3 <= 32'h00000000;
    tempDataReg2 <= 32'h00000000;
    tempDataReg1 <= 32'h00000000;
    tempDataReg0 <= 32'h00000000;
  end
  else if(nSRst == 1'b0)
  begin
    tempDataReg3 <= 32'h00000000;
    tempDataReg2 <= 32'h00000000;
    tempDataReg1 <= 32'h00000000;
    tempDataReg0 <= 32'h00000000;
  end
  else if(enable == 1'b1)
  begin
    tempDataReg3 <= nexttempDataReg3;
    tempDataReg2 <= nexttempDataReg2;
    tempDataReg1 <= nexttempDataReg1;
    tempDataReg0 <= nexttempDataReg0;
end

always@(posedge pClk or negedge nPRst)
begin
  if(nPRst == 1'b0)
  begin
    start <= 1'b0;
  end
  else if (nSRst == 1'b0)
  begin
    start <= 1'b0;
  end
  else
  begin
    if(aesInValid == 1'b1)
      start <= 1'b1;
    else if((roundCount == 4'h9) || ((loadFlag == 1'b1) && (roundCount == 4'h6)))
      start <= 1'b0;
  end
end

//Instantiation of Sub-Byte for 32 bits to perform the S-box operation
aesSBox U_aesSBox3a ( 
// Inputs
  .inData(tempDataReg3[31:24]),

// Outputs
  .outData(aesSBox3[31:24])
 );

aesSBox U_aesSBox2a( 
// Inputs
  .inData(tempDataReg3[23:16]),

// Outputs
  .outData(aesSBox3[23:16])
 );

aesSBox U_aesSBox1a( 
// Inputs
  .inData(tempDataReg3[15:8]),

// Outputs
  .outData(aesSBox3[15:8])
 );

aesSBox U_aesSBox0a( 
// Inputs
  .inData(tempDataReg3[7:0]),

// Outputs
  .outData(aesSBox3[7:0])
 );

//Instantiation of Sub-Byte for 32 bits to perform the S-box operation

aesSBox U_aesSBox3b ( 
// Inputs
  .inData(tempDataReg2[31:24]),

// Outputs
  .outData(aesSBox2[31:24])
 );

aesSBox U_aesSBox2b (
// Inputs
  .inData(tempDataReg2[23:16]),

// Outputs
  .outData(aesSBox2[23:16])
 );

aesSBox U_aesSBox1b ( 
// Inputs
  .inData(tempDataReg2[15:8]),

// Outputs
  .outData(aesSBox2[15:8])
 );

aesSBox U_aesSBox0b ( 
// Inputs
  .inData(tempDataReg2[7:0]),

// Outputs
  .outData(aesSBox2[7:0])
 );

//Instantiation of Sub-Byte for 32 bits to perform the S-box operation

aesSBox U_aesSBox3c ( 
// Inputs
  .inData(tempDataReg1[31:24]),

// Outputs
  .outData(aesSBox1[31:24])
 );

aesSBox U_aesSBox2c ( 
// Inputs
  .inData(tempDataReg1[23:16]),

// Outputs
  .outData(aesSBox1[23:16])
 );

aesSBox U_aesSBox1c ( 
// Inputs
  .inData(tempDataReg1[15:8]),

// Outputs
  .outData(aesSBox1[15:8])
 );

aesSBox U_aesSBox0c ( 
// Inputs
  .inData(tempDataReg1[7:0]),

// Outputs
  .outData(aesSBox1[7:0])
 );

//Instantiation of Sub-Byte for 32 bits to perform the S-box operation

aesSBox U_aesSBox3d ( 
// Inputs
  .inData(tempDataReg0[31:24]),

// Outputs
  .outData(aesSBox0[31:24])
 );

aesSBox U_aesSBox2d ( 
// Inputs
  .inData(tempDataReg0[23:16]),

// Outputs
  .outData(aesSBox0[23:16])
 );

aesSBox U_aesSBox1d ( 
// Inputs
  .inData(tempDataReg0[15:8]),

// Outputs
  .outData(aesSBox0[15:8])
 );

aesSBox U_aesSBox0d ( 
// Inputs
  .inData(tempDataReg0[7:0]),

// Outputs
  .outData(aesSBox0[7:0])
 );

// 128 bits after Sub-Byte Data will be fed to aesMixColumn Block
// for Encryption process

aesMixColumn U_aesMixColumn3 (
// Inputs
  .wordin(aesSBox3),

// Outputs
  .wordout(mixData3)
 );

aesMixColumn U_aesMixColumn2 (
// Inputs
  .wordin(aesSBox2),

// Outputs
  .wordout(mixData2)
 );

aesMixColumn U_aesMixColumn1 (
// Inputs
  .wordin(aesSBox1),

// Outputs
  .wordout(mixData1)
 );

aesMixColumn U_aesMixColumn0 (
// Inputs
  .wordin(aesSBox0),

// Outputs
  .wordout(mixData0)
 );

`ifdef RW_AES_AC
// Mux to for Encryption to put the intemediate data in Tempreg
assign intOutData3 = !(aesOutValid_int_p || aesOutValid_p) && start ? mixData3 : aesSBox3;
//intOutData2
assign intOutData2 = !(aesOutValid_int_p || aesOutValid_p) && start ? mixData2 : aesSBox2;
//intOutData1
assign intOutData1 = !(aesOutValid_int_p || aesOutValid_p) && start ? mixData1 : aesSBox1;
//intOutData0
assign intOutData0 = !(aesOutValid_int_p || aesOutValid_p) && start ? mixData0 : aesSBox0;
`else
// Mux to for Encryption to put the intemediate data in Tempreg
assign intOutData3 = !aesOutValid_p && start ? mixData3 : aesSBox3;
//intOutData2
assign intOutData2 = !aesOutValid_p && start ? mixData2 : aesSBox2;
//intOutData1
assign intOutData1 = !aesOutValid_p && start ? mixData1 : aesSBox1;
//intOutData0
assign intOutData0 = !aesOutValid_p && start ? mixData0 : aesSBox0;
`endif

// Add Round Key for the perticular round for Encryption performed on 128 bits
always@(intOutData3 or intOutData2 or intOutData1 or intOutData0 or
        roundKey)
begin
  encryptWord3= intOutData3 ^ roundKey[127:96];
  encryptWord2= intOutData2 ^ roundKey[95:64];
  encryptWord1= intOutData1 ^ roundKey[63:32];
  encryptWord0= intOutData0 ^ roundKey[31:0];
end

// Shift the data before putting into temporaray data register for next Round 
// in case of Encryption operation 
assign encShiftedWord3 = {encryptWord2[31:24], encryptWord1[23:16],
                          encryptWord0[15:8], encryptWord3[7:0]};
//encShiftedWord2
assign encShiftedWord2 = {encryptWord1[31:24], encryptWord0[23:16],
                          encryptWord3[15:8], encryptWord2[7:0]};
//encShiftedWord1
assign encShiftedWord1 = {encryptWord0[31:24], encryptWord3[23:16],
                          encryptWord2[15:8], encryptWord1[7:0]};
//encShiftedWord0
assign encShiftedWord0 = {encryptWord3[31:24], encryptWord2[23:16],
                          encryptWord1[15:8], encryptWord0[7:0]};

// The FeedBack data between Encryption 
assign    roundWord0 = encShiftedWord0;
//roundWord1 
assign    roundWord1 = encShiftedWord1; 
//roundWord2
assign    roundWord2 = encShiftedWord2; 
//roundWord3
assign    roundWord3 = encShiftedWord3; 

// Output data.
`ifdef RW_AES_AC
always @(posedge pClk or negedge nPRst)
begin
  if(nPRst == 1'b0)
  begin
    aesOutData    <= 128'h0;
    aesOutValid_p <= 1'b0;
  end
  else if (nSRst == 1'b0)
  begin
    aesOutData    <= 128'h0;
    aesOutValid_p <= 1'b0;
  end
  else
  begin
    aesOutData    <= {encryptWord3, encryptWord2, encryptWord1, encryptWord0};
    aesOutValid_p <= aesOutValid_int_p;
  end
end
`else
assign aesOutData = {encryptWord3, encryptWord2, encryptWord1, encryptWord0};
`endif
endmodule
//------------------- END OF FILE ----------------//
