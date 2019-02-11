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
// Description      : This module is used for FIFO Flag generation as well as
//                    for generating FIFO addresses.
//                    
// Simulation Notes : 
// Synthesis Notes  :
// Application Note :                                                       
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
`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"

`include "global_define.v"
module encryptRxBufCntrl(

   //$port_g Input ports
   input  wire                                 hardRstBbClk_n,         // reset signal from hardware
   input  wire                                 softRstBbClk_p,         // reset signal from software
   input  wire                                 bbClk,                  // base band clock signal

   input  wire                                 pushDataInBuffer,       // pulse to push data into buffer
   input  wire                                 popDataOutBuffer_p,     // pulse to pop data from buffer
   
   input  wire                          [15:0] rxPayloadLen,           // rx length
`ifdef CCMP
   input  wire                                 rxCCMP,                 // indicates that CCMP encryption
                                                                       // is being used for decryption
`endif
`ifdef RW_WAPI_EN
   input  wire                                 rxWAPI,                 // indicates that WAPI encryption is being used for decryption
   output wire                                 nextBufferEmptyFlag,
`endif //RW_WAPI_EN
   input  wire                                 encrRxBufFlush_p,       // Signal to flush the Encr. Rx Buffer

   input  wire                                 encrRxFIFOReset,        // Encryption RX FIFO Reset
   output wire                                 encrRxFIFOResetIn,      // encrRxFIFOResetIn
   output wire                                 encrRxFIFOResetInValid, // Clear the encrRxFIFOReset bit

   //$port_g Output ports
   output wire                                 writeEnEncrRxBuffer,    // write enable signal for RAM port A
   output wire                                 bufferEmptyFlag,        // flag to indicate buffer empty
   output wire                                 bufferAlmostEmptyFlag,  // flag to indicate 8 bytes of data left
   output wire [`RX_BUFFER_ADDR_WIDTH - 1 : 0] readAddrEncrRxBuffer,   // read address to RAM port B

   output wire                                 bufferFullFlag,         // flag to indicate buffer full

   output wire [`RX_BUFFER_ADDR_WIDTH - 1 : 0] writeAddrEncrRxBuffer   // write address to RAM port A

);

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

   parameter RXBUFCNTRLRXBUFFERSIZE = 32'd1;

   reg [`RX_BUFFER_ADDR_WIDTH    :0]      flagCnt;
   reg [`RX_BUFFER_ADDR_WIDTH - 1:0]      rdAddr;
   reg [`RX_BUFFER_ADDR_WIDTH - 1:0]      wrAddr;
   reg [15:0]                             readCnt;

   wire                                   wrEn;
   wire                                   rdEn;
   wire                                   emptyFlag;
   wire                                   almostEmptyFlag;
   wire                                   fullFlag;
   wire                                   almostFullFlag;
   wire [31:0]                            rxBufferSizeMinusOne;
   wire [31:0]                            rxBufferSizeMinusThree;



//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

assign rxBufferSizeMinusOne   = RXBUFCNTRLRXBUFFERSIZE - 32'd1;
assign rxBufferSizeMinusThree = RXBUFCNTRLRXBUFFERSIZE - 32'd3;

// when wrEn is present, flagCnt is incremented.
// when rdEn is present, flagCnt is decremented.
// when rdEn and wrEn is present, flagCnt is not changed.

always @ (posedge bbClk or negedge hardRstBbClk_n)
  begin: FlagCntGeneration
    if (!hardRstBbClk_n)
    begin
       flagCnt        <= {1'b0,`RX_BUFFER_ADDR_WIDTH'h0};
       readCnt        <= 16'd0;
    end
    else if (softRstBbClk_p)
    begin
       flagCnt        <= {1'b0,`RX_BUFFER_ADDR_WIDTH'h0};
       readCnt        <= 16'd0;
    end
    else if (encrRxBufFlush_p || encrRxFIFOReset)
    begin
       flagCnt        <= {1'b0,`RX_BUFFER_ADDR_WIDTH'h0};
       readCnt        <= 16'd0;
    end
    else if (wrEn && rdEn)
    begin
       flagCnt        <= flagCnt;
       if(rdEn)
         readCnt <= readCnt + 16'd1;
    end
    else if (wrEn) 
      begin
        if (flagCnt == RXBUFCNTRLRXBUFFERSIZE[`RX_BUFFER_ADDR_WIDTH:0])
          flagCnt        <= flagCnt;
        else
          flagCnt        <= flagCnt + {1'b0,`RX_BUFFER_ADDR_WIDTH'h1};
      end
    else if (rdEn)
      begin
        readCnt <= readCnt + 16'd1;
        if (flagCnt == {1'b0,`RX_BUFFER_ADDR_WIDTH'h0})
          flagCnt        <= flagCnt;
        else
          flagCnt        <= flagCnt - {1'b0,`RX_BUFFER_ADDR_WIDTH'h1};
      end
    else 
       flagCnt        <= flagCnt;
  end

//-------------- Flag generation -----------------------//

// Full Flag Generation

assign fullFlag = (flagCnt == rxBufferSizeMinusOne[`RX_BUFFER_ADDR_WIDTH:0]) ? 1'b1 : 1'b0;

// Almost Full Flag Generation

assign almostFullFlag = (flagCnt >= rxBufferSizeMinusThree[`RX_BUFFER_ADDR_WIDTH:0]) ? 1'b1 : 1'b0;


// Empty Flag generation

assign emptyFlag = (flagCnt == {1'b0,`RX_BUFFER_ADDR_WIDTH'h0}) ? 1'b1: 1'b0;   

// AlmostEmpty Flag generation
// If CCMP decryption is in progress, the this flag is generated when 12 bytes
// are left in the buffer.

`ifdef CCMP 
//  `ifdef RW_WAPI_EN
//assign almostEmptyFlag = (( rxWAPI && ((flagCnt <= {1'b0,`RX_BUFFER_ADDR_WIDTH'd2})  || ((readCnt >= rxPayloadLen-16'd20) && !bufferEmptyFlag))) ||
//                          (rxCCMP && ((flagCnt <= {1'b0,`RX_BUFFER_ADDR_WIDTH'd2})  || ((readCnt >= rxPayloadLen-16'd12) && !bufferEmptyFlag))) ||
//                          (~rxCCMP && ~rxWAPI && (flagCnt <= {1'b0,`RX_BUFFER_ADDR_WIDTH'd8} ))    ) ? 1'b1 : 1'b0;
//  `else
assign almostEmptyFlag = (( rxCCMP && ((flagCnt <= {1'b0,`RX_BUFFER_ADDR_WIDTH'd2})  || ((readCnt >= rxPayloadLen-16'd12) && !bufferEmptyFlag))) ||
                          (~rxCCMP && (flagCnt <= {1'b0,`RX_BUFFER_ADDR_WIDTH'd8} ))    ) ? 1'b1 : 1'b0;
//  `endif // RW_WAPI_EN
`else
//  `ifdef RW_WAPI_EN
//assign almostEmptyFlag = (( rxWAPI && ((flagCnt <= {1'b0,`RX_BUFFER_ADDR_WIDTH'd2})  || ((readCnt >= rxPayloadLen-16'd20) && !bufferEmptyFlag))) ||
//                          (~rxWAPI && (flagCnt <= {1'b0,`RX_BUFFER_ADDR_WIDTH'd8} ))    ) ? 1'b1 : 1'b0;
//  `else
assign almostEmptyFlag = (flagCnt <= {1'b0,`RX_BUFFER_ADDR_WIDTH'd8}) ? 1'b1 : 1'b0;
//  `endif // RW_WAPI_EN
`endif

assign bufferFullFlag = almostFullFlag;

//------------------------------------------------------//

// wrEn signal generation

assign wrEn = pushDataInBuffer && (~fullFlag);
assign writeEnEncrRxBuffer = wrEn;

// rdEn signal generation

assign rdEn = (popDataOutBuffer_p) && (~emptyFlag);


//------------------------------------------------------//

assign bufferEmptyFlag = emptyFlag;

assign bufferAlmostEmptyFlag = almostEmptyFlag;

assign readAddrEncrRxBuffer = rdAddr;

assign writeAddrEncrRxBuffer = wrAddr;

`ifdef RW_WAPI_EN
assign nextBufferEmptyFlag = ((flagCnt == {1'b0,`RX_BUFFER_ADDR_WIDTH'h1}) && ~wrEn && rdEn) ? 1'b1 : 1'b0;
`endif //RW_WAPI_EN

//------------- read write address generation --------------//

// read address generation

always @ (posedge bbClk or negedge hardRstBbClk_n)
  begin: readAddressGeneration
    if (!hardRstBbClk_n)
       rdAddr        <= `RX_BUFFER_ADDR_WIDTH'h0;
    else if (softRstBbClk_p)
       rdAddr        <= `RX_BUFFER_ADDR_WIDTH'h0;
    else if (encrRxBufFlush_p || encrRxFIFOReset)
       rdAddr        <= `RX_BUFFER_ADDR_WIDTH'h0;
    else if (rdEn)
      begin
        if (rdAddr == rxBufferSizeMinusOne[`RX_BUFFER_ADDR_WIDTH-1:0])
          rdAddr        <= `RX_BUFFER_ADDR_WIDTH'h0;
        else
          rdAddr        <= rdAddr + `RX_BUFFER_ADDR_WIDTH'h1;
      end 
    else
          rdAddr        <= rdAddr;
  end


// write address generation

always @ (posedge bbClk or negedge hardRstBbClk_n)
  begin: writeAddressGeneration
    if (!hardRstBbClk_n)
       wrAddr        <= `RX_BUFFER_ADDR_WIDTH'h0;
    else if (softRstBbClk_p)
       wrAddr        <= `RX_BUFFER_ADDR_WIDTH'h0;
    else if (encrRxBufFlush_p || encrRxFIFOReset)
       wrAddr        <= `RX_BUFFER_ADDR_WIDTH'h0;
    else if (wrEn)
      begin
        if (wrAddr == rxBufferSizeMinusOne[`RX_BUFFER_ADDR_WIDTH-1:0])
          wrAddr        <= `RX_BUFFER_ADDR_WIDTH'h0;
        else
          wrAddr        <= wrAddr + `RX_BUFFER_ADDR_WIDTH'h1;
      end 
    else
          wrAddr        <= wrAddr;
  end

//------------- FIFO reset register --------------//

assign encrRxFIFOResetIn      = 1'b0;
assign encrRxFIFOResetInValid = encrRxFIFOReset && 
                                (wrAddr == `RX_BUFFER_ADDR_WIDTH'h0) &&
                                (rdAddr == `RX_BUFFER_ADDR_WIDTH'h0);

endmodule
