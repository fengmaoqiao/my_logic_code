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
// Description      : Top level of txFIFO module
//                    
// Simulation Notes : 
// Synthesis Notes  :
// Application Note :                                                       
// Simulator        :                                                       
// Parameters       :
//                 TXFIFOADDRWIDTH : Address bus bitwidth of the RAM.
//                     TXFIFODEPTH : Depth of the TxFifo.
//   TXFIFO_ALMOST_EMPTY_THRESHOLD : Almost Empty indication threshold
//    TXFIFO_ALMOST_FULL_THRESHOLD : Almost Full indication threshold
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
//`include "commonDefineR1.v"
//`include "commonDefineR1Capt.v"
//`include "commonDefineR2.v"
//`include "commonDefineR2Capt.v"
//`include "commonDefineR3.v"
//`include "commonDefineR3Capt.v"

`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"
`default_nettype none
// pragma coverage pragmas = on
// pragma coverage implicit_default=off 

module txFifo ( 
   //$port_g Clock and Reset of write interface           
   input  wire                            macPITxClk,             // MAC Platform Transmit Clock
   input  wire                            macPIClkHardRst_n,      // Hard Reset of the MAC Platform Clock domain
                                                                  // active low

   //$port_g Clock and Reset of read interface
   input  wire                            macCoreTxClk,           // MAC Core Transmit Clock
   input  wire                            macCoreClkHardRst_n,    // Hard Reset of the MAC Core Clock domain 
                                                                  // active low
   input  wire                            macCoreTxClkSoftRst_n,  // Soft Reset of the MAC Core Clock domain 
                                                                  // active low

   //$port_g Control and Status register
   input  wire                            txFIFOReset,            // Reset the FIFO
   output wire                            txFIFOResetInValid,     // Clear of FIFO reset

   //$port_g Write control interface
   input  wire                            txFIFOWrFlush,          // Request from MAC Platform Clock domain to flush the FIFO
   input  wire                            txFIFOWrite,            // Write a new word in the Tx FIFO
   input  wire              [31:0]        txFIFOWrData,           // Data written to the TX FIFO
   input  wire              [ 5:0]        txFIFOWrTag,            // Tag written to the TX FIFO
   output wire                            txFIFOAlmostFull,       // Indicates that the TX FIFO is almost full
   output wire                            txFIFOFull,             // Indicates that the TX FIFO is full and cannot accept new write
   output wire                            txFIFOAlmEmptyWrClk,    // Indicates that the TX FIFO is almost empty
   output wire                            txFIFOEmptyWrClk,       // Indicates that the TX FIFO is empty

   //$port_g Read control interface       
   input  wire                            txFIFORdFlush,          // Request from MAC Core Clock domain to flush the FIFO
   input  wire                            txFIFORead,             // Request a new byte from the Tx FIFO
   input  wire                            txFIFOReadByFour,       // Indicates that the TX FIFO has to be read per word and not per byte
   input  wire                            txFIFOReadByTwo,        // Indicates that the TX FIFO has to be read per hlf-word and not per byte
   output wire                            txFIFOEmpty,            // Indicates that the TX FIFO is empty
   output wire                            txFIFODataValid,        // Indicates when the read data is valid
   output reg               [ 7:0]        txFIFORdData,           // Byte read from the TX FIFO
   output reg               [ 1:0]        txFIFOMPDUDelimiters,   // Tag read from the TX FIFO
                                          

   //$port_g Memory Read Interface        
   input  wire              [37:0]        txFIFOReadData,         // Transmit FIFO Read Data bus.
   output wire [(`TXFIFOADDRWIDTH - 1):0] txFIFOReadAddr,         // Transmit FIFO and transmit tag FIFO Read Address bus.
   output wire                            txFIFOReadEn,           // Transmit FIFO and transmit tag FIFO Read Enable. 
                                                                  // This signal is asserted for read operations to the Transmit FIFO and the Transmit Tag FIFO.

   //$port_g Memory Read Interface       
   output wire [(`TXFIFOADDRWIDTH - 1):0] txFIFOWriteAddr,        // Transmit FIFO and transmit tag FIFO Write Address bus
   output wire                     [37:0] txFIFOWriteData,        // Transmit FIFO Write Data bus.
   output wire                            txFIFOWriteEn           // Transmit FIFO and transmit tag FIFO Write Enable. 
                                                                  // This signal is asserted for write operations to the Transmit FIFO and the Transmit Tag FIFO.
   );



//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

localparam ALMOST_EMPTY_THRESHOLD = `TXFIFO_ALMOST_EMPTY_THRESHOLD;
localparam ALMOST_FULL_THRESHOLD  = `TXFIFO_ALMOST_FULL_THRESHOLD;


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
reg  [1:0] cnt;
reg  [1:0] cnt_ff1;
reg  [1:0] currentByte;
wire       txFIFOReadWord;
reg        txFIFORead_ff1;
//wire [3:0] activeBytes;
reg  [2:0] nBytes;
reg        readNow;
reg        readNow_ff1;
wire [5:0] txTagFIFOReadData;

wire       wrFlush;
wire       rdFlush;

wire       macCoreTxClkSoftRst;
wire       macCoreTxClkSoftRstResync;
wire       txFIFOResetResync;
wire       fifoPtrsNull;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

txFifoController #(.ADDRWIDTH(`TXFIFOADDRWIDTH),
                   .DEPTH(`TXFIFODEPTH),
                   .ALMOST_EMPTY_THRESHOLD(ALMOST_EMPTY_THRESHOLD),
                   .ALMOST_FULL_THRESHOLD(ALMOST_FULL_THRESHOLD)) 
  U_txFifoController (
		.wrClk             (macPITxClk),
		.wrHardReset_n     (macPIClkHardRst_n),
		.rdClk             (macCoreTxClk),
		.rdHardReset_n     (macCoreClkHardRst_n),
		.wrFlush           (wrFlush),
		.fifoWrite         (txFIFOWrite),
		.fifoAlmostFull    (txFIFOAlmostFull),
		.fifoFull          (txFIFOFull),
		.fifoAlmEmptyWrClk (txFIFOAlmEmptyWrClk),
		.fifoEmptyWrClk    (txFIFOEmptyWrClk),
		.fifoWrPtr         (txFIFOWriteAddr),
		.rdFlush           (rdFlush),
		.fifoRead          (txFIFOReadWord),
		.fifoEmpty         (txFIFOEmpty),
		.fifoRdPtr         (txFIFOReadAddr),
		.fifoPtrsNull      (fifoPtrsNull)
		);

pulse2PulseSynchro U_txFIFOSoftReset_synchro (
                .srcclk (macCoreTxClk),
                .srcresetn (macCoreClkHardRst_n),
                .dstclk (macPITxClk),
                .dstresetn (macPIClkHardRst_n),
                .srcdata (macCoreTxClkSoftRst),
                .dstdata (macCoreTxClkSoftRstResync)
                );


pulse2PulseSynchro U_txFIFOReset_synchro (
                .srcclk (macCoreTxClk),
                .srcresetn (macCoreClkHardRst_n),
                .dstclk (macPITxClk),
                .dstresetn (macPIClkHardRst_n),
                .srcdata (txFIFOReset),
                .dstdata (txFIFOResetResync)
                );

assign txFIFOResetInValid   = fifoPtrsNull && txFIFOReset;

assign macCoreTxClkSoftRst = !macCoreTxClkSoftRst_n;

assign wrFlush              = txFIFOWrFlush || 
                              macCoreTxClkSoftRstResync ||
                              txFIFOResetResync;
assign rdFlush              = txFIFORdFlush || 
                              macCoreTxClkSoftRst ||
                              txFIFOReset;

assign txFIFOWriteData    = {txFIFOWrTag,txFIFOWrData};

assign txFIFOWriteEn    = txFIFOWrite;
assign txFIFOReadEn     = txFIFORead;

assign txFIFOReadWord = (txFIFORead && (readNow || txFIFOReadByFour)) ? 1'b1 : 1'b0;

assign txTagFIFOReadData = txFIFOReadData[37:32];

// Count the number of read bytes per word
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    cnt      <= 2'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || txFIFORdFlush)  // Synchronous Reset
    cnt      <= 2'b0; 
  else
  begin
    if (txFIFORead && !txFIFOReadByFour && !txFIFOReadByTwo)
      cnt      <= cnt + 2'b01;
    else if (txFIFORead && !txFIFOReadByFour)
      cnt      <= cnt + 2'b10;

    if (txFIFOReadWord && !txFIFOReadByFour)
      cnt      <= 2'b00;
  end    
end

// Count the number of read bytes per word delayed of one clock cycle
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    cnt_ff1      <= 2'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || txFIFORdFlush)  // Synchronous Reset
    cnt_ff1      <= 2'b0; 
  else
    cnt_ff1      <= cnt;
end

// This process creates the readNow signal which indicates when a new word from the FIFO 
// has to be fetched. This signal is high when the last valid bytes has been read by the 
// Tx Controller
always @ *
begin
    casex ({nBytes, cnt, txFIFOReadByTwo})

           {3'h4, 2'd3, 1'bx} :readNow  = 1'b1; 
           {3'h3, 2'd2, 1'b0} :readNow  = 1'b1; 
           {3'h2, 2'd1, 1'bx} :readNow  = 1'b1; 
           {3'h1, 2'd1, 1'bx} :readNow  = 1'b1; 
           {3'hx, 2'd2, 1'b1} :readNow  = 1'b1;
                      default :readNow  = 1'b0;
    endcase

end

// This process generates the txFIFORead_ff1 signal which is the txFIFORead input delay
// of one clock cycle
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txFIFORead_ff1      <= 1'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || txFIFORdFlush)  // Synchronous Reset
    txFIFORead_ff1      <= 1'b0; 
  else
    txFIFORead_ff1      <= txFIFORead;
      
end

// The txFIFODataValid indication is generated one clock cycle after the request. However,
// there is a case where this condition is not true. This is when the current quadlet has 
// only one valid byte. In this case, the data is not valid for one clock cycle in order 
// to fetch a new word in the FIFO
assign txFIFODataValid = txFIFORead_ff1 && !((cnt == 2'd0) && nBytes == 3'd1);


// This process assigns the currentByte signal that indicates which byte is the next active byte.
// It depends on the number of active byte within the quadlet and what are the position of these 
// active bytes
//
// If the number of active bytes is 4 (tag 4'b1111), the currentByte is cnt
// If the number of active bytes is 3 (tag 4'b0111 or 4'b1110), 
//    the currentByte is :
//      either cnt     (if tag is 4'b0111)
//          or cnt + 1 (if tag is 4'b1110)
// If the number of active bytes is 2 (tag 4'b0011 or 4'b1100 or 4'b0110), 
//    the currentByte is :
//      either cnt     (if tag is 4'b0011)
//          or cnt + 1 (if tag is 4'b0110)
//          or cnt + 2 (if tag is 4'b1100)
// If the number of active bytes is 1 (tag 4'b0001 or 4'b0010 or 4'b0100 or 4'b1000), 
//    the currentByte is :
//    either cnt     (if tag is 4'b0001)
//        or cnt + 1 (if tag is 4'b0010)
//        or cnt + 2 (if tag is 4'b0100)
//        or cnt + 3 (if tag is 4'b1000)
always @ * 
begin
  case (nBytes)
    3'h4 : 
      currentByte = cnt_ff1;            // (if tag is 4'b1111)
    3'h3 : 
      begin
        if (txTagFIFOReadData[0] == 1'b1)
          currentByte = cnt_ff1;        // (if tag is 4'b0111)
        else
          currentByte = cnt_ff1 + 2'b1; // (if tag is 4'b1110)
      end  
    3'h2 :  
      begin
        if (txTagFIFOReadData[0] == 1'b1)
          currentByte = cnt_ff1;        // (if tag is 4'b0011)
        else if (txTagFIFOReadData[1] == 1'b1)
          currentByte = cnt_ff1 + 2'h1; // (if tag is 4'b0110)
        else
          currentByte = cnt_ff1 + 2'h2; // (if tag is 4'b1100)
      end  
    3'h1 :
      begin
        if (txTagFIFOReadData[0] == 1'b1)
          currentByte = cnt_ff1;        // (if tag is 4'b0001)
        else if (txTagFIFOReadData[1] == 1'b1)
          currentByte = cnt_ff1 + 2'h1; // (if tag is 4'b0010)
        else if (txTagFIFOReadData[2] == 1'b1)
          currentByte = cnt_ff1 + 2'h2; // (if tag is 4'b0100)
        else
          currentByte = cnt_ff1 + 2'h3; // (if tag is 4'b1000)
      end 
    default:   
      currentByte = cnt_ff1;
  endcase
end



// Assign the read data based on currentByte information.
always @*
begin
  case (currentByte)
    2'd0 : txFIFORdData = txFIFOReadData[7:0];
    2'd1 : txFIFORdData = txFIFOReadData[15:8];
    2'd2 : txFIFORdData = txFIFOReadData[23:16];
    2'd3 : txFIFORdData = txFIFOReadData[31:24];
  endcase    
end

// This process generates the readNow_ff1 signal which is the readNow input delay
// of one clock cycle
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    readNow_ff1      <= 1'b0; 
  else if (macCoreTxClkSoftRst_n == 1'b0 || txFIFORdFlush)  // Synchronous Reset
    readNow_ff1      <= 1'b0; 
  else
    readNow_ff1      <= readNow;
      
end

// Assign the MPDU Delimiters
// The MPDU delimiter read from the TAG FIFO is not provided as is to the Tx Controller.
// In case of MPDU delimiter indicating first quadlet (2'b00), only the first active byte of this qualet
// will be provided to the Tx Controller with 2'00 as delimiter. The others bytes of this quadlet will 
// get 2'b01 delimiter.
// In case of MPDU delimiter indicating last quadlet (2'b10), only the last active byte of this qualet
// will be provided to the Tx Controller with 2'10 as delimiter. The others bytes of this quadlet will 
// get 2'b01 delimiter.
//   1- If only one valid byte is contained in the last quadlet, the MPDU delimiter takes the value 2'b10 immediatly 
//      when readNow is set. In this case, the next quadlet is poped from the FIFO immediatly.
//   2- If more than one valid byte is contained in the last quadlet, the MPDU delimiter takes the value 2'b10 
//     when readNow_ff1 will be set.
// For all the others delimiters, the delimiter is provided as is.
always @*
begin
  case (txTagFIFOReadData[5:4])
    2'b00 : 
      begin
        if (cnt_ff1 == 2'd0)
          txFIFOMPDUDelimiters = 2'b00;
        else  
          txFIFOMPDUDelimiters = 2'b01;
      end  
    2'b01 : 
      txFIFOMPDUDelimiters = 2'b01;
    2'b10 : 
      begin
        if (((nBytes == 3'd1) && readNow) || ((nBytes != 3'd1) && readNow_ff1))
          txFIFOMPDUDelimiters = 2'b10;
        else
          txFIFOMPDUDelimiters = 2'b01;
      end  
    2'b11 : 
      txFIFOMPDUDelimiters = 2'b11;
  endcase    
end


//assign activeBytes = txTagFIFOReadData[3:0];


// Count the number of valid bytes in TX FIFO based on TX FIFO TAG information
always @*
begin
  case (txTagFIFOReadData[3:0])
    4'b0001 : nBytes = 3'h1;
    4'b0010 : nBytes = 3'h1;
    4'b0100 : nBytes = 3'h1;
    4'b1000 : nBytes = 3'h1;
    4'b0011 : nBytes = 3'h2;
    4'b0110 : nBytes = 3'h2;
//    `ifdef RW_MPDU_AC
//    4'b1100 : nBytes = txTagFIFOReadData[4] ? 3'h2 :3'h4; // if first from header then 4 bytes else (payload) 2 bytes
//    `else
    4'b1100 : nBytes = 3'h2;
//    `endif
    4'b1110 : nBytes = 3'h3;
    4'b0111 : nBytes = 3'h3;
    4'b1111 : nBytes = 3'h4;
     // pragma coverage block = off
     // This default state has been removed fromt he coverage because it is not allowed and 
     // already protected by an assertion 
    default : nBytes = 3'b0;
     // pragma coverage block = on 
  endcase    
end



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


// System Verilog Assertions
////////////////////////////

`ifdef RW_ASSERT_ON
//$rw_sva Checks if the valid byte information contained in TAG FIFO is correct
property readEmptyTag_prop;
@(posedge macCoreTxClk)
    (txFIFORead == 1'b1) |=> nBytes > 0;
endproperty
readEmptyTag: assert property (readEmptyTag_prop); 

//$rw_sva Checks if the txFIFOAlmost full indication is high when txFIFO is full
property fifoFullwithAlmostFullLow_prop;
@(posedge macCoreTxClk)
    (txFIFOFull == 1'b1) |-> txFIFOAlmostFull == 1'b1;
endproperty
fifoFullwithAlmostFullLow: assert property (fifoFullwithAlmostFullLow_prop); 

`endif // RW_ASSERT_ON
endmodule
 
