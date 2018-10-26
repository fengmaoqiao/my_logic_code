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
// Description      : Top level of rxFIFO module
//                    
// Simulation Notes : 
// Synthesis Notes  :
// Application Note :                                                       
// Simulator        :                                                       
// Parameters       :
//        ADDRWIDTH : Address bus bitwidth of the RAM.
//            DEPTH : Depth of the rxFifo.
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


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"
// pragma coverage pragmas = on
// pragma coverage implicit_default=off 

module rxFifo (
          //$port_g Clock and Reset of read interface           
          input  wire                                 macPIRxClk,             // MAC Platform Receive Clock
          input  wire                                 macPIClkHardRst_n,      // Hard Reset of the MAC Platform Clock domain
                                                                              // active low

          //$port_g Clock and Reset of write interface
          input  wire                                 macCoreRxClk,           // MAC Core Receive Clock
          input  wire                                 macCoreClkHardRst_n,    // Hard Reset of the MAC Core Clock domain 
                                                                              // active low
          //$port_g Control and Status register
          input  wire                                 rxFIFOReset,            // Reset the FIFO
          output wire                                 rxFIFOResetInValid,     // Clear of FIFO reset

          //$port_g Write control interface
          input  wire                                 rxFIFOWrFlush,          // Request from MAC Core Clock domain to flush the FIFO
          input  wire                                 rxFIFOWrite,            // Write a new word in the rx FIFO
          input  wire                          [31:0] rxFIFOWrData,           // Data written to the rx FIFO
          input  wire                          [ 3:0] rxFIFOWrTag,            // Tag written to the rx FIFO
          output wire                                 rxFIFOAlmostFull,       // Indicates that the rx FIFO is almost full
          output wire                                 rxFIFOFull,             // Indicates that the rx FIFO is full and cannot accept new write
          output wire                                 rxFIFOAlmEmptyWrClk,    // Indicates that the rx FIFO is almost empty
          output wire                                 rxFIFOEmptyWrClk,       // Indicates that the rx FIFO is empty

          //$port_g Read control interface
          input  wire                                 rxFIFORdFlush,          // Request from MAC Platform Clock domain to flush the FIFO
          input  wire                                 rxFIFORead,             // Request a new byte from the rx FIFO
          output wire                                 rxFIFOAlmEmpty,         // Indicates that the rx FIFO is almost empty
          output wire                                 rxFIFOEmpty,            // Indicates that the rx FIFO is empty
          output reg                                  rxFIFODataValid,        // Indicates when the read data is valid
          output wire                         [ 31:0] rxFIFORdData,           // Byte read from the rx FIFO
          output wire                          [ 3:0] rxFIFOMPDUDelimiters,   // Tag read from the rx FIFO
          
          //$port_g Memory Read Interface
          input  wire                          [35:0] rxFIFOReadData,         // Receive FIFO Read Data bus.
          output wire      [(`RXFIFOADDRWIDTH - 1):0] rxFIFOReadAddr,         // Receive FIFO and receive tag FIFO Read Address bus.
          output wire                                 rxFIFOReadEn,           // Receive FIFO and receive tag FIFO Read Enable. 
                                                                              // This signal is asserted for read operations to the receive FIFO and the receive Tag FIFO.

          //$port_g Memory Read Interface
          output wire      [(`RXFIFOADDRWIDTH - 1):0] rxFIFOWriteAddr,        // Receive FIFO and receive tag FIFO Write Address bus
          output wire                          [35:0] rxFIFOWriteData,        // Receive FIFO Write Data bus.
          output wire                                 rxFIFOWriteEn           // Receive FIFO and receive tag FIFO Write Enable. 
          );


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
wire  wrFlush;
wire  rdFlush;
wire  rxFIFOResetResync;
wire  fifoPtrsNull;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

rxFifoController #(.ADDRWIDTH(`RXFIFOADDRWIDTH),.DEPTH(`RXFIFODEPTH)) U_rxFifoController (
		.wrClk             (macCoreRxClk),         
		.wrHardReset_n     (macCoreClkHardRst_n),
		.rdClk             (macPIRxClk),
		.rdHardReset_n     (macPIClkHardRst_n),
		.wrFlush           (wrFlush),
		.fifoWrite         (rxFIFOWrite),
		.fifoAlmostFull    (rxFIFOAlmostFull),
		.fifoFull          (rxFIFOFull),
		.fifoAlmEmptyWrClk (rxFIFOAlmEmptyWrClk),
		.fifoEmptyWrClk    (rxFIFOEmptyWrClk),
		.fifoWrPtr         (rxFIFOWriteAddr),
		.fifoPtrsNull      (fifoPtrsNull),
		.rdFlush           (rdFlush),
		.fifoRead          (rxFIFORead),
		.fifoAlmEmpty      (rxFIFOAlmEmpty),
		.fifoEmpty         (rxFIFOEmpty),
		.fifoRdPtr         (rxFIFOReadAddr)
		);

pulse2PulseSynchro U_rxFIFOReset_synchro (
                .srcclk (macCoreRxClk),
                .srcresetn (macCoreClkHardRst_n),
                .dstclk (macPIRxClk),
                .dstresetn (macPIClkHardRst_n),
                .srcdata (rxFIFOReset),
                .dstdata (rxFIFOResetResync)
                );
                
assign rxFIFOResetInValid   = fifoPtrsNull && rxFIFOReset;

assign wrFlush              = rxFIFOWrFlush || rxFIFOReset;
assign rdFlush              = rxFIFORdFlush || rxFIFOResetResync;

assign rxFIFOWriteData      = {rxFIFOWrTag,rxFIFOWrData};

assign rxFIFOWriteEn        = rxFIFOWrite;
assign rxFIFOReadEn         = rxFIFORead;

assign rxFIFORdData         = rxFIFOReadData[31:0];
assign rxFIFOMPDUDelimiters = rxFIFOReadData[35:32];

// This process generates the rxFIFODataValid signal which is the rxFIFORead input delay
// of one clock cycle
always @ (posedge macPIRxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxFIFODataValid <= 1'b0; 
  else if (rxFIFORdFlush)         // During flush data is not valid
    rxFIFODataValid <= 1'b0; 
  else
    rxFIFODataValid <= rxFIFORead;
end


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// System Verilog Assertions
////////////////////////////

`ifdef RW_ASSERT_ON
//$rw_sva Checks no read appears when fifo is empty
property noReadWhenEmpty_prop;
@(posedge macPIRxClk)
    rxFIFORead |-> !rxFIFOEmpty;
endproperty
noReadWhenEmpty: assert property (noReadWhenEmpty_prop); 

//$rw_sva Count write request when fifo is full
property noWriteWhenFull_prop;
@(posedge macCoreRxClk)
    rxFIFOWrite |-> !rxFIFOFull;
endproperty
noWriteWhenFull: cover property (noWriteWhenFull_prop); 

`endif // RW_ASSERT_ON
endmodule
 
