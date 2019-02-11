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
// Description      : This module accepts the request from the list processors 
//                    and status updater blocks and translates the request to
//                    perform accesses to AHB bus and data movement between 
//                    Local SRAM and TX FIFO as well as fetching descriptors
//                    from SRAM as requested by teh modules
// Simulation Notes : System verilog assertions can be enabled with RW_ASSERT_ON
//                    Then a system verilog capable simulator is needed
// Synthesis Notes  : 
// Application Note :                                                       
// Simulator        :                                                       
// Parameters       :                                                       
// Terms & concepts :                                                       
// Bugs             :
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

module rdWrCtlr(

   //$port_g clocks and reset
   input wire                                    macPIClk,                 //Platform1 Clock Domain
   input wire                                    macPIClkHardRst_n,        //Hard Reset synchronized to macPIClk,
   input wire                                    macPIClkSoftRst_n,        //Soft Reset syncrhonized to macPIClk,

   
   //$port_g host If port
   output reg    [31:0]                          dmaHIFAddressIn,          // Address for the single transfer or starting address for a burst
   output reg                                    dmaHIFRead,               // Signal indicating a read.
   output reg                                    dmaHIFWrite,              // Signal indicating a write
   output reg    [ 2:0]                          dmaHIFSize,               // Signal indicating the write size
   output reg    [31:0]                          dmaHIFWriteDataIn,        // The data to be written into addressed location 
   //
   input  wire                                   dmaHIFError,              // Asserted if an error response is received.
   input  wire   [31:0]                          dmaHIFReadDataOut,        // data read from AHB
   input  wire                                   dmaHIFReadDataValid,      // read data data valid
   input  wire                                   dmaHIFReady,              // Asserted when next data has to be pushed.
   input  wire                                   dmaHIFTransComplete,      // Asserted when next data last data has been pushed
   
   //$port_g status to be shared with others blocks
   output wire                                   rdWrCtlrIdle,             // the controller is idle
   
   //$port_g Tx List Processor port
   input  wire   [31:0]                          rxListStartAddress,       // Starting Address from the system memory to read or write the data
   input  wire                                   rxListRead,               // Read enable
   input  wire                                   rxListWrite,              // Write enable
   input  wire   [ 2:0]                          rxListSize,               // Access size
   input  wire   [31:0]                          rxListWriteData,          // Written data
   input  wire                                   rxListLast,               // Last read access
   //
   output wire                                   rxListError,              // Indicate a transfer error
   output wire                                   rxListNextData,           // Data written, push the next data        
   output wire   [31:0]                          rxListReadData,           // Read data
   output wire                                   rxListReadDataValid,      // Read data Valid
   output wire                                   rxListTransComplete,      // transaction done

   //$port_g Tx List Processor port
   input  wire   [31:0]                          txListStartAddress,       // Starting Address from the system memory to read or write the data
   input  wire                                   txListWrite,              // Write enable
   input  wire   [ 2:0]                          txListSize,               // Access size
   input  wire   [31:0]                          txListWriteData,          // Written data
   input  wire                                   txListRead,               // Read enable
   input  wire                                   txListLast,               // Last Access
   //
   output wire                                   txListError,              // Indicate a transfer error
   output wire                                   txListNextData,           // Data written, push the next data        
   output wire   [31:0]                          txListReadData,           // Read data
   output wire                                   txListReadDataValid,      // Read data Valid
   output wire                                   txListTransComplete,      // transaction done
   
   //$port_g Tx Status updater port
   input  wire   [31:0]                          staUpdStartAddress,       // Starting Address from the system memory to read or write the data
   input  wire                                   staUpdWrite,              // Write enable
   input  wire   [31:0]                          staUpdWriteData,          // Written data
   //
   output wire                                   staUpdError,              // Indicate a transfer error
   output wire                                   staUpdNextData,           // Data written, push the next data        
   output wire                                   staUpdTransComplete,      // transaction done

   output wire   [15:0]                          debugPortDmaRdWrCtlr      // Debug Purpose
);



//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// Signals initiating the read and write
reg            writeEnable;
wire           writeEnable_c;
reg            readEnable;
wire           readEnable_c;
wire           lastAccess;

// Signal indicating the active port (TxList, StaUpd, Rxlist)
reg  [ 1:0]    portSel;      //active port
                             // 1: rxList
                             // 2: txList
                             // 3: staUpd
              

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// as soon as a write or read request is asserted and as long as the port selection
// is not cleared
assign rdWrCtlrIdle = (writeEnable_c || readEnable_c || (portSel != 2'b0)) ? 1'b0 :1'b1;


assign lastAccess    =  ((rxListLast  == 1'b1) || (txListLast  == 1'b1));
assign writeEnable_c =  ((rxListWrite == 1'b1) || (txListWrite == 1'b1) || (staUpdWrite == 1'b1));
assign readEnable_c  =  ((rxListRead  == 1'b1) || (txListRead  == 1'b1));

// muxing the controls and data
// muxing the write data
always @*
begin
  case(portSel)
    2'd1:
      dmaHIFWriteDataIn = rxListWriteData;
    2'd2:
      dmaHIFWriteDataIn = txListWriteData;
    2'd3:
      dmaHIFWriteDataIn = staUpdWriteData;
    default:
      dmaHIFWriteDataIn = 32'b0;
  endcase
end

always @*
begin
  case(portSel)
    2'd1:
      dmaHIFSize = rxListSize;
    2'd2:
      dmaHIFSize = txListSize;
    2'd3:
      dmaHIFSize = 3'b010;
    default:
      dmaHIFSize = 3'b0;
  endcase
end

always @ (posedge macPIClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    dmaHIFAddressIn <= 32'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    dmaHIFAddressIn <= 32'b0;
  end
  else
  begin
    // access start
    if ( (readEnable_c &&  !readEnable) || // start a read
         (writeEnable_c &&  !writeEnable)) // start a begin
    begin
      if ( rxListWrite || rxListRead)      // sample first Rx address
         dmaHIFAddressIn <= {rxListStartAddress[31:2],2'b00};
      else if (txListWrite || txListRead)                         // sample first Tx address
         dmaHIFAddressIn <= {txListStartAddress[31:2],2'b00};
      else if (staUpdWrite)                        // sample first status updater address
        dmaHIFAddressIn <= {staUpdStartAddress[31:2],2'b00};

    end
    // access started 
    else if (readEnable || writeEnable) 
    begin  
      if (dmaHIFReady)
        dmaHIFAddressIn <= dmaHIFAddressIn + 32'h4;
      else
        dmaHIFAddressIn <= dmaHIFAddressIn;
        
    end
    else      
      dmaHIFAddressIn <= 32'b0;
  end
end

// error handling
assign rxListError = ((portSel == 2'd1) && (dmaHIFError == 1'b1)) ?  1'b1 : 1'b0;
assign txListError = ((portSel == 2'd2) && (dmaHIFError == 1'b1)) ?  1'b1 : 1'b0;
assign staUpdError = ((portSel == 2'd3) && (dmaHIFError == 1'b1)) ?  1'b1 : 1'b0;

// muxing rxList outputs
assign rxListNextData      = (portSel == 2'd1) ? dmaHIFReady         :  1'b0;
assign rxListTransComplete = (portSel == 2'd1) ? dmaHIFTransComplete :  1'b0;
assign rxListReadData      = (portSel == 2'd1) ? dmaHIFReadDataOut   : 32'b0;
assign rxListReadDataValid = ((portSel == 2'd1) && readEnable_c) ? dmaHIFReadDataValid :  1'b0;

// muxing TxList outputs
assign txListNextData      = (portSel == 2'd2) ? dmaHIFReady         :  1'b0;
assign txListTransComplete = (portSel == 2'd2) ? dmaHIFTransComplete :  1'b0;
assign txListReadData      = (portSel == 2'd2) ? dmaHIFReadDataOut   : 32'b0;
assign txListReadDataValid = ((portSel == 2'd2) && readEnable_c) ? dmaHIFReadDataValid :  1'b0;
 
// muxing staUpd outputs
assign staUpdNextData      = (portSel == 2'd3) ? dmaHIFReady         :  1'b0;
assign staUpdTransComplete = (portSel == 2'd3) ? dmaHIFTransComplete :  1'b0;
 
//registering read and write controls
always @ (posedge macPIClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    writeEnable <= 1'b0;
    readEnable  <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    writeEnable <= 1'b0;
    readEnable  <= 1'b0;
  end
  else
  begin
    if (writeEnable_c)
      writeEnable <= 1'b1;
    else      
      writeEnable <= 1'b0;
    if (readEnable_c)
      readEnable <= 1'b1;
    else      
      readEnable <= 1'b0;
  end
end

//registering active Port
always @ (posedge macPIClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    portSel <= 2'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    portSel <= 2'b0;
  end
  else
  begin
    // port selection management
    // sample the control during the first write clock cycle
    if ( writeEnable_c  && !writeEnable)
    begin
      // Rxlist request
      if (rxListWrite == 1'b1)
        portSel <= 2'd1;
      // TxList request
      else if (txListWrite == 1'b1)
        portSel <= 2'd2;
      // status updated request
      else if (staUpdWrite) 
        portSel <= 2'd3;
    end
    else if (readEnable_c && !readEnable )
    begin
      // Rxlist request
      if (rxListRead)
        portSel <= 2'd1;
      // TxList request
      else if (txListRead) 
        portSel <= 2'd2;
    end
    else if (dmaHIFTransComplete)
      portSel <= 2'b0;
  end
end

////////////// Handling DMA host if controls


// handle the read and write controls on the host if
always @*
begin
  // generate read
  if (readEnable && readEnable_c && !lastAccess) 
    dmaHIFRead   = 1'b1;
  else
    dmaHIFRead   = 1'b0;
  // generate write
  if (writeEnable && writeEnable_c)
    dmaHIFWrite  = 1'b1;
  else
    dmaHIFWrite  = 1'b0;
end    

// Debug
assign debugPortDmaRdWrCtlr     = {rdWrCtlrIdle,
                                   dmaHIFRead,
                                   dmaHIFWrite,
                                   dmaHIFError,
                                   dmaHIFReadDataValid,
                                   dmaHIFReady,
                                   dmaHIFTransComplete,
                                   lastAccess,
                                   rxListTransComplete,
                                   rxListNextData,
                                   readEnable_c,
                                   readEnable,
                                   writeEnable_c,
                                   writeEnable,
                                   portSel[1:0]
                                  };


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_ASSERT_ON
///////////////////////////////////////////////////////
// rdWrCtrl INTERFACE PROPERTIES
///////////////////////////////////////////////////////

//$rw_sva Check when there is a write, there is no read
property writeNotRead_prop;
@(posedge macPIClk)
  disable iff(macPIClkHardRst_n==0)
  writeEnable|->!readEnable;
endproperty
writeNotRead: assert property (writeNotRead_prop); 

//$rw_sva Check dmaHIFread is not asserted while dmaHIFwrite
property readNotWrite_prop;
@(posedge macPIClk)
  disable iff(macPIClkHardRst_n==0)
  readEnable|->!writeEnable;
endproperty
readNotWrite: assert property (readNotWrite_prop); 

//$rw_sva Check RxListRead is not assert during another read
property readRxNotReadTx_prop;
@(posedge macPIClk)
  disable iff(macPIClkHardRst_n==0)
  rxListRead|->!(txListRead);
endproperty
readRxNotReadTx: assert property (readRxNotReadTx_prop); 

//$rw_sva Check TxListRead is not assert during another read
property readTxNotReadRx_prop;
@(posedge macPIClk)
  disable iff(macPIClkHardRst_n==0)
  txListRead|->!(rxListRead);
endproperty
readTxNotReadRx: assert property (readTxNotReadRx_prop); 

//$rw_sva Check RxListWrite is not assert during another Write
property WriteRxNotReadTx_prop;
@(posedge macPIClk)
  disable iff(macPIClkHardRst_n==0)
  rxListWrite |-> !(staUpdWrite | txListWrite);
endproperty
WriteRxNotReadTx: assert property (WriteRxNotReadTx_prop); 


//$rw_sva Check UpListWrite is not assert during another Write
property WriteUpNotReadRx_prop;
@(posedge macPIClk)
  disable iff(macPIClkHardRst_n==0)
  staUpdWrite|->!(rxListWrite);
endproperty
WriteUpNotReadRx: assert property (WriteUpNotReadRx_prop); 


//$rw_sva Check read address is never equal to 0
property NoReadAtAddr0_prop;
@(posedge macPIClk)
  disable iff(macPIClkHardRst_n==0)
  dmaHIFRead|->(dmaHIFAddressIn != 0);
endproperty
NoReadAtAddr0: assert property (NoReadAtAddr0_prop); 

`endif

endmodule
