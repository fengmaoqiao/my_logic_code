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
// Description      : AHB Master IF file. 
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
`default_nettype none

module ahbMasterIF (

  //$port_g clock and reset
  input wire                                    macPIClk             ,// AHB Clock (12MHz to 100 MHz)   
  input wire                                    macPIClkHardRst_n    ,// AHB Reset signal. Power on reset.  

  //$port_g DMA interface
  input wire    [31:0]                          dmaHIFAddressIn      ,// Address for the single transfer or starting address for a burst
  input wire                                    dmaHIFRead           ,// Signal indicating a dmaHIFRead.
  input wire                                    dmaHIFWrite          ,// Signal indicating a dmaHIFWrite
  input wire    [ 2:0]                          dmaHIFSize           ,// Signal indicating the dmaHIFWrite dmaHIFSize
  input wire    [31:0]                          dmaHIFWriteDataIn    ,// The data to be written into addressed location 
  //
  output wire                                   dmaHIFError          ,// Asserted if an dmaHIFError response is received.
  output wire   [31:0]                          dmaHIFReadDataOut    ,// data dmaHIFRead from AHB
  output wire                                   dmaHIFReadDataValid  ,// dmaHIFRead data data valid
  output wire                                   dmaHIFReady          ,// Asserted when next data has to be pushed.
  output reg                                    dmaHIFTransComplete  ,// Asserted when next data last data has been pushed
  
  //$port_g AHB interface
  output wire   [31:0]                          hMAddr                ,// Address for the transaction for external AHB slave
  output reg    [ 1:0]                          hMTrans               ,// Transfer Type, for external AHB slave
  output reg    [ 2:0]                          hMSize                ,// dmaHIFSize of each transfer, for external AHB slave
  output reg                                    hMWrite               ,// Control signal, 1-dmaHIFWrite transfer 0 -dmaHIFRead transfer for external AHB slave
  output reg    [ 2:0]                          hMBurst               ,// Type of burst for external AHB slave.
  output reg    [31:0]                          hMWData               ,// The data for the dmaHIFWrite transfer, for external AHB slave

  input wire                                    hMReady               ,// dmaHIFReady signal. 1- transfer can complete, 0- the data phase to be extended. From the addressed slave.
  input wire    [ 1:0]                          hMResp                ,// Transfer response for the initited transfer. From the adddressed slave.
  input wire    [31:0]                          hMRData                // Data dmaHIFRead from the addressed location. It is valid when hMReady is 1 from the addressed slave


);


reg                     dmaHIFWriteDataPhase;    // indicate the dmaHIFWrite data phase is started
reg                     dmaHIFReadDataPhase;     // indicate the dmaHIFRead data phase is started
wire                    lastData;                // the last data has been transfered
reg                     boundaryCross;           // detect 1k boundary crossing

assign hMAddr  = dmaHIFAddressIn;

// start of logic
assign dmaHIFReady = (hMTrans != 2'b0) ? hMReady : 1'b0; 

assign dmaHIFError = (hMResp != 2'b0)  ? 1'b1 : 1'b0; 

//generate the hMBurst and hMSize
always @*
begin
  if (dmaHIFRead || dmaHIFWrite)
  begin
    // setup hMWrite
    if(dmaHIFWrite)
      hMWrite    = 1'b1;
    else
      hMWrite    = 1'b0;
    // setup the burst
    hMBurst      = 3'b001; 
    // setup hMSize  
    hMSize       = dmaHIFSize;
  end
  else
  begin
    hMSize     = 3'b0;
    hMBurst    = 3'b0;
    hMWrite    = 1'b0;
  end
end

//generate hMTrans and dataPhase
always @*
begin
  if (dmaHIFRead || dmaHIFWrite)
  begin
    // whem data phase is started set trans to 3
    if ((dmaHIFWriteDataPhase || dmaHIFReadDataPhase) && !boundaryCross)
      hMTrans = 2'b11;
    // else set it to 2 at the starte
    else
      hMTrans = 2'b10;
  end
  else
  begin
    hMTrans    = 2'b00;
  end
end

//handling signal indicating data phase
always @ (posedge macPIClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    dmaHIFWriteDataPhase     <= 1'b0; 
    dmaHIFReadDataPhase      <= 1'b0; 
  end
  else 
  begin
    // trans indicate start of access
    if ((hMTrans != 2'b0) && hMReady)
    begin
      if (hMWrite)
        dmaHIFWriteDataPhase <= 1'b1;
      else
        dmaHIFReadDataPhase  <= 1'b1;
    end
    // reset it when last data has been received
    else if (lastData)
    begin
      dmaHIFWriteDataPhase <= 1'b0;
      dmaHIFReadDataPhase  <= 1'b0;
    end
  end
end 

// when an access is started, and no address phase is active 
// and data is valid then the lastData is transfered
assign lastData = ((dmaHIFWriteDataPhase || dmaHIFReadDataPhase) &&
                   (hMTrans == 2'b0) &&
                   hMReady) ? 1'b1 : 1'b0; 

//dmaHIFWrite data Handling
// regsiter to insert a clock cycle delay
always @ (posedge macPIClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    hMWData     <= 32'b0; 
  else 
  begin
    if ((hMTrans != 2'b00) && hMWrite && hMReady)
      hMWData <= dmaHIFWriteDataIn;
  end
end


assign dmaHIFReadDataOut    = (dmaHIFReadDataValid) ? hMRData : 32'b0;
assign dmaHIFReadDataValid  = (hMReady && dmaHIFReadDataPhase)  ? 1'b1 : 1'b0;

always @ (posedge macPIClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    dmaHIFTransComplete <= 1'b0; 
  else 
  begin
    dmaHIFTransComplete <= lastData;
  end
end

// provides detection of 1k bytes crossing
always @ (posedge macPIClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    boundaryCross <= 1'b0;
  else
  begin
    if (hMReady == 1'b1)
    begin
      if ((hMTrans != 2'b0) && (hMAddr[9:2] == 8'hFF))
        boundaryCross <= 1'b1;
      else
        boundaryCross <= 1'b0;
    end
  end
end




`ifdef RW_ASSERT_ON
///////////////////////////////////////////////////////
// AHB INTERFACE PROPERTIES
///////////////////////////////////////////////////////
//$rw_sva Check dmaHIFWrite is not asserted while dmaHIFRead
property dmaHIFReadNotdmaHIFWrite_prop;
@(posedge macPIClk)
  disable iff(macPIClk==0)
  dmaHIFRead|->!dmaHIFWrite;
endproperty
dmaHIFReadNotdmaHIFWrite: assert property (dmaHIFReadNotdmaHIFWrite_prop); 

//$rw_sva Check dmaHIFRead is not asserted while dmaHIFWrite
property dmaHIFWriteNotdmaHIFRead_prop;
@(posedge macPIClk)
  disable iff(macPIClk==0)
  dmaHIFWrite|->!dmaHIFRead;
endproperty
dmaHIFWriteNotdmaHIFRead: assert property (dmaHIFWriteNotdmaHIFRead_prop); 
`endif


endmodule

