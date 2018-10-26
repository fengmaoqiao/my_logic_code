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
`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"
module mibResync( 

  //$port_g Resets and Clocks
  input  wire                            macPIClkHardRst_n     ,// Active low hard reset signal synchronized to the macPIClk.
  input  wire                            macCoreClkHardRst_n   ,// Active low hard reset signal synchronized to the macCoreClk.
  input  wire                            macCoreClk            ,// Primary MAC Core Clock
  input  wire                            macPIClk              ,// Primary MAC Platform Interface Clock

  //$port_g hostIf interface
  output reg  [`RW_MIB_DATA_WIDTH-1 : 0] mibHostIfRdData       ,// Read Data forwarded to Host
  output wire                            mibHostIfReady        ,// Output MIB busy indication to host
  output reg                             mibHostDataValid      ,// Output MIB busy indication to host
  //
  input  wire [`RW_REG_ADDR_WIDTH-1 : 0] mibHostIfAddr         ,// Address From Host
  input  wire [`RW_MIB_DATA_WIDTH-1 : 0] mibHostIfWrData       ,// Data from Host to be written to RAM
  input  wire                            mibHostIfWr           ,// Wr Enable signal from host
  input  wire                            mibHostIfRd           ,// Rd Enable signal from host
    

  //$port_g mibController Interface
  input  wire [`RW_MIB_DATA_WIDTH-1 : 0] mibRdData             ,// Read Data forwarded to Host from mib
  input  wire                            mibBusy               ,// Output MIB busy indication to host
  //
  output reg  [`RW_MIB_ADDR_WIDTH-1 : 0] mibAddr               ,// Address From Host
  output reg  [`RW_MIB_DATA_WIDTH-1 : 0] mibWrData             ,// Data from Host to be written to RAM
  output wire                            mibWr                 ,// Wr Enable signal from host
  output wire                            mibRd                  // Rd Enable signal from host


                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
wire                     accessDataDone;
reg                      writeBusy;
reg                      readBusy;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////



assign mibHostIfReady    = (mibHostIfWr || mibHostIfRd || writeBusy || readBusy) ? 1'b0 : 1'b1;


// generate a pulse for validating data
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if(macPIClkHardRst_n == 1'b0)
     mibHostDataValid <= 1'b0;
  else
  begin
    if ((accessDataDone == 1'b1) && (mibHostIfReady== 1'b0))
      mibHostDataValid <= 1'b1;
    else
      mibHostDataValid <= 1'b0;
  end
end


// sample written data  and address and keep them until they are sampled on macCoreclock    
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if(macPIClkHardRst_n == 1'b0)
  begin
     mibWrData      <= `RW_MIB_DATA_WIDTH'b0;
     mibAddr        <= `RW_MIB_ADDR_WIDTH'b0;
  end
  else
  begin
    if ((mibHostIfWr == 1'b1) || (mibHostIfRd== 1'b1))
    begin
      mibWrData      <= mibHostIfWrData;
      mibAddr        <= mibHostIfAddr[`RW_MIB_ADDR_WIDTH-1:0];
    end
  end
end


// sample written data and keep them until they are sampled on macCoreclock    
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if(macPIClkHardRst_n == 1'b0)
  begin
     writeBusy      <= 1'b0;
     readBusy       <= 1'b0;
  end
  else
  begin
    if ( mibHostIfWr == 1'b1)
    begin
      writeBusy      <= 1'b1;
    end
    else if (accessDataDone == 1'b1)
    begin
      writeBusy      <= 1'b0;
    end
    if ( mibHostIfRd == 1'b1)
    begin
      readBusy       <= 1'b1;
    end
    else if (accessDataDone == 1'b1)
    begin
      readBusy       <= 1'b0;
    end
  end
end

// sample read data when access is done
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if(macPIClkHardRst_n == 1'b0)
  begin
    mibHostIfRdData <=  `RW_MIB_DATA_WIDTH'b0;
  end
  else
  begin
    if ( accessDataDone == 1'b1)
      mibHostIfRdData <= mibRdData;
  end  
end


pulse2PulseSynchro U_wrValidSynchro (
		.srcclk       (macPIClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (mibHostIfWr),
		.dstdata      (mibWr)
);
pulse2PulseSynchro U_rdValidSynchro (
		.srcclk       (macPIClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (mibHostIfRd),
		.dstdata      (mibRd)
);

// generate a pulse when the busy is falling
fallingEdgeDetector U_mibBusySynchro (
		.dstclk       (macPIClk),
		.dstresetn    (macPIClkHardRst_n),
		.srcdata      (mibBusy),
		.dstdata      (accessDataDone)
);




endmodule
                 
