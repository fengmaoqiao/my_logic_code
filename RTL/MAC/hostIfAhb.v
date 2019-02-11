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
// Description      : Top level of hostIfAhb module
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
`default_nettype none
module hostIfAhb( 

  //$port_g Resets and Clocks
  input  wire                             macPIClkHardRst_n     ,// Active low hard reset signal synchronized to the macPIClk.
  input  wire                             macCoreClkHardRst_n   ,// Active low hard reset signal synchronized to the macCoreClk.
  input  wire                             macPIClk              ,// platform clock reset
  input  wire                             macCoreClk            ,// Primary MAC Core Clock

  //$port_g ARM AHB/AHBLite Slave Interface
  input  wire [(`RW_HOST_ADDR_WIDTH-1):0] hSAddr                ,// ahb slave address
  input  wire [ 1:0]                      hSTrans               ,// ahb slave trans
  input  wire                             hSWrite               ,// ahb slave Write
  input  wire [ 2:0]                      hSSize                ,// ahb slave access size
  input  wire [31:0]                      hSWData               ,// ahb slave write data
  input  wire                             hSSel                 ,// ahb slave select
  input  wire                             hSReadyIn             ,// ahb slave ready in
  output wire [31:0]                      hSRData               ,// ahb slave read data
  output wire                             hSReadyOut            ,// ahb slave ready out
  output wire [ 1:0]                      hSResp                ,// ahb slave response
                                                                 
  //$port_g ARM AHB/AHBLite Master Interface                  
  output wire                             hMBusReq              ,// ahb master bus request
  output wire                             hMLock                ,// ahb master lock
  input  wire                             hMGrant               ,// ahb master bus grant
  output wire [31:0]                      hMAddr                ,// ahb master address
  output wire [ 1:0]                      hMTrans               ,// ahb master trans
  output wire                             hMWrite               ,// ahb master Write
  output wire [ 2:0]                      hMSize                ,// ahb master access size
  output wire [ 2:0]                      hMBurst               ,// ahb master burst
  output wire [ 3:0]                      hMProt                ,// ahb master protection
  output wire [31:0]                      hMWData               ,// ahb master write data
  input  wire [31:0]                      hMRData               ,// ahb master read data
  input  wire                             hMReady               ,// ahb master ready in
  input  wire [ 1:0]                      hMResp                ,// ahb master response
                                                     
`ifdef RW_MAC_MIBCNTL_EN
  //$port_g mibController Interface
  input  wire [`RW_MIB_DATA_WIDTH-1 :0]   mibRdData             ,// Read Data forwarded to Host
  input  wire                             mibBusy               ,// Output MIB busy indication to host
  //
  output wire [`RW_MIB_ADDR_WIDTH-1 :0]   mibAddr               ,// Address From Host
  output wire [`RW_MIB_DATA_WIDTH-1 :0]   mibWrData             ,// Data from Host to be written to RAM
  output wire                             mibWr                 ,// Wr Enable signal from host
  output wire                             mibRd                 ,// Rd Enable signal from host
`endif // RW_MAC_MIBCNTL_EN

  //$port_g Control and Status Register interface
  input  wire                             regReadyIn            ,// read data valid or write completed 
  input  wire [(`RW_REG_DATA_WIDTH-1):0]  regReadData           ,// Data read from registers
  //
  output wire                             regWrite              ,// Write enable
  output wire                             regRead               ,// Read enable
  output wire [(`RW_REG_ADDR_WIDTH-1):0]  regAddr               ,// Register address
  output wire [(`RW_REG_DATA_WIDTH-1):0]  regWriteData          ,// Data to be written to the registers



  //$port_g DMA interface
  input  wire                             dmaHIFRead            ,// dma host interface read enable
  input  wire                             dmaHIFWrite           ,// dma host interface write enable
  input  wire [31:0]                      dmaHIFAddressIn       ,// dma host interface address
  output wire [31:0]                      dmaHIFReadDataOut     ,// dma host interface read data
  output wire                             dmaHIFReadDataValid   ,// dma host interface read data valid
  input  wire [ 2:0]                      dmaHIFSize            ,// dma host interface byte enable
  output wire                             dmaHIFReady           ,// dma host interface next data
  input  wire [31:0]                      dmaHIFWriteDataIn     ,// dma host interface write data
  output wire                             dmaHIFTransComplete   ,// dma host interface transfer complete
  output wire                             dmaHIFError            // dma host interface error
);                                                          
                                                            

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
assign hMProt = 4'b0000;
assign hMBusReq = 1'b1;
assign hMLock   = 1'b0;

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
reg  [(`RW_REG_DATA_WIDTH-1):0]   ReadData;

wire [(`RW_REG_DATA_WIDTH-1):0]   mibHostIfRdData;
wire                              mibHostIfReady ;
wire                              mibHostDataValid ;

wire                              mibHostIfWr;
wire                              mibHostIfRd;

wire                              mibSelect;
wire                              WriteEnable;
wire                              ReadEnable;


wire [31:0]                       hMAddr_Pre;
wire [ 1:0]                       hMTrans_Pre;
wire                              hMWrite_Pre;
wire [ 2:0]                       hMSize_Pre;
wire [ 2:0]                       hMBurst_Pre;
wire [ 3:0]                       hMProt_Pre;
wire [31:0]                       hMWData_Pre;
wire [31:0]                       hMRData_Pre;
wire                              hMReady_Pre;
wire [ 1:0]                       hMResp_Pre;
	
//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

ahbSlaveIF U_ahbSlaveIF (
                .hClk                   (macPIClk),
                .hardRstHClk_n          (macPIClkHardRst_n),
                .hSelect                (hSSel),
                .hAddr                  (hSAddr),
                .hWrite                 (hSWrite),
                .hTrans                 (hSTrans),
                .hSize                  (hSSize[1:0]),
                .hWData                 (hSWData),
                .hReadyIn               (hSReadyIn),
                .hRData                 (hSRData),
                .hReady                 (hSReadyOut),
                .hResp                  (hSResp),
                .readDataIn             (ReadData),
                .readyIn                (regReadyIn),
                .mibReadyIn             (mibHostIfReady),
                .rdWrAddr               (regAddr),
                .writeDataOut           (regWriteData),
                .regWrite               (WriteEnable),
                .regRead                (ReadEnable)
                );

`ifdef RW_AHB_DELAY
// Instanciation of ahbMasterDelay
// Name of the instance : U_ahbMasterDelay
// Name of the file containing this module : ahbMasterDelay.v
ahbMasterDelay U_ahbMasterDelay (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .hMAddr_Del             (hMAddr[31:0]),
                .hMTrans_Del            (hMTrans[1:0]),
                .hMSize_Del             (hMSize[2:0]),
                .hMWrite_Del            (hMWrite),
                .hMBurst_Del            (hMBurst[2:0]),
                .hMWData_Del            (hMWData[31:0]),
                .hMReady_Del            (hMReady),
                .hMResp_Del             (hMResp[1:0]),
                .hMRData_Del            (hMRData[31:0]),
                .hMAddr                 (hMAddr_Pre[31:0]),
                .hMTrans                (hMTrans_Pre[1:0]),
                .hMSize                 (hMSize_Pre[2:0]),
                .hMWrite                (hMWrite_Pre),
                .hMBurst                (hMBurst_Pre[2:0]),
                .hMWData                (hMWData_Pre[31:0]),
                .hMReady                (hMReady_Pre),
                .hMResp                 (hMResp_Pre[1:0]),
                .hMRData                (hMRData_Pre[31:0]));
`endif // RW_AHB_DELAY


// Instanciation of ahbMasterIF
// Name of the instance : U_ahbMasterIF
// Name of the file containing this module : ahbMasterIF.v
ahbMasterIF U_ahbMasterIF (
		.macPIClk               (macPIClk),
		.macPIClkHardRst_n      (macPIClkHardRst_n),
		.dmaHIFAddressIn        (dmaHIFAddressIn),
		.dmaHIFRead             (dmaHIFRead),
		.dmaHIFWrite            (dmaHIFWrite),
		.dmaHIFSize             (dmaHIFSize),
		.dmaHIFWriteDataIn      (dmaHIFWriteDataIn),
		.dmaHIFError            (dmaHIFError),
		.dmaHIFReadDataOut      (dmaHIFReadDataOut),
		.dmaHIFReadDataValid    (dmaHIFReadDataValid),
		.dmaHIFReady            (dmaHIFReady),
		.dmaHIFTransComplete    (dmaHIFTransComplete),
`ifdef RW_AHB_DELAY
		.hMAddr                 (hMAddr_Pre),
		.hMTrans                (hMTrans_Pre),
		.hMSize                 (hMSize_Pre),
		.hMWrite                (hMWrite_Pre),
		.hMBurst                (hMBurst_Pre),
		.hMWData                (hMWData_Pre),
		.hMReady                (hMReady_Pre),
		.hMResp                 (hMResp_Pre),
		.hMRData                (hMRData_Pre)
`else
    .hMAddr                 (hMAddr),
    .hMTrans                (hMTrans),
    .hMSize                 (hMSize),
    .hMWrite                (hMWrite),
    .hMBurst                (hMBurst),
    .hMWData                (hMWData),
    .hMReady                (hMReady),
    .hMResp                 (hMResp),
    .hMRData                (hMRData)
`endif // RW_AHB_DELAY

		);

`ifdef RW_MAC_MIBCNTL_EN
// Instanciation of mibResync
// Name of the instance : U_mibResync
// Name of the file containing this module : mibResync.v
mibResync U_mibResync (
		.macPIClkHardRst_n      (macPIClkHardRst_n),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClk             (macCoreClk),
		.macPIClk               (macPIClk),
		.mibHostIfRdData        (mibHostIfRdData),
		.mibHostIfReady         (mibHostIfReady),
		.mibHostDataValid       (mibHostDataValid),
		.mibHostIfAddr          (regAddr),
		.mibHostIfWrData        (regWriteData),
		.mibHostIfWr            (mibHostIfWr),
		.mibHostIfRd            (mibHostIfRd),
		.mibRdData              (mibRdData),
		.mibBusy                (mibBusy),
		.mibAddr                (mibAddr),
		.mibWrData              (mibWrData),
		.mibWr                  (mibWr),
		.mibRd                  (mibRd)
		);
`endif // RW_MAC_MIBCNTL_EN


// address decoding range 0x600 to 0x9fC
assign mibSelect = (regAddr[9] == 1'b1) ? 1'b1 : 1'b0;

// mib controls
assign mibHostIfWr  = ((mibSelect == 1'b1) && (WriteEnable == 1'b1)) ? 1'b1   : 1'b0; 
assign mibHostIfRd  = ((mibSelect == 1'b1) && (ReadEnable  == 1'b1)) ? 1'b1   : 1'b0; 
// reg controls
assign regWrite  = ((mibSelect == 1'b0) && (WriteEnable == 1'b1)) ? 1'b1   : 1'b0;
assign regRead   = ((mibSelect == 1'b0) && (ReadEnable  == 1'b1)) ? 1'b1   : 1'b0;


// input multiplexing
always @*
begin
  if ( mibHostDataValid == 1'b1)
     ReadData = mibHostIfRdData;
  else
     ReadData = regReadData;
end


endmodule
                 

