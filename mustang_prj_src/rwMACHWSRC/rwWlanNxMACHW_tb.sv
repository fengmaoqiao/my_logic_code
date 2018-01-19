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
// Description      : Top level testbench of rwWlanNxMACHW.v module
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
`timescale  100ps/1ps

import filePkg::*;

module rwWlanNxMACHW_tb (); 

// *** Input, Inouts to UUT ***
reg  macPIClkHardRst_n;
reg  macCoreClkHardRst_n;
reg  macWTClkHardRst_n;
reg  mpIFClkHardRst_n;
//wire macPIClk;
//wire macPISlaveClk;
//wire macPITxClk;
//wire macPIRxClk;
//wire macCoreClk;
//wire macCoreTxClk;
//wire macCoreRxClk;
//wire macLPClk;
wire macWTClk;
wire mpIFClk;

reg  macPIClkInt;
reg  macCoreClkInt;
reg  macLPClkInt;
reg  macWTClkInt;
reg  mpIFClkInt;

reg  debugKSR;
wire  [31:0] hSAddr;
wire  [ 1:0] hSTrans;
wire  hSWrite;
wire  [ 2:0] hSSize;
reg   [ 2:0] hSBurst;
reg   [ 3:0] hSProt;
wire  [31:0] hSWData;
wire  [ 1:0] hSSel;
reg  hSReadyIn;
reg  hMGrant;
wire  [31:0] hMRData;
wire  hMReady;
wire  [ 1:0] hMResp;
wire  phyRdy;
wire  txEnd_p;
wire  [ 7:0] rxData;
wire  CCAPrimary20;
wire  CCASecondary20;
wire  CCASecondary40;
wire  CCASecondary80;
wire  rxEndForTiming_p;
wire  rxErr_p;
wire  rxEnd_p;
wire  phyErr_p;
wire  rifsRxDetected;
wire  [37:0] txFIFOReadData;
wire  [35:0] rxFIFOReadData;
`ifdef RW_WAPI_EN
wire  [314:0]  keyStorageReadData;
`else
wire  [186:0]  keyStorageReadData;
`endif // RW_WAPI_EN
wire  [ 7:0] sBoxAReadData;
wire  [ 7:0] sBoxBReadData;
wire  [ 7:0] mpIFTxFIFOReadData;
wire  [ 7:0] mpIFRxFIFOReadData;
wire  [ 7:0] encrRxFIFOReadData;
wire  [87:0] psBitmapReadData;
wire [31:0] mibTableReadData;

// *** Outputs from UUT ***
wire  macPriClkEn;
wire  platformWakeUp;
wire  macPITxClkEn;
wire  macPIRxClkEn;
wire  macCoreTxClkEn;
wire  macCoreRxClkEn;
wire  macCryptClkEn;
wire  macLPClkSwitch;
wire  macWTClkEn;
wire  mpIFClkEn;
wire  intGen_n;
wire  intTxRx_n;
wire  intProtTrigger_n;
wire  intTxTrigger_n;
wire  intRxTrigger_n;
wire  intTxRxMisc_n;
wire  intTxRxTimer_n;

wire  internalError;
wire  [31:0] debugPort;
wire  [31:0] hSRData;
wire  hSReadyOut;
wire  [ 1:0] hSResp;
wire  hMBusReq;
wire  hMLock;
wire  [31:0] hMAddr;
wire  [ 1:0] hMTrans;
wire  hMWrite;
wire  [ 2:0] hMSize;
wire  [ 2:0] hMBurst;
wire  [ 3:0] hMProt;
wire  [31:0] hMWData;
wire [15:0] hSplit;

wire  txReq;
wire  rxReq;
wire  [ 7:0] txData;
wire  macDataValid;
wire  mimoCmdValid;
wire  keepRFOn;
wire  txFIFOReadEn;
wire  [`TXFIFOADDRWIDTH-1:0] txFIFOReadAddr;
wire  txFIFOWriteEn;
wire  [`TXFIFOADDRWIDTH-1:0] txFIFOWriteAddr;
wire  [37:0] txFIFOWriteData;
wire  rxFIFOReadEn;
wire  [`RXFIFOADDRWIDTH-1:0] rxFIFOReadAddr;
wire  rxFIFOWriteEn;
wire  [`RXFIFOADDRWIDTH-1:0] rxFIFOWriteAddr;
wire  [35:0] rxFIFOWriteData;
wire  keyStorageEn;
wire  keyStorageWriteEn;
wire  [  5:0]  keyStorageAddr;
`ifdef RW_WAPI_EN
wire  [314:0]  keyStorageWriteData;
`else
wire  [186:0]  keyStorageWriteData;
`endif // RW_WAPI_EN
wire  sBoxAEn;
wire  sBoxAWriteEn;
wire  [ 7:0] sBoxAAddr;
wire  [ 7:0] sBoxAWriteData;
wire  sBoxBEn;
wire  sBoxBWriteEn;
wire  [ 7:0] sBoxBAddr;
wire  [ 7:0] sBoxBWriteData;
wire  mpIFTxFIFOReadEn;
wire  [`MPIFTXADDRWIDTH-1:0] mpIFTxFIFOReadAddr;
wire  mpIFTxFIFOWriteEn;
wire  [`MPIFTXADDRWIDTH-1:0] mpIFTxFIFOWriteAddr;
wire  [ 7:0] mpIFTxFIFOWriteData;
wire  mpIFRxFIFOReadEn;
wire  [`MPIFRXADDRWIDTH-1:0] mpIFRxFIFOReadAddr;
wire  mpIFRxFIFOWriteEn;
wire  [`MPIFRXADDRWIDTH-1:0] mpIFRxFIFOWriteAddr;
wire  [ 7:0] mpIFRxFIFOWriteData;
wire  encrRxFIFOReadEn;
wire  [ 6:0] encrRxFIFOReadAddr;
wire  encrRxFIFOWriteEn;
wire  [ 6:0] encrRxFIFOWriteAddr;
wire  [ 7:0] encrRxFIFOWriteData;
wire  psBitmapEn;
wire  psBitmapWriteEn;
wire  [ 1:0] psBitmapAddr;
wire  [87:0] psBitmapWriteData;
wire  mibTableEn;
wire  mibTableWriteEn;
wire  [ 7:0] mibTableAddr;
wire  [31:0] mibTableWriteData;

// Coex Interface
`ifdef RW_WLAN_COEX_EN
wire                            coexWlanTx;            // Indicates that a WLAN Transmission is on-going
wire                            coexWlanRx;            // Indicates that a WLAN Reception is on-going
reg                             coexWlanTxAbort;       // Requests from external arbiter abort all on-going transmission 
wire [3:0]                      coexWlanPTI;           // Indicates the priority of the on-going traffic
wire                            coexWlanPTIToggle;     // Indicates the priority of the on-going traffic
wire                            coexWlanChanBw;        // Indicates the BW of the on-going traffic
wire [6:0]                      coexWlanChanFreq;      // Indicates the Center frequency of the on-going traffic
wire                            coexWlanChanOffset;    // Indicates the Center frequency of the on-going traffic
`endif // RW_WLAN_COEX_EN

// *** Local Variable Declarations ***
// Local Parameter Declarations:
// N/A
// Local Wire Declarations:
// N/A
// Local Register Declarations:

wire  sync_req;
wire  sync_ack;
wire  hit_error;
wire  done;
wire  ahbMemDone;
wire  ahbMasterDone;

// Intruction parser
integer         status;
reg [15:0]      tmp_cmd;
reg [15:0]      tmp_cmd2;
reg             caracter;



reg          phyabort;

// TEMPORARY STUFF
integer fileHandle1;
integer fileHandle2;
integer rxHandle1;
// Beacon 
reg [31:0] bcnQueueHeadPtr;
reg txNewHeadBcn;
reg rstNewHeadBcn;
reg trigTxBcn;
reg checkError;
reg mpduSuccess_p;
reg manualFlush;

// interrupt vector
wire[31:0] interruptVector;

reg        tbForceMacClkEn;

// *** Local Integer Declarations ***
integer      j,i;
integer      results_file;  // for writing signal values
integer      errorCount = 0;
integer      waitcycle;
integer      watchdog       = 0;
integer      timeout        = 4000000; // timeout*mpIFCl_period in ns ~ 6 ms

reg [1:0] wtclk_cnt;
real      wtclk_halfperiod;
integer previoustime;
integer mpIFClkResyncIssue = 0;

wire                  macPIClk; // Primary MAC Platform Interafce clock.
wire                  macPIRxClk; // Secondary MAC Platform Interafce 1 clock	
wire                  macPITxClk; // Secondary MAC Platform Interafce 2 clock
wire                  macCoreClk; // Primary MAC Core clock 
wire                  macCoreRxClk; // Secondary MAC Core 1 clock 
wire                  macCoreTxClk; // Secondary MAC Core 2 clock 
wire                  macCryptClk; // Secondary MAC Core 2 clock 
wire                  macLPClk; // MAC Low power clock.
reg                   wtClk;// WEP/TKIP clock	
reg                   ref1MhzClk;
wire                  macPISlaveClk;
reg                   lpClk;




string comment1;
string comment2;
string comment3;
string comment4;
string comment5;
string comment6;
string comment7;
string comment8;
string comment9;
string comment10;
string comment11;
string comment12;
string comment13;
string comment14;
string comment15;
string comment16;
string comment17;

assign done = ahbMemDone && ahbMasterDone;

assign interruptVector = {24'b0,!platformWakeUp,intTxRxTimer_n,intTxRxMisc_n,intRxTrigger_n,intTxTrigger_n,intProtTrigger_n,intTxRx_n,intGen_n};

assign intTxRx_n = intTxRxTimer_n && intTxRxMisc_n && intRxTrigger_n && intTxTrigger_n && intProtTrigger_n;


 

// Instantiate the UUT module:
rwWlanNxMACHW  uut  (
      .macPIClkHardRst_n (macPIClkHardRst_n),
      .macCoreClkHardRst_n (macCoreClkHardRst_n),
      .macWTClkHardRst_n (macWTClkHardRst_n),
      .mpIFClkHardRst_n (mpIFClkHardRst_n),
      .macPIClk (macPIClk),
      .macPITxClk (macPITxClk),
      .macPIRxClk (macPIRxClk),
      .macPISlaveClk (macPISlaveClk),
      .macCoreClk (macCoreClk),
      .macCoreTxClk (macCoreTxClk),
      .macCoreRxClk (macCoreRxClk),
      .macCryptClk (macCryptClk),
      .macLPClk (macLPClk),
      .macWTClk (macWTClk),
      .mpIFClk (mpIFClk),
      .macPriClkEn (macPriClkEn),
      .platformWakeUp (platformWakeUp),
      .macPITxClkEn (macPITxClkEn),
      .macPIRxClkEn (macPIRxClkEn),
      .macCoreTxClkEn (macCoreTxClkEn),
      .macCoreRxClkEn (macCoreRxClkEn),
      .macCryptClkEn (macCryptClkEn),
      .macLPClkSwitch (macLPClkSwitch),
      .macWTClkEn (macWTClkEn),
      .mpIFClkEn (mpIFClkEn),
      .intGen_n (intGen_n),
      .intProtTrigger_n (intProtTrigger_n),
      .intTxTrigger_n (intTxTrigger_n),
      .intRxTrigger_n (intRxTrigger_n),
      .intTxRxMisc_n (intTxRxMisc_n),
      .intTxRxTimer_n (intTxRxTimer_n),
      .internalError (internalError),
      .debugPort (debugPort),
      .debugKSR (debugKSR),
      .hSAddr (hSAddr[`RW_AHB_ADDR_WIDTH-1:0]),
      .hSTrans (hSTrans),
      .hSWrite (hSWrite),
      .hSSize (hSSize),
      .hSBurst (hSBurst),
      .hSProt (hSProt),
      .hSWData (hSWData),
      .hSSel (hSSel[0]),
      .hSReadyIn (hSReadyIn),
      .hSRData (hSRData),
      .hSReadyOut (hSReadyOut),
      .hSResp (hSResp),
      .hMBusReq (hMBusReq),
      .hMLock (hMLock),
      .hMGrant (hMGrant),
      .hMAddr (hMAddr),
      .hMTrans (hMTrans),
      .hMWrite (hMWrite),
      .hMSize (hMSize),
      .hMBurst (hMBurst),
      .hMProt (hMProt),
      .hMWData (hMWData),
      .hMRData (hMRData),
      .hMReady (hMReady),
      .hMResp (hMResp),
      .phyRdy (phyRdy),
      .txEnd_p (txEnd_p),
      .rxData (rxData),
      .CCAPrimary20   (CCAPrimary20),
      .CCASecondary20 (CCASecondary20),
      .CCASecondary40 (CCASecondary40),
      .CCASecondary80 (CCASecondary80),
      .rxEndForTiming_p (rxEndForTiming_p),
      .rxErr_p (rxErr_p),
      .rxEnd_p (rxEnd_p),
      .phyErr_p (phyErr_p),
      .rifsRxDetected (rifsRxDetected),
      .txReq (txReq),
      .rxReq (rxReq),
      .txData (txData),
      .macDataValid (macDataValid),
      .mimoCmdValid (mimoCmdValid),
      .keepRFOn (keepRFOn),
  `ifdef RW_WLAN_COEX_EN
      .coexWlanTx (coexWlanTx),
      .coexWlanRx (coexWlanRx),
      .coexWlanTxAbort (coexWlanTxAbort),
      .coexWlanPTI (coexWlanPTI),
      .coexWlanPTIToggle (coexWlanPTIToggle),
      .coexWlanChanBw (coexWlanChanBw),
      .coexWlanChanFreq (coexWlanChanFreq),
      .coexWlanChanOffset (coexWlanChanOffset),
  `endif // RW_WLAN_COEX_EN
      .txFIFOReadEn (txFIFOReadEn),
      .txFIFOReadAddr (txFIFOReadAddr),
      .txFIFOReadData (txFIFOReadData),
      .txFIFOWriteEn (txFIFOWriteEn),
      .txFIFOWriteAddr (txFIFOWriteAddr),
      .txFIFOWriteData (txFIFOWriteData),
      .rxFIFOReadEn (rxFIFOReadEn),
      .rxFIFOReadAddr (rxFIFOReadAddr),
      .rxFIFOReadData (rxFIFOReadData),
      .rxFIFOWriteEn (rxFIFOWriteEn),
      .rxFIFOWriteAddr (rxFIFOWriteAddr),
      .rxFIFOWriteData (rxFIFOWriteData),
      .keyStorageEn (keyStorageEn),
      .keyStorageWriteEn (keyStorageWriteEn),
      .keyStorageAddr (keyStorageAddr),
      .keyStorageReadData (keyStorageReadData),
      .keyStorageWriteData (keyStorageWriteData),
      .sBoxAEn (sBoxAEn),
      .sBoxAWriteEn (sBoxAWriteEn),
      .sBoxAAddr (sBoxAAddr),
      .sBoxAReadData (sBoxAReadData),
      .sBoxAWriteData (sBoxAWriteData),
      .sBoxBEn (sBoxBEn),
      .sBoxBWriteEn (sBoxBWriteEn),
      .sBoxBAddr (sBoxBAddr),
      .sBoxBReadData (sBoxBReadData),
      .sBoxBWriteData (sBoxBWriteData),
      .mpIFTxFIFOReadEn (mpIFTxFIFOReadEn),
      .mpIFTxFIFOReadAddr (mpIFTxFIFOReadAddr),
      .mpIFTxFIFOReadData (mpIFTxFIFOReadData),
      .mpIFTxFIFOWriteEn (mpIFTxFIFOWriteEn),
      .mpIFTxFIFOWriteAddr (mpIFTxFIFOWriteAddr),
      .mpIFTxFIFOWriteData (mpIFTxFIFOWriteData),
      .mpIFRxFIFOReadEn (mpIFRxFIFOReadEn),
      .mpIFRxFIFOReadAddr (mpIFRxFIFOReadAddr),
      .mpIFRxFIFOReadData (mpIFRxFIFOReadData),
      .mpIFRxFIFOWriteEn (mpIFRxFIFOWriteEn),
      .mpIFRxFIFOWriteAddr (mpIFRxFIFOWriteAddr),
      .mpIFRxFIFOWriteData (mpIFRxFIFOWriteData),
      .encrRxFIFOReadEn (encrRxFIFOReadEn),
      .encrRxFIFOReadAddr (encrRxFIFOReadAddr),
      .encrRxFIFOReadData (encrRxFIFOReadData),
      .encrRxFIFOWriteEn (encrRxFIFOWriteEn),
      .encrRxFIFOWriteAddr (encrRxFIFOWriteAddr),
      .encrRxFIFOWriteData (encrRxFIFOWriteData),
`ifdef RW_MAC_MIBCNTL_EN
      .mibTableEn (mibTableEn),
      .mibTableWriteEn (mibTableWriteEn),
      .mibTableAddr (mibTableAddr),
      .mibTableReadData (mibTableReadData),
      .mibTableWriteData (mibTableWriteData),
`endif // RW_MAC_MIBCNTL_EN
      .psBitmapEn (psBitmapEn),
      .psBitmapWriteEn (psBitmapWriteEn),
      .psBitmapAddr (psBitmapAddr),
      .psBitmapReadData (psBitmapReadData),
      .psBitmapWriteData (psBitmapWriteData)
      );


// Modules instanciation
ahbMaster U_ahbMaster (
                .clk (macPISlaveClk),
                .rst_n (macPIClkHardRst_n),
                .interrupt (interruptVector),
                .hready (hSReadyOut),
                .hsel (hSSel),
                .haddr (hSAddr),
                .htrans (hSTrans),
                .hwrite (hSWrite),
                .hsize (hSSize),
                .hrdata (hSRData),
                .hwdata (hSWData),
                .hresp (hSResp),
                .sync_req (sync_req),
                .sync_ack (sync_ack),
                .hit_error (hit_error),
                .enable(1'b1),
                .ahbMasterDone (ahbMasterDone)
                );

integer mpIFtxFifoWriteCnt;
always @(posedge macCoreTxClk, negedge txReq)
begin
  if(!txReq)
    mpIFtxFifoWriteCnt = 0;
  else if(mpIFTxFIFOWriteEn)
    mpIFtxFifoWriteCnt = mpIFtxFifoWriteCnt + 1;
end

integer mpIFtxFifoReadCnt;
always @(posedge mpIFClk, negedge txReq)
begin
  if(!txReq)
    mpIFtxFifoReadCnt  = 0;
  else if(mpIFTxFIFOReadEn)
    mpIFtxFifoReadCnt = mpIFtxFifoReadCnt + 1;
end


// Instanciation of tp_ram
// Name of the instance : U_mpIFTxFIFO
// Name of the file containing this module : tp_ram.v
tp_ram #(.ADDRWIDTH(`MPIFTXADDRWIDTH),.DATAWIDTH(8)) U_mpIFTxFIFO (
    .clka         (macCoreTxClk),
    .dina         (mpIFTxFIFOWriteData),
    .addra        (mpIFTxFIFOWriteAddr),
    .wea          (mpIFTxFIFOWriteEn),
    .clkb         (mpIFClk),
    .addrb        (mpIFTxFIFOReadAddr),
    .reb          (mpIFTxFIFOReadEn),
    .doutb        (mpIFTxFIFOReadData)
    );

// Instanciation of tp_ram
// Name of the instance : U_mpIFRxFIFO
// Name of the file containing this module : tp_ram.v
tp_ram #(.ADDRWIDTH(`MPIFRXADDRWIDTH),.DATAWIDTH(8)) U_mpIFRxFIFO (
    .clka         (mpIFClk),
    .dina         (mpIFRxFIFOWriteData),
    .addra        (mpIFRxFIFOWriteAddr),
    .wea          (mpIFRxFIFOWriteEn),
    .clkb         (macCoreRxClk),
    .addrb        (mpIFRxFIFOReadAddr),
    .reb          (mpIFRxFIFOReadEn),
    .doutb        (mpIFRxFIFOReadData)
    );

// Instanciation of tp_ram
// Name of the instance : U_TxFIFO
// Name of the file containing this module : tp_ram.v
tp_ram #(.ADDRWIDTH(`TXFIFOADDRWIDTH),.DATAWIDTH(38)) U_TxFIFO (
    .clka         (macPITxClk),
    .dina         (txFIFOWriteData),
    .addra        (txFIFOWriteAddr),
    .wea          (txFIFOWriteEn),
    .clkb         (macCoreTxClk),
    .addrb        (txFIFOReadAddr),
    .reb          (txFIFOReadEn),
    .doutb        (txFIFOReadData)
    );

// Instanciation of tp_ram
// Name of the instance : U_RxFIFO
// Name of the file containing this module : tp_ram.v
tp_ram #(.ADDRWIDTH(`RXFIFOADDRWIDTH),.DATAWIDTH(36)) U_RxFIFO (
    .clka         (macCoreRxClk),
    .dina         (rxFIFOWriteData),
    .addra        (rxFIFOWriteAddr),
    .wea          (rxFIFOWriteEn),
    .clkb         (macPIRxClk),
    .addrb        (rxFIFOReadAddr),
    .reb          (rxFIFOReadEn),
    .doutb        (rxFIFOReadData)
    );


`ifdef RW_MAC_MIBCNTL_EN
// Instanciation of sp_ram
// Name of the instance : U_mibRAM
// Name of the file containing this module : sp_ram.v
sp_ram #(.ADDRWIDTH(8),.DATAWIDTH(32)) U_mibRAM (
		.clk          (macCoreClk),
		.din          (mibTableWriteData),
		.addr         (mibTableAddr),
		.we           (mibTableWriteEn),
		.cs           (mibTableEn),
		.dout         (mibTableReadData)
		);
`endif // RW_MAC_MIBCNTL_EN

// Instanciation of sp_ram
// Name of the instance : U_psBitmapRAM
// Name of the file containing this module : sp_ram.v
sp_ram #(.ADDRWIDTH(2),.DATAWIDTH(88)) U_psBitmapRAM (
		.clk          (macCoreClk),
		.din          (psBitmapWriteData),
		.addr         (psBitmapAddr),
		.we           (psBitmapWriteEn),
		.cs           (psBitmapEn),
		.dout         (psBitmapReadData)
		);

// Instanciation of sp_ram
// Name of the instance : U_keyStorageRAM
// Name of the file containing this module : sp_ram.v
`ifdef RW_WAPI_EN
sp_ram #(.ADDRWIDTH(6),.DATAWIDTH(315)) U_keyStorageRAM (
    .clk          (macCoreClk),
    .din          (keyStorageWriteData),
    .addr         (keyStorageAddr),
    .we           (keyStorageWriteEn),
    .cs           (keyStorageEn),
    .dout         (keyStorageReadData)
    );
`else
sp_ram #(.ADDRWIDTH(6),.DATAWIDTH(187)) U_keyStorageRAM (
    .clk          (macCoreClk),
    .din          (keyStorageWriteData),
    .addr         (keyStorageAddr),
    .we           (keyStorageWriteEn),
    .cs           (keyStorageEn),
    .dout         (keyStorageReadData)
    );
`endif


// Instanciation of tp_ram
// Name of the instance : U_encrRxFIFO
// Name of the file containing this module : tp_ram.v
tp_ram #(.ADDRWIDTH(7),.DATAWIDTH(8)) U_encrRxFIFO (
    .clka         (macCoreRxClk),
    .dina         (encrRxFIFOWriteData),
    .addra        (encrRxFIFOWriteAddr),
    .wea          (encrRxFIFOWriteEn),
    .clkb         (macCoreRxClk),
    .addrb        (encrRxFIFOReadAddr),
    .reb          (encrRxFIFOReadEn),
    .doutb        (encrRxFIFOReadData)
		);

// Instanciation of dp_ram
// Name of the instance : U_dp_ram
// Name of the file containing this module : dp_ram.v
dp_ram #(.ADDRWIDTH(8),.DATAWIDTH(8)) U_sBox (
		.clka         (macWTClk),
		.addra        (sBoxAAddr),
		.ea           (sBoxAEn),
		.wea          (sBoxAWriteEn),
		.dina         (sBoxAWriteData),
		.douta        (sBoxAReadData),
		.clkb         (macWTClk),
		.addrb        (sBoxBAddr),
		.eb           (sBoxBEn),
		.web          (sBoxBWriteEn),
		.dinb         (sBoxBWriteData),
		.doutb        (sBoxBReadData)
		);

// Instanciation of phy_model
// Name of the instance : U_phy_model
// Name of the file containing this module : phy_model.v
phy_model U_phy_model (
    .mpIFClk                (mpIFClkInt),
    .mpIFClkHardRst_n       (mpIFClkHardRst_n),
    .txReq                  (txReq),
    .rxReq                  (rxReq),
    .txData                 (txData),
    .macDataValid           (macDataValid),
    .mimoCmdValid           (mimoCmdValid),
    .keepRFOn               (keepRFOn),
    .phyRdy                 (phyRdy),
    .txend_p                (txEnd_p),
    .rxData                 (rxData),
    .CCAPrimary20           (CCAPrimary20),
    .CCASecondary20         (CCASecondary20),
    .CCASecondary40         (CCASecondary40),
    .CCASecondary80         (CCASecondary80),
    .rxEndForTiming_p       (rxEndForTiming_p),
    .rxErr_p                (rxErr_p),
    .rxEnd_p                (rxEnd_p),
    .phyErr_p               (phyErr_p),
    .rifsRxDetected         (rifsRxDetected),
    .abort                  (phyabort)
    );


// Instanciation of ahbMem
// Name of the instance : U_ahbMem
// Name of the file containing this module : ahbMem.v
ahbMem U_ahbMem (
    .hClk         (macPIClk),
    .hReset_n     (macPIClkHardRst_n),
    .hSelect      (1'b1),
    .hAddr        (hMAddr),
    .hWrite       (hMWrite),
    .hTrans       (hMTrans),
    .hSize        (hMSize),
    .hBurst       (hMBurst),
    .hWData       (hMWData),
    .hReadyIn     (1'b1),
    .hMaster      (4'b0000),
    .hReady       (hMReady),
    .hResp        (hMResp),
    .hRData       (hMRData),
    .hSplit       (hSplit),
    .enable       (1'b1),
    .ahbMemDone   (ahbMemDone)
    );


///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
// CLOCKS GEENRATION
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////

`ifndef MACPI_CLK_FREQ
  `define MACPI_CLK_FREQ 100
`endif // MACPI_CLK_FREQ

`ifndef MACCORE_CLK_FREQ
  `define MACCORE_CLK_FREQ `MAC_FREQ
`endif // MACCORE_CLK_FREQ

`ifndef MPIF_CLK_FREQ
  `define MPIF_CLK_FREQ 30
`endif // MPIF_CLK_FREQ

`ifndef MACCORE_CLK_WT_CLK_MULT
  `define MACCORE_CLK_WT_CLK_MULT `WEP_2_BB_CLK_RATIO  
`endif // MACCORE_CLK_WT_CLK_MULT

`define LP_CLK_FREQ 32

`define MACPI_CLK_PERIOD      10000.0/$itor(`MACPI_CLK_FREQ)
`define MACPI_CLK_HALFPERIOD   5000.0/$itor(`MACPI_CLK_FREQ)
`define MACCORE_CLK_PERIOD    10000.0/$itor(`MACCORE_CLK_FREQ)
`define MACCORE_CLK_HALFPERIOD 5000.0/$itor(`MACCORE_CLK_FREQ)
`define MPIF_CLK_PERIOD       10000.0/$itor(`MPIF_CLK_FREQ)
`define MPIF_CLK_HALFPERIOD    5000.0/$itor(`MPIF_CLK_FREQ)
`define LP_CLK_HALFPERIOD   5000000.0/$itor(`LP_CLK_FREQ)

  always #(0500.00*10.0) ref1MhzClk = ~ref1MhzClk;

  initial
  begin
    wtclk_halfperiod = ((`MACCORE_CLK_PERIOD)/($itor(2*`MACCORE_CLK_WT_CLK_MULT)));
    forever
    begin
      @(`MACCORE_CLK_PERIOD/2);
      wtclk_halfperiod = ((`MACCORE_CLK_PERIOD)/($itor(2*`MACCORE_CLK_WT_CLK_MULT)));
    end
  end

  initial
  begin
    wtClk = 0;
    ref1MhzClk = 0;
  end

  // wtClk
  initial
  begin
    forever
    begin
      @(posedge ref1MhzClk);
      wtClk = ~wtClk;
      for(int i=0; i < $rtoi(10000.0/wtclk_halfperiod)-1; i=i+1)
      begin
        #wtclk_halfperiod wtClk = ~wtClk;
      end
    end
  end

  always @(negedge wtClk,negedge macWTClkHardRst_n)
  begin
    if(macWTClkHardRst_n == 1'b0)
    begin
      wtclk_cnt <= 2'b00;
    end
    else
    begin
      if(wtclk_cnt == `MACCORE_CLK_WT_CLK_MULT-1)
        wtclk_cnt <= 2'b00;
      else
        wtclk_cnt <= wtclk_cnt + 1;
    end
  end

  // macPIClk
  always #(`MACPI_CLK_HALFPERIOD) macPIClkInt = ~macPIClkInt;

  // mpIFClkInt 
  always #(`MPIF_CLK_HALFPERIOD) mpIFClkInt = ~mpIFClkInt;

  // lpClk
  always #(`LP_CLK_HALFPERIOD) lpClk = ~lpClk;

  initial
  begin
    mpIFClkInt = 0;
    lpClk      = 0;
  end

assign macCoreClk    = wtClk && (wtclk_cnt == 2'b00) && macPriClkEn;
assign macLPClk      = (macLPClkSwitch)? lpClk : wtClk && (wtclk_cnt == 2'b00);
assign macCoreTxClk  = wtClk && (wtclk_cnt == 2'b00) && macPriClkEn && macCoreTxClkEn;
assign macCoreRxClk  = wtClk && (wtclk_cnt == 2'b00) && macPriClkEn && macCoreRxClkEn;
assign macCryptClk   = wtClk && (wtclk_cnt == 2'b00) && macPriClkEn && macCryptClkEn;
assign macWTClk      = wtClk && macWTClkEn;

`ifdef ALL_CLK_ALIGNED
assign macPIClk      = wtClk && (wtclk_cnt == 2'b00) && macPriClkEn;
assign macPISlaveClk = wtClk && (wtclk_cnt == 2'b00);
assign macPITxClk    = wtClk && (wtclk_cnt == 2'b00) && macPriClkEn && macPITxClkEn;
assign macPIRxClk    = wtClk && (wtclk_cnt == 2'b00) && macPriClkEn && macPIRxClkEn;
assign mpIFClk       = wtClk && (wtclk_cnt == 2'b00) && macPriClkEn && mpIFClkEn;
`else
assign macPIClk      = macPIClkInt && macPriClkEn;
assign macPISlaveClk = macPIClkInt;
assign macPITxClk    = macPIClkInt && macPriClkEn && macPITxClkEn;
assign macPIRxClk    = macPIClkInt && macPriClkEn && macPIRxClkEn;
assign mpIFClk       = mpIFClkInt && macPriClkEn && mpIFClkEn;
`endif // ALL_CLK_ALIGNED


///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////


// initial block
initial
begin
  // initialize signals
  line_pos          <= 0;
  macPIClkHardRst_n <= 0;
  macCoreClkHardRst_n <= 0;
  macWTClkHardRst_n <= 0;
  mpIFClkHardRst_n <= 0;
  macPIClkInt <= 0;
  macCoreClkInt <= 0;
  macLPClkInt <= 0;
  mpIFClkInt <= 0;
  debugKSR <= 1;
  hMGrant <= 1;
  phyabort <= 0;
  tbForceMacClkEn <= 1;
  hSReadyIn <= 1;
  hSBurst <= 0;
  hSProt <= 0;
  
  `ifdef RW_WLAN_COEX_EN
  coexWlanTxAbort <= 0;
  `endif // RW_WLAN_COEX_EN
  
  filePkg::instructionLine = "";

  // wait 1 clk cycle, de-assert rst_n
  generateHardRst_n;

  @(posedge macPIClkInt);
  
  filePkg::input_file = $fopen("./inputAC.txt","rb");
  filePkg::rxHandle2  = $fopen("./rxmem.txt","wb");
  filePkg::txMemHandle  = $fopen("./txmem.txt","wb");
    
  while (!$feof(filePkg::input_file))
  begin
    watchdog = 0;
    tmp_cmd  = "##";
    status   = $fgets(filePkg::instructionLine,filePkg::input_file);
    //$display ("filePkg::instructionLine: %s", instructionLine);
    status   = $sscanf(filePkg::instructionLine," %c%c",tmp_cmd[15:8],tmp_cmd[7:0]);
    //$display("command = %s",tmp_cmd);
    //tmp_cmd = filePkg::instructionLine.substr(0,1);
    if (tmp_cmd == "WA")
    begin
      status   = $sscanf(filePkg::instructionLine," %c%c %c%c",tmp_cmd[15:8],tmp_cmd[7:0],tmp_cmd2[15:8],tmp_cmd2[7:0]);
      if (tmp_cmd2 == "TX")
      begin
        $display("TB: Wait for the end of the on-going transmission");
        while (!txEnd_p) @(posedge mpIFClkInt);
        $display("TB: End of Transmission\n");
      end 
      else if (tmp_cmd2 == "RX")
      begin
        while (!rxEnd_p) @(posedge mpIFClkInt);
        @(posedge mpIFClkInt); 
        @(posedge mpIFClkInt);        
        $display("TB: End of Reception\n");
      end 
      else 
      begin
        status   = $sscanf(filePkg::instructionLine," %c%c %d",tmp_cmd[15:8],tmp_cmd[7:0],waitcycle);
//        for (i = 0; i<waitcycle;i++) @(posedge macLPClk);
        //$display("TB: Wait for %0d",waitcycle);
        for (i = 0; i<(waitcycle*`MACCORE_CLK_FREQ/20);i++) @(posedge macLPClk);
        //#1;
      end  
    end 
    else if (tmp_cmd == "DI")
    begin
      status   = $sscanf(filePkg::instructionLine," %c%c %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s",tmp_cmd[15:8],tmp_cmd[7:0],comment1,comment2,comment3,comment4,comment5,comment6,comment7,comment8,comment9,comment10,comment11,comment12,comment13,comment14,comment15,comment16,comment17);
      $display("%s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s",comment1,comment2,comment3,comment4,comment5,comment6,comment7,comment8,comment9,comment10,comment11,comment12,comment13,comment14,comment15,comment16,comment17);
      comment1  = "";
      comment2  = "";
      comment3  = "";
      comment4  = "";
      comment5  = "";
      comment6  = "";
      comment7  = "";
      comment8  = "";
      comment9  = "";
      comment10 = "";
      comment11 = "";
      comment12 = "";
      comment13 = "";
      comment14 = "";
      comment15 = "";
      comment16 = "";
      comment17 = "";
    end 
    else if (tmp_cmd == "CK")
    begin
      status   = $sscanf(filePkg::instructionLine," %c%c %c%c",tmp_cmd[15:8],tmp_cmd[7:0],tmp_cmd2[15:8],tmp_cmd2[7:0]);
      if (tmp_cmd2 == "EN")
      begin
        $display("TB: Enable the macCoreClk");
        tbForceMacClkEn <= 1;

      end 
      else if (tmp_cmd2 == "DI")
      begin
        $display("TB: Disable the macCoreClk");
        tbForceMacClkEn <= 0;
      end 
      else 
      begin
        status   = $sscanf(filePkg::instructionLine," %c%c %d",tmp_cmd[15:8],tmp_cmd[7:0],waitcycle);
//        for (i = 0; i<waitcycle;i++) @(posedge macLPClk);
        for (i = 0; i<(waitcycle*`MACCORE_CLK_FREQ/20);i++) @(posedge macLPClk);
      end  
    end 
    else if (tmp_cmd == "PH")
    begin
      // Wait one mpIFClkInt clock cycle for correct sampling into phy_Model
      @(posedge mpIFClkInt); 
      @(posedge mpIFClkInt); 
    end 
    else if (tmp_cmd == "QT")
    begin
      $display("TB: Quit the simulation");


      if(errorCount || (U_ahbMaster.discrepency_count > 0) || (U_ahbMem.discrepency_count > 0)) 
      begin
        $display("");
        $display("Testbench errorCount = %0d",errorCount);
        $display("ahbMaster errorCount = %0d",U_ahbMaster.discrepency_count);
        $display("ahbMem    errorCount = %0d",U_ahbMem.discrepency_count);
        $display("");
        $display("Simulation FAILED");
      end
      else 
        $display("Simulation SUCCESSFUL");
      $display();
      $finish;
    end 
    line_pos = line_pos + 1;
    @(posedge macPIClkInt);
    while (!done) #1;
  end

  while(! done) @(posedge macPIClkInt);
  // $display();
  // $display();

  generateHardRst_n;

  if(errorCount || (U_ahbMaster.discrepency_count > 0) || (U_ahbMem.discrepency_count > 0)) 
  begin
    $display("");
    $display("Testbench errorCount = %0d",errorCount);
    $display("ahbMaster errorCount = %0d",U_ahbMaster.discrepency_count);
    $display("ahbMem    errorCount = %0d",U_ahbMem.discrepency_count);
    $display("");
    $display("Simulation FAILED");
  end
  else 
    $display("Simulation SUCCESSFUL");
  $display();
  $finish;
end


// Add more test bench stuff here as well

always @ (posedge uut.U_macCore.respTO_p)
begin
  $display("MAC: Response Time-Out");
end   

// Test Bench Tasks

// task generate Reset:
task generateHardRst_n;
begin
  macPIClkHardRst_n = 0;
  macCoreClkHardRst_n = 0;
  macWTClkHardRst_n = 0;
  mpIFClkHardRst_n = 0;
  @ (posedge macPIClkInt);
  @ (posedge macCoreClk);
  @ (posedge mpIFClkInt);
  @ (posedge macPIClkInt);
  @ (posedge macCoreClk);
  @ (posedge mpIFClkInt);
  @ (posedge macPIClkInt);
  @ (posedge macCoreClk);
  @ (posedge mpIFClkInt);
  macPIClkHardRst_n = 1;
  @ (posedge macCoreClk);
  macCoreClkHardRst_n = 1;
  macWTClkHardRst_n = 1;
  @ (posedge mpIFClkInt);
  mpIFClkHardRst_n = 1;
  @ (posedge macPIClkInt);
  @ (posedge macPIClkInt);
  @ (posedge macPIClkInt);
  @ (posedge macPIClkInt);
  @ (posedge macPIClkInt);
end
endtask


// Simulation watchdog
always @ (posedge mpIFClkInt)
begin
  watchdog = watchdog + 1;
  if ( watchdog === timeout)
  begin
    $display("Simulation TIMEOUT");
    $display("Simulation FAILED");
    $finish;
  end
  
  if(txReq && rxReq)
  begin
    for(int i=0; i<100; i=i+1)
    begin
      @ (posedge mpIFClkInt);
    end
    $display("Simulation txReq and rxReq is both high");
    $display("Simulation FAILED");
    $finish;
  end
end


endmodule
`timescale  1ns/1ps

