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
// Dependencies     : pulseSynchro, simpleSynchro, txRxFifoControl, RxStateCtl
//                    TxStateCtl                                                     
// Description      : Top level of macPhyIf module
//                    
// Simulation Notes : Simulated with ncsim
//    For simulation, two defines are available
//
//    RW_SIMU_ON   : which creates string signals to display the FSM states on  
//                   the waveform viewers
//
//    RW_ASSERT_ON : which enables System Verilog Assertions.
//
// Synthesis Notes  : 
//    all the inpout/output are synchronous the block clock 
//    the are interfaced to. I.E interface with RxController
//    is synchronous with macCoreRxClk, Tx controller 
//    macCoreTxClk and so on. The main clock of the block is
//    mpIFClk. 
//    All the reysnchroniztions flop are called <name>_resync
// Application Note :                                                       
// Simulator        :                                                       
//    For simulation with RW_ASSERT_ON, the simulator must support System 
//    Verilog Assertions
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
module macPhyIf( 
         //$port_g clock and Reset                                                                
         input  wire                           mpIFClk,                   // PHY clock                     
         input  wire                           mpIFClkHardRst_n,          // PHY clock reset               
         input  wire                           mpIFClkSoftRst_n,          // PHY clock soft reset
         input  wire                           macCoreRxClk,              // mac core Rx clock             
         input  wire                           macCoreTxClk,              // mac core Tx clock             
         input  wire                           macCoreClkHardRst_n,       // mac core Tx clock reset       
         input  wire                           macCoreClkSoftRst_n,       // mac core Tx clock reset       
         
         //$port_g Phy If                                                                                  
         input  wire                           phyRdy,                    // data valid signal             
         input  wire                           txEnd_p,                   // end of transaction            
         input  wire [ 7:0]                    rxData,                    // rx data                 
         input  wire                           CCAPrimary20,              // CCA on Primary 20MHz channel                       
         input  wire                           CCASecondary20,            // CCA on Secondary 20MHz channel                       
         input  wire                           CCASecondary40,            // CCA on Secondary 40MHz channel                       
  	     input  wire                           CCASecondary80,            // CCA on Secondary 80MHz channel                       
         input  wire                           rxEndForTiming_p,          // end of transmission (antenna) 
         input  wire                           rxErr_p,                   // Rx error                      
         input  wire                           rxEnd_p,                   // Rx end                        
         input  wire                           phyErr_p,                  // phy error                     
         input  wire                           rifsRxDetected,            // rifs detected                 
         //                                                                                                
         output wire                           txReq,                     // Tx request                    
         output wire                           rxReq,                     // Rx request                    
         output wire [ 7:0]                    txData,                    // Tx data                       
         output wire                           macDataValid,              // data valid                    
         output wire                           mimoCmdValid,              // mimo command                  
         output wire                           keepRFOn,                  // Keep RF on                    
                                                                                        
         //$port_g Mac Controller If                                                            
         input  wire                           startRx,                   // Start Rx trigger
         input  wire                           stopRx_p,                  // Stop Rx trigger 
         input  wire                           mpifKeepRFon,              // Keep RF On
         output wire                           macPhyIfRxStart_p,         // Start of reception pulse
         output wire                           macPhyIfRxFlush_p,         // Rx flush pulse
                                                                                        
         //$port_g Tx  Controller If                                                           
         input  wire                           startTx_p,                 // Start Tx trigger          
         input  wire                           stopTx_p,                  // Stop Tx trigger           
         input  wire [ 7:0]                    mpIfTxFifoData,            // Data to transmit          
         input  wire                           mpIfTxFifoWrite,           // Data valid                

         input  wire [ 7:0]                    txPwrLevel,                // Transmit Power Level             
         input  wire [ 1:0]                    chBW,                      // TX Vector Channel Bandwidth             
         input  wire [ 1:0]                    chOffset,                  // TX Vector transmit vector field              
         input  wire                           smoothing,                 // TX Vector Smoothing recommended            
         input  wire [ 7:0]                    antennaSet,                // TX Vector Antenna Set           
         input  wire [ 7:0]                    smmIndex,                  // TX Vector Spatial Map Matrix Index           
         input  wire [ 6:0]                    mcs,                       // TX Vector Modulation Coding Scheme           
         input  wire                           preType,                   // TX Vector Preamble Type         
         input  wire [ 2:0]                    formatMod,                 // TX Vector Format and Modulation           
         input  wire [ 1:0]                    numExtnSS,                 // TX Vector Number of Extension Spatial Streams              
         input  wire [ 1:0]                    stbc,                      // TX Vector Space Time Block Coding           
         input  wire                           fecCoding,                 // TX Vector FEC Coding             
         input  wire                           sounding,                  // TX Vector Indicates whether this PPDU is Sounding        
         input  wire [11:0]                    legLength,                 // TX Vector Legacy Length of the PPDU            
         input  wire [ 3:0]                    legRate,                   // TX Vector Legacy Rate of the PPDU               
         input  wire [15:0]                    service,                   // TX Vector Service              
         input  wire [19:0]                    htLength,                  // TX Vector Length of the HT and VHT PPDU              
         input  wire [ 2:0]                    nTx,                       // TX Vector Number of Transmit Chains.      
         input  wire [ 2:0]                    nSTS,                      // TX Vector Indicates the number of space-time streams.
         input  wire                           shortGI,                   // TX Vector Short Guard Interval              
         input  wire                           aggreation,                // TX Vector MPDU Aggregate
         input  wire                           beamFormed,                // TX Vector BeamFormed
         input  wire                           disambiguityBit,           // TX Vector Disambiguity
         input  wire [8:0]                     partialAID,                // TX Vector partial AID
         input  wire [5:0]                     groupID,                   // TX Vector group ID
         input  wire                           dozeNotAllowed,            // TX Vector TXOP PS Not Allowed
         input  wire                           continuousTx,              // TX Vector continuous transmit 
         //                                                                                            
         output wire                           mpIfTxFifoFull,            // FIFO status               
         output wire                           mpIfTxErr_p,               // Transmit error            
         output reg                            mpIfTxEn,                  // Transmit Enable           

         //$port_g Encryption Engine
         output wire                           macPhyTxEnd_p,             // Pulse tx end resync on MacCoreCLk

         //$port_g Rx Controller                                                               
         input  wire                           macPhyIfRxFifoReadEn,      // FIFO read enable from the Rx controller                 
         //                                                                                            
         output wire                           macPhyIfRxFifoEmpty,       // FIFO empty signal                       
         output wire [ 7:0]                    macPhyIfRxFifoData,        // FIFO data                               
         output wire                           macPhyIfRxErr_p,           // abort pulse                             
         output wire                           macPhyIfRxEnd_p,           // end of reception pulse                   
         output wire                           macPhyIfRxEndForTiming_p,  // end of reception at the antenna                  
         output wire                           macPhyIfRifsRxDetected,    // RIFS detected indication                
         output wire                           macPhyIfRxCca,             // CCA trigger                    
         output wire                           macPhyIfRxCcaSec20,        // CCA trigger Lower                  
         output wire                           macPhyIfRxCcaSec40,        // CCA trigger Lower                  
         output wire                           macPhyIfRxCcaSec80,        // CCA trigger Lower                  

         //$port_g Registers
         input  wire                           macPHYIFFIFOReset,         // Flush the FIFO
         input  wire                           rateControllerMPIF,        // Select reverse handshaking or PHy strobe tranmit mechanism
                                                                          // 0 reverse handshaking
                                                                          // 1 phy strobe
         input  wire                           rxReqForceDeassertion,     // Force deassertion of rxReq after each rxEnd_p
         //
         output wire                           macPHYIFFIFOResetInValid,  // Clear of FIFO Flush

         //$port_g Interrupt controller
         output wire                           macPHYIFUnderRun,          // underrun status
         output wire                           macPHYIFOverflow,          // overflow status
                                                                                                 
         //$port_g Tx FIFO                                                                     
         input  wire [ 7:0]                    mpIFTxFIFOReadData,        // data from TP RAM                                     
         //                                                                             
         output wire [ 7:0]                    mpIFTxFIFOWriteData,       // data to TP RAM                                         
         output wire [ (`MPIFTXADDRWIDTH-1):0] mpIFTxFIFOWriteAddr,       // write address to TP RAM                                       
         output wire                           mpIFTxFIFOWriteEn,         // write enable to TP RAM                                        
         output wire [ (`MPIFTXADDRWIDTH-1):0] mpIFTxFIFOReadAddr,        // read address                                      
         output wire                           mpIFTxFIFOReadEn,          // MAC-PHY Interface Transmit FIFO Read Enable. 
          
         //$port_g Rx FIFO                                                                     
         input  wire [ 7:0]                    mpIFRxFIFOReadData,        // data from TP RAM                                                
         //                                                                                                        
         output reg  [ 7:0]                    mpIFRxFIFOWriteData,       // data to TP RAM                                                 
         output reg  [ (`MPIFRXADDRWIDTH-1):0] mpIFRxFIFOWriteAddr,       // write address to TP RAM                                        
         output reg                            mpIFRxFIFOWriteEn,         // write enable to TP RAM                                         
         output wire [ (`MPIFRXADDRWIDTH-1):0] mpIFRxFIFOReadAddr,        // read address                                                   
         output wire                           mpIFRxFIFOReadEn,          // MAC-PHY Interface Receive FIFO Read Enable. 

         //$port_g Debug ports
         output wire [15:0]                    debugPortMACPhyIf,         // Debug port for validation
         output wire [15:0]                    debugPortMACPhyIf2         // Debug port for validation

);

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
// Rx controller
wire       mpifOverflow;           // overflow
wire       startRx_mpIFClk;        // resynchornized start Rx
wire       stopRx_mpIFClk_p;       // resynchornized stop Rx
//wire       rxFifoWrClkFlush;       // macCore clock Tx fifo flush
wire       rxFifoRdClkFlush;       // mpif    clock Tx fifo flush

// Tx controller
wire       mpifUnderRun;           // underrun
wire       startTx_mpIFClk_p;      // resynchornized start Tx
wire       stopTx_mpIFClk_p;       // resynchornized stop Tx
wire       txFifoRdClkFlush;       // Flush txFifo, mpficlk synchronized
//wire       txFifoWrClkFlush;       // Flush txFifo, macCoreClk synchronized

// Rx fifo
wire       fifoWriteEn;            // Rx fifo Write Enable
wire       mpIfRxFifoFull;         // Rx fifo full
wire       mpifRxRdFifoflush;      // Rx fifo read clock flush
wire       fifoRxPtrsNull;         // active when both write and read RX pointers are null

// Tx fifo
wire       mpIfTxFifoEmtpy;        // Tx fifo empty
wire       mpifTxRdFifoflush;      // mpif    clock Tx fifo flush
wire       mpIfFifoReadEn;         // fifo read enable
wire       fifoTxPtrsNull;         // active when both write and read TX pointers are null
reg        fifoTxPtrsNull_ff1;     // FF for fifoTxPtrsNull before resync
wire       fifoTxPtrsNullSync;     // fifoTxPtrsNull resync on mac core clock

// Mac controller
wire       mackeepRFOn;            // Keep RF on from mac
wire       RxkeepRFOn;             // Keep RF on from Rx
wire       TxkeepRFOn;             // Keep RF on from Tx

wire       forceCCAPrimary;        // Force the CCA Primary high between the first byte
                                   // of the rxVector1 and the rxEndForTiming_p

wire [ (`MPIFRXADDRWIDTH-1):0] mpIFRxFIFOWriteAddrInt;       // write address to TP RAM                                        

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


// output connections
///////////////////////////////////////////////////////
//   -- add by fengmaoqiao                                  --  //
//   -- this code set the mpif out signal to valid value    --//
//   -- if want use the phy ,should disable this code       --//
assign mpIFTxFIFOWriteEn         = mpIfTxFifoWrite;
assign mpIFTxFIFOReadEn          = mpIfFifoReadEn;
assign mpIFTxFIFOWriteData       = mpIfTxFifoData;

always @(posedge macCoreTxClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
    mpIfTxEn <= 1'b0;               //edit
  else if((macCoreClkSoftRst_n == 1'b0) || (macPhyTxEnd_p == 1'b1))
    mpIfTxEn <= 1'b0;               //edit
  else if(startTx_p == 1'b1)
    mpIfTxEn <= 1'b1;
end

always @(posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
   if(mpIFClkHardRst_n == 1'b0) 
   begin
     mpIFRxFIFOWriteData       <= 8'd0;
     mpIFRxFIFOWriteEn         <= 1'b0;
     mpIFRxFIFOWriteAddr       <= {(`MPIFRXADDRWIDTH){1'b0}}; 
   end
   else 
   begin
     mpIFRxFIFOWriteData       <= rxData;
     mpIFRxFIFOWriteEn         <= fifoWriteEn;
     mpIFRxFIFOWriteAddr       <= mpIFRxFIFOWriteAddrInt; 
   end   
end

assign mpIFRxFIFOReadEn          = macPhyIfRxFifoReadEn;
assign macPhyIfRxFifoData        = mpIFRxFIFOReadData;

assign macPhyIfRxFlush_p         = rxFifoRdClkFlush;

assign macPHYIFFIFOResetInValid  = fifoTxPtrsNullSync && fifoRxPtrsNull && macPHYIFFIFOReset;

assign mimoCmdValid              = 1'b0;         // to be implemented

assign keepRFOn                  = RxkeepRFOn || TxkeepRFOn;

// Tx fifo flush
assign mpifTxRdFifoflush         =  txFifoRdClkFlush || !mpIFClkSoftRst_n;

// Rx fifo flush
assign mpifRxRdFifoflush         =  rxFifoRdClkFlush || !macCoreClkSoftRst_n;

// FF the fifoTxPtrsNull before resync on MAC Core Clk domain
// avoiding glitches
always @(posedge mpIFClk, negedge mpIFClkHardRst_n)
begin
  if (mpIFClkHardRst_n == 1'b0)
    fifoTxPtrsNull_ff1 <= 1'b0;
  else
    fifoTxPtrsNull_ff1 <= fifoTxPtrsNull;
end


// resynchronization cells
///////////////////////////////////////////////////////
pulse2PulseSynchro U_stoptRx_p_synchro (
                .srcclk (macCoreRxClk),
                .srcresetn (macCoreClkHardRst_n),
                .dstclk (mpIFClk),
                .dstresetn (mpIFClkHardRst_n),
                .srcdata (stopRx_p),
                .dstdata (stopRx_mpIFClk_p)
                );

pulse2PulseSynchro U_startTx_p_synchro (
                .srcclk (macCoreTxClk),
                .srcresetn (macCoreClkHardRst_n),
                .dstclk (mpIFClk),
                .dstresetn (mpIFClkHardRst_n),
                .srcdata (startTx_p),
                .dstdata (startTx_mpIFClk_p)
                );

pulse2PulseSynchro U_stoptTx_p_synchro (
                .srcclk (macCoreTxClk),
                .srcresetn (macCoreClkHardRst_n),
                .dstclk (mpIFClk),
                .dstresetn (mpIFClkHardRst_n),
                .srcdata (stopTx_p),
                .dstdata (stopTx_mpIFClk_p)
                );

pulse2PulseSynchro U_mpIfUnderRun_synchro (
                .srcclk (mpIFClk),
                .srcresetn (mpIFClkHardRst_n),
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (mpifUnderRun),
                .dstdata (macPHYIFUnderRun)
                );

pulse2PulseSynchro U_mpifOverflow_synchro (
                .srcclk (mpIFClk),
                .srcresetn (mpIFClkHardRst_n),
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (mpifOverflow),
                .dstdata (macPHYIFOverflow)
                );

pulse2PulseSynchro U_macPhyTxEnd_synchro (
                .srcclk (mpIFClk),
                .srcresetn (mpIFClkHardRst_n),
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (txEnd_p),
                .dstdata (macPhyTxEnd_p)
                );

simpleSynchro U_fifoTxPtrsNull_synchro (
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (fifoTxPtrsNull_ff1),
                .dstdata (fifoTxPtrsNullSync)
                );

simpleSynchro U_mpIfCCAPrim20_synchro (
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (CCAPrimary20|forceCCAPrimary),
                .dstdata (macPhyIfRxCca)
                );

simpleSynchro U_mpIfCCASec20_synchro (
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (CCASecondary20),
                .dstdata (macPhyIfRxCcaSec20)
                );

simpleSynchro U_mpIfCCASec40_synchro (
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (CCASecondary40),
                .dstdata (macPhyIfRxCcaSec40)
                );

simpleSynchro U_mpIfCCASec80_synchro (
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (CCASecondary80),
                .dstdata (macPhyIfRxCcaSec80)
                );

simpleSynchro U_keepRF_synchro (
                .dstclk (mpIFClk),
                .dstresetn (mpIFClkHardRst_n),
                .srcdata (mpifKeepRFon),
                .dstdata (mackeepRFOn)
                );

simpleSynchro U_rifsDetect_synchro (
                .dstclk (macCoreRxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (rifsRxDetected),
                .dstdata (macPhyIfRifsRxDetected)
                );

simpleSynchro U_startRx_p_synchro (
                .dstclk (mpIFClk),
                .dstresetn (mpIFClkHardRst_n),
                .srcdata (startRx),
                .dstdata (startRx_mpIFClk)
                );

///////////////////////////////////////////////////////
// MAC PHY IF RX FIFO
///////////////////////////////////////////////////////
mpiftxRxFifoControl #(.ADDRWIDTH(`MPIFRXADDRWIDTH)) U_RxFifoControl (
                .wrClk                     (mpIFClk),
                .wrHardReset_n             (mpIFClkHardRst_n),
                .rdClk                     (macCoreRxClk),
                .rdHardReset_n             (macCoreClkHardRst_n),
                .rdFlush                   (mpifRxRdFifoflush),
                .fifoWrite                 (fifoWriteEn),
                .fifoRead                  (macPhyIfRxFifoReadEn),
                .fifoWrPtr                 (mpIFRxFIFOWriteAddrInt),
                .fifoRdPtr                 (mpIFRxFIFOReadAddr),
                .fifoFull                  (mpIfRxFifoFull),
                .fifoEmpty                 (macPhyIfRxFifoEmpty),
                .fifoPtrsNull              (fifoRxPtrsNull)
                );

// Instanciation of RxStateCtl
// Name of the instance : u_RxStateCtl
// Name of the file containing this module : RxStateCtl.v
RxStateCtl U_RxStateCtl (
		.mpIFClk                          (mpIFClk),
		.mpIFClkHardRst_n                 (mpIFClkHardRst_n),
		.mpIFClkSoftRst_n                 (mpIFClkSoftRst_n),
		.macCoreRxClk                     (macCoreRxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.startRx                          (startRx_mpIFClk),
		.stopRx_p                         (stopRx_mpIFClk_p),
		.rxErr_p                          (rxErr_p),
		.rxEnd_p                          (rxEnd_p),
		.phyRdy                           (phyRdy),
		.rxEndForTiming_p                 (rxEndForTiming_p),
		.rxReq                            (rxReq),
		.mpIfRxFifoFull                   (mpIfRxFifoFull),
		.fifoWriteEn                      (fifoWriteEn),
		.rxFifoRdClkFlush                 (rxFifoRdClkFlush),
		.macPhyIfRxErr_p                  (macPhyIfRxErr_p),
		.macPhyIfRxEnd_p                  (macPhyIfRxEnd_p),
		.macPhyIfRxEndForTiming_p         (macPhyIfRxEndForTiming_p),
		.forceCCAPrimary                  (forceCCAPrimary),
		.macPhyIfRxStart_p                (macPhyIfRxStart_p),
		.macPHYIFFIFOReset                (macPHYIFFIFOReset),
		.rxReqForceDeassertion            (rxReqForceDeassertion),
		.mpifOverflow                     (mpifOverflow),
		.mackeepRFOn                      (mackeepRFOn),
		.RxkeepRFOn                       (RxkeepRFOn),
		.debugPortMACPhyIf2               (debugPortMACPhyIf2)
		);



///////////////////////////////////////////////////////
// MAC PHY IF TX FIFO
///////////////////////////////////////////////////////
mpiftxRxFifoControl #(.ADDRWIDTH(`MPIFTXADDRWIDTH)) U_txFifoControl (
                .wrClk                     (macCoreTxClk),
                .wrHardReset_n             (macCoreClkHardRst_n),
                .rdClk                     (mpIFClk),
                .rdHardReset_n             (mpIFClkHardRst_n),
                .rdFlush                   (mpifTxRdFifoflush),
                .fifoWrite                 (mpIfTxFifoWrite),
                .fifoRead                  (mpIfFifoReadEn),
                .fifoWrPtr                 (mpIFTxFIFOWriteAddr),
                .fifoRdPtr                 (mpIFTxFIFOReadAddr),
                .fifoFull                  (mpIfTxFifoFull),
                .fifoEmpty                 (mpIfTxFifoEmtpy),
                .fifoPtrsNull              (fifoTxPtrsNull)
                );

TxStateCtl U_TxStateCtl (
                .mpIFClk                   (mpIFClk),
                .mpIFClkHardRst_n          (mpIFClkHardRst_n),
                .mpIFClkSoftRst_n          (mpIFClkSoftRst_n),
                .macCoreTxClk              (macCoreTxClk),
                .macCoreClkHardRst_n       (macCoreClkHardRst_n),
                .startTx_p                 (startTx_mpIFClk_p),
                .stopTx_p                  (stopTx_mpIFClk_p),
                .mpIfTxErr_p               (mpIfTxErr_p),
//                .mpIfTxEn                  (mpIfTxEnInt),
                .txPwrLevel                (txPwrLevel),
                .chBW                      (chBW),
                .chOffset                  (chOffset),
                .smoothing                 (smoothing),
                .antennaSet                (antennaSet),
                .smmIndex                  (smmIndex),
                .mcs                       (mcs),
                .preType                   (preType),
                .formatMod                 (formatMod),
                .numExtnSS                 (numExtnSS),
                .stbc                      (stbc),
                .fecCoding                 (fecCoding),
                .sounding                  (sounding),
                .legLength                 (legLength),
                .legRate                   (legRate),
                .service                   (service),
                .htLength                  (htLength),
                .nTx                       (nTx),
                .nSTS                      (nSTS),
                .shortGI                   (shortGI),
                .aggreation                (aggreation),
                .beamFormed                (beamFormed),
                .disambiguityBit           (disambiguityBit),
                .partialAID                (partialAID),
                .groupID                   (groupID),
                .dozeNotAllowed            (dozeNotAllowed),
                .continuousTx              (continuousTx),
                .phyRdy                    (phyRdy),
                .txEnd_p                   (txEnd_p),
                .phyErr_p                  (phyErr_p),
                .txReq                     (txReq),
                .txData                    (txData),
                .macDataValid              (macDataValid),
                .mpIfTxFifoDataout         (mpIFTxFIFOReadData),
                .mpIfTxFifoEmtpy           (mpIfTxFifoEmtpy),
                .mpIfFifoReadEn            (mpIfFifoReadEn),
                .txFifoRdClkFlush          (txFifoRdClkFlush),
                .macPHYIFFIFOReset         (macPHYIFFIFOReset),
                .rateControllerMPIF        (rateControllerMPIF),
                .mackeepRFOn               (mackeepRFOn),
                .TxkeepRFOn                (TxkeepRFOn),
                .mpifUnderRun              (mpifUnderRun)
                );

///////////////////////////////////////////////////////
// Debug port
///////////////////////////////////////////////////////
assign debugPortMACPhyIf = {macPhyIfRxFifoReadEn,
                            macPhyIfRxFifoEmpty,
                            macPhyIfRxErr_p,
                            macPhyIfRxEnd_p,
                            macPhyIfRxEndForTiming_p,
                            macPhyIfRxCcaSec20,
                            macPhyIfRxCca,
                            macPhyIfRxStart_p,
                            stopRx_p,
                            startRx,
                            aggreation,
                            mpIfTxEn,
                            mpIfTxErr_p,
                            mpIfTxFifoFull,
                            stopTx_p,
                            startTx_p
                            };



`ifdef RW_ASSERT_ON

///////////////////////////////////////////////////////
// PHY INTERFACE PROPERTIES
///////////////////////////////////////////////////////

//$rw_sva Check for rxReq not asserted during transmisson
property txReqAndNotRrxReq_prop;
@(posedge macCoreTxClk)
  disable iff(macCoreClkHardRst_n==0)
  txReq|->!rxReq;
endproperty
txReqAndNotRrxReq: assert property (txReqAndNotRrxReq_prop); 

//$rw_sva Checks for txReq not asserted during reception
property rxReqAndNottxReq_prop;
@(posedge macCoreRxClk)
  disable iff(macCoreClkHardRst_n==0)
  rxReq|->!txReq;
endproperty
rxReqAndNottxReq: assert property (rxReqAndNottxReq_prop); 

//$rw_sva Checks for phyRdy asserted only during active transmission or
//reception
property rxReq_txReq_phyRdy_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  $rose(phyRdy) |-> $past(txReq || rxReq);
endproperty
rxReq_txReq_phyRdy: assert property (rxReq_txReq_phyRdy_prop); 

//$rw_sva Checks for phyRdy not assserted during TxVector phase
property txvector_phyRdy_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  $rose(txReq) |-> not (##[1:13]  (phyRdy));
endproperty  
txvector_phyRdy: assert property (txvector_phyRdy_prop); 

//$rw_sva Checks for assertion of txEnd_p 1-5 clock cycles after assertion of
//phyErr_p
property phyErr_txEnd_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  $rose(phyErr_p) |-> ##[1:5] $rose(txEnd_p);
endproperty 
phyErr_txEnd: assert property (phyErr_txEnd_prop); 

//$rw_sva Checks for de-assertion of txReq one clock after txEnd_p is asserted.
property txEnd_txReq_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  (txReq && $rose(txEnd_p)) |=> $fell(txReq);
endproperty
txEnd_txReq: assert property (txEnd_txReq_prop); 

//$rw_sva Checks for assertion of txEnd_p between 1-5  clock cycles after txReq
//is de-asserted.
property txReq_txEnd_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  ($past(txEnd_p==0) && $past(txReq) && $fell(txReq)) |-> ##[1:5] $rose(txEnd_p);
endproperty
txReq_txEnd: assert property (txReq_txEnd_prop); 

//$rw_sva Checks for assertion of macDataValid signal one cycle after assertion
//of phyRdy. This check is valid only during transmission.
property phyRdy_macDataValid_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n== 0 || txReq == 0 || rateControllerMPIF == 1)
  $fell(phyRdy) |=>  ##1(! macDataValid);
endproperty
phyRdy_macDataValid: assert property (phyRdy_macDataValid_prop); 

//$rw_sva Check for macDataValid is asserted only during transmission
property macDataValid_txReq_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  macDataValid |-> txReq || $past(txReq);
endproperty
macDataValid_txReq: assert property (macDataValid_txReq_prop); 

//$rw_sva Checks for LOW value on txReq line when cca lines are HIGH.
property cca_txReq_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  (CCAPrimary20)|->!txReq;
endproperty
cca_txReq: assert property (cca_txReq_prop); 

//$rw_sva Check for HIGH value on rxReq line when cca lines are HIGH
property cca_rxReq_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  $fell(rxReq) |-> ##[1:30] (!(CCAPrimary20));
endproperty
cca_rxReq: assert property (cca_rxReq_prop); 


// //Normal Rx End 
// //$rw_sva Checks for de-assertion of rxReq one clock cycle after rxEnd_p is
// //asserted.
// property rxEnd_rxReq_prop;
// @(posedge mpIFClk)
//   disable iff(mpIFClkHardRst_n==0)
//   (rxReq && $rose(rxEnd_p)) |=> $fell(rxReq);
// endproperty
// rxEnd_rxReq: assert property (rxEnd_rxReq_prop); 


//$rw_sva The following properties check for keepRFOn. The keepRFOn signal
//should not be asserted or de-asserted when both txReq and rxReq are LOW
property txReq_rxReq_keepRFOn_prop;
@(posedge mpIFClk)
  (!txReq && !rxReq)|=>not ($rose(keepRFOn) || $fell(keepRFOn));
endproperty 
txReq_rxReq_keepRFOn: assert property (disable iff (mpIFClkHardRst_n) txReq_rxReq_keepRFOn_prop); 

//$rw_sva Checks for keepRFOn assertion atleast one clock cycle before txEnd_p is
//asserted during transmission
property keepRFOn_txReq_txEnd_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  ($rose(keepRFOn) && txReq)|->(!txEnd_p ##1 !$fell(txReq));
endproperty
keepRFOn_txReq_txEnd: assert property (keepRFOn_txReq_txEnd_prop); 

//$rw_sva Checks for keepRFOn not be de-asserted one clock cycle after txReq is
//asserted.
property keepRFOn_txReq_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  $rose(txReq)|->!($fell(keepRFOn));
endproperty
keepRFOn_txReq: assert property (keepRFOn_txReq_prop); 

//$rw_sva Checks for keepRFOn assertion atleast a clock cycle before
//rxEndForTiming_p is asserted during reception.
property keepRFOn_rxReq_rxEndForTiming_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  ($rose(keepRFOn) && rxReq)|->!rxEndForTiming_p ##[1:10] !rxEnd_p;
endproperty
keepRFOn_rxReq_rxEndForTiming: assert property (keepRFOn_rxReq_rxEndForTiming_prop); 

//$rw_sva Check for de-assertion of keepRFOn atlest a clock cycle after rxReq is
//asserted.
property keepRFOn_rxReq_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  $rose(rxReq) |->!($fell(keepRFOn));
endproperty
keepRFOn_rxReq: assert property (keepRFOn_rxReq_prop); 

//$rw_sva Checks for phyErr signal asserted for a clock cycle
property phyErr_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  $rose(phyErr_p)|=>$fell(phyErr_p);
endproperty
phyErr: assert property (phyErr_prop); 

//$rw_sva Checks for txEnd signal asserted for a clock cycle
property txEnd_prop;
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  $rose(txEnd_p)|=>$fell(txEnd_p);
endproperty
txEnd: assert property (txEnd_prop); 

//$rw_sva Checks for rxErr signal asserted for a clock cycle
property rxErr_prop; 
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  $rose(rxErr_p)|=>$fell(rxErr_p);
endproperty
rxErr: assert property (rxErr_prop); 

//$rw_sva Checks for rxEndForTiming signal asserted for a clock cycle
property rxEndForTiming_prop; 
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  $rose(rxEndForTiming_p)|=>$fell(rxEndForTiming_p);
endproperty
rxEndForTiming: assert property (rxEndForTiming_prop); 

//$rw_sva Checks for rxEnd signal asserted for a clock cycle
property rxEnd_prop; 
@(posedge mpIFClk)
  disable iff(mpIFClkHardRst_n==0)
  $rose(rxEnd_p)|=>$fell(rxEnd_p);
endproperty
rxEnd: assert property (rxEnd_prop); 

///////////////////////////////////////////////////////
// FIFO HANDLING PROPERTIES
///////////////////////////////////////////////////////

//$rw_sva Checks the controller does not write into the Tx FIFO when it's full
property noWriteWhenTxFifoFullCheck_prop;
@(posedge macCoreTxClk)
    (mpIfTxFifoFull == 1'b1) |-> mpIfTxFifoWrite == 1'b0;
endproperty
noWriteWhenTxFifoFullCheck: assert property (noWriteWhenTxFifoFullCheck_prop); 


//$rw_sva Checks the controller does not read into the Tx FIFO when it's empty
property noReadWhenTxFifoEmptyCheck_prop;
@(posedge macCoreTxClk)
    (mpIfTxFifoEmtpy == 1'b1) |-> mpIfFifoReadEn == 1'b0;
endproperty
noReadWhenTxFifoEmptyChecks: assert property (noReadWhenTxFifoEmptyCheck_prop); 


//$rw_sva Checks the controller does not write into the Rx FIFO when it's full
property noWriteWhenRxFifoFullCheck_prop;
@(posedge mpIFClk)
    (mpIfRxFifoFull == 1'b1) |-> fifoWriteEn == 1'b0;
endproperty
//noWriteWhenRxFifoFullCheck: assert property (noWriteWhenRxFifoFullCheck_prop); 

//$rw_sva Checks the controller does not read into the Rx FIFO when it's empty
property noReadWhenRxFifoEmptyCheck_prop;
@(posedge macCoreRxClk)
    (macPhyIfRxFifoEmpty == 1'b1) |-> macPhyIfRxFifoReadEn == 1'b0;
endproperty
noReadWhenRxFifoEmptyCheck: assert property (noReadWhenRxFifoEmptyCheck_prop); 

`endif // RW_ASSERT_ON
endmodule
                 
