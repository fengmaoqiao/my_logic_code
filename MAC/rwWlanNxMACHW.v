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
// Description      : Top level of rwWlanNxMACHW module
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

`include "defineAHB.v"
`include "defineDMA.v"
`include "define.v"
`include "commonDefine.v"
`include "commonDefines.v"

module rwWlanNxMACHW( 
  ///////////////////////////////////////////////
  //$port_g Resets
  ///////////////////////////////////////////////
  input  wire                            macPIClkHardRst_n,     // Active low hard reset signal synchronized to the macPIClk.
  input  wire                            macCoreClkHardRst_n,   // Active low hard reset signal synchronized to the macCoreClk.
  input  wire                            macWTClkHardRst_n,     // Active low hard reset signal synchronized to the macWTClk.
  input  wire                            mpIFClkHardRst_n,      // Active low hard reset signal synchronized to the mpIFClk. 

  ///////////////////////////////////////////////
  //$port_g Clocks
  ///////////////////////////////////////////////
  input  wire                            macPIClk,              // Primary MAC Platform Interface Clock
  input  wire                            macPITxClk,            // Secondary MAC Platform Interface Clock for TX
  input  wire                            macPIRxClk,            // Secondary MAC Platform Interface Clock for RX
  input  wire                            macPISlaveClk,         // MAC Platform Interface Slave Clock
  input  wire                            macCoreClk,            // Primary MAC Core Clock
  input  wire                            macCryptClk,           // Secondary MAC Core Clock for encryption
  input  wire                            macCoreTxClk,          // Secondary MAC Core Clock for TX
  input  wire                            macCoreRxClk,          // Secondary MAC Core Clock for RX
  input  wire                            macLPClk,              // MAC Low Power clock. 
  input  wire                            macWTClk,              // Clock input for WEP/TKIP blocks.
  input  wire                            mpIFClk,               // MAC PHY Interface Clock

  ///////////////////////////////////////////////
  //$port_g Clock Enables
  ///////////////////////////////////////////////
  output wire                            macPriClkEn,           // Clock Enable for macPriClk Clocks
  output wire                            platformWakeUp,        // Wake Up platform
  output wire                            macPITxClkEn,          // Clock Enable for macPITxClk Clock
  output wire                            macPIRxClkEn,          // Clock Enable for macPIRxClk Clock
  output wire                            macCoreTxClkEn,        // Clock Enable for macCoreTxClk Clock
  output wire                            macCoreRxClkEn,        // Clock Enable for macCoreRxClk Clock
  output wire                            macLPClkSwitch,        // Switch MAC Lower Clock.
  output wire                            macWTClkEn,            // Clock Enable for macWTClk Clock
  output wire                            macCryptClkEn,         // Clock Enable for macCryptClk Clock
  output wire                            mpIFClkEn,             // Clock Enable for mpIFClk Clock

  ///////////////////////////////////////////////
  //$port_g Interrupts
  ///////////////////////////////////////////////
  output wire                            intGen_n,              // Active low general interrupt signal.
  output wire                            intProtTrigger_n,      // Active low protocol event interrupt signal
  output wire                            intTxTrigger_n,        // Active low TX event interrupt signal
  output wire                            intRxTrigger_n,        // Active low Rx event interrupt signal
  output wire                            intTxRxMisc_n,         // Active low Misc Tx/Rx event interrupt signal
  output wire                            intTxRxTimer_n,        // Active low Timer Tx Rx timer interrupt signal

  ///////////////////////////////////////////////
  //$port_g Debug Interface
  ///////////////////////////////////////////////
  output reg                             internalError,         // Internal Error
  output wire                     [31:0] debugPort,             // Debug Port
  input  wire                            debugKSR,              // Debug Key Storage RAM.
  `ifdef RW_SWPROF_DEBUG_PORT
  output wire                     [31:0] swProfDebugPort,       // Debug Port dedicated to Software Profiling
  `endif // RW_SWPROF_DEBUG_PORT

  ///////////////////////////////////////////////
  //$port_g ARM AHB/AHBLite Slave Interface
  ///////////////////////////////////////////////
  input  wire  [`RW_HOST_ADDR_WIDTH-1:0] hSAddr,                // The 16-bit system address bus.
  input  wire                     [ 1:0] hSTrans,               // Transfer type of the current transfer, 
  input  wire                            hSWrite,               // Transfer direction. When HIGH this signal indicates a write transfer and when LOW a read transfer
  input  wire                     [ 2:0] hSSize,                // Transfer size. Indicates the size of the transfer, which is typically byte (8-bit), halfword (16-bit) or word (32-bit).
  input  wire                     [ 2:0] hSBurst,               // Burst type. Indicates if the transfer forms part of a burst. Four, eight and sixteen beat bursts are supported and the burst may be either incrementing or wrapping.
  input  wire                     [ 3:0] hSProt,                // Protection control. Not used.
  input  wire                     [31:0] hSWData,               // Write data bus. The write data bus is used to transfer data from the master to the bus slaves during write operations. 
  input  wire                            hSSel,                 // Slave select. This signal is asserted from the decoder to indicate that the current transfer is meant for a particular slave.
  input  wire                            hSReadyIn,             // Transfer Done. When HIGH the hSReadyIn signal indicates that a transfer has finished on the bus. This signal signals the status of other slaves on the AHB.
  output wire                     [31:0] hSRData,               // Read data bus. The read data bus is used to transfer data from bus slaves to the bus master during read operations.
  output wire                            hSReadyOut,            // Transfer done. When HIGH the hSReadyOut signal indicates that a transfer has finished on the bus. This signal may be driven LOW to extend a transfer. Note: Slaves on the bus require hReady as both an input and an output signal.
  output wire                     [ 1:0] hSResp,                // Transfer response. The transfer response provides additional information on the status of a transfer. Two different responses are provided, OKAY and ERROR.
                                                                // RETRY and SPLIT are NA in an AHBLite system.

  ///////////////////////////////////////////////
  //$port_g ARM AHB/AHBLite Master Interface
  ///////////////////////////////////////////////
  output wire                            hMBusReq,              // Bus request. (Not used in AHB-Lite system)
  output wire                            hMLock,                // Locked transfers. When HIGH this signal indicates that the master requires locked access to the bus and no other master should be granted the bus until this signal is LOW.
  input  wire                            hMGrant,               // Bus Grant indication. (only used in AHB system. Must be tied high in AHB-Lite system).
  output wire                     [31:0] hMAddr,                // The 32-bit system address bus.
  output wire                     [ 1:0] hMTrans,               // Transfer type of the current transfer, which can be NONSEQUENTIAL, SEQUENTIAL, IDLE or BUSY.
  output wire                            hMWrite,               // Transfer direction. When HIGH this signal indicates a write transfer and when LOW a read transfer.
  output wire                     [ 2:0] hMSize,                // Transfer size. Indicates the size of the transfer, which is typically byte (8-bit), halfword (16-bit) or word (32-bit). The protocol allows for larger transfer sizes up to a maximum of 1024 bits.
  output wire                     [ 2:0] hMBurst,               // Burst type. Indicates if the transfer forms part of a burst. Four, eight and sixteen beat bursts are supported and the burst may be either incrementing or wrapping.
  output wire                     [ 3:0] hMProt,                // Protection control. Fixed to non-cache data. 
  output wire                     [31:0] hMWData,               // Write data bus. The write data bus is used to transfer data from the master to the bus slaves during write operations. 
  input  wire                     [31:0] hMRData,               // Read data bus. The read data bus is used to transfer data from bus slaves to the bus master during read operations.
  input  wire                            hMReady,               // Transfer done. When HIGH the hMReady signal indicates that a transfer has finished on the bus. This signal may be driven LOW to extend a transfer. 
  input  wire                     [ 1:0] hMResp,                // Transfer response. The transfer response provides additional information on the status of a transfer. Two different responses are provided, OKAY and ERROR.
                                                                // RETRY and SPLIT are NA in an AHBLite system.

  ///////////////////////////////////////////////
  //$port_g PHY interface
  ///////////////////////////////////////////////
  (*syn_keep = "true" , mark_debug = "true" *)
  input  wire                            phyRdy,                // data valid signal 
  (*syn_keep = "true" , mark_debug = "true" *)            
  input  wire                            txEnd_p,               // end of transaction              
  input  wire                     [ 7:0] rxData,                // rx data                 
  input  wire                            CCAPrimary20,          // CCA on Primary 20MHz channel                       
  input  wire                            CCASecondary20,        // CCA on Secondary 20MHz channel                       
  input  wire                            CCASecondary40,        // CCA on Secondary 40MHz channel                       
  input  wire                            CCASecondary80,        // CCA on Secondary 80MHz channel                       
  input  wire                            rxEndForTiming_p,      // end of transmission (antenna) 
  input  wire                            rxErr_p,               // Rx error                      
  input  wire                            rxEnd_p,               // Rx end                        
  input  wire                            phyErr_p,              // phy error                     
  input  wire                            rifsRxDetected,        // rifs detected
  (*syn_keep = "true" , mark_debug = "true" *)                 
  output wire                            txReq,                 // Tx request                     
  output wire                            rxReq,                 // Rx request                     
  output wire                     [ 7:0] txData,                // Tx data
  (*syn_keep = "true" , mark_debug = "true" *)                        
  output wire                            macDataValid,          // data valid                     
  output wire                            mimoCmdValid,          // mimo command                   
  output wire                            keepRFOn,              // Keep RF on                     
  
  ///////////////////////////////////////////////
  //$port_g Coex Interface
  ///////////////////////////////////////////////
  `ifdef RW_WLAN_COEX_EN
  output wire                            coexWlanTx,            // Indicates that a WLAN Transmission is on-going
  output wire                            coexWlanRx,            // Indicates that a WLAN Reception is on-going
  input  wire                            coexWlanTxAbort,       // Requests from external arbiter abort all on-going transmission 
  output wire [3:0]                      coexWlanPTI,           // Indicates the priority of the on-going traffic
  output wire                            coexWlanPTIToggle,     // Indicates a new priority value
  output wire                            coexWlanChanBw,        // Indicates the BW of the on-going traffic
  output wire [6:0]                      coexWlanChanFreq,      // Indicates the Center frequency of the on-going traffic
  output wire                            coexWlanChanOffset,    // Indicates the Center frequency of the on-going traffic
  `endif // RW_WLAN_COEX_EN

  ///////////////////////////////////////////////
  //$port_g Memory Interface
  ///////////////////////////////////////////////
  //$port_g TxFIFO 64*38 Two Ports SRAM 
  ///////////////////////////////////////////////
  output wire                            txFIFOReadEn,          // Transmit FIFO Read Enable. 
  output wire     [`TXFIFOADDRWIDTH-1:0] txFIFOReadAddr,        // Transmit FIFO Read Address bus.
  input  wire                     [37:0] txFIFOReadData,        // Transmit FIFO Read Data bus.
  output wire                            txFIFOWriteEn,         // Transmit FIFO Write Enable.
  output wire     [`TXFIFOADDRWIDTH-1:0] txFIFOWriteAddr,       // Transmit FIFO Write Address bus.
  output wire                     [37:0] txFIFOWriteData,       // Transmit FIFO Write Data bus.

  ///////////////////////////////////////////////
  //$port_g RxFIFO 64*36 Two Ports SRAM 
  ///////////////////////////////////////////////
  output wire                            rxFIFOReadEn,          // Receive FIFO Read Enable. 
  output wire     [`RXFIFOADDRWIDTH-1:0] rxFIFOReadAddr,        // Receive FIFO Read Address bus.
  input  wire                     [35:0] rxFIFOReadData,        // Receive FIFO Read Data bus.
  output wire                            rxFIFOWriteEn,         // Receive FIFO Write Enable.
  output wire     [`RXFIFOADDRWIDTH-1:0] rxFIFOWriteAddr,       // Receive FIFO Write Address bus.
  output wire                     [35:0] rxFIFOWriteData,       // Receive FIFO Write Data bus.

  ///////////////////////////////////////////////
  //$port_g Key Storage RAM 64*186 Single Port SRAM 
  ///////////////////////////////////////////////
  output wire                            keyStorageEn,          // Enable Key Storage RAM
                                                                // This signal is asserted for both read and write operations to the Key Storage RAM.
  output wire                            keyStorageWriteEn,     // Write Enable Key Storage RAM
                                                                // This signal is asserted for write operations to the Key Storage RAM.
  output wire     [`KEY_INDEX_WIDTH-1:0] keyStorageAddr,        // Key Storage RAM write data bus
`ifdef RW_WAPI_EN
  input  wire                    [314:0] keyStorageReadData,    // Key Storage RAM read data bus.
  output wire                    [314:0] keyStorageWriteData,   // Key Storage RAM address bus.
`else
  input  wire                    [186:0] keyStorageReadData,    // Key Storage RAM read data bus.
  output wire                    [186:0] keyStorageWriteData,   // Key Storage RAM address bus.
`endif // RW_WAPI_EN

  ///////////////////////////////////////////////
  //$port_g RC4 PRNG 256*8 Dual Ports SRAM
  ///////////////////////////////////////////////
  output wire                            sBoxAEn,               // Enable SBox RAM port A
                                                                // This signal is asserted for both read and write operations to the SBox RAM port A.
  output wire                            sBoxAWriteEn,          // Write Enable SBox RAM port A
                                                                // This signal is asserted for write operations to the SBox RAM port A.
  output wire                     [ 7:0] sBoxAAddr,             // SBox RAM port A address bus.
  input  wire                     [ 7:0] sBoxAReadData,         // SBox RAM port A read data bus.
  output wire                     [ 7:0] sBoxAWriteData,        // SBox RAM port A write data bus.

  output wire                            sBoxBEn,               // Enable SBox RAM port B
                                                                // This signal is asserted for both read and write operations to the SBox RAM port B.
  output wire                            sBoxBWriteEn,          // Write Enable SBox RAM port B
                                                                // This signal is asserted for write operations to the SBox RAM port B.
  output wire                     [ 7:0] sBoxBAddr,             // SBox RAM port B address bus.
  input  wire                     [ 7:0] sBoxBReadData,         // SBox RAM port B read data bus.
  output wire                     [ 7:0] sBoxBWriteData,        // SBox RAM port B write data bus.

  ///////////////////////////////////////////////
  //$port_g MAC-PHY IF TX FIFO RAM 256*8 Two Ports SRAM
  ///////////////////////////////////////////////
  output wire                            mpIFTxFIFOReadEn,      // MAC-PHY Interface Transmit FIFO Read Enable. 
                                                                // This signal is asserted for read operations to the MAC-PHY interface Transmit FIFO.
  output wire     [`MPIFTXADDRWIDTH-1:0] mpIFTxFIFOReadAddr,    // MAC-PHY Interface Transmit FIFO Read Address bus.
  input  wire                     [ 7:0] mpIFTxFIFOReadData,    // MAC-PHY Interface Transmit FIFO Read Data bus.
  output wire                            mpIFTxFIFOWriteEn,     // MAC-PHY InterFace Transmit FIFO Write Enable.
                                                                // This signal is asserted for write operations to the MAC-PHY interface Transmit FIFO.
  output wire     [`MPIFTXADDRWIDTH-1:0] mpIFTxFIFOWriteAddr,   // MAC-PHY Interface Transmit FIFO Write Address bus.
  output wire                     [ 7:0] mpIFTxFIFOWriteData,   // MAC-PHY Interface Transmit FIFO Write Data bus.

  ///////////////////////////////////////////////
  //$port_g MAC-PHY IF RX FIFO RAM 64*8 Two Ports SRAM
  ///////////////////////////////////////////////
  output wire                            mpIFRxFIFOReadEn,      // MAC-PHY Interface Receive FIFO Read Enable. 
                                                                // This signal is asserted for read operations to the MAC-PHY interface Receive FIFO.
  output wire     [`MPIFRXADDRWIDTH-1:0] mpIFRxFIFOReadAddr,    // MAC-PHY Interface Receive FIFO Read Address bus.
  input  wire                     [ 7:0] mpIFRxFIFOReadData,    // MAC-PHY Interface Receive FIFO Read Data bus.
  output wire                            mpIFRxFIFOWriteEn,     // MAC-PHY InterFace Receive FIFO Write Enable.
                                                                // This signal is asserted for write operations to the MAC-PHY interface Receive FIFO.
  output wire     [`MPIFRXADDRWIDTH-1:0] mpIFRxFIFOWriteAddr,   // MAC-PHY Interface Receive FIFO Write Address bus.
  output wire                     [ 7:0] mpIFRxFIFOWriteData,   // MAC-PHY Interface Receive FIFO Write Data bus.

  ///////////////////////////////////////////////
  //$port_g Encryption RX FIFO RAM 128*8 Two Ports SRAM
  ///////////////////////////////////////////////
  output wire                            encrRxFIFOReadEn,      // Encryption Receive FIFO Read Enable. 
                                                                // This signal is asserted for read operations to the Encryption Receive FIFO.
  output wire                     [ 6:0] encrRxFIFOReadAddr,    // Encryption Receive FIFO Read Address bus.
  input  wire                     [ 7:0] encrRxFIFOReadData,    // Encryption Receive FIFO Read Data bus.
  output wire                            encrRxFIFOWriteEn,     // Encryption Receive FIFO Write Enable.
                                                                // This signal is asserted for write operations to the Encryption Receive FIFO.
  output wire                     [ 6:0] encrRxFIFOWriteAddr,   // Encryption Receive FIFO Write Address bus.
  output wire                     [ 7:0] encrRxFIFOWriteData,   // Encryption Receive FIFO Write Data bus.

`ifdef RW_MAC_MIBCNTL_EN
  ///////////////////////////////////////////////
  //$port_g MIB Table RAM 256*32 Single Port SRAM
  ///////////////////////////////////////////////
  output wire                            mibTableEn,            // MIB Table Enable. 
                                                                // This signal is asserted for both read and write operations to the MIB Table.
  output wire                            mibTableWriteEn,       // MIB Table Write Enable.
                                                                // This signal is asserted for write operations to the MIB Table.
  output wire                     [ 7:0] mibTableAddr,          // MIB Table Address bus.
  input  wire                     [31:0] mibTableReadData,      // MIB Table Read Data bus.
  output wire                     [31:0] mibTableWriteData,     // MIB Table Write Data bus.
`endif // RW_MAC_MIBCNTL_EN

  ///////////////////////////////////////////////
  //$port_g PS BITMAP RAM 8*32 Single Port SRAM
  ///////////////////////////////////////////////
  output wire                            psBitmapEn,            // Partial State Bitmap Enable. 
                                                                // This signal is asserted for both read and write operations to the Partial State Bitmap.
  output wire                            psBitmapWriteEn,       // Partial State Bitmap Write Enable.
                                                                // This signal is asserted for write operations to the Partial State Bitmap.
  output wire                     [ 1:0] psBitmapAddr,          // Partial State Bitmap Address bus.
  input  wire                     [87:0] psBitmapReadData,      // Partial State Bitmap Read Data bus.
  output wire                     [87:0] psBitmapWriteData      // Partial State Bitmap Write Data bus.
          
);


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

wire  ZERO_CT;
wire [31 : 0] signature;     
 // VERSION1REG register.
wire  mac80211MHFormat;
wire  coex;
wire  wapi;
wire  tpc;
wire  vht;                    
wire  ht;                    
wire  rce;                   
wire  ccmp;                  
wire  tkip;                  
wire  wep;                   
wire  security;              
wire  sme;                   
wire  hcca;                  
wire  edca;                  
wire  qos;                   
 // VERSION2REG register.
wire [2 : 0] phaseNumber;    
wire [5 : 0] releaseNumber;  
wire  ieRelease;             
wire [6 : 0] umVersion ;     
 // BITMAPCNTREG register.
wire [15 : 0] bitmapCnt;     



wire        statuserrInHWLevel3;        // status err In Hw Level 3
wire        statuserrInTxRxLevel2;      // status err Tx/Rx Hw Level 1
wire        statuserrInRxLevel1;        // status err Rx Hw Level 1
wire        statuserrInTxLevel1;        // status err Tx Hw Level 1
wire        tsfUpdatedBySWIn ;          // Input to clear the Software update request
wire        tsfUpdatedBySWInValid ;     // Data valid  
wire        dtimUpdatedBySWIn ;         // Input to clear the Software update request
wire        dtimUpdatedBySWInValid ;    // Data valid  


wire        mpIFClkSoftRst_n;           // Soft Reset of the mpIF Clock domain 
                                        // active low
wire        macCoreClkSoftRst_n;        // Soft Reset of the MAC Core Clock domain 
                                        // active low
wire        macPIClkSoftRst_n;          // Soft Reset for the MAC Platform Clock domain 
                                        // active low
wire        macWTClkSoftRst_n;          // Soft Reset for the WT Clock domain 
                                        // active low
wire        macPISlaveClkSoftRst_n;     // mac PI Slave Soft reset
                                        // active low

wire        dmaSoftRst_n;               // dma soft reset active low
wire        mpifSoftRst_n;              // mpif soft reset active low
wire        txFifoSoftRst_n;            // txFifo soft reset active low

wire        hwErr;                      // Indicate a HW Error

// Interconnect between TX FIFO and TX Controller
wire        txFIFOWrFlush;              // Request from MAC Platform Clock domain to flush the FIFO
wire        txFIFOWrite;                // Write a new word in the Tx FIFO
wire [31:0] txFIFOWrData;               // Data written to the TX FIFO
wire [ 5:0] txFIFOWrTag;                // Tag written to the TX FIFO
wire        txFIFOAlmostFull;           // Indicates that the TX FIFO is almost full
wire        txFIFOFull;                 // Indicates that the TX FIFO is full and cannot accept new write
wire        txFIFOAlmEmptyWrClk;        // Indicates that the TX FIFO is almost empty
wire        txFIFOEmptyWrClk;           // Indicates that the TX FIFO is empty
wire        txFIFORdFlush;              // Request from MAC Core Clock domain to flush the FIFO
wire        txFIFORead;                 // Request a new byte from the Tx FIFO
wire        txFIFOReadByFour;           // Indicates that the TX FIFO has to be read per word and not per byte
wire        txFIFOReadByTwo;            // Indicates that the TX FIFO has to be read per hlf-word and not per byte
wire        txFIFOEmpty;                // Indicates that the TX FIFO is empty
wire        txFIFODataValid;            // Indicates when the read data is valid
wire [ 7:0] txFIFORdData;               // Byte read from the TX FIFO
wire [ 1:0] txFIFOMPDUDelimiters;       // Tag read from the TX FIFO
          

// Interconnect between Tx Parameters Cache and the DMA Engine
wire         txCtrlRegWr;               // TX parameter Cache module signals
wire  [31:0] txCtrlRegData;             // TX parameter Cache module signals
wire         txCtrlRegPT;               // Indicates currently Policy table information is
wire         txCtrlRegHD;               // Indicates currently Header descriptor information
wire         discardPrevHD_p;           // Signal to TX Parameter Cache module.
wire         txCtrlRegBusy;             // Indicates there are 2 sets of parameters 

// Interconnect between RX FIFO and RX Controller
wire         rxFIFOAlmostFull;          // RX FIFO is almost full
wire         rxFIFOFull;                // RX FIFO is full

wire [3:0]   rxFIFOWrTag;               // RX FIFO write tag
wire [31:0]  rxFIFOWrData;              // RX FIFO write data
wire         rxFIFOWrite;               // RX FIFO write enable


// Interconnect between MAC-PHY IF and Mac Controller
wire        macPhyIfRxStart_p;          // Start of reception pulse
wire        macPhyIfRxFlush_p;          // Rx flush pulse
wire        startRx;                    // Start Rx trigger                   
wire        stopRx_p;                   // Stop Rx trigger                    
wire        mpifKeepRFon;               // Keep RF On
                                                                                         
// Interconnect between MAC-PHY IF and Tx  Controller If                                                            
wire        startTx_p;                  // Start Tx trigger              
wire        stopTx_p;                   // Stop Tx trigger               
wire [ 7:0] mpIfTxFifoData;             // Data to transmit              
wire        mpIfTxFifoWrite;            // Data valid                    

wire [ 7:0] txPwrLevel;                 // Transmit Power Level             
wire [ 1:0] chBW;                       // Channel Bandwidth             
wire [ 2:0] formatMod;                  // Format and Modulation           
wire [19:0] htLength;                   // Length of the HT and VHT PPDU              
wire [ 2:0] nTx;                        // Number of Transmit Chains.      
wire [ 1:0] chOffset;                   // transmit vector field              
wire        smoothing;                  // Smoothing recommended            
wire [ 7:0] antennaSet;                 // Antenna Set           
wire [ 7:0] smmIndex;                   // Spatial Map Matrix Index           
wire [ 6:0] mcs;                        // Modulation Coding Scheme           
wire        preType;                    // Preamble Type         
wire [ 1:0] numExtnSS;                  // Number of Extension Spatial Streams              
wire [ 1:0] stbc;                       // Space Time Block Coding           
wire        fecCoding;                  // FEC Coding             
wire        sounding;                   // Indicates whether this PPDU is Sounding        
wire [11:0] legLength;                  // Legacy Length of the PPDU            
wire [ 3:0] legRate;                    // Legacy Rate of the PPDU               
wire [15:0] service;                    // Service              
wire [ 2:0] nSTS;                       // Indicates the number of space-time streams.
wire        shortGI;                    // Short Guard Interval              
wire        aggreation;                 // MPDU Aggregate
wire        beamFormed;                 // BeamFormed
wire        disambiguityBit;            // Disambiguity
wire [8:0]  partialAID;                 // partial AID
wire [5:0]  groupID;                    // group ID
wire        dozeNotAllowed;             // TXOP PS Not Allowed
wire        continuousTx;               // Enable continuous transmit 

wire        mpIfTxFifoFull;             // FIFO status                        
wire        mpIfTxErr_p;                // Transmit error                     
wire        mpIfTxEn;                   // Transmit Enable                    
                                                                                         
// Interconnect between MAC-PHY IF and Rx Controller                                                                
wire        macPhyTxEnd_p;              // Pulse tx end from phy domain to core domain
wire        macPhyIfRxFifoReadEn;       // FIFO read enable from the Rx controller                                    
wire        macPhyIfRxFifoEmpty;        // FIFO empty signal                                     
wire [ 7:0] macPhyIfRxFifoData;         // FIFO data 
wire        macPhyIfRxErr_p;            // abort pulse                                     
wire        macPhyIfRxEnd_p;            // end of reception pulse                                      
wire        macPhyIfRxEndForTiming_p;   // end of reception at the antenna                                     
wire        macPhyIfRifsRxDetected;     // RIFS detected indication                                   
wire        macPhyIfRxCca;              // CCA trigger                    
wire        macPhyIfRxCcaSec20;         // CCA trigger on Secondary 20MHz channel                    
wire        macPhyIfRxCcaSec40;         // CCA trigger on Secondary 40MHz channel                  
wire        macPhyIfRxCcaSec80;         // CCA trigger on Secondary 80MHz channel                  

// Interconnect between MAC-PHY IF and Registers
wire        macPHYIFFIFOReset;          // Flush the FIFO
wire        macPHYIFFIFOResetIn;        // Flush the FIFO In
wire        macPHYIFFIFOResetInValid;   // Flush the FIFO clear
wire        rateControllerMPIF;         // Select reverse handshaking or PHy strobe tranmit mechanism
wire        macPHYIFUnderRun;           // underrun status

// MAC Timer Unit with the DMA Engine
wire        rxTrig_p;                   // RX trigger

// Interconnect Host IF to Control and Status Registers
wire                            regReadyIn;              // read data valid or write completed 
wire [(`RW_REG_DATA_WIDTH-1):0] regReadData;             // Data read from registers
wire                            regWrite;                // Write enable
wire                            regRead;                 // Read enable
wire [(`RW_REG_ADDR_WIDTH-1):0] regAddr;                 // Register address
wire [(`RW_REG_DATA_WIDTH-1):0] regWriteData;            // Data to be written to the registers

// Interconnect Host IF to  DMA interface
wire                          dmaHIFRead            ;// dma host interface read enable
wire                          dmaHIFWrite           ;// dma host interface write enable
wire                          dmaHIFBurstEn         ;// dma host interface burst enable
wire [31:0]                   dmaHIFAddressIn       ;// dma host interface address
wire [31:0]                   dmaHIFReadDataOut     ;// dma host interface read data
wire                          dmaHIFReadDataValid   ;// dma host interface read data valid
wire [ 2:0]                   dmaHIFSize            ;// dma host interface byte enable
wire                          dmaHIFBurstTerminate  ;// dma host interface burst terminate
wire                          dmaHIFReady           ;// dma host interface next data
wire [31:0]                   dmaHIFWriteDataIn     ;// dma host interface write data
wire                          dmaHIFTransComplete   ;// dma host interface transfer complete
wire                          dmaHIFError           ;// dma host interface error


wire                   [19:0] ppduLength;              // PPDU Length
                                                       // This field gives the length of the PPDU for computing time on air.
wire                    [1:0] ppduBW;                  // PPDU Bandwidth
                                                       // This field indicates that that the PPDU should be transmitted at 20,40,80 or 160 MHz.
wire                    [2:0] ppduPreType;             // PPDU Preamble Type
                                                       // This field indicates what type of preamble is transmitted for the frame.
                                                       // The encoding is as follows:
                                                       // 3'b000: Non-HT-Short
                                                       // 3'b001: Non-HT-Long
                                                       // 3'b010: HT-MF
                                                       // 3'b011: HT-GF
                                                       // 3'b100: VHT
wire                    [1:0] ppduNumExtnSS;           // Start Transmission with Number of Extension Spatial Streams      
wire                    [1:0] ppduSTBC;                // Start Transmission with Space Time Block Coding          
wire                          ppduShortGI;             // PPDU Short Guard Interval
                                                       // Indicates that the frame should be transmitted with Short GI.
wire                    [6:0] ppduMCSIndex;            // PPDU LegRate or MCS Index
                                                       // This field indicates the rate at which this PPDU is transmitted. 
wire                          computeDuration;         // Request to perform a Time on Air computation
wire                          computeDurationIn;       // Time on Air computation done
wire                          computeDurationInValid;  // Time on Air computation done valid
wire                   [15:0] timeOnAir;               // Time On Air
                                                       // This field gives the time taken for frame transmission in microseconds (us)
                                                       // computed from parameters programmed in timeOnAirParamReg register.

wire                          timeOnAirValid;          // Time On Air Valid
                                                       // This field is set when the air time computation is completed.

// Interconnect Interrupt Controller
wire                         phyRxStart;               // phyRxStart internal interruption
wire                         phyErr;                   // phyErr internal interruption
wire                         impSecDTIM;               // impSecDTIM internal interruption
wire                         impPriDTIM;               // impPriDTIM internal interruption
wire                         bcnTxDMADead;             // bcnTxDMADead internal interruption
wire                         ac3TxDMADead;             // ac3TxDMADead internal interruption
wire                         ac2TxDMADead;             // ac2TxDMADead internal interruption
wire                         ac1TxDMADead;             // ac1TxDMADead internal interruption
wire                         ac0TxDMADead;             // ac0TxDMADead internal interruption
wire                         ptError;                  // ptError internal interruption
wire                         timSet;                   // timSet internal interruption
wire                         olbcDSSS;                 // olbcDSSS internal interruption
wire                         olbcOFDM;                 // olbcOFDM internal interruption
wire                         rxFIFOOverFlow;           // rxFIFOOverFlow internal interruption
wire                         rxDMAEmpty;               // rxDMAEmpty internal interruption
wire                         macPHYIFOverflow;         // macPHYIFOverflow internal interruption
wire                         rxPayloadDMADead;         // rxPayloadDMADead internal interruption
wire                         rxHeaderDMADead;          // rxHeaderDMADead internal interruption
wire [9:0]                   absTimers;                // absTimer2 internal interruption
wire                         idleInterrupt;            // idleInterrupt internal interruption
wire                         impSecTBTT;               // impSecTBTT internal interruption
wire                         impPriTBTT;               // impPriTBTT internal interruption
wire                         timerRxTrigger;           // timerRxTrigger internal interruption
wire                         bcnTxBufTrigger;          // bcnTxBufTrigger internal interruption
wire                         ac3TxBufTrigger;          // ac3TxBufTrigger internal interruption
wire                         ac2TxBufTrigger;          // ac2TxBufTrigger internal interruption
wire                         ac1TxBufTrigger;          // ac1TxBufTrigger internal interruption
wire                         ac0TxBufTrigger;          // ac0TxBufTrigger internal interruption
wire                         timerTxTrigger;           // timerTxTrigger internal interruption
wire                         txopComplete;             // txopComplete internal interruption
wire                         rdTxTrigger;              // rdTxTrigger internal interruption
wire                         hccaTxTrigger;            // hccaTxTrigger internal interruption
wire                         bcnTxTrigger;             // bcnTxTrigger internal interruption
wire                         ac3TxTrigger;             // ac3TxTrigger internal interruption
wire                         ac2TxTrigger;             // ac2TxTrigger internal interruption
wire                         ac1TxTrigger;             // ac1TxTrigger internal interruption
wire                         ac0TxTrigger;             // ac0TxTrigger internal interruption
wire                         rdProtTrigger;            // rdProtTrigger internal interruption
wire                         hccaProtTrigger;          // hccaProtTrigger internal interruption
wire                         ac3ProtTrigger;           // ac3ProtTrigger internal interruption
wire                         ac2ProtTrigger;           // ac2ProtTrigger internal interruption
wire                         ac1ProtTrigger;           // ac1ProtTrigger internal interruption
wire                         ac0ProtTrigger;           // ac0ProtTrigger internal interruption
wire                         ac3BWDropTrigger;         // ac3BWDropTrigger internal interruption
wire                         ac2BWDropTrigger;         // ac2BWDropTrigger internal interruption
wire                         ac1BWDropTrigger;         // ac1BWDropTrigger internal interruption
wire                         ac0BWDropTrigger;         // ac0BWDropTrigger internal interruption


// Interconnect Control and Status Register and Encryption Engine
wire                         encrRxFIFOReset;          // Encryption RX FIFO reset
wire                         encrRxFIFOResetIn;        // Encryption RX FIFO reset In
wire                         encrRxFIFOResetInValid;   // Encryption RX FIFO reset clear

// Interconnect Control and Status Register and Key search Engine
wire                         keyStoRAMReset;                // Key Storage RAM reset
wire                         keyStoRAMResetIn;              // Key Storage RAM reset In
wire                         keyStoRAMResetInValid;         // Key Storage RAM reset clear
wire                 [31: 0] encrKeyRAMWord0;               // Write Crypto key [31 : 0]
wire                 [31: 0] encrKeyRAMWord1;               // Write Crypto key [63 :32]
wire                 [31: 0] encrKeyRAMWord2;               // Write Crypto key [95 :64]
wire                 [31: 0] encrKeyRAMWord3;               // Write Crypto key [127:96]
`ifdef RW_WAPI_EN
wire                 [31: 0] encrIntKeyRAMWord0;          // Write Integrity Crypto key [31 : 0]
wire                 [31: 0] encrIntKeyRAMWord1;          // Write Integrity Crypto key [63 :32]
wire                 [31: 0] encrIntKeyRAMWord2;          // Write Integrity Crypto key [95 :64]
wire                 [31: 0] encrIntKeyRAMWord3;          // Write Integrity Crypto key [127:96]
`endif //RW_WAPI_EN
wire                 [31: 0] macAddrRAMLow;                 // Write MAC address [31: 0]
wire                 [15: 0] macAddrRAMHigh;                // Write MAC address [47:32]
wire                 [31: 0] encrKeyRAMWord0In;             // Read Crypto key [31 : 0]
wire                 [31: 0] encrKeyRAMWord1In;             // Read Crypto key [63 :32]
wire                 [31: 0] encrKeyRAMWord2In;             // Read Crypto key [95 :64]
wire                 [31: 0] encrKeyRAMWord3In;             // Read Crypto key [127:96]
`ifdef RW_WAPI_EN
wire                 [31: 0] encrIntKeyRAMWord0In;        // Read Integrity Crypto key [31 : 0]
wire                 [31: 0] encrIntKeyRAMWord1In;        // Read Integrity Crypto key [63 :32]
wire                 [31: 0] encrIntKeyRAMWord2In;        // Read Integrity Crypto key [95 :64]
wire                 [31: 0] encrIntKeyRAMWord3In;        // Read Integrity Crypto key [127:96]
`endif //RW_WAPI_EN
wire                 [31: 0] macAddrRAMLowIn;               // Read MAC address [31: 0]
wire                 [15: 0] macAddrRAMHighIn;              // Read MAC address [47:32]
wire                         encrKeyRAMWord0InValid;        // Read Valid Crypto key [31 : 0]
wire                         encrKeyRAMWord1InValid;        // Read Valid Crypto key [63 :32]
wire                         encrKeyRAMWord2InValid;        // Read Valid Crypto key [95 :64]
wire                         encrKeyRAMWord3InValid;        // Read Valid Crypto key [127:96]
`ifdef RW_WAPI_EN
wire                         encrIntKeyRAMWord0InValid;   // Read Valid Integrity Crypto key [31 : 0]
wire                         encrIntKeyRAMWord1InValid;   // Read Valid Integrity Crypto key [63 :32]
wire                         encrIntKeyRAMWord2InValid;   // Read Valid Integrity Crypto key [95 :64]
wire                         encrIntKeyRAMWord3InValid;   // Read Valid Integrity Crypto key [127:96]
`endif //RW_WAPI_EN
wire                         macAddrRAMLowInValid;          // Read Valid MAC address [31: 0]
wire                         macAddrRAMHighInValid;         // Read Valid MAC address [47:32]
wire                 [ 9: 0] keyIndexRAM;                   // Index of Key Storage RAM
wire                         newWrite;                      // Trigger for write operation
wire                         newWriteIn;                    // newWriteIn
wire                         newWriteInValid;               // Clearing newWrite
wire                         newRead;                       // Trigger for read operation
wire                         newReadIn;                     // newReadIn
wire                         newReadInValid;                // Clearing newRead
wire                         newWriteClr_p;                 // Pulse signal to clear the newWrite signal initiated by CSReg
wire                         newReadClr_p;                  // Pulse signal to clear the newRead signal initiated by CSReg
wire                         cLenRAM;                       // Cipher length indication for WEP
wire                         cLenRAMIn;                     // cLenRAM from Key Search Engine
wire                         cLenRAMInValid;                // cLenRAM update
wire                         useDefKeyRAM;                  // Indication for usage of Default Keys.
wire                         useDefKeyRAMIn;                // useDefKeyRAM from Key Search Engine
wire                         useDefKeyRAMInValid;           // useDefKeyRAM update
wire                   [1:0] sppRAM;                        // Indication for handling A-MSDU frames
wire                   [1:0] sppRAMIn;                      // sppRAM from Key Search Engine
wire                         sppRAMInValid;                 // sppRAM update
wire                   [3:0] vlanIDRAM;                     // Virtual LAN ID for searching default key
wire                   [3:0] vlanIDRAMIn;                   // vlanIDRAM from Key Search Engine
wire                         vlanIDRAMInValid;              // vlanIDRAM update
wire                   [2:0] cTypeRAM;                      // Cipher type
wire                   [2:0] cTypeRAMIn;                    // cTypeRAM from Key Search Engine
wire                         cTypeRAMInValid;               // cTypeRAM update

// Interconnect Control and Status Register and BA controller
wire                         baPSBitmapReset;          // PS Bitmap reset
wire                         baPSBitmapResetIn;        // PS Bitmap reset In
wire                         baPSBitmapResetInValid;   // PS Bitmap reset clear

// Interconnect Control and Status Register
wire statussetrxPayloadDMADead;  // rxPayloadDMADead interruption status       
wire statussetrxHeaderDMADead;   // rxHeaderDMADead interruption status       
wire statussetphyRxStart;        // phyRxStart interruption status       
wire statussetphyErr;            // phyErr interruption status           
wire statussetmacPHYIFUnderRun;  // macPHYIFUnderRun interruption status 
wire statussethwErr;             // hwErr interruption status            
wire statussetimpSecDTIM;        // impSecDTIM interruption status       
wire statussetimpPriDTIM;        // impPriDTIM interruption status       
wire statussetbcnTxDMADead;      // bcnTxDMADead interruption status     
wire statussetac3TxDMADead;      // ac3TxDMADead interruption status     
wire statussetac2TxDMADead;      // ac2TxDMADead interruption status     
wire statussetac1TxDMADead;      // ac1TxDMADead interruption status     
wire statussetac0TxDMADead;      // ac0TxDMADead interruption status     
wire statussetptError;           // ptError interruption status          
wire statussettimSet;            // timSet interruption status           
wire statussetolbcDSSS;          // olbcDSSS interruption status         
wire statussetolbcOFDM;          // olbcOFDM interruption status         
wire statussetrxFIFOOverFlow;    // rxFIFOOverFlow interruption status   
wire statussetrxDMAEmpty;        // rxDMAEmpty interruption status       
wire statussetmacPHYIFOverflow;  // macPHYIFOverflow interruption status       
wire statusabsGenTimers;         // absGenTimer interruption status 
wire [9:0]statussetabsTimers;    // absTimers interruption status 
wire statussetidleInterrupt;     // idleInterrupt interruption status    
wire statussetimpSecTBTT;        // impSecTBTT interruption status       
wire statussetimpPriTBTT;        // impPriTBTT interruption status       
wire statussetcounterRxTrigger;  // counterRxTrigger interruption status
wire statussetbaRxTrigger;       // baRxTrigger interruption status
wire statussettimerRxTrigger;    // timerRxTrigger interruption status
wire statussetrxTrigger;         // rxTrigger interruption status
wire statussetbcnTxBufTrigger;   // bcnTxBufTrigger interruption status
wire statussetac3TxBufTrigger;   // ac3TxBufTrigger interruption status
wire statussetac2TxBufTrigger;   // ac2TxBufTrigger interruption status
wire statussetac1TxBufTrigger;   // ac1TxBufTrigger interruption status
wire statussetac0TxBufTrigger;   // ac0TxBufTrigger interruption status
wire statussettimerTxTrigger;    // timerTxTrigger interruption status
wire statussettxopComplete;      // txopComplete interruption status
wire statussetrdTxTrigger;       // rdTxTrigger interruption status
wire statussethccaTxTrigger;     // hccaTxTrigger interruption status
wire statussetbcnTxTrigger;      // bcnTxTrigger interruption status
wire statussetac3TxTrigger;      // ac3TxTrigger interruption status
wire statussetac2TxTrigger;      // ac2TxTrigger interruption status
wire statussetac1TxTrigger;      // ac1TxTrigger interruption status
wire statussetac0TxTrigger;      // ac0TxTrigger interruption status
wire statussetrdProtTrigger;     // rdProtTrigger interruption status
wire statussethccaProtTrigger;   // hccaProtTrigger interruption status
wire statussetac3ProtTrigger;    // ac3ProtTrigger interruption status
wire statussetac2ProtTrigger;    // ac2ProtTrigger interruption status
wire statussetac1ProtTrigger;    // ac1ProtTrigger interruption status
wire statussetac0ProtTrigger;    // ac0ProtTrigger interruption status
wire statussetac3BWDropTrigger;  // ac3BWDropTrigger interruption status
wire statussetac2BWDropTrigger;  // ac2BWDropTrigger interruption status
wire statussetac1BWDropTrigger;  // ac1BWDropTrigger interruption status
wire statussetac0BWDropTrigger;  // ac0BWDropTrigger interruption status

wire  softReset;                   // soft reset sample 
wire  softResetMACCoreClksync;     // soft reset sample resynchronized with macCoreClk
wire  softResetMACCoreClkBacksync; // soft reset sample resynchronized with macPIClk
wire  softResetmpIFClksync;        // soft reset sample resynchronized with mpIFClk
wire  softResetmpIFClkBacksync;    // soft reset sample resynchronized with macPIClk
wire  softResetMACWTClksync;       // soft reset sample resynchronized with macWTClk
wire  softResetMACWTClkBacksync;   // soft reset sample resynchronized with macPIClk
wire  softResetMACPISlaveClksync;  // soft reset sample resynchronized with macPISlaveClk
wire  softResetMacPIClk;           // soft reset sample 
//wire  softResetMacPIClksync;       // soft reset sample 

wire  setphyRxStart;          // set phyRxStart interruption      
wire  setphyErr;              // set phyErr interruption           
wire  setmacPHYIFUnderRun;    // set macPHYIFUnderRun interruption 
wire  sethwErr;               // set hwErr interruption            
wire  setimpSecDTIM;          // set impSecDTIM interruption       
wire  setimpPriDTIM;          // set impPriDTIM interruption       
wire  setbcnTxDMADead;        // set bcnTxDMADead interruption     
wire  setac3TxDMADead;        // set ac3TxDMADead interruption     
wire  setac2TxDMADead;        // set ac2TxDMADead interruption     
wire  setac1TxDMADead;        // set ac1TxDMADead interruption     
wire  setac0TxDMADead;        // set ac0TxDMADead interruption     
wire  setptError;             // set ptError interruption          
wire  settimSet;              // set timSet interruption           
wire  setolbcDSSS;            // set olbcDSSS interruption         
wire  setolbcOFDM;            // set olbcOFDM interruption         
wire  setrxFIFOOverFlow;      // set rxFIFOOverFlow interruption   
wire  setrxDMAEmpty;          // set rxDMAEmpty interruption       
wire  setmacPHYIFOverflow;    // set macPHYIFOverflow interruption       
wire  setrxPayloadDMADead;    // set rxPayloadDMADead interruption       
wire  setrxHeaderDMADead;     // set rxHeaderDMADead interruption       
wire  absGenTimers;           // set All absTimers interruption
wire [9:0] setabsTimers;      // set absTimers interruption
wire  setidleInterrupt;       // set idleInterrupt interruption    
wire  setimpSecTBTT;          // set impSecTBTT interruption       
wire  setimpPriTBTT;          // set impPriTBTT interruption       
wire  clearrxPayloadDMADead;  // clear rxPayloadDMADead interruption
wire  clearrxHeaderDMADead;   // clear rxHeaderDMADead interruption
wire  clearphyRxStart;        // clear phyRxStart interruption      
wire  clearphyErr;            // clear phyErr interruption           
wire  clearmacPHYIFUnderRun;  // clear macPHYIFUnderRun interruption 
wire  clearhwErr;             // clear hwErr interruption            
wire  clearimpSecDTIM;        // clear impSecDTIM interruption       
wire  clearimpPriDTIM;        // clear impPriDTIM interruption       
wire  clearbcnTxDMADead;      // clear bcnTxDMADead interruption     
wire  clearac3TxDMADead;      // clear ac3TxDMADead interruption     
wire  clearac2TxDMADead;      // clear ac2TxDMADead interruption     
wire  clearac1TxDMADead;      // clear ac1TxDMADead interruption     
wire  clearac0TxDMADead;      // clear ac0TxDMADead interruption     
wire  clearptError;           // clear ptError interruption          
wire  cleartimSet;            // clear timSet interruption           
wire  clearolbcDSSS;          // clear olbcDSSS interruption         
wire  clearolbcOFDM;          // clear olbcOFDM interruption         
wire  clearrxFIFOOverFlow;    // clear rxFIFOOverFlow interruption   
wire  clearrxDMAEmpty;        // clear rxDMAEmpty interruption       
wire  clearmacPHYIFOverflow;  // clear macPHYIFOverflow interruption       
wire [9:0] clearabsTimers;    // clear absTimers interruption        
wire  clearidleInterrupt;     // clear idleInterrupt interruption    
wire  clearimpSecTBTT;        // clear impSecTBTT interruption       
wire  clearimpPriTBTT;        // clear impPriTBTT interruption       
wire  masterGenIntEn;         // General Interrupt master Enable
wire  maskphyRxStart;         // phyRxStart output mask interruption
wire  maskphyErr;             // phyErr output mask interruption
wire  maskmacPHYIFUnderRun;   // macPHYIFUnderRun output mask interruption
wire  maskhwErr;              // hwErr output mask interruption
wire  maskimpSecDTIM;         // impSecDTIM output mask interruption
wire  maskimpPriDTIM;         // impPriDTIM output mask interruption
wire  maskbcnTxDMADead;       // bcnTxDMADead output mask interruption
wire  maskac3TxDMADead;       // ac3TxDMADead output mask interruption
wire  maskac2TxDMADead;       // ac2TxDMADead output mask interruption
wire  maskac1TxDMADead;       // ac1TxDMADead output mask interruption
wire  maskac0TxDMADead;       // ac0TxDMADead output mask interruption
wire  maskptError;            // ptError output mask interruption
wire  masktimSet;             // timSet output mask interruption
wire  maskolbcDSSS;           // olbcDSSS output mask interruption
wire  maskolbcOFDM;           // olbcOFDM output mask interruption
wire  maskrxFIFOOverFlow;     // rxFIFOOverFlow output mask interruption
wire  maskrxDMAEmpty;         // rxDMAEmpty output mask interruption
wire  maskmacPHYIFOverflow;   // macPHYIFOverflow output mask interruption
wire  maskrxPayloadDMADead;   // rxPayloadDMADead output mask interruption
wire  maskrxHeaderDMADead;    // rxHeaderDMADead output mask interruption
wire  maskabsGenTimers;       // All absTimers output mask interruption
wire [9:0] maskabsTimers;     // absTimers output mask interruption
wire  maskidleInterrupt;      // idleInterrupt output mask interruption
wire  maskimpSecTBTT;         // impSecTBTT output mask interruption
wire  maskimpPriTBTT;         // impPriTBTT interruption       
wire  setcounterRxTrigger;    // set counterRxTrigger
wire  setbaRxTrigger;         // set baRxTrigger
wire  settimerRxTrigger;      // set timerRxTrigger  
wire  setrxTrigger;           // set rxTrigger       
wire  setbcnTxBufTrigger;        // set bcnTxBufTrigger
wire  setac3TxBufTrigger;        // set ac3TxBufTrigger    
wire  setac2TxBufTrigger;        // set ac2TxBufTrigger    
wire  setac1TxBufTrigger;        // set ac1TxBufTrigger    
wire  setac0TxBufTrigger;        // set ac0TxBufTrigger    
wire  settimerTxTrigger;      // set timerTxTrigger  
wire  settxopComplete;        // set txopComplete    
wire  setrdTxTrigger;         // set rdTxTrigger     
wire  sethccaTxTrigger;       // set hccaTxTrigger   
wire  setbcnTxTrigger;        // set bcnTxTrigger
wire  setac3TxTrigger;        // set ac3TxTrigger    
wire  setac2TxTrigger;        // set ac2TxTrigger    
wire  setac1TxTrigger;        // set ac1TxTrigger    
wire  setac0TxTrigger;        // set ac0TxTrigger    
wire  setrdProtTrigger;       // set rdProtTrigger   
wire  sethccaProtTrigger;     // set hccaProtTrigger 
wire  setac3ProtTrigger;      // set ac3ProtTrigger  
wire  setac2ProtTrigger;      // set ac2ProtTrigger  
wire  setac1ProtTrigger;      // set ac1ProtTrigger  
wire  setac0ProtTrigger;      // set ac0ProtTrigger  
wire  setac3BWDropTrigger;      // set ac3ProtTrigger  
wire  setac2BWDropTrigger;      // set ac2ProtTrigger  
wire  setac1BWDropTrigger;      // set ac1ProtTrigger  
wire  setac0BWDropTrigger;      // set ac0ProtTrigger  
wire  clearcounterRxTrigger;  // clear counterRxTrigger
wire  clearbaRxTrigger;       // clear baRxTrigger
wire  cleartimerRxTrigger;    // clear timerRxTrigger  
wire  clearrxTrigger;         // clear rxTrigger       
wire  clearbcnTxBufTrigger;   // clear clearbcnTxBufTrigger    
wire  clearac3TxBufTrigger;   // clear ac3TxBufTrigger    
wire  clearac2TxBufTrigger;   // clear ac2TxBufTrigger    
wire  clearac1TxBufTrigger;   // clear ac1TxBufTrigger    
wire  clearac0TxBufTrigger;   // clear ac0TxBufTrigger    
wire  cleartimerTxTrigger;    // clear timerTxTrigger  
wire  cleartxopComplete;      // clear txopComplete    
wire  clearrdTxTrigger;       // clear rdTxTrigger     
wire  clearhccaTxTrigger;     // clear hccaTxTrigger   
wire  clearbcnTxTrigger;      // clear clearbcnTxTrigger    
wire  clearac3TxTrigger;      // clear ac3TxTrigger    
wire  clearac2TxTrigger;      // clear ac2TxTrigger    
wire  clearac1TxTrigger;      // clear ac1TxTrigger    
wire  clearac0TxTrigger;      // clear ac0TxTrigger    
wire  clearrdProtTrigger;     // clear rdProtTrigger   
wire  clearhccaProtTrigger;   // clear hccaProtTrigger 
wire  clearac3ProtTrigger;    // clear ac3ProtTrigger  
wire  clearac2ProtTrigger;    // clear ac2ProtTrigger  
wire  clearac1ProtTrigger;    // clear ac1ProtTrigger  
wire  clearac0ProtTrigger;    // clear ac0ProtTrigger  
wire  clearac3BWDropTrigger;  // clear ac3BWRopTrigger  
wire  clearac2BWDropTrigger;  // clear ac2BWRopTrigger  
wire  clearac1BWDropTrigger;  // clear ac1BWRopTrigger  
wire  clearac0BWDropTrigger;  // clear ac0BWRopTrigger  
wire  masterTxRxIntEn;        // TxRx Interruption master enable
wire  masktimerRxTrigger;     // timerRxTrigger output interruption mask 
wire  maskrxTrigger;          // rxTrigger output interruption mask 
wire  maskcounterRxTrigger;   // counterRxTrigger output interruption mask 
wire  maskbaRxTrigger;        // baRxTrigger output interruption mask 
wire  maskac3TxBufTrigger;    // ac3TxBufTrigger output interruption mask 
wire  maskac2TxBufTrigger;    // ac2TxBufTrigger output interruption mask 
wire  maskac1TxBufTrigger;    // ac1TxBufTrigger output interruption mask 
wire  maskac0TxBufTrigger;    // ac0TxBufTrigger output interruption mask 
wire  maskbcnTxBufTrigger;    // bcnTxBufTrigger output interruption mask 
wire  masktimerTxTrigger;     // timerTxTrigger output interruption mask 
wire  masktxopComplete;       // txopComplete output interruption mask 
wire  maskrdTxTrigger;        // rdTxTrigger output interruption mask 
wire  maskhccaTxTrigger;      // hccaTxTrigger output interruption mask 
wire  maskac3TxTrigger;       // ac3TxTrigger output interruption mask 
wire  maskac2TxTrigger;       // ac2TxTrigger output interruption mask 
wire  maskac1TxTrigger;       // ac1TxTrigger output interruption mask 
wire  maskac0TxTrigger;       // ac0TxTrigger output interruption mask 
wire  maskbcnTxTrigger;       // bcnTxTrigger output interruption mask 
wire  maskrdProtTrigger;      // rdProtTrigger output interruption mask 
wire  maskhccaProtTrigger;    // hccaProtTrigger output interruption mask 
wire  maskac3ProtTrigger;     // ac3ProtTrigger output interruption mask 
wire  maskac2ProtTrigger;     // ac2ProtTrigger output interruption mask 
wire  maskac1ProtTrigger;     // ac1ProtTrigger output interruption mask 
wire  maskac0ProtTrigger;     // ac0ProtTrigger output interruption mask 
wire  maskac3BWDropTrigger;   // ac3BWDropTrigger output interruption mask 
wire  maskac2BWDropTrigger;   // ac2BWDropTrigger output interruption mask 
wire  maskac1BWDropTrigger;   // ac1BWDropTrigger output interruption mask 
wire  maskac0BWDropTrigger;   // ac0BWDropTrigger output interruption mask 
wire [15:0] nextTBTT;         // Next TBTT counter in 32 us

wire [15: 0] probeDelay;                 // Probe delay during active scan
wire  [15:0] listenInterval;             // Listen interval
wire         wakeupDTIM;                 // Wakeup DTIM interval
wire  [14:0] atimW;                      // ATIM Window / Auto Wake Up Time Out
wire  [15:0] beaconInt;                  // Beacon interval
wire  [6:0]  impTBTTPeriod;              // Impending TBTT Period
wire         impTBTTIn128Us;             // Impending TBTT Interrupt Period in 128us
wire  [7:0]  noBcnTxTime;                // No Beacon Transmit Time in 16us
wire  [7:0]  dtimPeriod;                 // DTIM Period
wire  [7:0]  cfpPeriod;                  // CFP period
wire  [15:0] cfpMaxDuration;             // CFP Max duration
wire  [31:0] tsfTimerLow;                // TSF[31:0] from register
wire  [31:0] tsfTimerLowIn;              // TSF[31:0] to register
wire         tsfTimerLowInValid;         // Indicates that the tsfTimerLow register has to be updated with tsfTimerLowIn
wire  [31:0] tsfTimerHigh;               // TSF[63:32] from register
wire  [31:0] tsfTimerHighIn;             // TSF[63:32] to register
wire         tsfTimerHighInValid;        // Indicates that the tsfTimerHigh register has to be updated with tsfTimerHighIn
wire  [ 7:0] timOffset;                  // Indicates to the HW the offset, from the first byte of the Beacon frame, 
                                         // at which the first byte of the TIM field is located
wire  [15:0] olbcTimer;                  // OLBC Timer
wire  [7:0]  ofdmCount;                  // OFDM Count
wire  [7:0]  dsssCount;                  // DSSS/CCK Count
wire  [7:0]  macCoreClkFreq;             // MAC Core Clock Frequency
wire  [ 9:0] txRFDelayInMACClk;          // Indicates the TX delay on the RF
wire  [ 9:0] txChainDelayInMACClk;       // Indicates the TX delay on the PHY
wire  [ 7:0] slotTime;                   // slot time for timeout
wire  [15:0] slotTimeInMACClk;           // Slot time in MAC Clocks
wire  [9:0]  macProcDelayInMACClk;       // MAC Processing Delay in MAC Clocks
wire  [9:0]  txDelayRFOnInMACClk;        // Transmit Delay with RF On in MAC Clocks
wire  [9:0]  rxRFDelayInMACClk;          // Receive RF Delay in MAC Clocks
wire  [9:0]  radioWakeUpTime;            // RF wakeup time in 32us resolution
wire  [15:0] sifsBInMACClk;              // SIFS Duration for 802.11b in MAC Clocks
wire  [15:0] sifsAInMACClk;              // SIFS Duration for 802.11a in MAC Clocks
wire  [7:0]  sifsB;                      // SIFS Duration for 802.11b in us
wire  [7:0]  sifsA;                      // SIFS Duration for 802.11a in us
wire  [3:0]  rxCCADelay;                 // CCA Delay
wire  [9:0]  txDMAProcDlyInMACClk;       // Transmit DMA Processing Delay in MAC Clocks
wire  [9:0]  rifsTOInMACClk;             // RIFS TimeOut Duration in MAC Clocks
wire  [9:0]  rifsInMACClk;               // RIFS Duration in MAC Clocks
wire  [7:0]  rifs;                       // RIFS Duration TBD: remove when CSReg update
wire  [7:0]  txAbsoluteTimeout;          // Transmission Absolute Timeout
wire  [7:0]  txPacketTimeout;            // Transmission Packet Timeout
wire  [7:0]  rxAbsoluteTimeout;          // Reception Absolute Timeout
wire  [7:0]  rxPacketTimeout;            // Reception Packet Timeout
wire  [7:0]  rxPayloadUsedCount;         // Received Payload Used Count
wire  [31:0] ccaBusyDurIn;               // CCA Busy Duration
wire         ccaBusyDurInValid;          // Indicates that the ccaBusyDur register has to be updated with ccaBusyDurIn
wire  [31:0] ccaBusyDur;                 // CCA Busy Duration
wire  [31:0] ccaBusyDurSec20In;          // CCA Busy Duration on Secondary 20MHz
wire         ccaBusyDurSec20InValid;     // Indicates that the ccaBusyDurSec20 register has to be updated with ccaBusyDurSec20In
wire  [31:0] ccaBusyDurSec20;            // CCA Busy Duration on Secondary 20MHz
wire  [31:0] ccaBusyDurSec40In;          // CCA Busy Duration on Secondary 40MHz
wire         ccaBusyDurSec40InValid;     // Indicates that the ccaBusyDurSec40 register has to be updated with ccaBusyDurSec40In
wire  [31:0] ccaBusyDurSec40;            // CCA Busy Duration  on Secondary 40MHz
wire  [31:0] ccaBusyDurSec80In;          // CCA Busy Duration on Secondary 80MHz
wire         ccaBusyDurSec80InValid;     // Indicates that the ccaBusyDurSec80 register has to be updated with ccaBusyDurSec80In
wire  [31:0] ccaBusyDurSec80;            // CCA Busy Duration  on Secondary 80MHz
wire  [7:0]  quietCount1;                // Quiet Count 1
wire  [7:0]  quietPeriod1;               // Quiet Period 1
wire  [15:0] quietDuration1;             // Quiet Duration 1
wire  [15:0] quietOffset1;               // Quiet Offset 1
wire  [7:0]  quietCount2;                // Quiet Count 2
wire  [7:0]  quietPeriod2;               // Quiet Period 2
wire  [15:0] quietDuration2;             // Quiet Duration 2
wire  [15:0] quietOffset2;               // Quiet Offset 2
wire         ap;                         // Indicates the type of device (0: STA, 1: AP)
wire         bssType;                    // Indicates the type of BSS (0: IBSS, 1: Infrastructure)
wire         cfpAware;                   // CFP Aware

   
wire   [3:0] txAC0StateMC;               //DMA state for AC0 channel resynchronized on macCoreClk.
wire   [3:0] txAC1StateMC;               //DMA state for AC1 channel resynchronized on macCoreClk.
wire   [3:0] txAC2StateMC;               //DMA state for AC2 channel resynchronized on macCoreClk.
wire   [3:0] txAC3StateMC;               //DMA state for AC3 channel resynchronized on macCoreClk.
wire   [3:0] txBcnStateMC;               //DMA state for Beacon channel resynchronized on macCoreClk.


wire [ 9: 0] radioChirpTime          ;// out

wire [1 : 0] rxPayloadState          ;// DMA state for RX Payload Header channel.
wire [1 : 0] rxHeaderState           ;// DMA state for RX Header Header channel.
wire [1 : 0] txAC3State              ;// DMA state for AC0 channel
wire [1 : 0] txAC2State              ;// DMA state for AC1 channel
wire [1 : 0] txAC1State              ;// DMA state for AC2 channel
wire [1 : 0] txAC0State              ;// DMA state for AC3 channel
wire [1 : 0] txBcnState              ;// DMA state for Beacon channel

wire [1 : 0] txBWAfterDrop;

wire         rxPayNewHeadErr         ;// out
wire         rxHdrNewHeadErr         ;// out
wire         rxPayBusErr             ;// out
wire         rxHdrBusErr             ;// out
wire         rxPayNextPointerErr     ;// out
wire         rxHdrNextPointerErr     ;// out
wire         rxPayUPatternErr        ;// out
wire         rxHdrUPatternErr        ;// out
wire         txAC3NewHeadErr         ;// out
wire         txAC2NewHeadErr         ;// out
wire         txAC1NewHeadErr         ;// out
wire         txAC0NewHeadErr         ;// out
wire         txBcnNewHeadErr         ;// out
wire         txAC3BusErr             ;// out
wire         txAC2BusErr             ;// out
wire         txAC1BusErr             ;// out
wire         txAC0BusErr             ;// out
wire         txBcnBusErr             ;// out
wire         txAC3PTAddressErr       ;// out
wire         txAC2PTAddressErr       ;// out
wire         txAC1PTAddressErr       ;// out
wire         txAC0PTAddressErr       ;// out
wire         txBcnPTAddressErr       ;// out
wire         txAC3NextPointerErr     ;// out
wire         txAC2NextPointerErr     ;// out
wire         txAC1NextPointerErr     ;// out
wire         txAC0NextPointerErr     ;// out
wire         txBcnNextPointerErr     ;// out
wire         txAC3UPatternErr        ;// out
wire         txAC2UPatternErr        ;// out
wire         txAC1UPatternErr        ;// out
wire         txAC0UPatternErr        ;// out
wire         txBcnUPatternErr        ;// out
wire         txAC3LenMismatch        ;// in
wire         txAC2LenMismatch        ;// in
wire         txAC1LenMismatch        ;// in
wire         txAC0LenMismatch        ;// in
wire         txBcnLenMismatch        ;// in
wire         txAC3HaltAfterTXOP      ;// in
wire         txAC2HaltAfterTXOP      ;// in
wire         txAC1HaltAfterTXOP      ;// in
wire         txAC0HaltAfterTXOP      ;// in
wire         txBcnHaltAfterTXOP      ;// in
wire         txAC3EndQ               ;// in
wire         txAC2EndQ               ;// in
wire         txAC1EndQ               ;// in
wire         txAC0EndQ               ;// in
wire         txBcnEndQ               ;// in
wire         txAC3Startup            ;// in
wire         txAC2Startup            ;// in
wire         txAC1Startup            ;// in
wire         txAC0Startup            ;// in
wire         txBcnStartup            ;// in
wire [31: 0] bcnStatusPointer        ;// in
wire [31: 0] ac0StatusPointer        ;// in
wire [31: 0] ac1StatusPointer        ;// in
wire [31: 0] ac2StatusPointer        ;// in
wire [31: 0] ac3StatusPointer        ;// in
wire [31: 0] txCurrentPointer        ;// in
wire [31: 0] rxPayStatPointer        ;// in
wire [31: 0] rxHdrCurrentPointer     ;// in
wire [31: 0] rxHdrStatPointer        ;// in
wire [31: 0] rxPayCurrentPointer     ;// in

wire [31: 0] txBcnHeadPtr            ;// out
wire [31: 0] txAC0HeadPtr            ;// out
wire [31: 0] txAC1HeadPtr            ;// out
wire [31: 0] txAC2HeadPtr            ;// out
wire [31: 0] txAC3HeadPtr            ;// out
wire [ 5: 0] dmaRBDSize              ;// out
wire [ 5: 0] dmaRHDSize              ;// out
wire [ 5: 0] dmaTBDSize              ;// out
wire [ 5: 0] dmaTHDSize              ;// out
wire [ 5: 0] ptEntrySize             ;// out
wire [29: 0] rxHeaderHeadPtr         ;// out
wire         rxHeaderHeadPtrValid    ;// out
wire [29: 0] rxPayloadHeadPtr        ;// out
wire         rxPayloadHeadPtrValid   ;// out
wire [ 7: 0] rxFIFOThreshold         ;// out
wire [ 7: 0] txFIFOThreshold         ;// out

wire [31: 0] macAddrLow              ;// out
wire [15: 0] macAddrHigh             ;// out
wire [31: 0] macAddrLowMask          ;// out
wire [15: 0] macAddrHighMask         ;// out
wire [31: 0] bssIDLow                ;// out
wire [15: 0] bssIDHigh               ;// out
wire [31: 0] bssIDLowMask            ;// out
wire [15: 0] bssIDHighMask           ;// out
wire         rxRIFSEn                ;// out
wire         tsfUpdatedBySW          ;// out
wire         tsfMgtDisable           ;// out
wire [ 2: 0] abgnMode                ;// a/b/g/n Mode

wire         useErrDet               ;// out
wire         useErrRec               ;// in
wire         errInHWLevel3           ;// out
wire         errInTxRxLevel2         ;// out
wire         errInRxLevel1           ;// out
wire         errInTxLevel1           ;// out
wire         clearErrInHWLevel3      ;// out
wire         clearErrInTxRxLevel2    ;// out
wire         clearErrInRxLevel1      ;// out
wire         clearErrInTxLevel1      ;// out
wire         enDuplicateDetection    ;// out
wire [11: 0] aid                     ;// out
wire [ 7: 0] bcnUpdateOffset         ;// out
wire         dtimUpdatedBySW         ;// out

wire [ 7: 0] hccaTriggerTimer        ;// out
wire [ 7: 0] edcaTriggerTimer        ;// out

wire         statussetac3HasData     ;// out
wire         statussetac2HasData     ;// out
wire         statussetac1HasData     ;// out
wire         statussetac0HasData     ;// out
wire         setac3HasData           ;// out
wire         setac2HasData           ;// out
wire         setac1HasData           ;// out
wire         setac0HasData           ;// out
wire         clearac3HasData         ;// out
wire         clearac2HasData         ;// out
wire         clearac1HasData         ;// out
wire         clearac0HasData         ;// out

wire   [9:0] startTxKSRIndex         ;// out
wire   [1:0] startTxAC               ;// out
wire   [1:0] startTxFrmExType        ;// out
wire         startTxShortGI          ;// out
wire         startTxFecCoding        ;// out
wire  [15:0] durControlFrm           ;// out

wire         startTxLSTP             ;// out

wire   [1:0] backoffOffset           ;// out

wire  [25:0] navCounter              ;// out
wire  [25:0] navCounterIn            ;// out
wire         navCounterInValid       ;// out

wire         startTxFrameEx;             // Start Transmission with Frame Exchange
wire         startTxFrameExIn;           // Clear the start Transmission with Frame Exchange
wire         startTxFrameExInValid;      // Clear the start Transmission with Frame Exchange



wire         enableLPClkSwitch;    // Enable the switch to LP clock in DOZE  

wire [ 3: 0] currentState;         // Indicates the current state of the Core. The state encoding is as follows:
                                   // 0000 - IDLE state. This is the default state.
                                   // 0010 - DOZE state
                                   // 0011 - ACTIVE state
                                   // 0100 to 1111  - reserved
wire  [3:0] nextState;             // Indicates the next state of the Core
wire        latchNextState_p;      // Pulse in macPlReg domain to indicate that nextState has been updated
wire  [3:0] nextStateIn;           // When the current state goes back to IDLE, the nextState is also set to IDLE
wire        nextStateInValid;      // Indicates that the nextStateIn value can be capture.

wire        activeClkGating;       // Active Clock Gating This bit is set by SW to turn on 
                                   // active clock gating in HW. When reset; the HW does not 
                                   // perform active clock gating; i.e. does not turn off 
                                   // clocks to save power in ACTIVE state.
wire        macSecClkEn;           // Clock Enable for macSecClk Clocks
wire         disableACKResp;       // Disable ACK Response This bit is set by SW to disable 
                                   // the automatic ACK generation logic in HW.
wire         disableCTSResp;       // Disable CTS Response This bit is set by SW to disable 
                                   // the automatic CTS generation logic in HW.
wire         disableBAResp;        // Disable BA Response This bit is set by SW to disable 
                                   // the automatic BA generation logic in HW.


wire [47:0]  macAddr;                 // MAC Addr
wire [47:0]  macAddrMask;             // MAC Addr mask

wire [47:0]  bssID;                   // BSSID
wire [47:0]  bssIDMask;               // BSSID Mask

wire         excUnencrypted;          // Exclude unencrypted frames
wire         dontDecrypt;             // Don't decrypt frames
wire         acceptMulticast;         // Accept Multicast frames
wire         acceptBroadcast;         // Accept Broadcast frames
wire         acceptOtherBSSID;        // Accept other BSSID frames
wire         acceptErrorFrames;       // Accept error frames
wire         acceptUnicast;           // Accept Unicast frames
wire         acceptMyUnicast;         // Accept frames directed to this device
wire         acceptProbeReq;          // Accept Probe Request frames
wire         acceptProbeResp;         // Accept Probe Response frames
wire         acceptBeacon;            // Accept Beacon frames
wire         acceptAllBeacon;         // Accept all Beacon 
wire         acceptDecryptErrorFrames;// Accept frames which failed decryption
wire         acceptOtherMgmtFrames;   // Accept other management frames
wire         acceptBAR;               // Accept Block Ack Request frames
wire         acceptNotExpectedBA;     // Accept Block Ack Request frames received after SIFS
wire         acceptBA;                // Accept Block Ack frames
wire         acceptPSPoll;            // Accept PS-Poll frames
wire         acceptRTS;               // Accept RTS frames
wire         acceptCTS;               // Accept CTS frames
wire         acceptACK;               // Accept ACK frames
wire         acceptCFEnd;             // Accept CF-End frames
wire         acceptOtherCntrlFrames;  // Accept other control frames
wire         acceptData;              // Accept Data frames
wire         acceptCFWOData;          // Accept CF WithOut Data frames
wire         acceptQData;             // Accept QoS Data frames
wire         acceptQCFWOData;         // Accept QoS CF WithOut Data frames
wire         acceptQoSNull;           // Accept QoS Null frames
wire         acceptOtherDataFrames;   // Accept other Data frames
wire         acceptUnknown;           // Accept unknown frames

// hwFSMReset
wire         hwFSMReset;              // HW FSM Reset
wire         hwFSMResetIn;            // HW FSM Reset In
wire         hwFSMResetInValid;       // HW FSM Reset clear
wire         hwFSMResetmpIFClk;       // HW FSM Reset Resync on mpIFClk
wire         hwFSMResetBackmpIFClk;   // HW FSM Reset Resync on mpIFClk
wire         hwFSMResetPIClk;         // HW FSM Reset Resync on PIFClk
wire         hwFSMResetBackPIClk;     // HW FSM Reset Resync on PIFClk
wire         hwFSMResetWTClk;         // HW FSM Reset Resync on WTFClk
wire         hwFSMResetBackWTClk;     // HW FSM Reset Resync on WTFClk
wire         hwFSMResetCoreClk;       // HW FSM Reset Resync on CoreClk
wire         hwFSMResetAll;           // HW FSM Reset All from all clk domain


wire   [7:0] rxStartDelayMIMO;       // Receive Start Delay for MIMO
wire   [7:0] rxStartDelayShort;      // Receive Start Delay for DSSS/CCK Short preamble
wire   [7:0] rxStartDelayLong;       // Receive Start Delay for DSSS/CCK Long preamble
wire   [7:0] rxStartDelayOFDM;       // Receive Start Delay for OFDM

wire  [31:0] absTimerValue0;         // absolute timer 0 value
wire  [31:0] absTimerValue1;         // absolute timer 1 value
wire  [31:0] absTimerValue2;         // absolute timer 2 value
wire  [31:0] absTimerValue3;         // absolute timer 3 value
wire  [31:0] absTimerValue4;         // absolute timer 4 value
wire  [31:0] absTimerValue5;         // absolute timer 5 value
wire  [31:0] absTimerValue6;         // absolute timer 6 value
wire  [31:0] absTimerValue7;         // absolute timer 7 value
wire  [31:0] absTimerValue8;         // absolute timer 8 value
wire  [31:0] absTimerValue9;         // absolute timer 9 value
wire  [31:0] monotonicCounter1;      // monotonic counter 1
wire  [31:0] monotonicCounterLow2;   // monotonic counter 2
wire  [15:0] monotonicCounterHigh2;  // monotonic counter 2

wire [15:0] txOpLimit0;              // Transmit Opportunity Limit for AC0.
wire [15:0] txOpLimit1;              // Transmit Opportunity Limit for AC1.
wire [15:0] txOpLimit2;              // Transmit Opportunity Limit for AC2.
wire [15:0] txOpLimit3;              // Transmit Opportunity Limit for AC3.
wire [ 3:0] aifsn0;                  // AIFSN for AC0.
wire [ 3:0] aifsn1;                  // AIFSN for AC1.
wire [ 3:0] aifsn2;                  // AIFSN for AC2.
wire [ 3:0] aifsn3;                  // AIFSN for AC3.
wire [ 3:0] cwMin0;                  // Minimum CW for AC0.
wire [ 3:0] cwMin1;                  // Minimum CW for AC1.
wire [ 3:0] cwMin2;                  // Minimum CW for AC2.
wire [ 3:0] cwMin3;                  // Minimum CW for AC3.
wire [ 3:0] cwMax0;                  // Maximum CW for AC0.
wire [ 3:0] cwMax1;                  // Maximum CW for AC1.
wire [ 3:0] cwMax2;                  // Maximum CW for AC2.
wire [ 3:0] cwMax3;                  // Maximum CW for AC3.

wire [ 3:0] currentCW0;              // current Contetion window value
wire [ 3:0] currentCW1;              // current Contetion window value 
wire [ 3:0] currentCW2;              // current Contetion window value
wire [ 3:0] currentCW3;              // current Contetion window value
wire [15:0] ac1MOT;                  // medium occupancy timer of AC0
wire [15:0] ac0MOT;                  // medium occupancy timer of AC1
wire [15:0] ac3MOT;                  // medium occupancy timer of AC2
wire [15:0] ac2MOT;                  // medium occupancy timer of AC3
wire [15:0] miscMOT;                 // Reserved for future use
wire [15:0] hccaQAPMOT;              // Reserved for future use
wire [ 7:0] ac3QSRC;                 // short retry count on AC0
wire [ 7:0] ac2QSRC;                 // short retry count on AC1
wire [ 7:0] ac1QSRC;                 // short retry count on AC2
wire [ 7:0] ac0QSRC;                 // short retry count on AC3
wire [ 7:0] ac3QLRC;                 // long retry count on AC0
wire [ 7:0] ac2QLRC;                 // long retry count on AC1
wire [ 7:0] ac1QLRC;                 // long retry count on AC2
wire [ 7:0] ac0QLRC;                 // long retry count on AC3
wire [ 2:0] activeAC;                // Indicates which AC is currently selected.



wire [ 4:0] rxControlLs;             // RX Controller latched state
wire [ 4:0] rxControlCs;             // RX Controller current state
wire [ 8:0] txControlLs;             // TX Controller latched state
wire [ 8:0] txControlCs;             // TX Controller current state
wire [ 7:0] macControlLs;            // MAC Controller latched state
wire [ 7:0] macControlCs;            // MAC Controller current state


wire        pwrMgt;                // Power Management is enabled for the current
                                   // transmission
wire [ 7:0] dot11LongRetryLimit;   // dot11LongRetryLimit
wire [ 7:0] dot11ShortRetryLimit;  // dot11ShortRetryLimit
wire  [7:0] dsssMaxPwrLevel;           // Maximum Power Level for DSSS/CK frames
wire  [7:0] ofdmMaxPwrLevel;           // Maximum Power Level for OFDM frames
wire  [2:0] maxPHYNtx;             // Maximum Number of TX chains
wire [19:0] maxAllowedLength;      // Filter frames whose length is greater than this length

wire [15:0] cfEndSTBCDur;          // CF-End STBC Duration
wire  [7:0] ctsSTBCDur;            // CTS STBC Duration
wire        dualCTSProt;           // Dual-CTS Protection
wire  [6:0] basicSTBCMCS;          // Basic STBC MCS

wire  [1:0] startTxBW;             // Start Transmission with Bandwidth        
wire        startTxSmoothing;      // Start Transmission with Smoothing
wire  [7:0] startTxAntennaSet;     // Start Transmission with Antenna Set
wire  [7:0] startTxSMMIndex;       // Start Transmission with Spatial Map Matrix Index
wire        startTxPreType;        // Start Transmission with Preamble Type
                                   // 1'b0: SHORT
                                   // 1'b1: LONG
wire  [2:0] startTxFormatMod;      // Start Transmission with Format and Modulation
                                   // 3'b000: NON-HT
                                   // 3'b001: NON-HT-DUP-OFDM
                                   // 3'b010: HT-MF
                                   // 3'b011: HT-GF
                                   // 3'b100: VHT
wire  [1:0] startTxNumExtnSS;      // Start Transmission with Number of Extension Spatial Streams
wire  [1:0] startTxSTBC;           // Start Transmission with Space Time Block Coding        
wire [15:0] bbServiceA;            // Service field when the modulation is OFDM.
wire  [7:0] bbServiceB;            // Service field when the modulation is DSSS/CCK.
wire  [7:0] startTxMCSIndex0;      // Start Transmission with MCS Index 0
wire  [2:0] startTxNTx;            // Start Transmission with Number of Transmit Chains for PPDU        

wire        sendCFEnd;             // Send CF-End
wire        sendCFEndNow;          // Send CF-End Now
wire        sendCFEndNowInValid;   // Indicates that the sendCFEndNow register has to be updated with sendCFEndNowIn
wire        sendCFEndNowIn;        // Give the update value of sendCFEndNow
wire        keepTXOPOpen;          // Keep TXOP Open
wire        remTXOPInDurField;     // Remaining TXOP Indicated in Duration Field

wire        dynBWEn;               // Enable dynamic Bandwidth support
wire        dropToLowerBW;         // Drop To Lower Bandwidth
wire  [2:0] numTryBWAcquisition;   // Number of Tries for 40/80/160MHz TXOP Acquisition
wire  [1:0] defaultBWTXOP;         // Indicates the default bandwidth for TXOP acquisition
wire        defaultBWTXOPV;        // Indicates if the defaultBWTXOP setting is valid.
wire  [7:0] aPPDUMaxTime;          // aPPDU Maximum Time on Air
wire  [1:0] maxSupportedBW;        // max Supported BW

wire        supportLSTP;           // Indicates that the HW support L-SIG TXOP


wire [11:0] bssBasicRateSet;       // BSS Basic Rate Set
wire [15:0] bssBasicHTMCSSetEM;    // BSS Basic HT MCS Set for Equal Modulation
wire  [5:0] bssBasicHTMCSSetUM;    // BSS Basic HT MCS Set for Unequal Modulation
wire [15:0] bssBasicVHTMCSSet;     // BSS Basic VHT MCS Set

wire  [7:0] quietCount1In;         // Quiet Count 1 update 
wire        quietCount1InValid;    // Quiet Count 1 update valid
wire  [7:0] quietPeriod1In;        // Quiet Period 1 update
wire        quietPeriod1InValid;   // Quiet Period 1 update valid
wire [15:0] quietDuration1In;      // Quiet Duration 1 update 
wire        quietDuration1InValid; // Quiet Duration 1 update valid
wire [15:0] quietOffset1In;        // Quiet Offset 1 update
wire        quietOffset1InValid;   // Quiet Offset 1 update valid
wire        quietElement1InValid;  // Indicates that the Quiet 1 registers have to be updated with Quiet 1 In elements

wire  [7:0] quietCount2In;         // Quiet Count 2 update 
wire        quietCount2InValid;    // Quiet Count 2 update valid
wire  [7:0] quietPeriod2In;        // Quiet Period 2 update 
wire        quietPeriod2InValid;   // Quiet Period 2 update valid
wire [15:0] quietDuration2In;      // Quiet Duration 2 update 
wire        quietDuration2InValid; // Quiet Duration 2 update valid
wire [15:0] quietOffset2In;        // Quiet Offset 2 update 
wire        quietOffset2InValid;   // Quiet Offset 2 update valid
wire        quietElement2InValid;  // Indicates that the Quiet 1 registers have to be updated with Quiet 1 In elements

wire  [7:0] dtimPeriodIn;          // DTIM period
wire        dtimPeriodInValid;     // Indicates that the dtimPeriod register has to be updated with dtimPeriodIn
wire  [7:0] cfpPeriodIn;           // CFP period
wire        cfpPeriodInValid;      // Indicates that the cfpPeriod register has to be updated with cfpPeriodIn

// Interconnect between RX Controller and Doze controller
wire        wakeUpFromDoze;        // Wake Up From Doze
wire        wakeUpSW;              // Wake Up SW

wire        timWakeUp;             // AP has data -> wake-up
wire        timSleep;              // AP has no data -> sleep



wire        trigTxAC0;             // Trigger from the MAC Controller to indicate DMA to 
                                   // start fetching frames associated with AC0
wire        trigTxAC1;             // Trigger from the MAC Controller to indicate DMA to
                                   // start fetching frames associated with AC1
wire        trigTxAC2;             // Trigger from the MAC Controller to indicate DMA to 
                                   // start fetching frames associated with AC2
wire        trigTxAC3;             // Trigger from the MAC Controller to indicate DMA to
                                   // start fetching frames associated with AC3
wire        trigTxBcn;             // Trigger from the MAC Controller to indicate DMA to 
                                   // start fetching frames associated with Beacon
wire        frameRxed_p;           // MAC Controller indicates a frame is successfully
                                   // received
wire        rxListProcCsIsIdle;    // rxListProc FSM is in IDLE state                                   
wire        rxFifoAboveThreshold;  // Indication that the current level of FIFO is above the 
                                   // minimum threshold to start moving packets from the 
                                   // RX FIFO to the SRAM.
wire        swRTS_p;               // Asserted high if the current transmitted packet is a
                                   // RTS frame prepared by SW
wire        txMpduDone_p;          // Asserted high after every transmission of MPDU in an 
                                   // AMPDU frame
wire        ampduFrm_p;            // Asserted high if the transmitted packet was an AMPDU
                                   // frame
wire        retryFrame_p;          // If the transmitted frame has to be retried then this
                                   // signal is asserted.
wire        mpduSuccess_p;         // If the transmitted frame was successful. Not asserted
                                   // for RTS frames
wire        mpduFailed_p;          // If the transmitted frame was not successful. Not asserted
                                   // if the RTS frame failed
wire        rtsFailed_p;           // If the transmitted frame was a RTS frame and did not 
                                   // receive a CTS frame within the CTS timeout
wire        rtsSuccess_p;          // If the transmitted frame was a RTS frame and successfully
                                   // received a CTS in reponse.
wire        retryLimitReached_p;   // If the transmitted frame was not successful and has reached  
                                   // the retry limit.Is asserted for both RTS and other MPDU's    
wire [1:0]  transmissionBW;        // Indicates whether the frame was transmitted with 20MHz or 40Mhz BW
wire [7:0]  numMPDURetries;        // Indicates the number of retries for this MPDU. Valid when 
                                   // rtsFailed_p rtsSuccess_p mpduSuccess_p mpduFailed_p or 
                                   // retryLimitReached 
wire [7:0]  numRTSRetries;         // Indicates the number of retries for this RTS. Valid when 
                                   // rtsFailed_p rtsSuccess_p mpduSuccess_p mpduFailed_p or 
                                   // retryLimitReached 
wire [31:0] mediumTimeUsed;        // Indicates the medium Time Used for current transmission
                                   // Valid when DMA status is being updated

wire        rxFrmDiscard;          // Indicate the rxController to discard current frame
wire        rxDescAvailable;       // Indicate that the DMA has all the needed desc for the current rxFrame
wire        rxFlowCntrlEn;         // Indicate the rx Flow Control is enabled
wire [ 3:0] whichDescriptorSW;     // Indicates the value of the partAMorMSDU field Controller

wire        statusUpdated_p;       // Indication from the DMA that status have been updated.
wire        updateDMAStatus_p;     // trigs the DMA Status update.


// TX FIFO
wire        txFIFOAlmostEmpty;            // TX FIFO Almost Empty Indication
wire        txFIFOWr;                     // Read signal to TX FIFO
wire        flushTxFIFO;                  // Flush signal to TX FIFo
wire        txFIFOReset;                  // TX FIFO reset
wire        txFIFOResetIn;                // TX FIFO reset In
wire        txFIFOResetInValid;           // TX FIFO reset clear

// RX FIFO
wire        rxFIFOEmpty;                  // FIFO empty indication
wire [31:0] rxFIFORdData;                 // Data read from RX FIFO
wire  [3:0] rxFIFORdTag;                  // Data from TAG FIFO
wire        rxFIFORead;                   // Read signal to RX FIFO
wire  [5:0] txTagFIFOWrData;              // Data to write to TX TAG FIFO 
wire        rxFIFOAlmEmpty;               // RX FIFO Almst Empty indication
wire        rxFIFOReset;                  // RX FIFO reset
wire        rxFIFOResetIn;                // RX FIFO reset In
wire        rxFIFOResetInValid;           // RX FIFO reset clear
   
// DMA
wire        cleartxAC0NewTail;             //Clear signal to Clear the txAC0NewTail bit in
                                           //the DMA Control register
wire        cleartxAC1NewTail;             //Clear signal to Clear the txAC1NewTail bit in
                                           //the DMA Control register
wire        cleartxAC2NewTail;             //Clear signal to Clear the txAC2NewTail bit in
                                           //the DMA Control register
wire        cleartxAC3NewTail;             //Clear signal to Clear the txAC3NewTail bit in
                                           //the DMA Control register
wire        cleartxBcnNewTail;             //Clear signal to Clear the txBcnNewTail bit in
                                           //the DMA Control register
wire        cleartxAC0NewHead;             //Clear signal to Clear the txAC0NewHead bit in
                                           //the DMA Control register
wire        cleartxAC1NewHead;             //Clear signal to Clear the txAC1NewHead bit in
                                           //the DMA Control register
wire        cleartxAC2NewHead;             //Clear signal to Clear the txAC2NewHead bit in
                                           //the DMA Control register
wire        cleartxAC3NewHead;             //Clear signal to Clear the txAC3NewHead bit in
                                           //the DMA Control register
wire        cleartxBcnNewHead;             //Clear signal to Clear the txBcnNewHead bit in
                                           //the DMA Control register
wire        clearrxHeaderNewTail;          //Clear signal to Clear the rxHeaderNewTail bit in
                                           //the DMA Control register
wire        clearrxHeaderNewHead;          //Clear signal to Clear the rxHeaderNewHead bit in
                                           //the DMA Control register
wire        clearrxPayloadNewTail;         //Clear signal to Clear the rxPayloadNewTail bit in
                                           //the DMA Control register
wire        clearrxPayloadNewHead;         //Clear signal to Clear the rxPayloadNewHead bit in
                                           //the DMA Control register


wire        settxAC0NewTail;              //Set signal to Set the txAC0NewTail bit in
                                          //the DMA Control register
wire        settxAC1NewTail;              //Set signal to Set the txAC1NewTail bit in
                                          //the DMA Control register
wire        settxAC2NewTail;              //Set signal to Set the txAC2NewTail bit in
                                          //the DMA Control register
wire        settxAC3NewTail;              //Set signal to Set the txAC3NewTail bit in
                                          //the DMA Control register
wire        settxBcnNewTail;              //Set signal to Set the txBcnNewTail bit in
                                          //the DMA Control register
wire        settxAC0NewHead;              //Set signal to Set the txAC0NewHead bit in
                                          //the DMA Control register
wire        settxAC1NewHead;              //Set signal to Set the txAC1NewHead bit in
                                          //the DMA Control register
wire        settxAC2NewHead;              //Set signal to Set the txAC2NewHead bit in
                                          //the DMA Control register
wire        settxAC3NewHead;              //Set signal to Set the txAC3NewHead bit in
                                          //the DMA Control register
wire        settxBcnNewHead;              //Set signal to Set the txBcnNewHead bit in
                                          //the DMA Control register
wire        setrxHeaderNewTail;           //Set signal to Set the rxHeaderNewTail bit in
                                          //the DMA Control register
wire        setrxHeaderNewHead;           //Set signal to Set the rxHeaderNewHead bit in
                                          //the DMA Control register
wire        setrxPayloadNewTail;          //Set signal to Set the rxPayloadNewTail bit in
                                          //the DMA Control register
wire        setrxPayloadNewHead;          //Set signal to Set the rxPayloadNewHead bit in
                                          //the DMA Control register


wire        statussettxAC0NewTail;      //Status signal of txAC0NewTail bit in
                                        //the DMA Control register
wire        statussettxAC1NewTail;      //Status signal of txAC1NewTail bit in
                                        //the DMA Control register
wire        statussettxAC2NewTail;      //Status signal of txAC2NewTail bit in
                                        //the DMA Control register
wire        statussettxAC3NewTail;      //Status signal of txAC3NewTail bit in
                                        //the DMA Control register
wire        statussettxBcnNewTail;      //Status signal of txBcnNewTail bit in
                                        //the DMA Control register
wire        statussettxAC0NewHead;      //Status signal of txAC0NewHead bit in
                                        //the DMA Control register
wire        statussettxAC1NewHead;      //Status signal of txAC1NewHead bit in
                                        //the DMA Control register
wire        statussettxAC2NewHead;      //Status signal of txAC2NewHead bit in
                                        //the DMA Control register
wire        statussettxAC3NewHead;      //Status signal of txAC3NewHead bit in
                                        //the DMA Control register
wire        statussettxBcnNewHead;      //Status signal of txBcnNewHead bit in
                                        //the DMA Control register
wire        statussetrxHeaderNewTail;   //Status signal of rxHeaderNewTail bit in
                                        //the DMA Control register
wire        statussetrxHeaderNewHead;   //Status signal of rxHeaderNewHead bit in
                                        //the DMA Control register
wire        statussetrxPayloadNewTail;  //Status signal of rxPayloadNewTail bit in
                                        //the DMA Control register
wire        statussetrxPayloadNewHead;  //Status signal of rxPayloadNewHead bit in
                                        //the DMA Control register


wire        statussethaltAC0AfterTXOP;     //Indicates the status of the haltAC0AfterTXOP bit of the 
                                           //DMA Control register
wire        statussethaltAC1AfterTXOP;     //Indicates the status of the haltAC1AfterTXOP bit of the 
                                           //DMA Control register
wire        statussethaltAC2AfterTXOP;     //Indicates the status of the haltAC2AfterTXOP bit of the 
                                           //DMA Control register
wire        statussethaltAC3AfterTXOP;     //Indicates the status of the haltAC3AfterTXOP bit of the 
                                           //DMA Control register
wire        statussethaltBcnAfterTXOP;     //Indicates the status of the haltBcnAfterTXOP bit of the 
                                           //DMA Control register


wire        sethaltAC0AfterTXOP;     //Set the status of the haltAC0AfterTXOP bit of the 
                                     //DMA Control register
wire        sethaltAC1AfterTXOP;     //Set the status of the haltAC1AfterTXOP bit of the 
                                     //DMA Control register
wire        sethaltAC2AfterTXOP;     //Set the status of the haltAC2AfterTXOP bit of the 
                                     //DMA Control register
wire        sethaltAC3AfterTXOP;     //Set the status of the haltAC3AfterTXOP bit of the 
                                     //DMA Control register
wire        sethaltBcnAfterTXOP;     //Set the status of the haltBcnAfterTXOP bit of the 
                                     //DMA Control register


wire        clearhaltAC0AfterTXOP;   //Clear the status of the haltAC0AfterTXOP bit of the 
                                     //DMA Control register
wire        clearhaltAC1AfterTXOP;   //Clear the status of the haltAC1AfterTXOP bit of the 
                                     //DMA Control register
wire        clearhaltAC2AfterTXOP;   //Clear the status of the haltAC2AfterTXOP bit of the 
                                     //DMA Control register
wire        clearhaltAC3AfterTXOP;   //Clear the status of the haltAC3AfterTXOP bit of the 
                                     //DMA Control register
wire        clearhaltBcnAfterTXOP;   //Clear the status of the haltBcnAfterTXOP bit of the 
                                     //DMA Control register

// Interconnect between mibController module and register
wire        mibTableReset;              // mibTableReset from host indicating
                                        // of mibTableReset bit in
                                        // macCntrl1Reg
wire [9:0]  mibTableIndex;              // MIB Table Index in the MIB Table that needs to be updated.
wire        mibIncrementMode;           // MIB Increment Mode
                                        //   When set; the contents of the MIB entry pointed to 
                                        //   by the mibTableIndex are incremented by the mibValue.
                                        //   When reset; the contents of the MIB entry pointed to 
                                        //   by the mibTableIndex are overwritten by the mibValue.

wire [15:0] mibValue;                   // MIB Value
wire        mibWrite;                   // MIB Write
wire        mibWriteInValid;            // Clear the mibWrite bit
wire        mibWriteIn;                 // mibWrite
wire        mibTableResetIn;            // mibTableResetIn  
wire        mibTableResetInValid;       // Clear the mibTableReset bit


// Interconnect between debugPort module and register
wire [31:0] debugPortRead;               // Reflect to register the value of debugPort output
wire  [7:0] debugPortSel1;               // Debug Port Selection 1
wire  [7:0] debugPortSel2;               // Debug Port Selection 2
wire [15:0] debugPortBackoff;            // Debug Port from BackOff Module
wire [15:0] debugPortBackoff2;            // Debug Port from BackOff Module
wire [15:0] debugPortBackoff3;            // Debug Port from BackOff Module
wire [15:0] debugPortMainFSM1;           // Debug Port with Main FSMs
wire [15:0] debugPortMainFSM2;           // Debug Port with Main FSMs
wire [15:0] debugPortMainFSM;            // Debug Port with Main FSMs
wire [15:0] debugPortDMA1;               // Debug Port DMA 1
wire [15:0] debugPortDMA2;               // Debug Port DMA 2
wire [15:0] debugPortDMA3;               // Debug Port DMA 3
wire [15:0] debugPortDMA4;               // Debug Port DMA 4
wire [15:0] debugPortDMA5;               // Debug Port DMA 5
wire [15:0] debugPortDMA6;               // Debug Port DMA 6
wire [15:0] debugPortMACTimerUnit;       // Debug Port MAC Timer Unit
wire [15:0] debugPortMACTimerUnit2;      // Debug Port MAC Timer Unit
wire [15:0] debugPortMACTimerUnit3;      // Debug Port MAC Timer Unit
wire [15:0] debugPortDeaggregator;       // Debug port from Deaggregator
wire [15:0] debugPortDeaggregator2;      // Debug port from Deaggregator2
wire  [3:0] debugPortDeaggregatorFsm;    // Debug port from Deaggregator FSM
wire [15:0] debugPortRxController;       // Debug port from Rx Controller
wire [15:0] debugPortRxFrameDebug1;      // Debug port for Rx frame debug 1
wire [15:0] debugPortRxFrameDebug2;      // Debug port for Rx frame debug 2
wire [15:0] debugPortTxFrameDebug1;      // Debug port for Tx frame debug 1
wire [15:0] debugPortTxFrameDebug2;      // Debug port for Tx frame debug 2
wire [15:0] debugPortFrameDebug1;        // Debug port for frame debug 1
wire [15:0] debugPortFrameDebug2;        // Debug port for frame debug 2
wire [15:0] debugPortInterrupt;          // Debug port for Interrupts
wire [15:0] debugPortMACPhyIf;           // Debug port from MAC PHY IF
wire [15:0] debugPortMACPhyIf2;           // Debug port from MAC PHY IF
wire [15:0] debugPortBAController;       // Debug port from BA Controller
wire [15:0] debugPortBAController2;      // Debug port from BA Controller
wire [15:0] debugPortBAController3;      // Debug port from BA Controller
wire [15:0] debugPortTxParametersCache;  // Debug Port from TX Parameter Cache
wire [15:0] debugPortMACController1;     // Debug Port 1 from the MAC Controller
wire [15:0] debugPortMediumAccess;       // Debug Port Medium Access
wire [15:0] debugPortNAV;                // Debug Port NAV
wire [15:0] debugPortMACControllerRx;    // DebugPort of the MAC Controller Rx
wire [15:0] debugPortMACControllerTx;    // DebugPort of the MAC Controller Tx
wire [15:0] debugPortBWManagement;       // DebugPort of BW Management
wire [31:0] debugPortEncryptionEngine;   // DebugPort of the EncryptionEngine
`ifdef RW_WAPI_EN
wire [15:0] debugPortWapi;               // DebugPort of Wapi encryption engine
`endif //RW_WAPI_EN
wire [15:0] debugPortDMAStatus;          // DebugPort of DMA Status
wire [15:0] debugPortDMATxStatus;        // txStatusUpdater Debug Port
wire [15:0] debugPortDmaRdWrCtlr;        // DebugPort of DMA Rd Wr Controller
wire [15:0] debugPortTxRxListA;            // DebugPort of DMA Rx List
wire [15:0] debugPortAMPDU;              // Debug Port AMPDU
wire [15:0] debugPortKeySearch;          // Debug Port Key search Engine
wire [15:0] debugPortrxFIFOCntrl;        // Debug Port rxFifoController
wire [15:0] debugPortDecryptFsm;         // Debug Port rxDecryptFSM
wire [15:0] debugPortDozeController;     // DebugPort of the Doze Controller
wire [15:0] debugPortClockGating;            // Debug Port from BackOff Module
wire [15:0] debugPortClock;            // Debug Port from BackOff Module
wire        dmaInternalError;            // Generate a pulse when an internal error occured

wire        rxReqForceDeassertion;       // Force DEassertion of rxReq after each reception of rxEnd_p
wire [31:0] swProf;                      // Debug Port Software Profiling
wire [31:0] swProfInValid;               // Debug Port Software Profiling
wire [31:0] swProfIn;                    // Debug Port Software Profiling
wire [31:0] swSetProf;
wire [31:0] swClearProf;
wire [31:0] statusswSetProf;

`ifdef RW_MAC_MIBCNTL_EN

////////////////////////////////////////
// interconnect MIB HostIF
////////////////////////////////////////
wire [`RW_MIB_ADDR_WIDTH-1 :0] mibAddr;       // Address From Host
wire [`RW_MIB_DATA_WIDTH-1 :0] mibWrData;     // Data from Host to be
                                              // written to RAM
wire                           mibWr;         // Wr Enable signal from host
wire                           mibRd;         // Rd Enable signal from host
wire [`RW_MIB_DATA_WIDTH-1 :0] mibRdData;     // Read Data forwarded to Host
wire                           mibBusy;       // Output MIB busy indication to host

`endif // RW_MAC_MIBCNTL_EN


reg         macPIRxClkEnMC;
reg         macPITxClkEnMC;
wire        platformWakeUpMC;
wire        rxFIFOEmptyWrClk;
wire        txFIFOFlushDone_p;
wire        absGenTimersIntMC;
  
wire        rxTrigger;   //Trigger for receive interrupt
wire        baRxTrigger; //Trigger for BA receive interrupt
wire        counterRxTrigger; //Trigger for count receive interrupt

`ifdef RW_WLAN_COEX_EN                
wire       coexEnable;            // Enable Coex Feature
wire [3:0] coexPTIBKData;         // PTI default value for Data frame transmitted on BK AC
wire [3:0] coexPTIBEData;         // PTI default value for Data frame transmitted on BE AC
wire [3:0] coexPTIVIData;         // PTI default value for Data frame transmitted on VI AC
wire [3:0] coexPTIVOData;         // PTI default value for Data frame transmitted on VO AC
wire [3:0] coexPTIBcnData;        // PTI default value for Data frame transmitted on Beacon AC
wire [3:0] coexPTIMgt;            // PTI default value for Management frame
wire [3:0] coexPTICntl;           // PTI default value for Control frames other than ACK and BA
wire [3:0] coexPTIAck;            // PTI default value for ACK and BA
wire       coexWlanTxAbortGated;  // Gated version of coexWlanTxAbort by coexEnable
wire       coexWlanTxAbortResync; // coexWlanTxAbort resynchronized on macCoreClk 
`endif // RW_WLAN_COEX_EN                



`ifdef RW_SIMU_ON
wire [8:0]  hMSelSpy;
wire [8:0]  hSSelSpy;
wire [31:0] hSAddrSpy;
`endif // RW_SIMU_ON


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////



assign signature      = 32'd`MACHW_SIGNATURE;
//  // VERSION1REG register.
`ifdef RW_MPDU_AC
  assign mac80211MHFormat = 1'd1;
`else
  assign mac80211MHFormat = 1'd0;
`endif
assign coex             = 1'd`MACHW_COEX;
assign wapi             = 1'd`MACHW_WAPI;
assign vht              = 1'd`MACHW_VHT;        
assign tpc              = 1'd`MACHW_TPC;        
assign ht               = 1'd`MACHW_HT;        
assign rce              = 1'd`MACHW_RCE;       
assign ccmp             = 1'd`MACHW_CCMP;      
assign tkip             = 1'd`MACHW_TKIP;      
assign wep              = 1'd`MACHW_WEP;       
assign security         = 1'd`MACHW_SECURITY;  
assign sme              = 1'd`MACHW_SME;       
assign hcca             = 1'd`MACHW_HCCA;      
assign edca             = 1'd`MACHW_EDCA;      
assign qos              = 1'd`MACHW_QOS;       
 // VERSION2REG register.
assign phaseNumber      = 3'd`MACHW_PHASENUMBER;   
assign releaseNumber    = 6'd`MACHW_RELEASENUMBER; 
assign ieRelease        = 1'd`MACHW_IERELEASE;      
assign umVersion        = 7'd`MACHW_UMVERSION ;    
 // BITMAPCNTREG register.
assign bitmapCnt        = 16'd`MACHW_BITMAPCNT; 
 // ERRRECCTRL register.
assign useErrRec      = 1'b0;
// MACERRRECSTATUS1REG register
assign  statuserrInHWLevel3   = 1'b0;
assign  statuserrInTxRxLevel2 = 1'b0;
assign  statuserrInRxLevel1   = 1'b0;
assign  statuserrInTxLevel1   = 1'b0; 
//$port_g RXCNTRLREG register.
assign  enDuplicateDetection  = 1'b0;

// Instanciation of simpleSynchro
// Name of the instance : U_CoreClk_softReset_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_coreClk_softReset_synchro (
                .dstclk             (macCoreClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (softReset),
                .dstdata            (softResetMACCoreClksync)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_CoreClk_softReset_back_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_coreClk_softReset_back_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (softResetMACCoreClksync),
                .dstdata            (softResetMACCoreClkBacksync)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_mpIFClk_softReset_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_mpIFClk_softReset_synchro (
                .dstclk             (mpIFClk),
                .dstresetn          (mpIFClkHardRst_n),
                .srcdata            (softReset),
                .dstdata            (softResetmpIFClksync)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_mpIFClk_softReset_back_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_mpIFClk_softReset_back_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (softResetmpIFClksync),
                .dstdata            (softResetmpIFClkBacksync)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_macWTClk_softReset_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_macWTClk_softReset_synchro (
                .dstclk             (macCoreClk),
                .dstresetn          (macWTClkHardRst_n),
                .srcdata            (softReset),
                .dstdata            (softResetMACWTClksync)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_macWTClk_softReset_back_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_macWTClk_softReset_back_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (softResetMACWTClksync),
                .dstdata            (softResetMACWTClkBacksync)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_macPISlaveClk_softReset_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_macPISlaveClk_softReset_synchro (
                .dstclk             (macPISlaveClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (softResetMACCoreClksync),
                .dstdata            (softResetMACPISlaveClksync)
                );

//// Instanciation of simpleSynchro
//// Name of the instance : U_macPISlaveClk_softReset_synchro
//// Name of the file containing this module : simpleSynchro.v
//simpleSynchro U_macPIClk_softReset_synchro (
//                .dstclk             (macPIClk),
//                .dstresetn          (macPIClkHardRst_n),
//                .srcdata            (softResetMacPIClk),
//                .dstdata            (softResetMacPIClksync)
//                );

assign softResetMacPIClk = softResetMACPISlaveClksync && softResetMACWTClkBacksync && softResetmpIFClkBacksync && softResetMACCoreClkBacksync;

assign macCoreClkSoftRst_n    = !softResetMACCoreClksync;
assign mpIFClkSoftRst_n       = !softResetmpIFClksync;
assign macWTClkSoftRst_n      = !softResetMACWTClksync;
assign macPISlaveClkSoftRst_n = !softResetMACPISlaveClksync;
assign macPIClkSoftRst_n      = !softResetMacPIClk;


always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPIRxClkEnMC <= 1'b1; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macPIRxClkEnMC <= 1'b1; 
  else
  begin 
    if (macCoreRxClkEn || !activeClkGating)
      macPIRxClkEnMC <= 1'b1;
    else if (!macSecClkEn)
      macPIRxClkEnMC <= 1'b0;
    else if (rxListProcCsIsIdle && rxFIFOEmptyWrClk) 
      macPIRxClkEnMC <= 1'b0;
  end
end



always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    macPITxClkEnMC <= 1'b1;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    macPITxClkEnMC <= 1'b1;
  end
  else 
  begin
    if ((trigTxAC0 | trigTxAC1 | trigTxAC2 | trigTxAC3 | trigTxBcn) || macCoreTxClkEn || !activeClkGating)
      macPITxClkEnMC <= 1'b1;
    else if (!macSecClkEn || ((currentState != 4'd3) && activeClkGating))
      macPITxClkEnMC <= 1'b0;
  end
end


// Instanciation of simpleSynchro
// Name of the instance : U_hwFSMResetmpIFClk_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_platformWakeUpMC_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (platformWakeUpMC),
                .dstdata            (platformWakeUp)
                );


// Instanciation of simpleSynchro
// Name of the instance : U_macPIRxClkEnMC_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_macPIRxClkEnMC_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (macPIRxClkEnMC),
                .dstdata            (macPIRxClkEn)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_macPITxClkEnMC_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_macPITxClkEnMC_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (macPITxClkEnMC),
                .dstdata            (macPITxClkEn)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_hwFSMResetmpIFClk_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_hwFSMResetmpIFClk_synchro (
                .dstclk             (mpIFClk),
                .dstresetn          (mpIFClkHardRst_n),
                .srcdata            (hwFSMReset),
                .dstdata            (hwFSMResetmpIFClk)
                );

simpleSynchro U_hwFSMResetmpIFClk_back_synchro (
                .dstclk             (macCoreClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (hwFSMResetmpIFClk),
                .dstdata            (hwFSMResetBackmpIFClk)
                );


// Instanciation of simpleSynchro
// Name of the instance : U_hwFSMResetPIClk_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_hwFSMResetPIClk_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (hwFSMReset),
                .dstdata            (hwFSMResetPIClk)
                );

simpleSynchro U_hwFSMResetPIClk_back_synchro (
                .dstclk             (macCoreClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (hwFSMResetPIClk),
                .dstdata            (hwFSMResetBackPIClk)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_hwFSMResetWTClk_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_hwFSMResetWTClk_synchro (
                .dstclk             (macCoreClk),
                .dstresetn          (macWTClkHardRst_n),
                .srcdata            (hwFSMReset),
                .dstdata            (hwFSMResetWTClk)
                );

simpleSynchro U_hwFSMResetWTClk_back_synchro (
                .dstclk             (macCoreClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (hwFSMResetWTClk),
                .dstdata            (hwFSMResetBackWTClk)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_hwFSMResetCoreClk_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_hwFSMResetCoreClk_synchro (
                .dstclk             (macLPClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (hwFSMResetAll),
                .dstdata            (hwFSMResetCoreClk)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_statusabsGenTimers_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_statusabsGenTimers_synchro (
                .dstclk             (macLPClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (statusabsGenTimers),
                .dstdata            (absGenTimersIntMC)
                );


assign hwFSMResetAll     = hwFSMResetBackmpIFClk && hwFSMResetBackPIClk && hwFSMResetBackWTClk && hwFSMReset;
assign hwFSMResetIn      = !(hwFSMReset && hwFSMResetCoreClk);
assign hwFSMResetInValid =  (hwFSMReset && hwFSMResetCoreClk);

assign dmaSoftRst_n      = !hwFSMResetPIClk    && macPIClkSoftRst_n;
assign mpifSoftRst_n     = !hwFSMResetmpIFClk  && mpIFClkSoftRst_n;
assign txFifoSoftRst_n   = !hwFSMResetCoreClk  && macCoreClkSoftRst_n;

// Instanciation of txFifo
// Name of the instance : U_txFifo
// Name of the file containing this module : txFifo.v
txFifo U_txFifo (
    .macPITxClk                       (macPITxClk),
		.macPIClkHardRst_n                (macPIClkHardRst_n),
		//.macCoreTxClk                     (macCoreTxClk),
		.macCoreTxClk                     (macCoreClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreTxClkSoftRst_n            (txFifoSoftRst_n),
		.txFIFOReset                      (txFIFOReset),
		.txFIFOResetInValid               (txFIFOResetInValid),
		.txFIFOWrFlush                    (txFIFOWrFlush),
		.txFIFOWrite                      (txFIFOWrite),
		.txFIFOWrData                     (txFIFOWrData),
		.txFIFOWrTag                      (txFIFOWrTag),
		.txFIFOAlmostFull                 (txFIFOAlmostFull),
		.txFIFOFull                       (txFIFOFull),
		.txFIFOAlmEmptyWrClk              (txFIFOAlmEmptyWrClk),
		.txFIFOEmptyWrClk                 (txFIFOEmptyWrClk),
		.txFIFORdFlush                    (txFIFORdFlush),
		.txFIFORead                       (txFIFORead),
		.txFIFOReadByFour                 (txFIFOReadByFour),
		.txFIFOReadByTwo                  (txFIFOReadByTwo),
		.txFIFOEmpty                      (txFIFOEmpty),
		.txFIFODataValid                  (txFIFODataValid),
		.txFIFORdData                     (txFIFORdData),
		.txFIFOMPDUDelimiters             (txFIFOMPDUDelimiters),
		.txFIFOReadData                   (txFIFOReadData),
		.txFIFOReadAddr                   (txFIFOReadAddr),
		.txFIFOReadEn                     (txFIFOReadEn),
		.txFIFOWriteAddr                  (txFIFOWriteAddr),
		.txFIFOWriteData                  (txFIFOWriteData),
		.txFIFOWriteEn                    (txFIFOWriteEn)
		);

assign txFIFOResetIn = 1'b0;


// Instanciation of rxFifo
// Name of the instance : U_rxFifo
// Name of the file containing this module : rxFifo.v
rxFifo U_rxFifo (
		.macPIRxClk                       (macPIRxClk),
		.macPIClkHardRst_n                (macPIClkHardRst_n),
		.macCoreRxClk                     (macCoreRxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.rxFIFOReset                      (rxFIFOReset),
		.rxFIFOResetInValid               (rxFIFOResetInValid),
		.rxFIFOWrFlush                    (ZERO_CT),
		.rxFIFOWrite                      (rxFIFOWrite),
		.rxFIFOWrData                     (rxFIFOWrData),
		.rxFIFOWrTag                      (rxFIFOWrTag),
		.rxFIFOAlmostFull                 (rxFIFOAlmostFull),
		.rxFIFOFull                       (rxFIFOFull),
		.rxFIFOAlmEmptyWrClk              (),
		.rxFIFOEmptyWrClk                 (rxFIFOEmptyWrClk),
		.rxFIFORdFlush                    (ZERO_CT),
		.rxFIFORead                       (rxFIFORead),
		.rxFIFOAlmEmpty                   (rxFIFOAlmEmpty),
		.rxFIFOEmpty                      (rxFIFOEmpty),
		.rxFIFODataValid                  (),
		.rxFIFORdData                     (rxFIFORdData),
		.rxFIFOMPDUDelimiters             (rxFIFORdTag),
		.rxFIFOReadData                   (rxFIFOReadData),
		.rxFIFOReadAddr                   (rxFIFOReadAddr),
		.rxFIFOReadEn                     (rxFIFOReadEn),
		.rxFIFOWriteAddr                  (rxFIFOWriteAddr),
		.rxFIFOWriteData                  (rxFIFOWriteData),
		.rxFIFOWriteEn                    (rxFIFOWriteEn)
		);

assign rxFIFOResetIn = 1'b0;
assign ZERO_CT       = 1'b0;

// Instanciation of dmaEngineWrapper
// Name of the instance : U_dmaEngineWrapper
// Name of the file containing this module : dmaEngineWrapper.v
dmaEngineWrapper U_dmaEngineWrapper (
		.macPITxClk                       (macPITxClk),
		.macPIRxClk                       (macPIRxClk),
		.macCoreClk                       (macCoreClk),
		.macCoreRxClk                     (macCoreRxClk),
		.macPIClk                         (macPIClk),
		.macPITxClkHardRst_n              (macPIClkHardRst_n),
		.macPIRxClkHardRst_n              (macPIClkHardRst_n),
		.macPIClkHardRst_n                (macPIClkHardRst_n),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macPITxClkSoftRst_n              (dmaSoftRst_n),
		.macPIRxClkSoftRst_n              (dmaSoftRst_n),
		.macPIClkSoftRst_n                (dmaSoftRst_n),
		.dmaHIFReadDataOut                (dmaHIFReadDataOut),
		.dmaHIFReadDataValid              (dmaHIFReadDataValid),
		.dmaHIFReady                      (dmaHIFReady),
		.dmaHIFTransComplete              (dmaHIFTransComplete),
		.dmaHIFError                      (dmaHIFError),
		.trigTxAC0                        (trigTxAC0),
		.trigTxAC1                        (trigTxAC1),
		.trigTxAC2                        (trigTxAC2),
		.trigTxAC3                        (trigTxAC3),
		.trigTxBcn                        (trigTxBcn),
		.frameRxed_p                      (frameRxed_p),
    .rxListProcCsIsIdle               (rxListProcCsIsIdle),
		.tsfTimerValue                    (tsfTimerLowIn),
		.swRTS_p                          (swRTS_p),
		.txMpduDone_p                     (txMpduDone_p),
		.ampduFrm_p                       (ampduFrm_p),
		.retryFrame_p                     (retryFrame_p),
		.mpduSuccess_p                    (mpduSuccess_p),
		.mpduFailed_p                     (mpduFailed_p),
		.rtsFailed_p                      (rtsFailed_p),
		.rtsSuccess_p                     (rtsSuccess_p),
		.retryLimitReached_p              (retryLimitReached_p),
		.transmissionBW                   (transmissionBW),
		.numMPDURetries                   (numMPDURetries),
		.numRTSRetries                    (numRTSRetries),
    .mediumTimeUsed                   (mediumTimeUsed),
		.rxFrmDiscard                     (rxFrmDiscard),
    .rxDescAvailable                  (rxDescAvailable),
		.rxFlowCntrlEn                    (rxFlowCntrlEn),
		.whichDescriptorSW                (whichDescriptorSW),
		.macPHYIFUnderRun                 (macPHYIFUnderRun),
		.txBcnHeadPtr                     (txBcnHeadPtr),
		.txAC0HeadPtr                     (txAC0HeadPtr),
		.txAC1HeadPtr                     (txAC1HeadPtr),
		.txAC2HeadPtr                     (txAC2HeadPtr),
		.txAC3HeadPtr                     (txAC3HeadPtr),
		.rxHeaderHeadPtr                  (rxHeaderHeadPtr),
		.rxHeaderHeadPtrValid             (rxHeaderHeadPtrValid),
		.rxPayloadHeadPtr                 (rxPayloadHeadPtr),
		.rxPayloadHeadPtrValid            (rxPayloadHeadPtrValid),
		.rxPayloadUsedCount               (rxPayloadUsedCount),
		.txCtrlRegBusy                    (txCtrlRegBusy),
		.txFifoAlmostFull                 (txFIFOAlmostFull),
		.txFifoFull                       (txFIFOFull),
    .txFIFOFlushDone_p                (txFIFOFlushDone_p),
		.txFifoEmpty                      (txFIFOEmptyWrClk),
		.rxFifoEmpty                      (rxFIFOEmpty),
		.rxFIFOAlmEmpty                   (rxFIFOAlmEmpty),
		.rxFifoRdData                     (rxFIFORdData),
		.rxTagFifoRdData                  (rxFIFORdTag),
		.dmaHIFRead                       (dmaHIFRead),
		.dmaHIFWrite                      (dmaHIFWrite),
		.dmaHIFSize                       (dmaHIFSize),
		.dmaHIFAddressIn                  (dmaHIFAddressIn),
		.dmaHIFWriteDataIn                (dmaHIFWriteDataIn),
		.txCtrlRegWr                      (txCtrlRegWr),
		.txCtrlRegPT                      (txCtrlRegPT),
		.txCtrlRegHD                      (txCtrlRegHD),
		.discardPrevHD_p                  (discardPrevHD_p),
		.txAC0State                       (txAC0State),
		.txAC1State                       (txAC1State),
		.txAC2State                       (txAC2State),
		.txAC3State                       (txAC3State),
		.txBcnState                       (txBcnState),
		.rxHeaderState                    (rxHeaderState),
		.rxPayloadState                   (rxPayloadState),
		.txAC0StateMC                     (txAC0StateMC),
		.txAC1StateMC                     (txAC1StateMC),
		.txAC2StateMC                     (txAC2StateMC),
		.txAC3StateMC                     (txAC3StateMC),
		.txBcnStateMC                     (txBcnStateMC),
		.txBcnLenMismatch                 (txBcnLenMismatch),
		.txAC0LenMismatch                 (txAC0LenMismatch),
		.txAC1LenMismatch                 (txAC1LenMismatch),
		.txAC2LenMismatch                 (txAC2LenMismatch),
		.txAC3LenMismatch                 (txAC3LenMismatch),
		.txBcnUPatternErr                 (txBcnUPatternErr),
		.txAC0UPatternErr                 (txAC0UPatternErr),
		.txAC1UPatternErr                 (txAC1UPatternErr),
		.txAC2UPatternErr                 (txAC2UPatternErr),
		.txAC3UPatternErr                 (txAC3UPatternErr),
		.txBcnNextPointerErr              (txBcnNextPointerErr),
		.txAC0NextPointerErr              (txAC0NextPointerErr),
		.txAC1NextPointerErr              (txAC1NextPointerErr),
		.txAC2NextPointerErr              (txAC2NextPointerErr),
		.txAC3NextPointerErr              (txAC3NextPointerErr),
		.txBcnPTAddressErr                (txBcnPTAddressErr),
		.txAC0PTAddressErr                (txAC0PTAddressErr),
		.txAC1PTAddressErr                (txAC1PTAddressErr),
		.txAC2PTAddressErr                (txAC2PTAddressErr),
		.txAC3PTAddressErr                (txAC3PTAddressErr),
		.txBcnBusErr                      (txBcnBusErr),
		.txAC0BusErr                      (txAC0BusErr),
		.txAC1BusErr                      (txAC1BusErr),
		.txAC2BusErr                      (txAC2BusErr),
		.txAC3BusErr                      (txAC3BusErr),
		.txBcnNewHeadErr                  (txBcnNewHeadErr),
		.txAC0NewHeadErr                  (txAC0NewHeadErr),
		.txAC1NewHeadErr                  (txAC1NewHeadErr),
		.txAC2NewHeadErr                  (txAC2NewHeadErr),
		.txAC3NewHeadErr                  (txAC3NewHeadErr),
		.rxHdrUPatternErr                 (rxHdrUPatternErr),
		.rxPayUPatternErr                 (rxPayUPatternErr),
		.rxHdrNextPointerErr              (rxHdrNextPointerErr),
		.rxPayNextPointerErr              (rxPayNextPointerErr),
		.rxHdrBusErr                      (rxHdrBusErr),
		.rxPayBusErr                      (rxPayBusErr),
		.rxHdrNewHeadErr                  (rxHdrNewHeadErr),
		.rxPayNewHeadErr                  (rxPayNewHeadErr),
		.ptError                          (ptError),
		.txBcnStartup                     (txBcnStartup),
		.txAC0Startup                     (txAC0Startup),
		.txAC1Startup                     (txAC1Startup),
		.txAC2Startup                     (txAC2Startup),
		.txAC3Startup                     (txAC3Startup),
		.txBcnEndQ                        (txBcnEndQ),
		.txAC0EndQ                        (txAC0EndQ),
		.txAC1EndQ                        (txAC1EndQ),
		.txAC2EndQ                        (txAC2EndQ),
		.txAC3EndQ                        (txAC3EndQ),
		.txBcnHaltAfterTXOP               (txBcnHaltAfterTXOP),
		.txAC0HaltAfterTXOP               (txAC0HaltAfterTXOP),
		.txAC1HaltAfterTXOP               (txAC1HaltAfterTXOP),
		.txAC2HaltAfterTXOP               (txAC2HaltAfterTXOP),
		.txAC3HaltAfterTXOP               (txAC3HaltAfterTXOP),
		.debugPortDMA1                    (debugPortDMA1),
		.debugPortDMA2                    (debugPortDMA2),
		.debugPortDMA3                    (debugPortDMA3),
		.debugPortDMA4                    (debugPortDMA4),
		.debugPortDMA5                    (debugPortDMA5),
		.debugPortDMA6                    (debugPortDMA6),
		.debugPortDMAStatus               (debugPortDMAStatus),
		.debugPortDMATxStatus             (debugPortDMATxStatus),
    .debugPortTxRxListA               (debugPortTxRxListA),
    .debugPortDmaRdWrCtlr             (debugPortDmaRdWrCtlr),
		.dmaInternalError                 (dmaInternalError),
		.statusUpdated_p                  (statusUpdated_p),
		.updateDMAStatus_p                (updateDMAStatus_p),
		.rxTrig_p                         (rxTrig_p),
		.txFifoWr                         (txFIFOWrite),
		.txFIFOWrData                     (txFIFOWrData),
		.flushTxFifo                      (txFIFOWrFlush),
		.rxFifoRd                         (rxFIFORead),
		.txTagFifoWrData                  (txFIFOWrTag),
		.rxHeaderDMADead                  (rxHeaderDMADead),
		.rxPayloadDMADead                 (rxPayloadDMADead),
		.bcnTxDMADead                     (bcnTxDMADead),
		.ac0TxDMADead                     (ac0TxDMADead),
		.ac1TxDMADead                     (ac1TxDMADead),
		.ac2TxDMADead                     (ac2TxDMADead),
		.ac3TxDMADead                     (ac3TxDMADead),
		.rxDMAEmpty                       (rxDMAEmpty),
    .ac0TxTrigger                     (ac0TxTrigger),
    .ac1TxTrigger                     (ac1TxTrigger),
    .ac2TxTrigger                     (ac2TxTrigger),
    .ac3TxTrigger                     (ac3TxTrigger),
    .bcnTxTrigger                     (bcnTxTrigger),
    .ac0TxBufTrigger                  (ac0TxBufTrigger),
    .ac1TxBufTrigger                  (ac1TxBufTrigger),
    .ac2TxBufTrigger                  (ac2TxBufTrigger),
    .ac3TxBufTrigger                  (ac3TxBufTrigger),
    .bcnTxBufTrigger                  (bcnTxBufTrigger),
		.rxTrigger                        (rxTrigger),
		.counterRxTrigger                 (counterRxTrigger),
		.statussettxAC0NewTail            (statussettxAC0NewTail),
		.statussettxAC1NewTail            (statussettxAC1NewTail),
		.statussettxAC2NewTail            (statussettxAC2NewTail),
		.statussettxAC3NewTail            (statussettxAC3NewTail),
		.statussettxBcnNewTail            (statussettxBcnNewTail),
		.statussettxAC0NewHead            (statussettxAC0NewHead),
		.statussettxAC1NewHead            (statussettxAC1NewHead),
		.statussettxAC2NewHead            (statussettxAC2NewHead),
		.statussettxAC3NewHead            (statussettxAC3NewHead),
		.statussettxBcnNewHead            (statussettxBcnNewHead),
		.statussetrxHeaderNewTail         (statussetrxHeaderNewTail),
		.statussetrxHeaderNewHead         (statussetrxHeaderNewHead),
		.statussetrxPayloadNewTail        (statussetrxPayloadNewTail),
		.statussetrxPayloadNewHead        (statussetrxPayloadNewHead),
		.statussethaltBcnAfterTXOP        (statussethaltBcnAfterTXOP),
		.statussethaltAC3AfterTXOP        (statussethaltAC3AfterTXOP),
		.statussethaltAC2AfterTXOP        (statussethaltAC2AfterTXOP),
		.statussethaltAC1AfterTXOP        (statussethaltAC1AfterTXOP),
		.statussethaltAC0AfterTXOP        (statussethaltAC0AfterTXOP),
		.settxAC0NewTail                  (settxAC0NewTail),
		.settxAC1NewTail                  (settxAC1NewTail),
		.settxAC2NewTail                  (settxAC2NewTail),
		.settxAC3NewTail                  (settxAC3NewTail),
		.settxBcnNewTail                  (settxBcnNewTail),
		.settxAC0NewHead                  (settxAC0NewHead),
		.settxAC1NewHead                  (settxAC1NewHead),
		.settxAC2NewHead                  (settxAC2NewHead),
		.settxAC3NewHead                  (settxAC3NewHead),
		.settxBcnNewHead                  (settxBcnNewHead),
		.setrxHeaderNewTail               (setrxHeaderNewTail),
		.setrxHeaderNewHead               (setrxHeaderNewHead),
		.setrxPayloadNewTail              (setrxPayloadNewTail),
		.setrxPayloadNewHead              (setrxPayloadNewHead),
		.sethaltBcnAfterTXOP              (sethaltBcnAfterTXOP),
		.sethaltAC3AfterTXOP              (sethaltAC3AfterTXOP),
		.sethaltAC2AfterTXOP              (sethaltAC2AfterTXOP),
		.sethaltAC1AfterTXOP              (sethaltAC1AfterTXOP),
		.sethaltAC0AfterTXOP              (sethaltAC0AfterTXOP),
		.cleartxAC0NewTail                (cleartxAC0NewTail),
		.cleartxAC1NewTail                (cleartxAC1NewTail),
		.cleartxAC2NewTail                (cleartxAC2NewTail),
		.cleartxAC3NewTail                (cleartxAC3NewTail),
		.cleartxBcnNewTail                (cleartxBcnNewTail),
		.cleartxAC0NewHead                (cleartxAC0NewHead),
		.cleartxAC1NewHead                (cleartxAC1NewHead),
		.cleartxAC2NewHead                (cleartxAC2NewHead),
		.cleartxAC3NewHead                (cleartxAC3NewHead),
		.cleartxBcnNewHead                (cleartxBcnNewHead),
		.clearrxHeaderNewTail             (clearrxHeaderNewTail),
		.clearrxHeaderNewHead             (clearrxHeaderNewHead),
		.clearrxPayloadNewTail            (clearrxPayloadNewTail),
		.clearrxPayloadNewHead            (clearrxPayloadNewHead),
		.clearhaltBcnAfterTXOP            (clearhaltBcnAfterTXOP),
		.clearhaltAC3AfterTXOP            (clearhaltAC3AfterTXOP),
		.clearhaltAC2AfterTXOP            (clearhaltAC2AfterTXOP),
		.clearhaltAC1AfterTXOP            (clearhaltAC1AfterTXOP),
		.clearhaltAC0AfterTXOP            (clearhaltAC0AfterTXOP),
		.ac0StatusPointer                 (ac0StatusPointer),
		.ac1StatusPointer                 (ac1StatusPointer),
		.ac2StatusPointer                 (ac2StatusPointer),
		.ac3StatusPointer                 (ac3StatusPointer),
 		.txCurrentPointer                 (txCurrentPointer),
		.bcnStatusPointer                 (bcnStatusPointer),
		.rxHdrStatPointer                 (rxHdrStatPointer),
		.rxPayStatPointer                 (rxPayStatPointer),
		.rxPayCurrentPointer              (rxPayCurrentPointer)
		);

assign rxFifoAboveThreshold = !rxFIFOAlmEmpty;
assign txCtrlRegData        = dmaHIFReadDataOut;


// Instanciation of hostIfAhb
// Name of the instance : U_hostIfAhb
// Name of the file containing this module : hostIfAhb.v
hostIfAhb U_hostIfAhb (
                .macPIClkHardRst_n                (macPIClkHardRst_n),
                .macCoreClkHardRst_n              (macCoreClkHardRst_n),
                .macPIClk                         (macPISlaveClk),
                .macCoreClk                       (macCoreClk),
                .hSAddr                           (hSAddr),
                .hSTrans                          (hSTrans),
                .hSWrite                          (hSWrite),
                .hSSize                           (hSSize),
                .hSWData                          (hSWData),
                .hSSel                            (hSSel),
                .hSReadyIn                        (hSReadyIn),
                .hSRData                          (hSRData),
                .hSReadyOut                       (hSReadyOut),
                .hSResp                           (hSResp),
                .hMBusReq                         (hMBusReq),
                .hMLock                           (hMLock),
                .hMGrant                          (hMGrant),
                .hMAddr                           (hMAddr),
                .hMTrans                          (hMTrans),
                .hMWrite                          (hMWrite),
                .hMSize                           (hMSize),
                .hMBurst                          (hMBurst),
                .hMProt                           (hMProt),
                .hMWData                          (hMWData),
                .hMRData                          (hMRData),
                .hMReady                          (hMReady),
                .hMResp                           (hMResp),
              `ifdef RW_MAC_MIBCNTL_EN
                .mibRdData                        (mibRdData),
                .mibBusy                          (mibBusy),
                .mibAddr                          (mibAddr),
                .mibWrData                        (mibWrData),
                .mibWr                            (mibWr),
                .mibRd                            (mibRd),
              `endif // RW_MAC_MIBCNTL_EN
                .regReadyIn                       (regReadyIn),
                .regReadData                      (regReadData),
                .regWrite                         (regWrite),
                .regRead                          (regRead),
                .regAddr                          (regAddr),
                .regWriteData                     (regWriteData),
                .dmaHIFRead                       (dmaHIFRead),
                .dmaHIFWrite                      (dmaHIFWrite),
                .dmaHIFAddressIn                  (dmaHIFAddressIn),
                .dmaHIFReadDataOut                (dmaHIFReadDataOut),
                .dmaHIFReadDataValid              (dmaHIFReadDataValid),
                .dmaHIFSize                       (dmaHIFSize),
                .dmaHIFReady                      (dmaHIFReady),
                .dmaHIFWriteDataIn                (dmaHIFWriteDataIn),
                .dmaHIFTransComplete              (dmaHIFTransComplete),
                .dmaHIFError                      (dmaHIFError)
                );

assign hwErr = macPHYIFUnderRun;
assign timSet = 1'b0; //$todo
assign rdTxTrigger = 1'b0; //$todo
assign hccaTxTrigger = 1'b0; //$todo
assign rdProtTrigger = 1'b0; //$todo
assign hccaProtTrigger = 1'b0; //$todo


// Instanciation of intCtrl
// Name of the instance : U_intCtrl
// Name of the file containing this module : intCtrl.v
intCtrl U_intCtrl (
		.macPIClk                         (macPISlaveClk),
		.macPIClkHardRst_n                (macPIClkHardRst_n),
		.masterGenIntEn                   (masterGenIntEn),
		.setphyRxStart                    (setphyRxStart),
		.setphyErr                        (setphyErr),
		.setmacPHYIFUnderRun              (setmacPHYIFUnderRun),
		.sethwErr                         (sethwErr),
		.setimpSecDTIM                    (setimpSecDTIM),
		.setimpPriDTIM                    (setimpPriDTIM),
		.setbcnTxDMADead                  (setbcnTxDMADead),
		.setac3TxDMADead                  (setac3TxDMADead),
		.setac2TxDMADead                  (setac2TxDMADead),
		.setac1TxDMADead                  (setac1TxDMADead),
		.setac0TxDMADead                  (setac0TxDMADead),
		.setptError                       (setptError),
		.settimSet                        (settimSet),
		.setolbcDSSS                      (setolbcDSSS),
		.setolbcOFDM                      (setolbcOFDM),
		.setrxFIFOOverFlow                (setrxFIFOOverFlow),
		.setrxDMAEmpty                    (setrxDMAEmpty),
		.setmacPHYIFOverflow              (setmacPHYIFOverflow),
		.setrxPayloadDMADead              (setrxPayloadDMADead),
		.setrxHeaderDMADead               (setrxHeaderDMADead),
    .setabsTimers                     (setabsTimers),
    .absGenTimers                     (absGenTimers),
		.setidleInterrupt                 (setidleInterrupt),
		.setimpSecTBTT                    (setimpSecTBTT),
		.setimpPriTBTT                    (setimpPriTBTT),
		.clearphyRxStart                  (clearphyRxStart),
		.clearphyErr                      (clearphyErr),
		.clearmacPHYIFUnderRun            (clearmacPHYIFUnderRun),
		.clearhwErr                       (clearhwErr),
		.clearimpSecDTIM                  (clearimpSecDTIM),
		.clearimpPriDTIM                  (clearimpPriDTIM),
		.clearbcnTxDMADead                (clearbcnTxDMADead),
		.clearac3TxDMADead                (clearac3TxDMADead),
		.clearac2TxDMADead                (clearac2TxDMADead),
		.clearac1TxDMADead                (clearac1TxDMADead),
		.clearac0TxDMADead                (clearac0TxDMADead),
		.clearptError                     (clearptError),
		.cleartimSet                      (cleartimSet),
		.clearolbcDSSS                    (clearolbcDSSS),
		.clearolbcOFDM                    (clearolbcOFDM),
		.clearrxFIFOOverFlow              (clearrxFIFOOverFlow),
		.clearrxDMAEmpty                  (clearrxDMAEmpty),
		.clearmacPHYIFOverflow            (clearmacPHYIFOverflow),
		.clearrxPayloadDMADead            (clearrxPayloadDMADead),
		.clearrxHeaderDMADead             (clearrxHeaderDMADead),
    .clearabsTimers                   (clearabsTimers),
		.clearidleInterrupt               (clearidleInterrupt),
		.clearimpSecTBTT                  (clearimpSecTBTT),
		.clearimpPriTBTT                  (clearimpPriTBTT),
		.maskphyRxStart                   (maskphyRxStart),
		.maskphyErr                       (maskphyErr),
		.maskmacPHYIFUnderRun             (maskmacPHYIFUnderRun),
		.maskhwErr                        (maskhwErr),
		.maskimpSecDTIM                   (maskimpSecDTIM),
		.maskimpPriDTIM                   (maskimpPriDTIM),
		.maskbcnTxDMADead                 (maskbcnTxDMADead),
		.maskac3TxDMADead                 (maskac3TxDMADead),
		.maskac2TxDMADead                 (maskac2TxDMADead),
		.maskac1TxDMADead                 (maskac1TxDMADead),
		.maskac0TxDMADead                 (maskac0TxDMADead),
		.maskptError                      (maskptError),
		.masktimSet                       (masktimSet),
		.maskolbcDSSS                     (maskolbcDSSS),
		.maskolbcOFDM                     (maskolbcOFDM),
		.maskrxFIFOOverFlow               (maskrxFIFOOverFlow),
		.maskrxDMAEmpty                   (maskrxDMAEmpty),
		.maskmacPHYIFOverflow             (maskmacPHYIFOverflow),
		.maskrxPayloadDMADead             (maskrxPayloadDMADead),
		.maskrxHeaderDMADead              (maskrxHeaderDMADead),
    .maskabsTimers                    (maskabsTimers),
    .maskabsGenTimers                 (maskabsGenTimers),
		.maskidleInterrupt                (maskidleInterrupt),
		.maskimpSecTBTT                   (maskimpSecTBTT),
		.maskimpPriTBTT                   (maskimpPriTBTT),
		.statussetphyRxStart              (statussetphyRxStart),
		.statussetphyErr                  (statussetphyErr),
		.statussetmacPHYIFUnderRun        (statussetmacPHYIFUnderRun),
		.statussethwErr                   (statussethwErr),
		.statussetimpSecDTIM              (statussetimpSecDTIM),
		.statussetimpPriDTIM              (statussetimpPriDTIM),
		.statussetbcnTxDMADead            (statussetbcnTxDMADead),
		.statussetac3TxDMADead            (statussetac3TxDMADead),
		.statussetac2TxDMADead            (statussetac2TxDMADead),
		.statussetac1TxDMADead            (statussetac1TxDMADead),
		.statussetac0TxDMADead            (statussetac0TxDMADead),
		.statussetptError                 (statussetptError),
		.statussettimSet                  (statussettimSet),
		.statussetolbcDSSS                (statussetolbcDSSS),
		.statussetolbcOFDM                (statussetolbcOFDM),
		.statussetrxFIFOOverFlow          (statussetrxFIFOOverFlow),
		.statussetrxDMAEmpty              (statussetrxDMAEmpty),
		.statussetmacPHYIFOverflow        (statussetmacPHYIFOverflow),
		.statussetrxPayloadDMADead        (statussetrxPayloadDMADead),
		.statussetrxHeaderDMADead         (statussetrxHeaderDMADead),
        .statussetabsTimers               (statussetabsTimers),
    .statusabsGenTimers               (statusabsGenTimers),
		.statussetidleInterrupt           (statussetidleInterrupt),
		.statussetimpSecTBTT              (statussetimpSecTBTT),
		.statussetimpPriTBTT              (statussetimpPriTBTT),
		.masterTxRxIntEn                  (masterTxRxIntEn),
		.settimerRxTrigger                (settimerRxTrigger),
		.setrxTrigger                     (setrxTrigger),
		.setcounterRxTrigger              (setcounterRxTrigger),
		.setbaRxTrigger                   (setbaRxTrigger),
    .setac3TxBufTrigger               (setac3TxBufTrigger),
    .setac2TxBufTrigger               (setac2TxBufTrigger),
    .setac1TxBufTrigger               (setac1TxBufTrigger),
    .setac0TxBufTrigger               (setac0TxBufTrigger),
    .setbcnTxBufTrigger               (setbcnTxBufTrigger),
		.settimerTxTrigger                (settimerTxTrigger),
		.settxopComplete                  (settxopComplete),
		.setrdTxTrigger                   (setrdTxTrigger),
		.sethccaTxTrigger                 (sethccaTxTrigger),
		.setac3TxTrigger                  (setac3TxTrigger),
		.setac2TxTrigger                  (setac2TxTrigger),
		.setac1TxTrigger                  (setac1TxTrigger),
		.setac0TxTrigger                  (setac0TxTrigger),
    .setac3BWDropTrigger              (setac3BWDropTrigger),
    .setac2BWDropTrigger              (setac2BWDropTrigger),
    .setac1BWDropTrigger              (setac1BWDropTrigger),
    .setac0BWDropTrigger              (setac0BWDropTrigger),
		.setbcnTxTrigger                  (setbcnTxTrigger),
		.setrdProtTrigger                 (setrdProtTrigger),
		.sethccaProtTrigger               (sethccaProtTrigger),
		.setac3ProtTrigger                (setac3ProtTrigger),
		.setac2ProtTrigger                (setac2ProtTrigger),
		.setac1ProtTrigger                (setac1ProtTrigger),
		.setac0ProtTrigger                (setac0ProtTrigger),
		.cleartimerRxTrigger              (cleartimerRxTrigger),
		.clearrxTrigger                   (clearrxTrigger),
		.clearcounterRxTrigger            (clearcounterRxTrigger),
		.clearbaRxTrigger                 (clearbaRxTrigger),
    .clearac3TxBufTrigger             (clearac3TxBufTrigger),
    .clearac2TxBufTrigger             (clearac2TxBufTrigger),
    .clearac1TxBufTrigger             (clearac1TxBufTrigger),
    .clearac0TxBufTrigger             (clearac0TxBufTrigger),
    .clearbcnTxBufTrigger             (clearbcnTxBufTrigger),
		.cleartimerTxTrigger              (cleartimerTxTrigger),
		.cleartxopComplete                (cleartxopComplete),
		.clearrdTxTrigger                 (clearrdTxTrigger),
		.clearhccaTxTrigger               (clearhccaTxTrigger),
		.clearac3TxTrigger                (clearac3TxTrigger),
		.clearac2TxTrigger                (clearac2TxTrigger),
		.clearac1TxTrigger                (clearac1TxTrigger),
		.clearac0TxTrigger                (clearac0TxTrigger),
    .clearac3BWDropTrigger            (clearac3BWDropTrigger),
    .clearac2BWDropTrigger            (clearac2BWDropTrigger),
    .clearac1BWDropTrigger            (clearac1BWDropTrigger),
    .clearac0BWDropTrigger            (clearac0BWDropTrigger),
		.clearbcnTxTrigger                (clearbcnTxTrigger),
		.clearrdProtTrigger               (clearrdProtTrigger),
		.clearhccaProtTrigger             (clearhccaProtTrigger),
		.clearac3ProtTrigger              (clearac3ProtTrigger),
		.clearac2ProtTrigger              (clearac2ProtTrigger),
		.clearac1ProtTrigger              (clearac1ProtTrigger),
		.clearac0ProtTrigger              (clearac0ProtTrigger),
		.masktimerRxTrigger               (masktimerRxTrigger),
		.maskrxTrigger                    (maskrxTrigger),
		.maskcounterRxTrigger             (maskcounterRxTrigger),
		.maskbaRxTrigger                  (maskbaRxTrigger),
    .maskac3TxBufTrigger              (maskac3TxBufTrigger),
    .maskac2TxBufTrigger              (maskac2TxBufTrigger),
    .maskac1TxBufTrigger              (maskac1TxBufTrigger),
    .maskac0TxBufTrigger              (maskac0TxBufTrigger),
    .maskbcnTxBufTrigger              (maskbcnTxBufTrigger),
		.masktimerTxTrigger               (masktimerTxTrigger),
		.masktxopComplete                 (masktxopComplete),
		.maskrdTxTrigger                  (maskrdTxTrigger),
		.maskhccaTxTrigger                (maskhccaTxTrigger),
		.maskac3TxTrigger                 (maskac3TxTrigger),
		.maskac2TxTrigger                 (maskac2TxTrigger),
		.maskac1TxTrigger                 (maskac1TxTrigger),
		.maskac0TxTrigger                 (maskac0TxTrigger),
    .maskac3BWDropTrigger             (maskac3BWDropTrigger),
    .maskac2BWDropTrigger             (maskac2BWDropTrigger),
    .maskac1BWDropTrigger             (maskac1BWDropTrigger),
    .maskac0BWDropTrigger             (maskac0BWDropTrigger),
		.maskbcnTxTrigger                 (maskbcnTxTrigger),
		.maskrdProtTrigger                (maskrdProtTrigger),
		.maskhccaProtTrigger              (maskhccaProtTrigger),
		.maskac3ProtTrigger               (maskac3ProtTrigger),
		.maskac2ProtTrigger               (maskac2ProtTrigger),
		.maskac1ProtTrigger               (maskac1ProtTrigger),
		.maskac0ProtTrigger               (maskac0ProtTrigger),
		.statussettimerRxTrigger          (statussettimerRxTrigger),
		.statussetrxTrigger               (statussetrxTrigger),
		.statussetcounterRxTrigger        (statussetcounterRxTrigger),
		.statussetbaRxTrigger             (statussetbaRxTrigger),
    .statussetac3TxBufTrigger         (statussetac3TxBufTrigger),
    .statussetac2TxBufTrigger         (statussetac2TxBufTrigger),
    .statussetac1TxBufTrigger         (statussetac1TxBufTrigger),
    .statussetac0TxBufTrigger         (statussetac0TxBufTrigger),
    .statussetbcnTxBufTrigger         (statussetbcnTxBufTrigger),
		.statussettimerTxTrigger          (statussettimerTxTrigger),
		.statussettxopComplete            (statussettxopComplete),
		.statussetrdTxTrigger             (statussetrdTxTrigger),
		.statussethccaTxTrigger           (statussethccaTxTrigger),
		.statussetac3TxTrigger            (statussetac3TxTrigger),
		.statussetac2TxTrigger            (statussetac2TxTrigger),
		.statussetac1TxTrigger            (statussetac1TxTrigger),
		.statussetac0TxTrigger            (statussetac0TxTrigger),
		.statussetbcnTxTrigger            (statussetbcnTxTrigger),
		.statussetrdProtTrigger           (statussetrdProtTrigger),
		.statussethccaProtTrigger         (statussethccaProtTrigger),
		.statussetac3ProtTrigger          (statussetac3ProtTrigger),
		.statussetac2ProtTrigger          (statussetac2ProtTrigger),
		.statussetac1ProtTrigger          (statussetac1ProtTrigger),
		.statussetac0ProtTrigger          (statussetac0ProtTrigger),
    .statussetac3BWDropTrigger        (statussetac3BWDropTrigger),
    .statussetac2BWDropTrigger        (statussetac2BWDropTrigger),
    .statussetac1BWDropTrigger        (statussetac1BWDropTrigger),
    .statussetac0BWDropTrigger        (statussetac0BWDropTrigger),
		.phyRxStart                       (phyRxStart),
		.phyErr                           (phyErr),
		.macPHYIFUnderRun                 (macPHYIFUnderRun),
		.hwErr                            (hwErr),
		.impSecDTIM                       (impSecDTIM),
		.impPriDTIM                       (impPriDTIM),
		.bcnTxDMADead                     (bcnTxDMADead),
		.ac3TxDMADead                     (ac3TxDMADead),
		.ac2TxDMADead                     (ac2TxDMADead),
		.ac1TxDMADead                     (ac1TxDMADead),
		.ac0TxDMADead                     (ac0TxDMADead),
		.ptError                          (ptError),
		.timSet                           (timSet),
		.olbcDSSS                         (olbcDSSS),
		.olbcOFDM                         (olbcOFDM),
		.rxFIFOOverFlow                   (rxFIFOOverFlow),
		.rxDMAEmpty                       (rxDMAEmpty),
		.macPHYIFOverflow                 (macPHYIFOverflow),
		.rxPayloadDMADead                 (rxPayloadDMADead),
		.rxHeaderDMADead                  (rxHeaderDMADead),
    .absTimers                        (absTimers),
		.idleInterrupt                    (idleInterrupt),
		.impSecTBTT                       (impSecTBTT),
		.impPriTBTT                       (impPriTBTT),
		.timerRxTrigger                   (timerRxTrigger),
		.rxTrigger                        (rxTrigger),
		.counterRxTrigger                 (counterRxTrigger),
		.baRxTrigger                      (baRxTrigger),
    .ac3TxBufTrigger                  (ac3TxBufTrigger),
    .ac2TxBufTrigger                  (ac2TxBufTrigger),
    .ac1TxBufTrigger                  (ac1TxBufTrigger),
    .ac0TxBufTrigger                  (ac0TxBufTrigger),
    .bcnTxBufTrigger                  (bcnTxBufTrigger),
		.timerTxTrigger                   (timerTxTrigger),
		.txopComplete                     (txopComplete),
		.rdTxTrigger                      (rdTxTrigger),
		.hccaTxTrigger                    (hccaTxTrigger),
		.ac3TxTrigger                     (ac3TxTrigger),
		.ac2TxTrigger                     (ac2TxTrigger),
		.ac1TxTrigger                     (ac1TxTrigger),
		.ac0TxTrigger                     (ac0TxTrigger),
		.bcnTxTrigger                     (bcnTxTrigger),
		.rdProtTrigger                    (rdProtTrigger),
		.hccaProtTrigger                  (hccaProtTrigger),
		.ac3ProtTrigger                   (ac3ProtTrigger),
		.ac2ProtTrigger                   (ac2ProtTrigger),
		.ac1ProtTrigger                   (ac1ProtTrigger),
		.ac0ProtTrigger                   (ac0ProtTrigger),
    .ac3BWDropTrigger                 (ac3BWDropTrigger),
    .ac2BWDropTrigger                 (ac2BWDropTrigger),
    .ac1BWDropTrigger                 (ac1BWDropTrigger),
    .ac0BWDropTrigger                 (ac0BWDropTrigger),
		.intGen_n                         (intGen_n),
		.intProtTrigger_n                 (intProtTrigger_n),
		.intTxTrigger_n                   (intTxTrigger_n),
		.intRxTrigger_n                   (intRxTrigger_n),
		.intTxRxMisc_n                    (intTxRxMisc_n),
		.intTxRxTimer_n                   (intTxRxTimer_n)
		);



assign phyRxStart = macPhyIfRxStart_p;
assign phyErr     = mpIfTxErr_p;

// Instanciation of macCSReg
// Name of the instance : U_macCSReg
// Name of the file containing this module : macCSReg.v
macCSReg U_macCSReg (
		.macPIClk                         (macPISlaveClk),
		.macPIClkHardRst_n                (macPIClkHardRst_n),
		.macPIClkSoftRst_n                (macPIClkSoftRst_n),
		.macCoreClk                       (macCoreClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (macCoreClkSoftRst_n),
		.nextStateIn                      (nextStateIn),
		.nextStateInValid                 (nextStateInValid),
		.currentState                     (currentState),
		.statussetrxPayloadDMADead        (statussetrxPayloadDMADead),
		.statussetrxHeaderDMADead         (statussetrxHeaderDMADead),
		.statussetphyRxStart              (statussetphyRxStart),
		.statussetphyErr                  (statussetphyErr),
		.statussetmacPHYIFUnderRun        (statussetmacPHYIFUnderRun),
		.statussethwErr                   (statussethwErr),
		.statussetimpSecDTIM              (statussetimpSecDTIM),
		.statussetimpPriDTIM              (statussetimpPriDTIM),
		.statussetbcnTxDMADead            (statussetbcnTxDMADead),
		.statussetac3TxDMADead            (statussetac3TxDMADead),
		.statussetac2TxDMADead            (statussetac2TxDMADead),
		.statussetac1TxDMADead            (statussetac1TxDMADead),
		.statussetac0TxDMADead            (statussetac0TxDMADead),
		.statussetptError                 (statussetptError),
		.statussettimSet                  (statussettimSet),
		.statussetolbcDSSS                (statussetolbcDSSS),
		.statussetolbcOFDM                (statussetolbcOFDM),
		.statussetrxFIFOOverFlow          (statussetrxFIFOOverFlow),
		.statussetrxDMAEmpty              (statussetrxDMAEmpty),
		.statussetmacPHYIFOverflow        (statussetmacPHYIFOverflow),
    .statussetabsTimers0              (statussetabsTimers[0]),
    .statussetabsTimers1              (statussetabsTimers[1]),
    .statussetabsTimers2              (statussetabsTimers[2]),
    .statussetabsTimers3              (statussetabsTimers[3]),
    .statussetabsTimers4              (statussetabsTimers[4]),
    .statussetabsTimers5              (statussetabsTimers[5]),
    .statussetabsTimers6              (statussetabsTimers[6]),
    .statussetabsTimers7              (statussetabsTimers[7]),
    .statussetabsTimers8              (statussetabsTimers[8]),
    .statussetabsTimers9              (statussetabsTimers[9]),
		.statusabsGenTimers               (statusabsGenTimers),
		.statussetidleInterrupt           (statussetidleInterrupt),
		.statussetimpSecTBTT              (statussetimpSecTBTT),
		.statussetimpPriTBTT              (statussetimpPriTBTT),
		.statussetcounterRxTrigger        (statussetcounterRxTrigger),
		.statussetbaRxTrigger             (statussetbaRxTrigger),
		.statussettimerRxTrigger          (statussettimerRxTrigger),
		.statussetrxTrigger               (statussetrxTrigger),
    .statussetbcnTxBufTrigger         (statussetbcnTxBufTrigger),
    .statussetac3TxBufTrigger         (statussetac3TxBufTrigger),
    .statussetac2TxBufTrigger         (statussetac2TxBufTrigger),
    .statussetac1TxBufTrigger         (statussetac1TxBufTrigger),
    .statussetac0TxBufTrigger         (statussetac0TxBufTrigger),
		.statussettimerTxTrigger          (statussettimerTxTrigger),
		.statussettxopComplete            (statussettxopComplete),
		.statussetrdTxTrigger             (statussetrdTxTrigger),
		.statussethccaTxTrigger           (statussethccaTxTrigger),
		.statussetbcnTxTrigger            (statussetbcnTxTrigger),
		.statussetac3TxTrigger            (statussetac3TxTrigger),
		.statussetac2TxTrigger            (statussetac2TxTrigger),
		.statussetac1TxTrigger            (statussetac1TxTrigger),
		.statussetac0TxTrigger            (statussetac0TxTrigger),
		.statussetrdProtTrigger           (statussetrdProtTrigger),
		.statussethccaProtTrigger         (statussethccaProtTrigger),
		.statussetac3ProtTrigger          (statussetac3ProtTrigger),
		.statussetac2ProtTrigger          (statussetac2ProtTrigger),
		.statussetac1ProtTrigger          (statussetac1ProtTrigger),
		.statussetac0ProtTrigger          (statussetac0ProtTrigger),
    .statussetac3BWDropTrigger        (statussetac3BWDropTrigger),
    .statussetac2BWDropTrigger        (statussetac2BWDropTrigger),
    .statussetac1BWDropTrigger        (statussetac1BWDropTrigger),
    .statussetac0BWDropTrigger        (statussetac0BWDropTrigger),
    .nextTBTT                         (nextTBTT),
		.tsfTimerLowIn                    (tsfTimerLowIn),
		.tsfTimerLowInValid               (tsfTimerLowInValid),
		.tsfTimerHighIn                   (tsfTimerHighIn),
		.tsfTimerHighInValid              (tsfTimerHighInValid),
		.computeDurationIn                (computeDurationIn),
		.computeDurationInValid           (computeDurationInValid),
		.timeOnAirValid                   (timeOnAirValid),
		.timeOnAir                        (timeOnAir),
		.statussetrxPayloadNewHead        (statussetrxPayloadNewHead),
		.statussetrxHeaderNewHead         (statussetrxHeaderNewHead),
		.statussetrxPayloadNewTail        (statussetrxPayloadNewTail),
		.statussetrxHeaderNewTail         (statussetrxHeaderNewTail),
		.statussethaltBcnAfterTXOP        (statussethaltBcnAfterTXOP),
		.statussethaltAC3AfterTXOP        (statussethaltAC3AfterTXOP),
		.statussethaltAC2AfterTXOP        (statussethaltAC2AfterTXOP),
		.statussethaltAC1AfterTXOP        (statussethaltAC1AfterTXOP),
		.statussethaltAC0AfterTXOP        (statussethaltAC0AfterTXOP),
		.statussettxAC3NewHead            (statussettxAC3NewHead),
		.statussettxAC2NewHead            (statussettxAC2NewHead),
		.statussettxAC1NewHead            (statussettxAC1NewHead),
		.statussettxAC0NewHead            (statussettxAC0NewHead),
		.statussettxBcnNewHead            (statussettxBcnNewHead),
		.statussettxAC3NewTail            (statussettxAC3NewTail),
		.statussettxAC2NewTail            (statussettxAC2NewTail),
		.statussettxAC1NewTail            (statussettxAC1NewTail),
		.statussettxAC0NewTail            (statussettxAC0NewTail),
		.statussettxBcnNewTail            (statussettxBcnNewTail),
		.rxPayloadState                   (rxPayloadState),
		.rxHeaderState                    (rxHeaderState),
		.txAC3State                       (txAC3State),
		.txAC2State                       (txAC2State),
		.txAC1State                       (txAC1State),
		.txAC0State                       (txAC0State),
		.txBcnState                       (txBcnState),
		.txAC3NewHeadErr                  (txAC3NewHeadErr),
		.txAC2NewHeadErr                  (txAC2NewHeadErr),
		.txAC1NewHeadErr                  (txAC1NewHeadErr),
		.txAC0NewHeadErr                  (txAC0NewHeadErr),
		.txBcnNewHeadErr                  (txBcnNewHeadErr),
		.txAC3BusErr                      (txAC3BusErr),
		.txAC2BusErr                      (txAC2BusErr),
		.txAC1BusErr                      (txAC1BusErr),
		.txAC0BusErr                      (txAC0BusErr),
		.txBcnBusErr                      (txBcnBusErr),
		.txAC3PTAddressErr                (txAC3PTAddressErr),
		.txAC2PTAddressErr                (txAC2PTAddressErr),
		.txAC1PTAddressErr                (txAC1PTAddressErr),
		.txAC0PTAddressErr                (txAC0PTAddressErr),
		.txBcnPTAddressErr                (txBcnPTAddressErr),
		.txAC3NextPointerErr              (txAC3NextPointerErr),
		.txAC2NextPointerErr              (txAC2NextPointerErr),
		.txAC1NextPointerErr              (txAC1NextPointerErr),
		.txAC0NextPointerErr              (txAC0NextPointerErr),
		.txBcnNextPointerErr              (txBcnNextPointerErr),
		.txAC3UPatternErr                 (txAC3UPatternErr),
		.txAC2UPatternErr                 (txAC2UPatternErr),
		.txAC1UPatternErr                 (txAC1UPatternErr),
		.txAC0UPatternErr                 (txAC0UPatternErr),
		.txBcnUPatternErr                 (txBcnUPatternErr),
		.txAC3LenMismatch                 (txAC3LenMismatch),
		.txAC2LenMismatch                 (txAC2LenMismatch),
		.txAC1LenMismatch                 (txAC1LenMismatch),
		.txAC0LenMismatch                 (txAC0LenMismatch),
		.txBcnLenMismatch                 (txBcnLenMismatch),
		.rxPayNewHeadErr                  (rxPayNewHeadErr),
		.rxHdrNewHeadErr                  (rxHdrNewHeadErr),
		.rxPayBusErr                      (rxPayBusErr),
		.rxHdrBusErr                      (rxHdrBusErr),
		.rxPayNextPointerErr              (rxPayNextPointerErr),
		.rxHdrNextPointerErr              (rxHdrNextPointerErr),
		.rxPayUPatternErr                 (rxPayUPatternErr),
		.rxHdrUPatternErr                 (rxHdrUPatternErr),
		.txAC3EndQ                        (txAC3EndQ),
		.txAC2EndQ                        (txAC2EndQ),
		.txAC1EndQ                        (txAC1EndQ),
		.txAC0EndQ                        (txAC0EndQ),
		.txBcnEndQ                        (txBcnEndQ),
		.txAC3Startup                     (txAC3Startup),
		.txAC2Startup                     (txAC2Startup),
		.txAC1Startup                     (txAC1Startup),
		.txAC0Startup                     (txAC0Startup),
		.txBcnStartup                     (txBcnStartup),
		.statussetac3HasData              (statussetac3HasData),
		.statussetac2HasData              (statussetac2HasData),
		.statussetac1HasData              (statussetac1HasData),
		.statussetac0HasData              (statussetac0HasData),
		.ac1MOT                           (ac1MOT),
		.ac0MOT                           (ac0MOT),
		.ac3MOT                           (ac3MOT),
		.ac2MOT                           (ac2MOT),
		.miscMOT                          (miscMOT),
		.hccaQAPMOT                       (hccaQAPMOT),
		.txBWAfterDrop                    (txBWAfterDrop),
		.bcnStatusPointer                 (bcnStatusPointer),
		.ac0StatusPointer                 (ac0StatusPointer),
		.ac1StatusPointer                 (ac1StatusPointer),
		.ac2StatusPointer                 (ac2StatusPointer),
		.ac3StatusPointer                 (ac3StatusPointer),
		.txCurrentPointer                 (txCurrentPointer),
		.rxPayStatPointer                 (rxPayStatPointer),
		.rxHdrStatPointer                 (rxHdrStatPointer),
		.rxPayCurrentPointer              (rxPayCurrentPointer),
		.signature                        (signature),
		.mac80211MHFormat                 (mac80211MHFormat), 
		.coex                             (coex),
		.wapi                             (wapi),
		.tpc                              (tpc),
		.vht                              (vht),
		.ht                               (ht),
		.rce                              (rce),
		.ccmp                             (ccmp),
		.tkip                             (tkip),
		.wep                              (wep),
		.security                         (security),
		.sme                              (sme),
		.hcca                             (hcca),
		.edca                             (edca),
		.qos                              (qos),
		.phaseNumber                      (phaseNumber),
		.releaseNumber                    (releaseNumber),
		.ieRelease                        (ieRelease),
		.umVersion                        (umVersion),
		.bitmapCnt                        (bitmapCnt),
		.tsfUpdatedBySWIn                 (tsfUpdatedBySWIn),
		.tsfUpdatedBySWInValid            (tsfUpdatedBySWInValid),
		.keyStoRAMResetIn                 (keyStoRAMResetIn),
		.keyStoRAMResetInValid            (keyStoRAMResetInValid),
		.mibTableResetIn                  (mibTableResetIn),
		.mibTableResetInValid             (mibTableResetInValid),
		.baPSBitmapResetIn                (baPSBitmapResetIn),
		.baPSBitmapResetInValid           (baPSBitmapResetInValid),
		.encrRxFIFOResetIn                (encrRxFIFOResetIn),
		.encrRxFIFOResetInValid           (encrRxFIFOResetInValid),
		.macPHYIFFIFOResetIn              (macPHYIFFIFOResetIn),
		.macPHYIFFIFOResetInValid         (macPHYIFFIFOResetInValid),
		.txFIFOResetIn                    (txFIFOResetIn),
		.txFIFOResetInValid               (txFIFOResetInValid),
		.rxFIFOResetIn                    (rxFIFOResetIn),
		.rxFIFOResetInValid               (rxFIFOResetInValid),
		.hwFSMResetIn                     (hwFSMResetIn),
		.hwFSMResetInValid                (hwFSMResetInValid),
		.useErrRec                        (useErrRec),
		.statuserrInHWLevel3              (statuserrInHWLevel3),
		.statuserrInTxRxLevel2            (statuserrInTxRxLevel2),
		.statuserrInRxLevel1              (statuserrInRxLevel1),
		.statuserrInTxLevel1              (statuserrInTxLevel1),
		.enDuplicateDetection             (enDuplicateDetection),
		.dtimUpdatedBySWIn                (dtimUpdatedBySWIn),
		.dtimUpdatedBySWInValid           (dtimUpdatedBySWInValid),
		.cfpPeriodIn                      (cfpPeriodIn),
		.cfpPeriodInValid                 (cfpPeriodInValid),
		.dtimPeriodIn                     (dtimPeriodIn),
		.dtimPeriodInValid                (dtimPeriodInValid),
		.encrKeyRAMWord0In                (encrKeyRAMWord0In),
		.encrKeyRAMWord0InValid           (encrKeyRAMWord0InValid),
		.encrKeyRAMWord1In                (encrKeyRAMWord1In),
		.encrKeyRAMWord1InValid           (encrKeyRAMWord1InValid),
		.encrKeyRAMWord2In                (encrKeyRAMWord2In),
		.encrKeyRAMWord2InValid           (encrKeyRAMWord2InValid),
		.encrKeyRAMWord3In                (encrKeyRAMWord3In),
		.encrKeyRAMWord3InValid           (encrKeyRAMWord3InValid),
`ifdef RW_WAPI_EN
    .encrIntKeyRAMWord0In             (encrIntKeyRAMWord0In),
    .encrIntKeyRAMWord0InValid        (encrIntKeyRAMWord0InValid),
    .encrIntKeyRAMWord1In             (encrIntKeyRAMWord1In),
    .encrIntKeyRAMWord1InValid        (encrIntKeyRAMWord1InValid),
    .encrIntKeyRAMWord2In             (encrIntKeyRAMWord2In),
    .encrIntKeyRAMWord2InValid        (encrIntKeyRAMWord2InValid),
    .encrIntKeyRAMWord3In             (encrIntKeyRAMWord3In),
    .encrIntKeyRAMWord3InValid        (encrIntKeyRAMWord3InValid),
`endif //RW_WAPI_EN
		.macAddrRAMLowIn                  (macAddrRAMLowIn),
		.macAddrRAMLowInValid             (macAddrRAMLowInValid),
		.macAddrRAMHighIn                 (macAddrRAMHighIn),
		.macAddrRAMHighInValid            (macAddrRAMHighInValid),
		.newReadIn                        (newReadIn),
		.newReadInValid                   (newReadInValid),
		.newWriteIn                       (newWriteIn),
		.newWriteInValid                  (newWriteInValid),
		.cTypeRAMIn                       (cTypeRAMIn),
		.cTypeRAMInValid                  (cTypeRAMInValid),
		.vlanIDRAMIn                      (vlanIDRAMIn),
		.vlanIDRAMInValid                 (vlanIDRAMInValid),
		.sppRAMIn                         (sppRAMIn),
		.sppRAMInValid                    (sppRAMInValid),
		.useDefKeyRAMIn                   (useDefKeyRAMIn),
		.useDefKeyRAMInValid              (useDefKeyRAMInValid),
		.cLenRAMIn                        (cLenRAMIn),
		.cLenRAMInValid                   (cLenRAMInValid),
		.hccaTriggerTimer                 (hccaTriggerTimer),
		.mibWriteIn                       (mibWriteIn),
		.mibWriteInValid                  (mibWriteInValid),
		.monotonicCounter1                (monotonicCounter1),
		.monotonicCounterLow2             (monotonicCounterLow2),
		.monotonicCounterHigh2            (monotonicCounterHigh2),
		.ccaBusyDurIn                     (ccaBusyDurIn),
		.ccaBusyDurInValid                (ccaBusyDurInValid),
		.ccaBusyDurSec20In                (ccaBusyDurSec20In),
		.ccaBusyDurSec20InValid           (ccaBusyDurSec20InValid),
    .ccaBusyDurSec40In                (ccaBusyDurSec40In),
    .ccaBusyDurSec40InValid           (ccaBusyDurSec40InValid),
    .ccaBusyDurSec80In                (ccaBusyDurSec80In),
    .ccaBusyDurSec80InValid           (ccaBusyDurSec80InValid),
		.sendCFEndNowIn                   (sendCFEndNowIn),
		.sendCFEndNowInValid              (sendCFEndNowInValid),
		.quietDuration1In                 (quietDuration1In),
		.quietDuration1InValid            (quietDuration1InValid),
		.quietPeriod1In                   (quietPeriod1In),
		.quietPeriod1InValid              (quietPeriod1InValid),
		.quietCount1In                    (quietCount1In),
		.quietCount1InValid               (quietCount1InValid),
		.quietOffset1In                   (quietOffset1In),
		.quietOffset1InValid              (quietOffset1InValid),
		.quietDuration2In                 (quietDuration2In),
		.quietDuration2InValid            (quietDuration2InValid),
		.quietPeriod2In                   (quietPeriod2In),
		.quietPeriod2InValid              (quietPeriod2InValid),
		.quietCount2In                    (quietCount2In),
		.quietCount2InValid               (quietCount2InValid),
		.quietOffset2In                   (quietOffset2In),
		.quietOffset2InValid              (quietOffset2InValid),
		.startTxFrameExIn                 (startTxFrameExIn),
		.startTxFrameExInValid            (startTxFrameExInValid),
		.macControlLs                     (macControlLs),
		.txControlLs                      (txControlLs),
		.rxControlLs                      (rxControlLs),
		.macControlCs                     (macControlCs),
		.txControlCs                      (txControlCs),
		.rxControlCs                      (rxControlCs),
		.debugPortRead                    (debugPortRead),
		.navCounterIn                     (navCounterIn),
		.navCounterInValid                (navCounterInValid),
		.activeAC                         (activeAC[1:0]),
		.currentCW3                       (currentCW3),
		.currentCW2                       (currentCW2),
		.currentCW1                       (currentCW1),
		.currentCW0                       (currentCW0),
		.ac3QSRC                          (ac3QSRC),
		.ac2QSRC                          (ac2QSRC),
		.ac1QSRC                          (ac1QSRC),
		.ac0QSRC                          (ac0QSRC),
		.ac3QLRC                          (ac3QLRC),
		.ac2QLRC                          (ac2QLRC),
		.ac1QLRC                          (ac1QLRC),
		.ac0QLRC                          (ac0QLRC),
		.nextState                        (nextState),
		.softReset                        (softReset),
		.setrxPayloadDMADead              (setrxPayloadDMADead),
		.setrxHeaderDMADead               (setrxHeaderDMADead),
		.setphyRxStart                    (setphyRxStart),
		.setphyErr                        (setphyErr),
		.setmacPHYIFUnderRun              (setmacPHYIFUnderRun),
		.sethwErr                         (sethwErr),
		.setimpSecDTIM                    (setimpSecDTIM),
		.setimpPriDTIM                    (setimpPriDTIM),
		.setbcnTxDMADead                  (setbcnTxDMADead),
		.setac3TxDMADead                  (setac3TxDMADead),
		.setac2TxDMADead                  (setac2TxDMADead),
		.setac1TxDMADead                  (setac1TxDMADead),
		.setac0TxDMADead                  (setac0TxDMADead),
		.setptError                       (setptError),
		.settimSet                        (settimSet),
		.setolbcDSSS                      (setolbcDSSS),
		.setolbcOFDM                      (setolbcOFDM),
		.setrxFIFOOverFlow                (setrxFIFOOverFlow),
		.setrxDMAEmpty                    (setrxDMAEmpty),
		.setmacPHYIFOverflow              (setmacPHYIFOverflow),
		.setabsTimers0                    (setabsTimers[0]),
		.setabsTimers1                    (setabsTimers[1]),
		.setabsTimers2                    (setabsTimers[2]),
		.setabsTimers3                    (setabsTimers[3]),
		.setabsTimers4                    (setabsTimers[4]),
		.setabsTimers5                    (setabsTimers[5]),
		.setabsTimers6                    (setabsTimers[6]),
		.setabsTimers7                    (setabsTimers[7]),
		.setabsTimers8                    (setabsTimers[8]),
		.setabsTimers9                    (setabsTimers[9]),
		.absGenTimers                     (absGenTimers),
		.setidleInterrupt                 (setidleInterrupt),
		.setimpSecTBTT                    (setimpSecTBTT),
		.setimpPriTBTT                    (setimpPriTBTT),
		.clearrxPayloadDMADead            (clearrxPayloadDMADead),
		.clearrxHeaderDMADead             (clearrxHeaderDMADead),
		.clearphyRxStart                  (clearphyRxStart),
		.clearphyErr                      (clearphyErr),
		.clearmacPHYIFUnderRun            (clearmacPHYIFUnderRun),
		.clearhwErr                       (clearhwErr),
		.clearimpSecDTIM                  (clearimpSecDTIM),
		.clearimpPriDTIM                  (clearimpPriDTIM),
		.clearbcnTxDMADead                (clearbcnTxDMADead),
		.clearac3TxDMADead                (clearac3TxDMADead),
		.clearac2TxDMADead                (clearac2TxDMADead),
		.clearac1TxDMADead                (clearac1TxDMADead),
		.clearac0TxDMADead                (clearac0TxDMADead),
		.clearptError                     (clearptError),
		.cleartimSet                      (cleartimSet),
		.clearolbcDSSS                    (clearolbcDSSS),
		.clearolbcOFDM                    (clearolbcOFDM),
		.clearrxFIFOOverFlow              (clearrxFIFOOverFlow),
		.clearrxDMAEmpty                  (clearrxDMAEmpty),
		.clearmacPHYIFOverflow            (clearmacPHYIFOverflow),
    .clearabsTimers0                  (clearabsTimers[0]),
    .clearabsTimers1                  (clearabsTimers[1]),
    .clearabsTimers2                  (clearabsTimers[2]),
    .clearabsTimers3                  (clearabsTimers[3]),
    .clearabsTimers4                  (clearabsTimers[4]),
    .clearabsTimers5                  (clearabsTimers[5]),
    .clearabsTimers6                  (clearabsTimers[6]),
    .clearabsTimers7                  (clearabsTimers[7]),
    .clearabsTimers8                  (clearabsTimers[8]),
    .clearabsTimers9                  (clearabsTimers[9]),
		.clearidleInterrupt               (clearidleInterrupt),
		.clearimpSecTBTT                  (clearimpSecTBTT),
		.clearimpPriTBTT                  (clearimpPriTBTT),
		.masterGenIntEn                   (masterGenIntEn),
		.maskrxPayloadDMADead             (maskrxPayloadDMADead),
		.maskrxHeaderDMADead              (maskrxHeaderDMADead),
		.maskphyRxStart                   (maskphyRxStart),
		.maskphyErr                       (maskphyErr),
		.maskmacPHYIFUnderRun             (maskmacPHYIFUnderRun),
		.maskhwErr                        (maskhwErr),
		.maskimpSecDTIM                   (maskimpSecDTIM),
		.maskimpPriDTIM                   (maskimpPriDTIM),
		.maskbcnTxDMADead                 (maskbcnTxDMADead),
		.maskac3TxDMADead                 (maskac3TxDMADead),
		.maskac2TxDMADead                 (maskac2TxDMADead),
		.maskac1TxDMADead                 (maskac1TxDMADead),
		.maskac0TxDMADead                 (maskac0TxDMADead),
		.maskptError                      (maskptError),
		.masktimSet                       (masktimSet),
		.maskolbcDSSS                     (maskolbcDSSS),
		.maskolbcOFDM                     (maskolbcOFDM),
		.maskrxFIFOOverFlow               (maskrxFIFOOverFlow),
		.maskrxDMAEmpty                   (maskrxDMAEmpty),
		.maskmacPHYIFOverflow             (maskmacPHYIFOverflow),
    .maskabsTimers0                   (maskabsTimers[0]),
    .maskabsTimers1                   (maskabsTimers[1]),
    .maskabsTimers2                   (maskabsTimers[2]),
    .maskabsTimers3                   (maskabsTimers[3]),
    .maskabsTimers4                   (maskabsTimers[4]),
    .maskabsTimers5                   (maskabsTimers[5]),
    .maskabsTimers6                   (maskabsTimers[6]),
    .maskabsTimers7                   (maskabsTimers[7]),
    .maskabsTimers8                   (maskabsTimers[8]),
    .maskabsTimers9                   (maskabsTimers[9]),
		.maskabsGenTimers                 (maskabsGenTimers),
		.maskidleInterrupt                (maskidleInterrupt),
		.maskimpSecTBTT                   (maskimpSecTBTT),
		.maskimpPriTBTT                   (maskimpPriTBTT),
		.setcounterRxTrigger              (setcounterRxTrigger),
		.setbaRxTrigger                   (setbaRxTrigger),
		.settimerRxTrigger                (settimerRxTrigger),
		.setrxTrigger                     (setrxTrigger),
    .setbcnTxBufTrigger               (setbcnTxBufTrigger),
    .setac3TxBufTrigger               (setac3TxBufTrigger),
    .setac2TxBufTrigger               (setac2TxBufTrigger),
    .setac1TxBufTrigger               (setac1TxBufTrigger),
    .setac0TxBufTrigger               (setac0TxBufTrigger),
		.settimerTxTrigger                (settimerTxTrigger),
		.settxopComplete                  (settxopComplete),
		.setrdTxTrigger                   (setrdTxTrigger),
		.sethccaTxTrigger                 (sethccaTxTrigger),
		.setbcnTxTrigger                  (setbcnTxTrigger),
		.setac3TxTrigger                  (setac3TxTrigger),
		.setac2TxTrigger                  (setac2TxTrigger),
		.setac1TxTrigger                  (setac1TxTrigger),
		.setac0TxTrigger                  (setac0TxTrigger),
    .setac3BWDropTrigger              (setac3BWDropTrigger),
    .setac2BWDropTrigger              (setac2BWDropTrigger),
    .setac1BWDropTrigger              (setac1BWDropTrigger),
    .setac0BWDropTrigger              (setac0BWDropTrigger),
		.setrdProtTrigger                 (setrdProtTrigger),
		.sethccaProtTrigger               (sethccaProtTrigger),
		.setac3ProtTrigger                (setac3ProtTrigger),
		.setac2ProtTrigger                (setac2ProtTrigger),
		.setac1ProtTrigger                (setac1ProtTrigger),
		.setac0ProtTrigger                (setac0ProtTrigger),
		.clearcounterRxTrigger            (clearcounterRxTrigger),
		.clearbaRxTrigger                 (clearbaRxTrigger),
		.cleartimerRxTrigger              (cleartimerRxTrigger),
		.clearrxTrigger                   (clearrxTrigger),
    .clearbcnTxBufTrigger             (clearbcnTxBufTrigger),
    .clearac3TxBufTrigger             (clearac3TxBufTrigger),
    .clearac2TxBufTrigger             (clearac2TxBufTrigger),
    .clearac1TxBufTrigger             (clearac1TxBufTrigger),
    .clearac0TxBufTrigger             (clearac0TxBufTrigger),
		.cleartimerTxTrigger              (cleartimerTxTrigger),
		.cleartxopComplete                (cleartxopComplete),
		.clearrdTxTrigger                 (clearrdTxTrigger),
		.clearhccaTxTrigger               (clearhccaTxTrigger),
		.clearbcnTxTrigger                (clearbcnTxTrigger),
		.clearac3TxTrigger                (clearac3TxTrigger),
		.clearac2TxTrigger                (clearac2TxTrigger),
		.clearac1TxTrigger                (clearac1TxTrigger),
		.clearac0TxTrigger                (clearac0TxTrigger),
    .clearac3BWDropTrigger            (clearac3BWDropTrigger),
    .clearac2BWDropTrigger            (clearac2BWDropTrigger),
    .clearac1BWDropTrigger            (clearac1BWDropTrigger),
    .clearac0BWDropTrigger            (clearac0BWDropTrigger),
		.clearrdProtTrigger               (clearrdProtTrigger),
		.clearhccaProtTrigger             (clearhccaProtTrigger),
		.clearac3ProtTrigger              (clearac3ProtTrigger),
		.clearac2ProtTrigger              (clearac2ProtTrigger),
		.clearac1ProtTrigger              (clearac1ProtTrigger),
		.clearac0ProtTrigger              (clearac0ProtTrigger),
		.masterTxRxIntEn                  (masterTxRxIntEn),
		.maskcounterRxTrigger             (maskcounterRxTrigger),
		.maskbaRxTrigger                  (maskbaRxTrigger),
		.masktimerRxTrigger               (masktimerRxTrigger),
		.maskrxTrigger                    (maskrxTrigger),
    .maskbcnTxBufTrigger              (maskbcnTxBufTrigger),
    .maskac3TxBufTrigger              (maskac3TxBufTrigger),
    .maskac2TxBufTrigger              (maskac2TxBufTrigger),
    .maskac1TxBufTrigger              (maskac1TxBufTrigger),
    .maskac0TxBufTrigger              (maskac0TxBufTrigger),
		.masktimerTxTrigger               (masktimerTxTrigger),
		.masktxopComplete                 (masktxopComplete),
		.maskrdTxTrigger                  (maskrdTxTrigger),
		.maskhccaTxTrigger                (maskhccaTxTrigger),
		.maskbcnTxTrigger                 (maskbcnTxTrigger),
		.maskac3TxTrigger                 (maskac3TxTrigger),
		.maskac2TxTrigger                 (maskac2TxTrigger),
		.maskac1TxTrigger                 (maskac1TxTrigger),
		.maskac0TxTrigger                 (maskac0TxTrigger),
    .maskac3BWDropTrigger             (maskac3BWDropTrigger),
    .maskac2BWDropTrigger             (maskac2BWDropTrigger),
    .maskac1BWDropTrigger             (maskac1BWDropTrigger),
    .maskac0BWDropTrigger             (maskac0BWDropTrigger),
		.maskrdProtTrigger                (maskrdProtTrigger),
		.maskhccaProtTrigger              (maskhccaProtTrigger),
		.maskac3ProtTrigger               (maskac3ProtTrigger),
		.maskac2ProtTrigger               (maskac2ProtTrigger),
		.maskac1ProtTrigger               (maskac1ProtTrigger),
		.maskac0ProtTrigger               (maskac0ProtTrigger),
		.tsfTimerLow                      (tsfTimerLow),
		.tsfTimerHigh                     (tsfTimerHigh),
		.ppduSTBC                         (ppduSTBC),
		.ppduNumExtnSS                    (ppduNumExtnSS),
		.ppduMCSIndex                     (ppduMCSIndex),
		.ppduShortGI                      (ppduShortGI),
		.ppduPreType                      (ppduPreType),
		.ppduBW                           (ppduBW),
		.ppduLength                       (ppduLength),
		.computeDuration                  (computeDuration),
		.setrxPayloadNewHead              (setrxPayloadNewHead),
		.setrxHeaderNewHead               (setrxHeaderNewHead),
		.setrxPayloadNewTail              (setrxPayloadNewTail),
		.setrxHeaderNewTail               (setrxHeaderNewTail),
		.sethaltBcnAfterTXOP              (sethaltBcnAfterTXOP),
		.sethaltAC3AfterTXOP              (sethaltAC3AfterTXOP),
		.sethaltAC2AfterTXOP              (sethaltAC2AfterTXOP),
		.sethaltAC1AfterTXOP              (sethaltAC1AfterTXOP),
		.sethaltAC0AfterTXOP              (sethaltAC0AfterTXOP),
		.settxAC3NewHead                  (settxAC3NewHead),
		.settxAC2NewHead                  (settxAC2NewHead),
		.settxAC1NewHead                  (settxAC1NewHead),
		.settxAC0NewHead                  (settxAC0NewHead),
		.settxBcnNewHead                  (settxBcnNewHead),
		.settxAC3NewTail                  (settxAC3NewTail),
		.settxAC2NewTail                  (settxAC2NewTail),
		.settxAC1NewTail                  (settxAC1NewTail),
		.settxAC0NewTail                  (settxAC0NewTail),
		.settxBcnNewTail                  (settxBcnNewTail),
		.clearrxPayloadNewHead            (clearrxPayloadNewHead),
		.clearrxHeaderNewHead             (clearrxHeaderNewHead),
		.clearrxPayloadNewTail            (clearrxPayloadNewTail),
		.clearrxHeaderNewTail             (clearrxHeaderNewTail),
		.clearhaltBcnAfterTXOP            (clearhaltBcnAfterTXOP),
		.clearhaltAC3AfterTXOP            (clearhaltAC3AfterTXOP),
		.clearhaltAC2AfterTXOP            (clearhaltAC2AfterTXOP),
		.clearhaltAC1AfterTXOP            (clearhaltAC1AfterTXOP),
		.clearhaltAC0AfterTXOP            (clearhaltAC0AfterTXOP),
		.cleartxAC3NewHead                (cleartxAC3NewHead),
		.cleartxAC2NewHead                (cleartxAC2NewHead),
		.cleartxAC1NewHead                (cleartxAC1NewHead),
		.cleartxAC0NewHead                (cleartxAC0NewHead),
		.cleartxBcnNewHead                (cleartxBcnNewHead),
		.cleartxAC3NewTail                (cleartxAC3NewTail),
		.cleartxAC2NewTail                (cleartxAC2NewTail),
		.cleartxAC1NewTail                (cleartxAC1NewTail),
		.cleartxAC0NewTail                (cleartxAC0NewTail),
		.cleartxBcnNewTail                (cleartxBcnNewTail),
		.txBcnHaltAfterTXOP               (txBcnHaltAfterTXOP),
		.txAC3HaltAfterTXOP               (txAC3HaltAfterTXOP),
		.txAC2HaltAfterTXOP               (txAC2HaltAfterTXOP),
		.txAC1HaltAfterTXOP               (txAC1HaltAfterTXOP),
		.txAC0HaltAfterTXOP               (txAC0HaltAfterTXOP),
		.txBcnHeadPtr                     (txBcnHeadPtr),
		.txAC0HeadPtr                     (txAC0HeadPtr),
		.txAC1HeadPtr                     (txAC1HeadPtr),
		.txAC2HeadPtr                     (txAC2HeadPtr),
		.txAC3HeadPtr                     (txAC3HeadPtr),
		.dmaRBDSize                       (dmaRBDSize),
		.dmaRHDSize                       (dmaRHDSize),
		.dmaTBDSize                       (dmaTBDSize),
		.dmaTHDSize                       (dmaTHDSize),
		.ptEntrySize                      (ptEntrySize),
		.rxHeaderHeadPtr                  (rxHeaderHeadPtr),
		.rxHeaderHeadPtrValid             (rxHeaderHeadPtrValid),
		.rxPayloadHeadPtr                 (rxPayloadHeadPtr),
		.rxPayloadHeadPtrValid            (rxPayloadHeadPtrValid),
		.rxFIFOThreshold                  (rxFIFOThreshold),
		.txFIFOThreshold                  (txFIFOThreshold),
		.setac3HasData                    (setac3HasData),
		.setac2HasData                    (setac2HasData),
		.setac1HasData                    (setac1HasData),
		.setac0HasData                    (setac0HasData),
		.clearac3HasData                  (clearac3HasData),
		.clearac2HasData                  (clearac2HasData),
		.clearac1HasData                  (clearac1HasData),
		.clearac0HasData                  (clearac0HasData),
		.rxReqForceDeassertion            (rxReqForceDeassertion),
		.swProf0InValid                   (swProfInValid[0]),
		.swProf1InValid                   (swProfInValid[1]),
		.swProf2InValid                   (swProfInValid[2]),
		.swProf3InValid                   (swProfInValid[3]),
		.swProf4InValid                   (swProfInValid[4]),
		.swProf5InValid                   (swProfInValid[5]),
		.swProf6InValid                   (swProfInValid[6]),
		.swProf7InValid                   (swProfInValid[7]),
		.swProf8InValid                   (swProfInValid[8]),
		.swProf9InValid                   (swProfInValid[9]),
		.swProf10InValid                  (swProfInValid[10]),
		.swProf11InValid                  (swProfInValid[11]),
		.swProf12InValid                  (swProfInValid[12]),
		.swProf13InValid                  (swProfInValid[13]),
		.swProf14InValid                  (swProfInValid[14]),
		.swProf15InValid                  (swProfInValid[15]),
		.swProf16InValid                  (swProfInValid[16]),
		.swProf17InValid                  (swProfInValid[17]),
		.swProf18InValid                  (swProfInValid[18]),
		.swProf19InValid                  (swProfInValid[19]),
		.swProf20InValid                  (swProfInValid[20]),
		.swProf21InValid                  (swProfInValid[21]),
		.swProf22InValid                  (swProfInValid[22]),
		.swProf23InValid                  (swProfInValid[23]),
		.swProf24InValid                  (swProfInValid[24]),
		.swProf25InValid                  (swProfInValid[25]),
		.swProf26InValid                  (swProfInValid[26]),
		.swProf27InValid                  (swProfInValid[27]),
		.swProf28InValid                  (swProfInValid[28]),
		.swProf29InValid                  (swProfInValid[29]),
		.swProf30InValid                  (swProfInValid[30]),
		.swProf31InValid                  (swProfInValid[31]),
		.swProf0In                        (swProfIn[0]),
		.swProf1In                        (swProfIn[1]),
		.swProf2In                        (swProfIn[2]),
		.swProf3In                        (swProfIn[3]),
		.swProf4In                        (swProfIn[4]),
		.swProf5In                        (swProfIn[5]),
		.swProf6In                        (swProfIn[6]),
		.swProf7In                        (swProfIn[7]),
		.swProf8In                        (swProfIn[8]),
		.swProf9In                        (swProfIn[9]),
		.swProf10In                       (swProfIn[10]),
		.swProf11In                       (swProfIn[11]),
		.swProf12In                       (swProfIn[12]),
		.swProf13In                       (swProfIn[13]),
		.swProf14In                       (swProfIn[14]),
		.swProf15In                       (swProfIn[15]),
		.swProf16In                       (swProfIn[16]),
		.swProf17In                       (swProfIn[17]),
		.swProf18In                       (swProfIn[18]),
		.swProf19In                       (swProfIn[19]),
		.swProf20In                       (swProfIn[20]),
		.swProf21In                       (swProfIn[21]),
		.swProf22In                       (swProfIn[22]),
		.swProf23In                       (swProfIn[23]),
		.swProf24In                       (swProfIn[24]),
		.swProf25In                       (swProfIn[25]),
		.swProf26In                       (swProfIn[26]),
		.swProf27In                       (swProfIn[27]),
		.swProf28In                       (swProfIn[28]),
		.swProf29In                       (swProfIn[29]),
		.swProf30In                       (swProfIn[30]),
		.swProf31In                       (swProfIn[31]),
		.swSetProf0                       (swSetProf[0]),
		.swSetProf1                       (swSetProf[1]),
		.swSetProf2                       (swSetProf[2]),
		.swSetProf3                       (swSetProf[3]),
		.swSetProf4                       (swSetProf[4]),
		.swSetProf5                       (swSetProf[5]),
		.swSetProf6                       (swSetProf[6]),
		.swSetProf7                       (swSetProf[7]),
		.swSetProf8                       (swSetProf[8]),
		.swSetProf9                       (swSetProf[9]),
		.swSetProf10                      (swSetProf[10]),
		.swSetProf11                      (swSetProf[11]),
		.swSetProf12                      (swSetProf[12]),
		.swSetProf13                      (swSetProf[13]),
		.swSetProf14                      (swSetProf[14]),
		.swSetProf15                      (swSetProf[15]),
		.swSetProf16                      (swSetProf[16]),
		.swSetProf17                      (swSetProf[17]),
		.swSetProf18                      (swSetProf[18]),
		.swSetProf19                      (swSetProf[19]),
		.swSetProf20                      (swSetProf[20]),
		.swSetProf21                      (swSetProf[21]),
		.swSetProf22                      (swSetProf[22]),
		.swSetProf23                      (swSetProf[23]),
		.swSetProf24                      (swSetProf[24]),
		.swSetProf25                      (swSetProf[25]),
		.swSetProf26                      (swSetProf[26]),
		.swSetProf27                      (swSetProf[27]),
		.swSetProf28                      (swSetProf[28]),
		.swSetProf29                      (swSetProf[29]),
		.swSetProf30                      (swSetProf[30]),
		.swSetProf31                      (swSetProf[31]),
		.swClearProf0                     (swClearProf[0]),
		.swClearProf1                     (swClearProf[1]),
		.swClearProf2                     (swClearProf[2]),
		.swClearProf3                     (swClearProf[3]),
		.swClearProf4                     (swClearProf[4]),
		.swClearProf5                     (swClearProf[5]),
		.swClearProf6                     (swClearProf[6]),
		.swClearProf7                     (swClearProf[7]),
		.swClearProf8                     (swClearProf[8]),
		.swClearProf9                     (swClearProf[9]),
		.swClearProf10                    (swClearProf[10]),
		.swClearProf11                    (swClearProf[11]),
		.swClearProf12                    (swClearProf[12]),
		.swClearProf13                    (swClearProf[13]),
		.swClearProf14                    (swClearProf[14]),
		.swClearProf15                    (swClearProf[15]),
		.swClearProf16                    (swClearProf[16]),
		.swClearProf17                    (swClearProf[17]),
		.swClearProf18                    (swClearProf[18]),
		.swClearProf19                    (swClearProf[19]),
		.swClearProf20                    (swClearProf[20]),
		.swClearProf21                    (swClearProf[21]),
		.swClearProf22                    (swClearProf[22]),
		.swClearProf23                    (swClearProf[23]),
		.swClearProf24                    (swClearProf[24]),
		.swClearProf25                    (swClearProf[25]),
		.swClearProf26                    (swClearProf[26]),
		.swClearProf27                    (swClearProf[27]),
		.swClearProf28                    (swClearProf[28]),
		.swClearProf29                    (swClearProf[29]),
		.swClearProf30                    (swClearProf[30]),
		.swClearProf31                    (swClearProf[31]),
		.statusswSetProf0                 (statusswSetProf[0]),
		.statusswSetProf1                 (statusswSetProf[1]),
		.statusswSetProf2                 (statusswSetProf[2]),
		.statusswSetProf3                 (statusswSetProf[3]),
		.statusswSetProf4                 (statusswSetProf[4]),
		.statusswSetProf5                 (statusswSetProf[5]),
		.statusswSetProf6                 (statusswSetProf[6]),
		.statusswSetProf7                 (statusswSetProf[7]),
		.statusswSetProf8                 (statusswSetProf[8]),
		.statusswSetProf9                 (statusswSetProf[9]),
		.statusswSetProf10                (statusswSetProf[10]),
		.statusswSetProf11                (statusswSetProf[11]),
		.statusswSetProf12                (statusswSetProf[12]),
		.statusswSetProf13                (statusswSetProf[13]),
		.statusswSetProf14                (statusswSetProf[14]),
		.statusswSetProf15                (statusswSetProf[15]),
		.statusswSetProf16                (statusswSetProf[16]),
		.statusswSetProf17                (statusswSetProf[17]),
		.statusswSetProf18                (statusswSetProf[18]),
		.statusswSetProf19                (statusswSetProf[19]),
		.statusswSetProf20                (statusswSetProf[20]),
		.statusswSetProf21                (statusswSetProf[21]),
		.statusswSetProf22                (statusswSetProf[22]),
		.statusswSetProf23                (statusswSetProf[23]),
		.statusswSetProf24                (statusswSetProf[24]),
		.statusswSetProf25                (statusswSetProf[25]),
		.statusswSetProf26                (statusswSetProf[26]),
		.statusswSetProf27                (statusswSetProf[27]),
		.statusswSetProf28                (statusswSetProf[28]),
		.statusswSetProf29                (statusswSetProf[29]),
		.statusswSetProf30                (statusswSetProf[30]),
		.statusswSetProf31                (statusswSetProf[31]),
		.swProf0                          (swProf[0]),
		.swProf1                          (swProf[1]),
		.swProf2                          (swProf[2]),
		.swProf3                          (swProf[3]),
		.swProf4                          (swProf[4]),
		.swProf5                          (swProf[5]),
		.swProf6                          (swProf[6]),
		.swProf7                          (swProf[7]),
		.swProf8                          (swProf[8]),
		.swProf9                          (swProf[9]),
		.swProf10                         (swProf[10]),
		.swProf11                         (swProf[11]),
		.swProf12                         (swProf[12]),
		.swProf13                         (swProf[13]),
		.swProf14                         (swProf[14]),
		.swProf15                         (swProf[15]),
		.swProf16                         (swProf[16]),
		.swProf17                         (swProf[17]),
		.swProf18                         (swProf[18]),
		.swProf19                         (swProf[19]),
		.swProf20                         (swProf[20]),
		.swProf21                         (swProf[21]),
		.swProf22                         (swProf[22]),
		.swProf23                         (swProf[23]),
		.swProf24                         (swProf[24]),
		.swProf25                         (swProf[25]),
		.swProf26                         (swProf[26]),
		.swProf27                         (swProf[27]),
		.swProf28                         (swProf[28]),
		.swProf29                         (swProf[29]),
		.swProf30                         (swProf[30]),
		.swProf31                         (swProf[31]),
		.macAddrLow                       (macAddrLow),
		.macAddrHigh                      (macAddrHigh),
		.macAddrLowMask                   (macAddrLowMask),
		.macAddrHighMask                  (macAddrHighMask),
		.bssIDLow                         (bssIDLow),
		.bssIDHigh                        (bssIDHigh),
		.bssIDLowMask                     (bssIDLowMask),
		.bssIDHighMask                    (bssIDHighMask),
		.probeDelay                       (probeDelay),
		.atimW                            (atimW),
		.wakeupDTIM                       (wakeupDTIM),
		.listenInterval                   (listenInterval),
		.wakeUpSW                         (wakeUpSW),
		.wakeUpFromDoze                   (wakeUpFromDoze),
		.enableLPClkSwitch                (enableLPClkSwitch),
		.rxRIFSEn                         (rxRIFSEn),
		.tsfMgtDisable                    (tsfMgtDisable),
		.tsfUpdatedBySW                   (tsfUpdatedBySW),
		.abgnMode                         (abgnMode),
		.keyStoRAMReset                   (keyStoRAMReset),
		.mibTableReset                    (mibTableReset),
		.rateControllerMPIF               (rateControllerMPIF),
		.disableBAResp                    (disableBAResp),
		.disableCTSResp                   (disableCTSResp),
		.disableACKResp                   (disableACKResp),
		.activeClkGating                  (activeClkGating),
		.cfpAware                         (cfpAware),
		.pwrMgt                           (pwrMgt),
        .ap                               (ap),
		.bssType                          (bssType),
		.rxFlowCntrlEn                    (rxFlowCntrlEn),
		.baPSBitmapReset                  (baPSBitmapReset),
		.encrRxFIFOReset                  (encrRxFIFOReset),
		.macPHYIFFIFOReset                (macPHYIFFIFOReset),
		.txFIFOReset                      (txFIFOReset),
		.rxFIFOReset                      (rxFIFOReset),
		.hwFSMReset                       (hwFSMReset),
		.useErrDet                        (useErrDet),
		.errInHWLevel3                    (errInHWLevel3),
		.errInTxRxLevel2                  (errInTxRxLevel2),
		.errInRxLevel1                    (errInRxLevel1),
		.errInTxLevel1                    (errInTxLevel1),
		.clearErrInHWLevel3               (clearErrInHWLevel3),
		.clearErrInTxRxLevel2             (clearErrInTxRxLevel2),
		.clearErrInRxLevel1               (clearErrInRxLevel1),
		.clearErrInTxLevel1               (clearErrInTxLevel1),
		.acceptUnknown                    (acceptUnknown),
		.acceptOtherDataFrames            (acceptOtherDataFrames),
		.acceptQoSNull                    (acceptQoSNull),
		.acceptQCFWOData                  (acceptQCFWOData),
		.acceptQData                      (acceptQData),
		.acceptCFWOData                   (acceptCFWOData),
		.acceptData                       (acceptData),
		.acceptOtherCntrlFrames           (acceptOtherCntrlFrames),
		.acceptCFEnd                      (acceptCFEnd),
		.acceptACK                        (acceptACK),
		.acceptCTS                        (acceptCTS),
		.acceptRTS                        (acceptRTS),
		.acceptPSPoll                     (acceptPSPoll),
		.acceptBA                         (acceptBA),
		.acceptNotExpectedBA              (acceptNotExpectedBA),
		.acceptBAR                        (acceptBAR),
		.acceptOtherMgmtFrames            (acceptOtherMgmtFrames),
		.acceptDecryptErrorFrames         (acceptDecryptErrorFrames),
		.acceptAllBeacon                  (acceptAllBeacon),
		.acceptBeacon                     (acceptBeacon),
		.acceptProbeResp                  (acceptProbeResp),
		.acceptProbeReq                   (acceptProbeReq),
		.acceptMyUnicast                  (acceptMyUnicast),
		.acceptUnicast                    (acceptUnicast),
		.acceptErrorFrames                (acceptErrorFrames),
		.acceptOtherBSSID                 (acceptOtherBSSID),
		.acceptBroadcast                  (acceptBroadcast),
		.acceptMulticast                  (acceptMulticast),
		.dontDecrypt                      (dontDecrypt),
		.excUnencrypted                   (excUnencrypted),
		.noBcnTxTime                      (noBcnTxTime),
		.impTBTTIn128Us                   (impTBTTIn128Us),
		.impTBTTPeriod                    (impTBTTPeriod),
		.beaconInt                        (beaconInt),
		.aid                              (aid),
		.timOffset                        (timOffset),
		.bcnUpdateOffset                  (bcnUpdateOffset),
		.dtimUpdatedBySW                  (dtimUpdatedBySW),
		.cfpPeriod                        (cfpPeriod),
		.dtimPeriod                       (dtimPeriod),
		.cfpMaxDuration                   (cfpMaxDuration),
		.dot11LongRetryLimit              (dot11LongRetryLimit),
		.dot11ShortRetryLimit             (dot11ShortRetryLimit),
		.maxPHYNtx                        (maxPHYNtx),
		.dsssMaxPwrLevel                  (dsssMaxPwrLevel),
		.ofdmMaxPwrLevel                  (ofdmMaxPwrLevel),
		.bbServiceB                       (bbServiceB),
		.bbServiceA                       (bbServiceA),
		.encrKeyRAMWord0                  (encrKeyRAMWord0),
		.encrKeyRAMWord1                  (encrKeyRAMWord1),
		.encrKeyRAMWord2                  (encrKeyRAMWord2),
		.encrKeyRAMWord3                  (encrKeyRAMWord3),
`ifdef RW_WAPI_EN
		.encrIntKeyRAMWord0               (encrIntKeyRAMWord0),
		.encrIntKeyRAMWord1               (encrIntKeyRAMWord1),
		.encrIntKeyRAMWord2               (encrIntKeyRAMWord2),
		.encrIntKeyRAMWord3               (encrIntKeyRAMWord3),
`endif // WAPI_EN
		.macAddrRAMLow                    (macAddrRAMLow),
		.macAddrRAMHigh                   (macAddrRAMHigh),
		.newRead                          (newRead),
		.newWrite                         (newWrite),
		.keyIndexRAM                      (keyIndexRAM),
		.cTypeRAM                         (cTypeRAM),
		.vlanIDRAM                        (vlanIDRAM),
		.sppRAM                           (sppRAM),
		.useDefKeyRAM                     (useDefKeyRAM),
		.cLenRAM                          (cLenRAM),
		.bssBasicRateSet                  (bssBasicRateSet),
		.dsssCount                        (dsssCount),
		.ofdmCount                        (ofdmCount),
		.olbcTimer                        (olbcTimer),
		.txChainDelayInMACClk             (txChainDelayInMACClk),
		.txRFDelayInMACClk                (txRFDelayInMACClk),
		.macCoreClkFreq                   (macCoreClkFreq),
		.slotTimeInMACClk                 (slotTimeInMACClk),
		.slotTime                         (slotTime),
		.rxRFDelayInMACClk                (rxRFDelayInMACClk),
		.txDelayRFOnInMACClk              (txDelayRFOnInMACClk),
		.macProcDelayInMACClk             (macProcDelayInMACClk),
		.radioWakeUpTime                  (radioWakeUpTime),
		.radioChirpTime                   (radioChirpTime),
		.sifsBInMACClk                    (sifsBInMACClk),
		.sifsB                            (sifsB),
		.sifsAInMACClk                    (sifsAInMACClk),
		.sifsA                            (sifsA),
		.rxCCADelay                       (rxCCADelay),
		.rifs                             (rifs),
		.rxStartDelayMIMO                 (rxStartDelayMIMO),
		.rxStartDelayShort                (rxStartDelayShort),
		.rxStartDelayLong                 (rxStartDelayLong),
		.rxStartDelayOFDM                 (rxStartDelayOFDM),
		.rifsTOInMACClk                   (rifsTOInMACClk),
		.rifsInMACClk                     (rifsInMACClk),
		.txDMAProcDlyInMACClk             (txDMAProcDlyInMACClk),
		.edcaTriggerTimer                 (edcaTriggerTimer),
		.txPacketTimeout                  (txPacketTimeout),
		.txAbsoluteTimeout                (txAbsoluteTimeout),
		.rxPayloadUsedCount               (rxPayloadUsedCount),
		.rxPacketTimeout                  (rxPacketTimeout),
		.rxAbsoluteTimeout                (rxAbsoluteTimeout),
		.mibValue                         (mibValue),
		.mibWrite                         (mibWrite),
		.mibIncrementMode                 (mibIncrementMode),
		.mibTableIndex                    (mibTableIndex),
		.absTimerValue0                   (absTimerValue0),
		.absTimerValue1                   (absTimerValue1),
		.absTimerValue2                   (absTimerValue2),
		.absTimerValue3                   (absTimerValue3),
		.absTimerValue4                   (absTimerValue4),
		.absTimerValue5                   (absTimerValue5),
		.absTimerValue6                   (absTimerValue6),
		.absTimerValue7                   (absTimerValue7),
		.absTimerValue8                   (absTimerValue8),
		.absTimerValue9                   (absTimerValue9),
		.maxAllowedLength                 (maxAllowedLength),
		.txOpLimit0                       (txOpLimit0),
		.cwMax0                           (cwMax0),
		.cwMin0                           (cwMin0),
		.aifsn0                           (aifsn0),
		.txOpLimit1                       (txOpLimit1),
		.cwMax1                           (cwMax1),
		.cwMin1                           (cwMin1),
		.aifsn1                           (aifsn1),
		.txOpLimit2                       (txOpLimit2),
		.cwMax2                           (cwMax2),
		.cwMin2                           (cwMin2),
		.aifsn2                           (aifsn2),
		.txOpLimit3                       (txOpLimit3),
		.cwMax3                           (cwMax3),
		.cwMin3                           (cwMin3),
		.aifsn3                           (aifsn3),
		.ccaBusyDur                       (ccaBusyDur),
		.ccaBusyDurSec20                  (ccaBusyDurSec20),
    .ccaBusyDurSec40                  (ccaBusyDurSec40),
    .ccaBusyDurSec80                  (ccaBusyDurSec80),
		.keepTXOPOpen                     (keepTXOPOpen),
		.remTXOPInDurField                (remTXOPInDurField),
		.sendCFEnd                        (sendCFEnd),
		.sendCFEndNow                     (sendCFEndNow),
		.quietDuration1                   (quietDuration1),
		.quietPeriod1                     (quietPeriod1),
		.quietCount1                      (quietCount1),
		.quietOffset1                     (quietOffset1),
		.quietDuration2                   (quietDuration2),
		.quietPeriod2                     (quietPeriod2),
		.quietCount2                      (quietCount2),
		.quietOffset2                     (quietOffset2),
		.basicSTBCMCS                     (basicSTBCMCS),
		.dualCTSProt                      (dualCTSProt),
		.ctsSTBCDur                       (ctsSTBCDur),
		.cfEndSTBCDur                     (cfEndSTBCDur),
		.startTxBW                        (startTxBW),
		.startTxPreType                   (startTxPreType),
		.startTxFormatMod                 (startTxFormatMod),
		.startTxMCSIndex0                 (startTxMCSIndex0),
		.startTxKSRIndex                  (startTxKSRIndex),
		.startTxAC                        (startTxAC),
		.startTxFrmExType                 (startTxFrmExType),
		.startTxFrameEx                   (startTxFrameEx),
		.durControlFrm                    (durControlFrm),
		.startTxSMMIndex                  (startTxSMMIndex),
		.startTxAntennaSet                (startTxAntennaSet),
		.startTxLSTP                      (startTxLSTP),
		.startTxSmoothing                 (startTxSmoothing),
		.startTxShortGI                   (startTxShortGI),
		.startTxFecCoding                 (startTxFecCoding),
		.startTxNTx                       (startTxNTx),
		.startTxSTBC                      (startTxSTBC),
		.startTxNumExtnSS                 (startTxNumExtnSS),
		.aPPDUMaxTime                     (aPPDUMaxTime),
		.maxSupportedBW                   (maxSupportedBW),
		.dynBWEn                          (dynBWEn),
		.dropToLowerBW                    (dropToLowerBW),
		.numTryBWAcquisition              (numTryBWAcquisition),
		.defaultBWTXOP                    (defaultBWTXOP),
		.defaultBWTXOPV                   (defaultBWTXOPV),
		.supportLSTP                      (supportLSTP),
		.bssBasicHTMCSSetUM               (bssBasicHTMCSSetUM),
		.bssBasicHTMCSSetEM               (bssBasicHTMCSSetEM),
		.bssBasicVHTMCSSet                (bssBasicVHTMCSSet),
`ifdef RW_WLAN_COEX_EN                
		.coexWlanChanFreq                 (coexWlanChanFreq),
		.coexWlanChanOffset               (coexWlanChanOffset),
		.coexEnable                       (coexEnable),
		.coexPTIBKData                    (coexPTIBKData),
		.coexPTIBEData                    (coexPTIBEData),
		.coexPTIVIData                    (coexPTIVIData),
    .coexPTIVOData                    (coexPTIVOData),
    .coexPTIBcnData                   (coexPTIBcnData),
		.coexPTIMgt                       (coexPTIMgt),
		.coexPTICntl                      (coexPTICntl),
 		.coexPTIAck                       (coexPTIAck),
`endif // RW_WLAN_COEX_EN                
		.debugPortSel2                    (debugPortSel2),
		.debugPortSel1                    (debugPortSel1),
		.navCounter                       (navCounter),
		.backoffOffset                    (backoffOffset),
		.latchNextState_p                 (latchNextState_p),
		.regWrite                         (regWrite),
		.regRead                          (regRead),
		.regAddr                          (regAddr),
		.regWriteData                     (regWriteData),
		.regReadyIn                       (regReadyIn),
		.regReadData                      (regReadData)
		);


assign swProfInValid   = swSetProf | swClearProf;
assign swProfIn        = (swProf | swSetProf) & ~swClearProf;
assign statusswSetProf = 32'b0;


assign quietOffset1InValid   = quietElement1InValid;
assign quietDuration1InValid = quietElement1InValid;
assign quietPeriod1InValid   = quietElement1InValid;
assign quietCount1InValid    = quietElement1InValid;
assign quietOffset2InValid   = quietElement2InValid;
assign quietDuration2InValid = quietElement2InValid;
assign quietPeriod2InValid   = quietElement2InValid;
assign quietCount2InValid    = quietElement2InValid;

assign macAddr      =  {macAddrHigh,macAddrLow};
assign macAddrMask  =  {macAddrHighMask,macAddrLowMask};   

assign bssID        =  {bssIDHigh,bssIDLow};        
assign bssIDMask    =  {bssIDHighMask,bssIDLowMask};    

assign miscMOT      = 16'b0;  // Reserved for future use
assign hccaQAPMOT   = 16'b0;  // Reserved for future use


// Instanciation of macCore
// Name of the instance : U_macCore
// Name of the file containing this module : macCore.v
macCore U_macCore (
		.macPIClkHardRst_n                (macPIClkHardRst_n),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macWTClkHardRst_n                (macWTClkHardRst_n),
		.mpIFClkHardRst_n                 (mpIFClkHardRst_n),
		.macPIClkSoftRst_n                (macPIClkSoftRst_n),
		.macCoreClkSoftRst_n              (macCoreClkSoftRst_n),
		.macWTClkSoftRst_n                (macWTClkSoftRst_n),
		.macPISlaveClk                    (macPISlaveClk),
		.macPIClk                         (macPIClk),
		.macPITxClk                       (macPITxClk),
		.macCoreClk                       (macCoreClk),
		.macCoreTxClk                     (macCoreTxClk),
		.macCoreRxClk                     (macCoreRxClk),
		.macLPClk                         (macLPClk),
		.macWTClk                         (macWTClk),
		.macCryptClk                      (macCryptClk),
		.macPriClkEn                      (macPriClkEn),
		.macSecClkEn                      (macSecClkEn),
		.platformWakeUp                   (platformWakeUpMC),
		.macCoreTxClkEn                   (macCoreTxClkEn),
		.macCoreRxClkEn                   (macCoreRxClkEn),
		.macLPClkSwitch                   (macLPClkSwitch),
		.macCryptClkEn                    (macCryptClkEn),
		.macWTClkEn                       (macWTClkEn),
		.mpIFClkEn                        (mpIFClkEn),
		.absGenTimersInt                  (absGenTimersIntMC),
		.txopComplete                     (txopComplete),
		.ac3ProtTrigger                   (ac3ProtTrigger),
		.ac2ProtTrigger                   (ac2ProtTrigger),
		.ac1ProtTrigger                   (ac1ProtTrigger),
		.ac0ProtTrigger                   (ac0ProtTrigger),
		.ac3BWDropTrigger                 (ac3BWDropTrigger),
		.ac2BWDropTrigger                 (ac2BWDropTrigger),
		.ac1BWDropTrigger                 (ac1BWDropTrigger),
		.ac0BWDropTrigger                 (ac0BWDropTrigger),
		.olbcOFDM                         (olbcOFDM),
		.olbcDSSS                         (olbcDSSS),
		.impPriTBTT                       (impPriTBTT),
		.impSecTBTT                       (impSecTBTT),
		.impPriDTIM                       (impPriDTIM),
		.impSecDTIM                       (impSecDTIM),
		.timerTxTrigger                   (timerTxTrigger),
		.timerRxTrigger                   (timerRxTrigger),
		.idleInterrupt                    (idleInterrupt),
		.rxFIFOOverFlow                   (rxFIFOOverFlow),
		.baRxTrigger                      (baRxTrigger),
		.absTimers                        (absTimers),
		.hwErr                            (hwErr),
		.softReset                        (softReset),
		.txCtrlRegWr                      (txCtrlRegWr),
		.txCtrlRegData                    (txCtrlRegData),
		.txCtrlRegPT                      (txCtrlRegPT),
		.txCtrlRegHD                      (txCtrlRegHD),
		.discardPrevHD_p                  (discardPrevHD_p),
		.txCtrlRegBusy                    (txCtrlRegBusy),
		.rxFrmDiscard                     (rxFrmDiscard),
		.rxDescAvailable                  (rxDescAvailable),
		.statusUpdated_p                  (statusUpdated_p),
		.updateDMAStatus_p                (updateDMAStatus_p),
		.txAC0StateMC                     (txAC0StateMC),
		.txAC1StateMC                     (txAC1StateMC),
		.txAC2StateMC                     (txAC2StateMC),
		.txAC3StateMC                     (txAC3StateMC),
		.txBcnStateMC                     (txBcnStateMC),
		.trigTxAC0                        (trigTxAC0),
		.trigTxAC1                        (trigTxAC1),
		.trigTxAC2                        (trigTxAC2),
		.trigTxAC3                        (trigTxAC3),
		.trigTxBcn                        (trigTxBcn),
		.frameRxed_p                      (frameRxed_p),
		.swRTS_p                          (swRTS_p),
		.txMpduDone_p                     (txMpduDone_p),
		.ampduFrm_p                       (ampduFrm_p),
		.retryFrame_p                     (retryFrame_p),
		.mpduSuccess_p                    (mpduSuccess_p),
		.mpduFailed_p                     (mpduFailed_p),
		.rtsFailed_p                      (rtsFailed_p),
		.rtsSuccess_p                     (rtsSuccess_p),
		.retryLimitReached_p              (retryLimitReached_p),
		.transmissionBW                   (transmissionBW),
		.numMPDURetries                   (numMPDURetries),
		.numRTSRetries                    (numRTSRetries),
		.mediumTimeUsed                   (mediumTimeUsed),
		.whichDescriptorSW                (whichDescriptorSW),
		.rxTrig_p                         (rxTrig_p),
		.txFIFOMPDUDelimiters             (txFIFOMPDUDelimiters),
		.txFIFORdData                     (txFIFORdData),
		.txFIFOEmpty                      (txFIFOEmpty),
		.txFIFODataValid                  (txFIFODataValid),
		.txFIFORdFlush                    (txFIFORdFlush),
		.txFIFORead                       (txFIFORead),
		.txFIFOReadByFour                 (txFIFOReadByFour),
		.txFIFOReadByTwo                  (txFIFOReadByTwo),
		.rxFIFOAlmostFull                 (rxFIFOAlmostFull),
		.rxFIFOFull                       (rxFIFOFull),
		.rxFIFOEmptyWrClk                 (rxFIFOEmptyWrClk),
		.rxFIFOWrTag                      (rxFIFOWrTag),
		.rxFIFOWrData                     (rxFIFOWrData),
		.rxFIFOWrite                      (rxFIFOWrite),
		.macPhyIfRxStart_p                (macPhyIfRxStart_p),
		.macPhyIfRxFlush_p                (macPhyIfRxFlush_p),
		.startRx                          (startRx),
		.stopRx_p                         (stopRx_p),
		.mpifKeepRFon                     (mpifKeepRFon),
		.startTx_p                        (startTx_p),
		.stopTx_p                         (stopTx_p),
		.mpIfTxFifoData                   (mpIfTxFifoData),
		.mpIfTxFifoWrite                  (mpIfTxFifoWrite),
		.txPwrLevel                       (txPwrLevel),
		.chBW                             (chBW),
		.chOffset                         (chOffset),
		.smoothing                        (smoothing),
		.antennaSet                       (antennaSet),
		.smmIndex                         (smmIndex),
		.mcs                              (mcs),
		.preType                          (preType),
		.formatMod                        (formatMod),
		.numExtnSS                        (numExtnSS),
		.stbc                             (stbc),
		.fecCoding                        (fecCoding),
		.sounding                         (sounding),
		.legLength                        (legLength),
		.legRate                          (legRate),
		.service                          (service),
		.htLength                         (htLength),
		.nTx                              (nTx),
		.nSTS                             (nSTS),
		.shortGI                          (shortGI),
		.aggreation                       (aggreation),
		.beamFormed                       (beamFormed),
		.disambiguityBit                  (disambiguityBit),
		.partialAID                       (partialAID),
		.groupID                          (groupID),
		.dozeNotAllowed                   (dozeNotAllowed),
		.continuousTx                     (continuousTx),
		.mpIfTxFifoFull                   (mpIfTxFifoFull),
		.mpIfTxErr_p                      (mpIfTxErr_p),
		.mpIfTxEn                         (mpIfTxEn),
		.macPhyTxEnd_p                    (macPhyTxEnd_p),
		.macPhyIfRxFifoReadEn             (macPhyIfRxFifoReadEn),
		.macPhyIfRxFifoEmpty              (macPhyIfRxFifoEmpty),
		.macPhyIfRxFifoData               (macPhyIfRxFifoData),
		.macPhyIfRxErr_p                  (macPhyIfRxErr_p),
		.macPhyIfRxEnd_p                  (macPhyIfRxEnd_p),
		.macPhyIfRxEndForTiming_p         (macPhyIfRxEndForTiming_p),
		.macPhyIfRifsRxDetected           (macPhyIfRifsRxDetected),
		.macPhyIfRxCca                    (macPhyIfRxCca),
		.macPhyIfRxCcaSec20               (macPhyIfRxCcaSec20),
		.macPhyIfRxCcaSec40               (macPhyIfRxCcaSec40),
		.macPhyIfRxCcaSec80               (macPhyIfRxCcaSec80),
		.macPHYIFUnderRun                 (macPHYIFUnderRun),
		.macPHYIFOverflow                 (macPHYIFOverflow),
		.timWakeUp                        (timWakeUp),
		.timSleep                         (timSleep),
`ifdef RW_MAC_MIBCNTL_EN
		.mibAddr                          (mibAddr),
		.mibRd                            (mibRd),
		.mibRdData                        (mibRdData),
		.mibBusy                          (mibBusy),
		.mibTableEn                       (mibTableEn),
		.mibTableAddr                     (mibTableAddr),
		.mibTableWriteEn                  (mibTableWriteEn),
		.mibTableWriteData                (mibTableWriteData),
		.mibTableReadData                 (mibTableReadData),
`endif // RW_MAC_MIBCNTL_EN
		.psBitmapEn                       (psBitmapEn),
		.psBitmapWriteEn                  (psBitmapWriteEn),
		.psBitmapAddr                     (psBitmapAddr),
		.psBitmapReadData                 (psBitmapReadData),
		.psBitmapWriteData                (psBitmapWriteData),
		.keyStorageEn                     (keyStorageEn),
		.keyStorageWriteEn                (keyStorageWriteEn),
		.keyStorageAddr                   (keyStorageAddr),
		.keyStorageReadData               (keyStorageReadData),
		.keyStorageWriteData              (keyStorageWriteData),
		.sBoxAReadData                    (sBoxAReadData),
		.sBoxBReadData                    (sBoxBReadData),
		.sBoxAAddr                        (sBoxAAddr),
		.sBoxBAddr                        (sBoxBAddr),
		.sBoxAWriteData                   (sBoxAWriteData),
		.sBoxBWriteData                   (sBoxBWriteData),
		.sBoxAWriteEn                     (sBoxAWriteEn),
		.sBoxBWriteEn                     (sBoxBWriteEn),
		.sBoxAEn                          (sBoxAEn),
		.sBoxBEn                          (sBoxBEn),
		.encrRxFIFOReadData               (encrRxFIFOReadData),
		.encrRxFIFOWriteEn                (encrRxFIFOWriteEn),
		.encrRxFIFOWriteAddr              (encrRxFIFOWriteAddr),
		.encrRxFIFOWriteData              (encrRxFIFOWriteData),
		.encrRxFIFOReadEn                 (encrRxFIFOReadEn),
		.encrRxFIFOReadAddr               (encrRxFIFOReadAddr),
		.navCounter                       (navCounter),
		.navCounterIn                     (navCounterIn),
		.navCounterInValid                (navCounterInValid),
		.currentState                     (currentState),
		.nextState                        (nextState),
		.latchNextState_p                 (latchNextState_p),
		.nextStateIn                      (nextStateIn),
		.nextStateInValid                 (nextStateInValid),
		.wakeUpSW                         (wakeUpSW),
		.wakeUpFromDoze                   (wakeUpFromDoze),
		.enableLPClkSwitch                (enableLPClkSwitch),
		.activeClkGating                  (activeClkGating),
		.disableACKResp                   (disableACKResp),
		.disableCTSResp                   (disableCTSResp),
		.disableBAResp                    (disableBAResp),
		.macAddr                          (macAddr),
		.macAddrMask                      (macAddrMask),
		.bssID                            (bssID),
		.bssIDMask                        (bssIDMask),
		.excUnencrypted                   (excUnencrypted),
		.dontDecrypt                      (dontDecrypt),
		.acceptMulticast                  (acceptMulticast),
		.acceptBroadcast                  (acceptBroadcast),
		.acceptOtherBSSID                 (acceptOtherBSSID),
		.acceptErrorFrames                (acceptErrorFrames),
		.acceptUnicast                    (acceptUnicast),
		.acceptMyUnicast                  (acceptMyUnicast),
		.acceptProbeReq                   (acceptProbeReq),
		.acceptProbeResp                  (acceptProbeResp),
 		.acceptDecryptErrorFrames         (acceptDecryptErrorFrames),
		.acceptBeacon                     (acceptBeacon),
		.acceptAllBeacon                  (acceptAllBeacon),
		.acceptOtherMgmtFrames            (acceptOtherMgmtFrames),
		.acceptBAR                        (acceptBAR),
		.acceptBA                         (acceptBA),
		.acceptNotExpectedBA              (acceptNotExpectedBA),
		.acceptPSPoll                     (acceptPSPoll),
		.acceptRTS                        (acceptRTS),
		.acceptCTS                        (acceptCTS),
		.acceptACK                        (acceptACK),
		.acceptCFEnd                      (acceptCFEnd),
		.acceptOtherCntrlFrames           (acceptOtherCntrlFrames),
		.acceptData                       (acceptData),
		.acceptCFWOData                   (acceptCFWOData),
		.acceptQData                      (acceptQData),
		.acceptQCFWOData                  (acceptQCFWOData),
		.acceptQoSNull                    (acceptQoSNull),
		.acceptOtherDataFrames            (acceptOtherDataFrames),
		.acceptUnknown                    (acceptUnknown),
		.hwFSMResetPIClk                  (hwFSMResetPIClk),
		.hwFSMResetWTClk                  (hwFSMResetWTClk),
		.hwFSMResetCoreClk                (hwFSMResetCoreClk),
		.baPSBitmapReset                  (baPSBitmapReset),
		.baPSBitmapResetIn                (baPSBitmapResetIn),
		.baPSBitmapResetInValid           (baPSBitmapResetInValid),
		.encrRxFIFOReset                  (encrRxFIFOReset),
		.encrRxFIFOResetIn                (encrRxFIFOResetIn),
		.encrRxFIFOResetInValid           (encrRxFIFOResetInValid),
		.mibTableReset                    (mibTableReset),
		.mibTableResetIn                  (mibTableResetIn),
		.mibTableResetInValid             (mibTableResetInValid),
		.mibTableIndex                    (mibTableIndex),
		.mibIncrementMode                 (mibIncrementMode),
		.mibValue                         (mibValue),
		.mibWrite                         (mibWrite),
		.mibWriteInValid                  (mibWriteInValid),
		.mibWriteIn                       (mibWriteIn),
		.quietCount1In                    (quietCount1In),
		.quietPeriod1In                   (quietPeriod1In),
		.quietDuration1In                 (quietDuration1In),
		.quietOffset1In                   (quietOffset1In),
		.quietElement1InValid             (quietElement1InValid),
		.quietCount2In                    (quietCount2In),
		.quietPeriod2In                   (quietPeriod2In),
		.quietDuration2In                 (quietDuration2In),
		.quietOffset2In                   (quietOffset2In),
		.quietElement2InValid             (quietElement2InValid),
		.dtimPeriodIn                     (dtimPeriodIn),
		.dtimPeriodInValid                (dtimPeriodInValid),
		.cfpPeriodIn                      (cfpPeriodIn),
		.cfpPeriodInValid                 (cfpPeriodInValid),
		.edcaTriggerTimer                 (edcaTriggerTimer),
		.hccaTriggerTimer                 (hccaTriggerTimer),
		.txOpLimit0                       (txOpLimit0),
		.txOpLimit1                       (txOpLimit1),
		.txOpLimit2                       (txOpLimit2),
		.txOpLimit3                       (txOpLimit3),
		.setac3HasData                    (setac3HasData),
		.setac2HasData                    (setac2HasData),
		.setac1HasData                    (setac1HasData),
		.setac0HasData                    (setac0HasData),
		.clearac3HasData                  (clearac3HasData),
		.clearac2HasData                  (clearac2HasData),
		.clearac1HasData                  (clearac1HasData),
		.clearac0HasData                  (clearac0HasData),
		.statussetac3HasData              (statussetac3HasData),
		.statussetac2HasData              (statussetac2HasData),
		.statussetac1HasData              (statussetac1HasData),
		.statussetac0HasData              (statussetac0HasData),
		.aifsn0                           (aifsn0),
		.aifsn1                           (aifsn1),
		.aifsn2                           (aifsn2),
		.aifsn3                           (aifsn3),
		.cwMin0                           (cwMin0),
		.cwMin1                           (cwMin1),
		.cwMin2                           (cwMin2),
		.cwMin3                           (cwMin3),
		.cwMax0                           (cwMax0),
		.cwMax1                           (cwMax1),
		.cwMax2                           (cwMax2),
		.cwMax3                           (cwMax3),
		.ac0MOT                           (ac0MOT),
		.ac1MOT                           (ac1MOT),
		.ac2MOT                           (ac2MOT),
		.ac3MOT                           (ac3MOT),
		.rxControlLs                      (rxControlLs),
		.rxControlCs                      (rxControlCs),
		.txControlLs                      (txControlLs),
		.txControlCs                      (txControlCs),
		.macControlLs                     (macControlLs),
		.macControlCs                     (macControlCs),
		.probeDelay                       (probeDelay),
		.listenInterval                   (listenInterval),
		.wakeupDTIM                       (wakeupDTIM),
		.atimW                            (atimW),
		.beaconInt                        (beaconInt),
		.impTBTTPeriod                    (impTBTTPeriod),
		.impTBTTIn128Us                   (impTBTTIn128Us),
		.noBcnTxTime                      (noBcnTxTime),
		.dtimPeriod                       (dtimPeriod),
		.cfpPeriod                        (cfpPeriod),
		.cfpMaxDuration                   (cfpMaxDuration),
		.dtimUpdatedBySW                  (dtimUpdatedBySW),
		.dtimUpdatedBySWIn                (dtimUpdatedBySWIn),
		.dtimUpdatedBySWInValid           (dtimUpdatedBySWInValid),
		.tsfTimerHigh                     (tsfTimerHigh),
		.tsfTimerLow                      (tsfTimerLow),
		.tsfUpdatedBySW                   (tsfUpdatedBySW),
		.tsfMgtDisable                    (tsfMgtDisable),
		.txBWAfterDropResync              (txBWAfterDrop),
		.nextTBTT                         (nextTBTT),
		.timOffset                        (timOffset),
		.tsfUpdatedBySWIn                 (tsfUpdatedBySWIn),
		.tsfUpdatedBySWInValid            (tsfUpdatedBySWInValid),
		.tsfTimerLowIn                    (tsfTimerLowIn),
		.tsfTimerLowInValid               (tsfTimerLowInValid),
		.tsfTimerHighIn                   (tsfTimerHighIn),
		.tsfTimerHighInValid              (tsfTimerHighInValid),
		.absTimerValue0                   (absTimerValue0),
		.absTimerValue1                   (absTimerValue1),
		.absTimerValue2                   (absTimerValue2),
		.absTimerValue3                   (absTimerValue3),
		.absTimerValue4                   (absTimerValue4),
		.absTimerValue5                   (absTimerValue5),
		.absTimerValue6                   (absTimerValue6),
		.absTimerValue7                   (absTimerValue7),
		.absTimerValue8                   (absTimerValue8),
		.absTimerValue9                   (absTimerValue9),
		.monotonicCounter1                (monotonicCounter1),
		.monotonicCounterLow2             (monotonicCounterLow2),
		.monotonicCounterHigh2            (monotonicCounterHigh2),
		.abgnMode                         (abgnMode),
		.olbcTimer                        (olbcTimer),
		.ofdmCount                        (ofdmCount),
		.dsssCount                        (dsssCount),
		.macCoreClkFreq                   (macCoreClkFreq),
		.txRFDelayInMACClk                (txRFDelayInMACClk),
		.txChainDelayInMACClk             (txChainDelayInMACClk),
		.slotTime                         (slotTime),
		.slotTimeInMACClk                 (slotTimeInMACClk),
		.macProcDelayInMACClk             (macProcDelayInMACClk),
		.txDelayRFOnInMACClk              (txDelayRFOnInMACClk),
		.rxRFDelayInMACClk                (rxRFDelayInMACClk),
		.radioWakeUpTime                  (radioWakeUpTime),
		.sifsBInMACClk                    (sifsBInMACClk),
		.sifsAInMACClk                    (sifsAInMACClk),
		.sifsB                            (sifsB),
		.sifsA                            (sifsA),
		.rxCCADelay                       (rxCCADelay),
		.txDMAProcDlyInMACClk             (txDMAProcDlyInMACClk),
		.rifsTOInMACClk                   (rifsTOInMACClk),
		.rifsInMACClk                     (rifsInMACClk),
		.txAbsoluteTimeout                (txAbsoluteTimeout),
		.txPacketTimeout                  (txPacketTimeout),
		.rxAbsoluteTimeout                (rxAbsoluteTimeout),
		.rxPacketTimeout                  (rxPacketTimeout),
		.ccaBusyDur                       (ccaBusyDur),
		.ccaBusyDurIn                     (ccaBusyDurIn),
		.ccaBusyDurInValid                (ccaBusyDurInValid),
		.ccaBusyDurSec20                  (ccaBusyDurSec20),
		.ccaBusyDurSec20In                (ccaBusyDurSec20In),
		.ccaBusyDurSec20InValid           (ccaBusyDurSec20InValid),
		.ccaBusyDurSec40                  (ccaBusyDurSec40),
		.ccaBusyDurSec40In                (ccaBusyDurSec40In),
		.ccaBusyDurSec40InValid           (ccaBusyDurSec40InValid),
		.ccaBusyDurSec80                  (ccaBusyDurSec80),
		.ccaBusyDurSec80In                (ccaBusyDurSec80In),
		.ccaBusyDurSec80InValid           (ccaBusyDurSec80InValid),
		.quietCount1                      (quietCount1),
		.quietPeriod1                     (quietPeriod1),
		.quietDuration1                   (quietDuration1),
		.quietOffset1                     (quietOffset1),
		.quietCount2                      (quietCount2),
		.quietPeriod2                     (quietPeriod2),
		.quietDuration2                   (quietDuration2),
		.quietOffset2                     (quietOffset2),
		.rxStartDelayMIMO                 (rxStartDelayMIMO),
		.rxStartDelayShort                (rxStartDelayShort),
		.rxStartDelayLong                 (rxStartDelayLong),
		.rxStartDelayOFDM                 (rxStartDelayOFDM),
		.pwrMgt                           (pwrMgt),
		.ap                               (ap),
		.bssType                          (bssType),
		.cfpAware                         (cfpAware),
		.rxRIFSEn                         (rxRIFSEn),
		.dsssMaxPwrLevel                  (dsssMaxPwrLevel),
		.ofdmMaxPwrLevel                  (ofdmMaxPwrLevel),
		.maxPHYNtx                        (maxPHYNtx),
		.maxAllowedLength                 (maxAllowedLength),
		.ppduLength                       (ppduLength),
		.ppduBW                           (ppduBW),
		.ppduPreType                      (ppduPreType),
		.ppduNumExtnSS                    (ppduNumExtnSS),
		.ppduSTBC                         (ppduSTBC),
		.ppduShortGI                      (ppduShortGI),
		.ppduMCSIndex                     (ppduMCSIndex),
		.computeDuration                  (computeDuration),
		.computeDurationIn                (computeDurationIn),
		.computeDurationInValid           (computeDurationInValid),
		.timeOnAir                        (timeOnAir),
		.timeOnAirValid                   (timeOnAirValid),
		.cfEndSTBCDur                     (cfEndSTBCDur),
		.ctsSTBCDur                       (ctsSTBCDur),
		.dualCTSProt                      (dualCTSProt),
		.basicSTBCMCS                     (basicSTBCMCS),
		.startTxFrameEx                   (startTxFrameEx),
		.startTxFrameExIn                 (startTxFrameExIn),
		.startTxFrameExInValid            (startTxFrameExInValid),
		.startTxAC                        (startTxAC),
		.startTxKSRIndex                  (startTxKSRIndex),
		.startTxFrmExType                 (startTxFrmExType),
		.startTxMCSIndex0                 (startTxMCSIndex0),
		.startTxBW                        (startTxBW),
		.durControlFrm                    (durControlFrm),
		.startTxSmoothing                 (startTxSmoothing),
		.startTxAntennaSet                (startTxAntennaSet),
		.startTxSMMIndex                  (startTxSMMIndex),
		.startTxPreType                   (startTxPreType),
		.startTxFormatMod                 (startTxFormatMod),
		.startTxNumExtnSS                 (startTxNumExtnSS),
		.startTxSTBC                      (startTxSTBC),
		.startTxLSTP                      (startTxLSTP),
		.startTxShortGI                   (startTxShortGI),
		.startTxFecCoding                 (startTxFecCoding),
		.bbServiceA                       (bbServiceA),
		.bbServiceB                       (bbServiceB),
		.startTxNTx                       (startTxNTx),
		.keepTXOPOpen                     (keepTXOPOpen),
		.remTXOPInDurField                (remTXOPInDurField),
.sendCFEnd                        (sendCFEnd),
		.sendCFEndNow                     (sendCFEndNow),
		.sendCFEndNowInValid              (sendCFEndNowInValid),
		.sendCFEndNowIn                   (sendCFEndNowIn),
		.dynBWEn                          (dynBWEn),
		.dropToLowerBW                    (dropToLowerBW),
		.numTryBWAcquisition              (numTryBWAcquisition),
		.defaultBWTXOP                    (defaultBWTXOP),
		.defaultBWTXOPV                   (defaultBWTXOPV),
		.aPPDUMaxTime                     (aPPDUMaxTime),
		.maxSupportedBW                   (maxSupportedBW),
		.supportLSTP                      (supportLSTP),
		.bssBasicRateSet                  (bssBasicRateSet),
		.bssBasicHTMCSSetEM               (bssBasicHTMCSSetEM),
		.bssBasicHTMCSSetUM               (bssBasicHTMCSSetUM),
		.bssBasicVHTMCSSet                (bssBasicVHTMCSSet),
`ifdef RW_WLAN_COEX_EN                
    .coexEnable                       (coexEnable),
    .coexPTIBKData                    (coexPTIBKData),
    .coexPTIBEData                    (coexPTIBEData),
    .coexPTIVIData                    (coexPTIVIData),
    .coexPTIVOData                    (coexPTIVOData),
    .coexPTIBcnData                   (coexPTIBcnData),
    .coexPTIMgt                       (coexPTIMgt),
    .coexPTICntl                      (coexPTICntl),
    .coexPTIAck                       (coexPTIAck),
    .coexWlanTx                       (coexWlanTx),
    .coexWlanRx                       (coexWlanRx),
    .coexWlanTxAbort                  (coexWlanTxAbortGated),
    .coexWlanPTI                      (coexWlanPTI),
    .coexWlanPTIToggle                (coexWlanPTIToggle),
    .coexWlanChanBw                   (coexWlanChanBw),
`endif // RW_WLAN_COEX_EN                
		.backoffOffset                    (backoffOffset),
		.currentCW0                       (currentCW0),
		.currentCW1                       (currentCW1),
		.currentCW2                       (currentCW2),
		.currentCW3                       (currentCW3),
		.ac3QSRC                          (ac3QSRC),
		.ac2QSRC                          (ac2QSRC),
		.ac1QSRC                          (ac1QSRC),
		.ac0QSRC                          (ac0QSRC),
		.ac3QLRC                          (ac3QLRC),
		.ac2QLRC                          (ac2QLRC),
		.ac1QLRC                          (ac1QLRC),
		.ac0QLRC                          (ac0QLRC),
		.activeAC                         (activeAC),
		.keyStoRAMReset                   (keyStoRAMReset),
		.keyStoRAMResetIn                 (keyStoRAMResetIn),
		.keyStoRAMResetInValid            (keyStoRAMResetInValid),
		.debugKSR                         (debugKSR),
		.encrKeyRAMWord0                  (encrKeyRAMWord0),
		.encrKeyRAMWord1                  (encrKeyRAMWord1),
		.encrKeyRAMWord2                  (encrKeyRAMWord2),
		.encrKeyRAMWord3                  (encrKeyRAMWord3),
`ifdef RW_WAPI_EN
		.encrIntKeyRAMWord0               (encrIntKeyRAMWord0),
		.encrIntKeyRAMWord1               (encrIntKeyRAMWord1),
		.encrIntKeyRAMWord2               (encrIntKeyRAMWord2),
		.encrIntKeyRAMWord3               (encrIntKeyRAMWord3),
`endif //RW_WAPI_EN
		.macAddrRAMLow                    (macAddrRAMLow),
		.macAddrRAMHigh                   (macAddrRAMHigh),
		.encrKeyRAMWord0In                (encrKeyRAMWord0In),
		.encrKeyRAMWord1In                (encrKeyRAMWord1In),
		.encrKeyRAMWord2In                (encrKeyRAMWord2In),
		.encrKeyRAMWord3In                (encrKeyRAMWord3In),
`ifdef RW_WAPI_EN
		.encrIntKeyRAMWord0In             (encrIntKeyRAMWord0In),
		.encrIntKeyRAMWord1In             (encrIntKeyRAMWord1In),
		.encrIntKeyRAMWord2In             (encrIntKeyRAMWord2In),
		.encrIntKeyRAMWord3In             (encrIntKeyRAMWord3In),
`endif //RW_WAPI_EN
		.macAddrRAMLowIn                  (macAddrRAMLowIn),
		.macAddrRAMHighIn                 (macAddrRAMHighIn),
		.encrKeyRAMWord0InValid           (encrKeyRAMWord0InValid),
		.encrKeyRAMWord1InValid           (encrKeyRAMWord1InValid),
		.encrKeyRAMWord2InValid           (encrKeyRAMWord2InValid),
		.encrKeyRAMWord3InValid           (encrKeyRAMWord3InValid),
`ifdef RW_WAPI_EN
		.encrIntKeyRAMWord0InValid        (encrIntKeyRAMWord0InValid),
		.encrIntKeyRAMWord1InValid        (encrIntKeyRAMWord1InValid),
		.encrIntKeyRAMWord2InValid        (encrIntKeyRAMWord2InValid),
		.encrIntKeyRAMWord3InValid        (encrIntKeyRAMWord3InValid),
`endif //RW_WAPI_EN
		.macAddrRAMLowInValid             (macAddrRAMLowInValid),
		.macAddrRAMHighInValid            (macAddrRAMHighInValid),
		.keyIndexRAM                      (keyIndexRAM),
		.newWrite                         (newWrite),
		.newWriteIn                       (newWriteIn),
		.newWriteInValid                  (newWriteInValid),
		.newRead                          (newRead),
		.newReadIn                        (newReadIn),
		.newReadInValid                   (newReadInValid),
		.cLenRAM                          (cLenRAM),
		.cLenRAMIn                        (cLenRAMIn),
		.cLenRAMInValid                   (cLenRAMInValid),
		.useDefKeyRAM                     (useDefKeyRAM),
		.useDefKeyRAMIn                   (useDefKeyRAMIn),
		.useDefKeyRAMInValid              (useDefKeyRAMInValid),
		.sppRAM                           (sppRAM),
		.sppRAMIn                         (sppRAMIn),
		.sppRAMInValid                    (sppRAMInValid),
		.vlanIDRAM                        (vlanIDRAM),
		.vlanIDRAMIn                      (vlanIDRAMIn),
		.vlanIDRAMInValid                 (vlanIDRAMInValid),
		.cTypeRAM                         (cTypeRAM),
		.cTypeRAMIn                       (cTypeRAMIn),
		.cTypeRAMInValid                  (cTypeRAMInValid),
		.debugPortMACTimerUnit            (debugPortMACTimerUnit),
		.debugPortMACTimerUnit2           (debugPortMACTimerUnit2),
		.debugPortMACTimerUnit3           (debugPortMACTimerUnit3),
		.debugPortBackoff                 (debugPortBackoff),
		.debugPortBackoff2                (debugPortBackoff2),
		.debugPortBackoff3                (debugPortBackoff3),
		.debugPortDeaggregator            (debugPortDeaggregator),
		.debugPortDeaggregator2           (debugPortDeaggregator2),
		.debugPortDeaggregatorFsm         (debugPortDeaggregatorFsm),
		.debugPortRxController            (debugPortRxController),
		.debugPortRxFrameDebug1           (debugPortRxFrameDebug1),
		.debugPortRxFrameDebug2           (debugPortRxFrameDebug2),
		.debugPortTxFrameDebug1           (debugPortTxFrameDebug1),
		.debugPortTxFrameDebug2           (debugPortTxFrameDebug2),
		.debugPortBAController            (debugPortBAController),
		.debugPortBAController2           (debugPortBAController2),
		.debugPortBAController3           (debugPortBAController3),
		.debugPortTxParametersCache       (debugPortTxParametersCache),
		.debugPortMACController1          (debugPortMACController1),
		.debugPortMediumAccess            (debugPortMediumAccess),
		.debugPortNAV                     (debugPortNAV),
		.debugPortMACControllerRx         (debugPortMACControllerRx),
		.debugPortMACControllerTx         (debugPortMACControllerTx),
		.debugPortBWManagement            (debugPortBWManagement),
		.debugPortAMPDU                   (debugPortAMPDU[13:0]),
		.debugPortEncryptionEngine        (debugPortEncryptionEngine),
`ifdef RW_WAPI_EN
    .debugPortWapi                    (debugPortWapi),
`endif //RW_WAPI_EN
		.debugPortKeySearch               (debugPortKeySearch),
		.debugPortrxFIFOCntrl             (debugPortrxFIFOCntrl),
		.debugPortDecryptFsm              (debugPortDecryptFsm),
		.debugPortDozeController          (debugPortDozeController)
		);


// Instanciation of macPhyIf
// Name of the instance : U_macPhyIf
// Name of the file containing this module : macPhyIf.v
macPhyIf U_macPhyIf (
		.mpIFClk                          (mpIFClk),
		.mpIFClkHardRst_n                 (mpIFClkHardRst_n),
		.mpIFClkSoftRst_n                 (mpifSoftRst_n),
		.macCoreRxClk                     (macCoreClk),
		.macCoreTxClk                     (macCoreClk),
    //.macCoreTxClk                     (macCoreTxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (macCoreClkSoftRst_n),
		.phyRdy                           (phyRdy),
		.txEnd_p                          (txEnd_p),
		.rxData                           (rxData),
		.CCAPrimary20                     (CCAPrimary20),
		.CCASecondary20                   (CCASecondary20),
		.CCASecondary40                   (CCASecondary40),
		.CCASecondary80                   (CCASecondary80),
		.rxEndForTiming_p                 (rxEndForTiming_p),
		.rxErr_p                          (rxErr_p),
		.rxEnd_p                          (rxEnd_p),
		.phyErr_p                         (phyErr_p),
		.rifsRxDetected                   (rifsRxDetected),
		.txReq                            (txReq),
		.rxReq                            (rxReq),
		.txData                           (txData),
		.macDataValid                     (macDataValid),
		.mimoCmdValid                     (mimoCmdValid),
		.keepRFOn                         (keepRFOn),
		.startRx                          (startRx),
		.stopRx_p                         (stopRx_p),
		.mpifKeepRFon                     (mpifKeepRFon),
		.macPhyIfRxStart_p                (macPhyIfRxStart_p),
		.macPhyIfRxFlush_p                (macPhyIfRxFlush_p),
		.startTx_p                        (startTx_p),
		.stopTx_p                         (stopTx_p),
		.mpIfTxFifoData                   (mpIfTxFifoData),
		.mpIfTxFifoWrite                  (mpIfTxFifoWrite),
		.txPwrLevel                       (txPwrLevel),
		.chBW                             (chBW),
		.chOffset                         (chOffset),
		.smoothing                        (smoothing),
		.antennaSet                       (antennaSet),
		.smmIndex                         (smmIndex),
		.mcs                              (mcs),
		.preType                          (preType),
		.formatMod                        (formatMod),
		.numExtnSS                        (numExtnSS),
		.stbc                             (stbc),
		.fecCoding                        (fecCoding),
		.sounding                         (sounding),
		.legLength                        (legLength),
		.legRate                          (legRate),
		.service                          (service),
		.htLength                         (htLength),
		.nTx                              (nTx),
		.nSTS                             (nSTS),
		.shortGI                          (shortGI),
		.aggreation                       (aggreation),
		.beamFormed                       (beamFormed),
		.disambiguityBit                  (disambiguityBit),
		.partialAID                       (partialAID),
		.groupID                          (groupID),
		.dozeNotAllowed                   (dozeNotAllowed),
		.continuousTx                     (continuousTx),
		.mpIfTxFifoFull                   (mpIfTxFifoFull),
		.mpIfTxErr_p                      (mpIfTxErr_p),
		.mpIfTxEn                         (mpIfTxEn),
		.macPhyTxEnd_p                    (macPhyTxEnd_p),
		.macPhyIfRxFifoReadEn             (macPhyIfRxFifoReadEn),
		.macPhyIfRxFifoEmpty              (macPhyIfRxFifoEmpty),
		.macPhyIfRxFifoData               (macPhyIfRxFifoData),
		.macPhyIfRxErr_p                  (macPhyIfRxErr_p),
		.macPhyIfRxEnd_p                  (macPhyIfRxEnd_p),
		.macPhyIfRxEndForTiming_p         (macPhyIfRxEndForTiming_p),
		.macPhyIfRifsRxDetected           (macPhyIfRifsRxDetected),
		.macPhyIfRxCca                    (macPhyIfRxCca),
		.macPhyIfRxCcaSec20               (macPhyIfRxCcaSec20),
		.macPhyIfRxCcaSec40               (macPhyIfRxCcaSec40),
		.macPhyIfRxCcaSec80               (macPhyIfRxCcaSec80),
		.macPHYIFFIFOReset                (macPHYIFFIFOReset),
		.macPHYIFFIFOResetInValid         (macPHYIFFIFOResetInValid),
		.rateControllerMPIF               (rateControllerMPIF),
		.rxReqForceDeassertion            (rxReqForceDeassertion),
		.macPHYIFUnderRun                 (macPHYIFUnderRun),
		.macPHYIFOverflow                 (macPHYIFOverflow),
		.mpIFTxFIFOReadData               (mpIFTxFIFOReadData),
		.mpIFTxFIFOWriteData              (mpIFTxFIFOWriteData),
		.mpIFTxFIFOWriteAddr              (mpIFTxFIFOWriteAddr),
		.mpIFTxFIFOWriteEn                (mpIFTxFIFOWriteEn),
		.mpIFTxFIFOReadAddr               (mpIFTxFIFOReadAddr),
		.mpIFTxFIFOReadEn                 (mpIFTxFIFOReadEn),
		.mpIFRxFIFOReadData               (mpIFRxFIFOReadData),
		.mpIFRxFIFOWriteData              (mpIFRxFIFOWriteData),
		.mpIFRxFIFOWriteAddr              (mpIFRxFIFOWriteAddr),
		.mpIFRxFIFOWriteEn                (mpIFRxFIFOWriteEn),
		.mpIFRxFIFOReadAddr               (mpIFRxFIFOReadAddr),
		.mpIFRxFIFOReadEn                 (mpIFRxFIFOReadEn),
		.debugPortMACPhyIf                (debugPortMACPhyIf),
		.debugPortMACPhyIf2               (debugPortMACPhyIf2)
		);

assign macPHYIFFIFOResetIn = 1'b0;



////////////////////////////////////////////////////
/// DEBUG port assignment
////////////////////////////////////////////////////


//Important Note : macControlCs MSB is not connected to debugPort. 
//                 macController Tx FSM : DROPBW_LENGTH_UPDATE state will appear as "IDLE"
assign debugPortMainFSM1 = {txControlCs, macControlCs[7:5], macControlCs[3:0]};
assign debugPortMainFSM2 = {debugPortDeaggregatorFsm, rxControlCs, macControlCs[7:5],macControlCs[3:0]};

assign debugPortMainFSM = (txControlCs == 9'd0) ? debugPortMainFSM2 : debugPortMainFSM1;
// Instanciation of debugPortCtrl
// Name of the instance : U_debugPortCtrl
// Name of the file containing this module : debugPortCtrl.v
debugPortCtrl U_debugPortCtrl (
		.debugPortSel1          (debugPortSel1),
		.debugPortSel2          (debugPortSel2),
		.debugPortRead          (debugPortRead),
		.debugPort              (debugPort),
		.debugPortInt1          (debugPortBackoff),
		.debugPortInt2          (debugPortMainFSM1),
		.debugPortInt3          (debugPortMainFSM2),
		.debugPortInt4          (debugPortDMA1),
		.debugPortInt5          (debugPortMACTimerUnit),
		.debugPortInt6          (debugPortDeaggregator),
		.debugPortInt7          (debugPortRxController),
		.debugPortInt8          (debugPortDMA2),
		.debugPortInt9          (debugPortFrameDebug1),
		.debugPortInt10         (debugPortFrameDebug2),
		.debugPortInt11         (debugPortInterrupt),
		.debugPortInt12         (debugPortMACPhyIf),
		.debugPortInt13         (debugPortBAController),
		.debugPortInt14         (debugPortTxParametersCache),
		.debugPortInt15         (debugPortMACController1),
		.debugPortInt16         (debugPortDMA3),
		.debugPortInt17         (debugPortDMA4),
		.debugPortInt18         (debugPortDMA5),
		.debugPortInt19         (debugPortDMA6),
		.debugPortInt20         (debugPortMediumAccess),
		.debugPortInt21         (debugPortNAV),
		.debugPortInt22         (debugPortMACControllerRx),
		.debugPortInt23         (debugPortBAController2),
		.debugPortInt24         (debugPortBAController3),
		.debugPortInt25         (debugPortEncryptionEngine[15:0]),
		.debugPortInt26         (debugPortEncryptionEngine[31:16]),
		.debugPortInt27         (debugPortMACControllerTx),
		.debugPortInt28         (debugPortDMAStatus),
		.debugPortInt29         (debugPortAMPDU),
		.debugPortInt30         (debugPortDMATxStatus),
		.debugPortInt31         (swProf[15:0]),
		.debugPortInt32         (swProf[31:16]),
		.debugPortInt33         (debugPortKeySearch),
		.debugPortInt34         (debugPortrxFIFOCntrl),
		.debugPortInt35         (debugPortDecryptFsm),
		.debugPortInt36         (debugPortTxRxListA),
		.debugPortInt37         (debugPortDmaRdWrCtlr),
		.debugPortInt38         (debugPortMainFSM),
		.debugPortInt39         (debugPortDeaggregator2),
		.debugPortInt40         (debugPortMACTimerUnit2),
		.debugPortInt41         (debugPortMACTimerUnit3),
		.debugPortInt42         (debugPortDozeController),
		.debugPortInt43         (debugPortBWManagement),
		.debugPortInt44         (debugPortBackoff2),
		.debugPortInt45         (debugPortBackoff3),
		.debugPortInt46         (debugPortClockGating),
		.debugPortInt47         (debugPortClock),
`ifdef RW_WAPI_EN
    .debugPortInt49         (debugPortWapi),
`endif //RW_WAPI_EN
		.debugPortInt48         (debugPortMACPhyIf2)

    );

`ifdef RW_SWPROF_DEBUG_PORT
  // Additional debugPort dedicated to SW profiling
  assign swProfDebugPort = swProf;
`endif // RW_SWPROF_DEBUG_PORT



assign debugPortAMPDU[15] = !intRxTrigger_n;
assign debugPortAMPDU[14] = !intTxTrigger_n;

// Mux debugPortTxFrameDebug and debugPortRxFrameDebug
assign debugPortFrameDebug1 = (debugPortTxFrameDebug1[15]) ? {2'b10,debugPortTxFrameDebug1[13:0]} 
                                         : (debugPortRxFrameDebug1[15]) ? {2'b01,debugPortRxFrameDebug1[13:0]} 
                                                                        : 16'b0;
assign debugPortFrameDebug2 = (debugPortTxFrameDebug1[15]) ? debugPortTxFrameDebug2
                                         : (debugPortRxFrameDebug1[15]) ? debugPortRxFrameDebug2
                                                                        : 16'b0;

// Debug Port Interrupts assignment
assign debugPortInterrupt = {(phyErr | hwErr | macPHYIFUnderRun | rxFIFOOverFlow),
                             (bcnTxDMADead | ac0TxDMADead | ac1TxDMADead | ac2TxDMADead | ac3TxDMADead | ptError),
                             (ac3TxTrigger | ac2TxTrigger | ac1TxTrigger | ac0TxTrigger | bcnTxTrigger),
                             rxDMAEmpty,
                             idleInterrupt,
                             absTimers[1],
                             absTimers[0],
                             (impPriDTIM | impSecDTIM),
                             (impPriTBTT | impSecTBTT),                                                           
                             txopComplete,
                             !intGen_n,         
                             !intProtTrigger_n, 
                             !intTxTrigger_n,   
                             !intRxTrigger_n,   
                             !intTxRxMisc_n,    
                             !intTxRxTimer_n};  
                             
assign debugPortClockGating = {4'b0,
                               macSecClkEn,
                               activeClkGating,
                               macPriClkEn,
                               platformWakeUp,
                               macPITxClkEn,
                               macPIRxClkEn,
                               macCoreTxClkEn,
                               macCoreRxClkEn,
                               macCryptClkEn,
                               macLPClkSwitch,
                               macWTClkEn,
                               mpIFClkEn};


reg  macPIClkDbg;              // Primary MAC Platform Interface Clock
reg  macPITxClkDbg;            // Secondary MAC Platform Interface Clock for TX
reg  macPIRxClkDbg;            // Secondary MAC Platform Interface Clock for RX
reg  macPISlaveClkDbg;         // MAC Platform Interface Slave Clock
reg  macCoreClkDbg;            // Primary MAC Core Clock
reg  macCryptClkDbg;           // Secondary MAC Core Clock for encryption
reg  macCoreTxClkDbg;          // Secondary MAC Core Clock for TX
reg  macCoreRxClkDbg;          // Secondary MAC Core Clock for RX
reg  macLPClkDbg;              // MAC Low Power clock. 
reg  macWTClkDbg;              // Clock input for WEP/TKIP blocks.
reg  mpIFClkDbg;               // MAC PHY Interface Clock

assign debugPortClock = {                             
      macLPClkSwitch,
      macCoreTxClkEn,
      macCoreRxClkEn,
      activeClkGating,
      macPriClkEn,
macPIClkDbg,       
macPITxClkDbg,     
macPIRxClkDbg,     
macPISlaveClkDbg,  
macCoreClkDbg,     
macCryptClkDbg,    
macCoreTxClkDbg,   
macCoreRxClkDbg,   
macLPClkDbg,       
macWTClkDbg,       
mpIFClkDbg};

        
always @ (posedge macPIClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPIClkDbg <= 1'b0;
  else 
    macPIClkDbg <= ~macPIClkDbg;
end
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPITxClkDbg <= 1'b0;
  else 
    macPITxClkDbg <= ~macPITxClkDbg;
end

always @ (posedge macPIRxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPIRxClkDbg <= 1'b0;
  else 
    macPIRxClkDbg <= ~macPIRxClkDbg;
end
always @ (posedge macPISlaveClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPISlaveClkDbg <= 1'b0;
  else 
    macPISlaveClkDbg <= ~macPISlaveClkDbg;
end
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macCoreClkDbg <= 1'b0;
  else 
    macCoreClkDbg <= ~macCoreClkDbg;
end
always @ (posedge macCryptClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macCryptClkDbg <= 1'b0;
  else 
    macCryptClkDbg <= ~macCryptClkDbg;
end
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macCoreTxClkDbg <= 1'b0;
  else 
    macCoreTxClkDbg <= ~macCoreTxClkDbg;
end
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macCoreRxClkDbg <= 1'b0;
  else 
    macCoreRxClkDbg <= ~macCoreRxClkDbg;
end
always @ (posedge macLPClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macLPClkDbg <= 1'b0;
  else 
    macLPClkDbg <= ~macLPClkDbg;
end
always @ (posedge macWTClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macWTClkDbg <= 1'b0;
  else 
    macWTClkDbg <= ~macWTClkDbg;
end
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    mpIFClkDbg <= 1'b0;
  else 
    mpIFClkDbg <= ~mpIFClkDbg;
end


// Generate internalError indication based on the different error flags 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    internalError <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (hwFSMResetCoreClk == 1'b1)) // Synchronous Reset
     internalError <= 1'b0;
  else if (phyErr | hwErr | macPHYIFOverflow | macPHYIFUnderRun | rxFIFOOverFlow | dmaInternalError)
     internalError <= 1'b1;
end


////////////////////////////////////////////////////////////////////////////////
// Coex
////////////////////////////////////////////////////////////////////////////////
`ifdef RW_WLAN_COEX_EN
assign coexWlanTxAbortGated = coexWlanTxAbortResync && coexEnable;

// Instanciation of simpleSynchro
// Name of the instance : U_coexWlanTxAbort_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_coexWlanTxAbort_synchro (
                .dstclk             (macCoreClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (coexWlanTxAbort),
                .dstdata            (coexWlanTxAbortResync)
                );


`endif // RW_WLAN_COEX_EN

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
initial
begin
  $display(" ");
  $display("DUT Configuration");
  $display("-----------------");
  $display(" ");
  $display("  Features:");

  $display("    - MACHW_COEX        : %0d",`MACHW_COEX);
  $display("    - MACHW_VHT         : %0d",`MACHW_VHT);
  $display("    - MACHW_TPC         : %0d",`MACHW_TPC);
  $display("    - MACHW_HT          : %0d",`MACHW_HT);
  $display("    - MACHW_RCE         : %0d",`MACHW_RCE);
  $display("    - MACHW_CCMP        : %0d",`MACHW_CCMP);
  $display("    - MACHW_TKIP        : %0d",`MACHW_TKIP);
  $display("    - MACHW_WAPI        : %0d",`MACHW_WAPI);
  $display("    - MACHW_WEP         : %0d",`MACHW_WEP);
  $display("    - MACHW_SECURITY    : %0d",`MACHW_SECURITY);
  $display("    - MACHW_EDCA        : %0d",`MACHW_EDCA);
  $display("    - MACHW_QOS         : %0d",`MACHW_QOS);

`ifdef RW_MAC_MIBCNTL_EN  
  $display("    - RW_MAC_MIBCNTL_EN : 1");
`else        
  $display("    - RW_MAC_MIBCNTL_EN : 0");
`endif
`ifdef RW_MPDU_AC  
  $display("    - mac80211MHFormat  : 1");
`else        
  $display("    - mac80211MHFormat  : 0");
`endif
  $display(" ");

  $display("    - RW_MPIF_11AC");
  $display("    - RW_TXDESC_11AC");
  $display("    - RW_RXDESC_11AC");

`ifdef RW_TXTIME_DIVIDER_ONECYCLE  
  $display("    - RW_TXTIME_DIVIDER_ONECYCLE");
`else        
  $display("    - RW_TXTIME_DIVIDER_FIVECYCLE");
`endif

  $display(" ");

  $display("  Clocks:");
  $display("    - MAC_FREQ          : %0d",`MAC_FREQ);
`ifdef PRNG_FASTER_CLK
  $display("    - WT_CLOCK_FREQ     : %0d",`MAC_FREQ*`WEP_2_BB_CLK_RATIO);
  $display("    - WEP_2_BB_CLK_RATIO: %0d",`WEP_2_BB_CLK_RATIO);
`else  
  $display("    - WT_CLOCK_FREQ     : %0d",`MAC_FREQ);
`endif
  $display(" ");
  $display(" ");

end
`endif // RW_SIMU_ON

`ifdef RW_AHBSPY_ON

ahbSpy #(.ahbSpyNumber(0)) U_ahbMasterSpy (
  .resetn     (macPIClkHardRst_n),
  .clk        (macPIClk),
  .hready_in  (hMReady),
  .hsel       (hMSelSpy),
  .haddr      (hMAddr),
  .htrans     (hMTrans),
  .hburst     (hMBurst),
  .hsize      (hMSize),
  .hwrite     (hMWrite),
  .hresp      (hMResp),
  .hready     (hMReady),
  .hit        ()
  );

ahbSpy #(.ahbSpyNumber(1)) U_ahbSlaveSpy (
  .resetn     (macPIClkHardRst_n),
  .clk        (macPIClk),
  .hready_in  (hSReadyOut),
  .hsel       (hSSelSpy),
  .haddr      (hSAddrSpy),
  .htrans     (hSTrans),
  .hburst     (hSBurst),
  .hsize      (hSSize),
  .hwrite     (hSWrite),
  .hresp      (hSResp),
  .hready     (hSReadyOut),
  .hit        ()
  );

assign hMSelSpy  = {7'b0, 1'b1};
assign hSSelSpy  = {7'b0, 1'b1};
assign hSAddrSpy = {16'b0, hSAddr};

`endif // RW_AHBSPY_ON


`ifdef RW_ASSERT_ON
///////////////////////////////////////////////////////
// External Memory Interface Checks
///////////////////////////////////////////////////////

//$rw_sva Check addr and data in case of Write Access in mpIFTXFifo
property mpIFTXFifo_CheckAddrAndDataInWrite_prop;
@(posedge macCoreTxClk)
  disable iff(!macCoreClkHardRst_n)
  mpIFTxFIFOWriteEn |-> (^mpIFTxFIFOWriteAddr !== 1'bX && ^mpIFTxFIFOWriteData !== 1'bX);
endproperty
mpIFTXFifo_CheckAddrAndDataInWrite: assert property (mpIFTXFifo_CheckAddrAndDataInWrite_prop); 

//$rw_sva Check addr in case of Read Access in mpIFTXFifo
property mpIFTXFifo_CheckAddrInRead_prop;
@(posedge mpIFClk)
  disable iff(!mpIFClkHardRst_n)
  mpIFTxFIFOReadEn |-> (^mpIFTxFIFOReadAddr !== 1'bX);
endproperty
mpIFTXFifo_CheckAddrInRead: assert property (mpIFTXFifo_CheckAddrInRead_prop); 


//$rw_sva Check addr and data in case of Write Access in mpIFRxFIFO
property mpIFRxFIFO_CheckAddrAndDataInWrite_prop;
@(posedge mpIFClk)
  disable iff(!mpIFClkHardRst_n)
  mpIFRxFIFOWriteEn |-> (^mpIFRxFIFOWriteAddr !== 1'bX && ^mpIFRxFIFOWriteData !== 1'bX);
endproperty
mpIFRxFIFO_CheckAddrAndDataInWrite: assert property (mpIFRxFIFO_CheckAddrAndDataInWrite_prop); 

//$rw_sva Check addr in case of Read Access in mpIFRxFIFO
property mpIFRxFIFO_CheckAddrInRead_prop;
@(posedge macCoreTxClk)
  disable iff(!macCoreClkHardRst_n)
  mpIFRxFIFOReadEn |-> (^mpIFRxFIFOReadAddr !== 1'bX);
endproperty
mpIFRxFIFO_CheckAddrInRead: assert property (mpIFRxFIFO_CheckAddrInRead_prop); 


//$rw_sva Check addr in case of Write Access in txFifo
property txFifo_CheckAddrInWrite_prop;
@(posedge macPITxClk)
  disable iff(!macPIClkHardRst_n)
  txFIFOWriteEn |-> (^txFIFOWriteAddr !== 1'bX);
endproperty
txFifo_CheckAddrInWrite: assert property (txFifo_CheckAddrInWrite_prop); 

//$rw_sva Check data in case of Write Access in txFifo
property txFifo_CheckDataInWrite_prop;
@(posedge macPITxClk)
  disable iff(!macPIClkHardRst_n)
  txFIFOWriteEn |-> (^(txFIFOWriteData & {{6{1'b1}},{8{txFIFOWriteData[35]}},{8{txFIFOWriteData[34]}},{8{txFIFOWriteData[33]}},{8{txFIFOWriteData[32]}}}) !== 1'bX);
endproperty
txFifo_CheckDataInWrite: assert property (txFifo_CheckDataInWrite_prop); 

//$rw_sva Check addr in case of Read Access in txFifo
property txFifo_CheckAddrInRead_prop;
@(posedge macCoreTxClk)
  disable iff(!macCoreClkHardRst_n)
  txFIFOReadEn |-> (^txFIFOReadAddr !== 1'bX);
endproperty
txFifo_CheckAddrInRead: assert property (txFifo_CheckAddrInRead_prop); 


//$rw_sva Check addr and data in case of Write Access in rxFifo
property rxFifo_CheckAddrAndDataInWrite_prop;
@(posedge macCoreTxClk)
  disable iff(!macCoreClkHardRst_n)
  rxFIFOWriteEn |-> (^rxFIFOWriteAddr !== 1'bX && ^rxFIFOWriteData !== 1'bX);
endproperty
rxFifo_CheckAddrAndDataInWrite: assert property (rxFifo_CheckAddrAndDataInWrite_prop); 

//$rw_sva Check addr in case of Read Access in rxFifo
property rxFifo_CheckAddrInRead_prop;
@(posedge macPIRxClk)
  disable iff(!macPIClkHardRst_n)
  rxFIFOReadEn |-> (^rxFIFOReadAddr !== 1'bX);
endproperty
rxFifo_CheckAddrInRead: assert property (rxFifo_CheckAddrInRead_prop); 


//$rw_sva Check addr and data in case of Write Access in keyStorage
property keyStorage_CheckAddrAndDataInWrite_prop;
@(posedge macCoreClk)
  disable iff(!macCoreClkHardRst_n)
  keyStorageWriteEn |-> (keyStorageEn === 1 && ^keyStorageAddr !== 1'bX && ^keyStorageWriteData !== 1'bX);
endproperty
keyStorage_CheckAddrAndDataInWrite: assert property (keyStorage_CheckAddrAndDataInWrite_prop); 

//$rw_sva Check addr in case of Read Access in keyStorage
property keyStorage_CheckAddrInRead_prop;
@(posedge macCoreClk)
  disable iff(!macCoreClkHardRst_n)
  keyStorageEn |-> (^keyStorageAddr !== 1'bX);
endproperty
keyStorage_CheckAddrInRead: assert property (keyStorage_CheckAddrInRead_prop); 


`ifdef RW_MAC_MIBCNTL_EN

//$rw_sva Check addr and data in case of Write Access in mibTable
property mibTable_CheckAddrAndDataInWrite_prop;
@(posedge macCoreClk)
  disable iff(!macCoreClkHardRst_n)
  mibTableWriteEn |-> (mibTableEn === 1 && ^mibTableAddr !== 1'bX && ^mibTableWriteData !== 1'bX);
endproperty
mibTable_CheckAddrAndDataInWrite: assert property (mibTable_CheckAddrAndDataInWrite_prop); 

//$rw_sva Check addr in case of Read Access in mibTable
property mibTable_CheckAddrInRead_prop;
@(posedge macCoreClk)
  disable iff(!macCoreClkHardRst_n)
  mibTableEn |-> (^mibTableAddr !== 1'bX);
endproperty
mibTable_CheckAddrInRead: assert property (mibTable_CheckAddrInRead_prop); 

`endif // RW_MAC_MIBCNTL_EN


//$rw_sva Check addr and data in case of Write Access in psBitmap
property psBitmap_CheckAddrAndDataInWrite_prop;
@(posedge macCoreClk)
  disable iff(!macCoreClkHardRst_n)
  psBitmapWriteEn |-> (psBitmapEn === 1 && ^psBitmapAddr !== 1'bX && ^psBitmapWriteData !== 1'bX);
endproperty
psBitmap_CheckAddrAndDataInWrite: assert property (psBitmap_CheckAddrAndDataInWrite_prop); 

//$rw_sva Check addr in case of Read Access in psBitmap
property psBitmap_CheckAddrInRead_prop;
@(posedge macCoreClk)
  disable iff(!macCoreClkHardRst_n)
  psBitmapEn |-> (^psBitmapAddr !== 1'bX);
endproperty
psBitmap_CheckAddrInRead: assert property (psBitmap_CheckAddrInRead_prop); 


//$rw_sva Check addr and data in case of Write Access in encrRxFIFO
property encrRxFIFO_CheckAddrAndDataInWrite_prop;
@(posedge mpIFClk)
  disable iff(!mpIFClkHardRst_n)
  encrRxFIFOWriteEn |-> (^encrRxFIFOWriteAddr !== 1'bX && ^encrRxFIFOWriteData !== 1'bX);
endproperty
encrRxFIFO_CheckAddrAndDataInWrite: assert property (encrRxFIFO_CheckAddrAndDataInWrite_prop); 

//$rw_sva Check addr in case of Read Access in encrRxFIFO
property encrRxFIFO_CheckAddrInRead_prop;
@(posedge macCoreTxClk)
  disable iff(!macCoreClkHardRst_n)
  encrRxFIFOReadEn |-> (^encrRxFIFOReadAddr !== 1'bX);
endproperty
encrRxFIFO_CheckAddrInRead: assert property (encrRxFIFO_CheckAddrInRead_prop); 


//$rw_sva Check addr and data in case of Write Access in sBoxA
property sBoxA_CheckAddrAndDataInWrite_prop;
@(posedge macCryptClk)
  disable iff(!macCoreClkHardRst_n)
  sBoxAWriteEn |-> (sBoxAEn === 1 && ^sBoxAAddr !== 1'bX && ^sBoxAWriteData !== 1'bX);
endproperty
sBoxA_CheckAddrAndDataInWrite: assert property (sBoxA_CheckAddrAndDataInWrite_prop); 

//$rw_sva Check addr in case of Read Access in sBoxA
property sBoxA_CheckAddrInRead_prop;
@(posedge macCryptClk)
  disable iff(!macCoreClkHardRst_n)
  sBoxAEn |-> (^sBoxAAddr !== 1'bX);
endproperty
sBoxA_CheckAddrInRead: assert property (sBoxA_CheckAddrInRead_prop); 


//$rw_sva Check addr and data in case of Write Access in sBoxB
property sBoxB_CheckAddrAndDataInWrite_prop;
@(posedge macCryptClk)
  disable iff(!macCoreClkHardRst_n)
  sBoxBWriteEn |-> (sBoxBEn === 1 && ^sBoxBAddr !== 1'bX && ^sBoxBWriteData !== 1'bX);
endproperty
sBoxB_CheckAddrAndDataInWrite: assert property (sBoxB_CheckAddrAndDataInWrite_prop); 

//$rw_sva Check addr in case of Read Access in sBoxB
property sBoxB_CheckAddrInRead_prop;
@(posedge macCryptClk)
  disable iff(!macCoreClkHardRst_n)
  sBoxBEn |-> (^sBoxBAddr !== 1'bX);
endproperty
sBoxB_CheckAddrInRead: assert property (sBoxB_CheckAddrInRead_prop); 

`endif
endmodule
                    