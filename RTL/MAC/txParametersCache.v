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
// Description      : Top level of txParametersCache module
//                    
// Simulation Notes : 
//    For simulation, two defines are available
//
//    RW_SIMU_ON   : which creates string signals to display the FSM states on  
//                the waveform viewers
//
//    RW_ASSERT_ON : which enables System Verilog Assertions.
//
// Synthesis Notes  :
//     All the output signals to the MAC Controller (except txParameterHDReady
//     and txParameterPTReady) are considered as static and does not need 
//     resynchronization before being used by the MAC Cotnroller, TX Controller
//     and MAC-PHY IF. For the topo level synthesis, false path has to be defined
//
//     false_path from (hDescFrame*, hDescPHYCntrl*, hDescMACCntrl*, hDescStatus*
//                      pTablePHYCntrl*, pTableMACCntrl*, pTableMCSInf*)
//                to   (macCoreClk, macCoreTxClk mpIFClk)
//
// Application Note : 
//     All the signals coming from the MAC Controller must be resynchronized
//     to macPITxClk before being connected to this module
//     All the signals coming from the DMA Engine does not require 
//     resynchronization becasue both mnodule are running on the same clock.
//
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
//////////////////////////////////////////////////////////////////////////////


// pragma coverage pragmas = on
// pragma coverage implicit_default=off 

module txParametersCache ( 
          //$port_g Clock and Reset interface
          input wire         macPITxClk,            // MAC Platform Transmit Clock
          input wire         macPIClkHardRst_n,     // Hard Reset for the MAC Platform Clock domain 
                                                    // active low
          input wire         macPIClkSoftRst_n,     // Soft Reset for the MAC Platform Clock domain 
                                                    // active low

          //$port_g txCtrlReg Interface with the DMA Engine
          input wire         txCtrlRegWr,           // TX parameter Cache module signals
                                                    // Write signal to the Tx Parameter Cache.
          input wire  [31:0] txCtrlRegData,         // TX parameter Cache module signals
                                                    // Write signal to the Tx Parameter Cache.
          input wire         txCtrlRegPT,           // Indicates currently Policy table information is
                                                    // being passed.
          input wire         txCtrlRegHD,           // Indicates currently Header descriptor information
                                                    // is being passed.
          input wire         discardPrevHD_p,       // Signal to TX Parameter Cache module.
                                                    // Indicates to discard the recently 
                                                    // fetch Header Descriptor.
          output reg         txCtrlRegBusy,         // Indicates there are 2 sets of parameters 
                                                    // already in the tx Parameter Cache module
                                                    // and not to fetch more.
          
          //$port_g Interface with the MAC Controller
          input  wire        toggleHDSet_p,         // Indicates that the Header Descriptor Set can be toggled
          input  wire        togglePTSet_p,         // Indicates that the Policy Table Set can be toggled
          input  wire        clearSets_p,           // Indicates that the Sets have to be cleared.
          output wire        txParameterHDReady_p,    // Indicates if the Header Descriptor fields are usable 
          output wire        txParameterPTReady_p,    // Indicates if the Policy Table fields are usable
          output wire        txParameterNextPTReady_p,// Indicates if a second policy table has already been loaded

          //$port_g P-Table PHY Control Information 1
          output wire  [2:0] nTxProtPT,             // Number of Transmit Chains for Protection Frame
          output wire  [2:0] nTxPT,                 // Number of Transmit Chains for PPDU
          output reg         shortGIPT,             // Short Guard Interval for Transmission
                                                    // When High, it indicates whether a short Guard Interval
          output wire  [1:0] stbcPT,                // Space Time Block Coding
          output wire        fecCodingPT,           // FEC Coding
          output wire  [1:0] numExtnSSPT,           // Number of Extension Spatial Streams
          output wire        bfFrmExPT,             // Beam Forming Frame Exchange
                                                    // 1'b0: QoS Null/ACK
                                                    // 1'b1: RTS/CTS
          //$port_g P-Table PHY Control Information 2
          output wire        beamFormedPT,          // BeamFormed frame
          output wire  [7:0] smmIndexPT,            // Spatial Map Matrix Index
          output wire  [7:0] antennaSetPT,          // Antenna Set

          //$port_g P-Table MAC Control Information 1
          output wire  [9:0] keySRAMIndex,          // Key Storage RAM Index
          output wire  [9:0] keySRAMIndexRA,        // Key Storage RAM Index for Receiver Address

          //$port_g P-Table MAC Control Information 2
          output wire [11:0] rtsThreshold,          // RTS Threshold
          output wire  [7:0] shortRetryLimit,       // Short Retry Limit
          output wire  [7:0] longRetryLimit,        // Long Retry Limit

          //$port_g H-Descriptor PHY Control Information 
          output wire        useRIFSTx,             // Use RIFS for Transmission
          output wire        continuousTx,          // Enable continuous transmission for this frame 

          //$port_g H-Descriptor Frame Lenght
          output wire [15:0] MPDUFrameLengthTx,     // Length of the MPDU

          //$port_g H-Descriptor Status Information
          output wire        lifetimeExpired,       // Indicates that the lifetime of this MPDU expired

          //$port_g P-Table RATE Control
          output reg   [2:0] formatModProtTx,       // Format and Modulation of Protection frame for Transmission
                                                    // 3'b000: NON-HT
                                                    // 3'b001: NON-HT-DUP-OFDM
                                                    // 3'b010: HT-MF
                                                    // 3'b011: HT-GF
                                                    // 3'b100: VHT
          output reg   [2:0] formatModTx,           // Format and Modulation of PPDU for Transmission
                                                    // Same coding than formatModProtTx
          output reg   [1:0] bwProtTx,              // Band Width of Protection frame for Transmission
          output reg   [1:0] bwTx,                  // Band Width of PPDU for Transmission
          
          //$port_g P-Table Power Control Information
          output reg  [7:0] txPwrLevelPT,          // Transmit Power Level
          output reg  [7:0] txPwrLevelProtPT,      // Transmit Power Level of Protection frame for Transmission
          
          //$port_g H-Descriptor Status Information
          output wire  [7:0] numMPDURetries,        // Indicates the number of MPDU retries already done   
          output wire  [7:0] numRTSRetries,         // Indicates the number of RTS retries already done  
          
          //$port_g H-Descriptor Medium Time used
          output wire [31:0] mediumTimeUsed,        // Indicates the medium time already used for the current descriptor

          //$port_g H-Descriptor Frame Length
          output reg  [19:0] aMPDUFrameLengthTx,    // Length of the entire A-MPDU
          
          //$port_g H-Descriptor Optional Frame Length drop to 20 Mhz
          output reg  [19:0] aMPDUOptFrameLength20Tx,    // Length of the entire A-MPDU
          
          //$port_g H-Descriptor Optional Frame Length drop to 40 Mhz
          output reg  [19:0] aMPDUOptFrameLength40Tx,    // Length of the entire A-MPDU
          
          //$port_g H-Descriptor Optional Frame Length drop to 80 Mhz
          output reg  [19:0] aMPDUOptFrameLength80Tx,    // Length of the entire A-MPDU
          
          //$port_g P-Table RATE Control
          output reg   [6:0] mcsIndex0ProtTx,       // MCS Index 0 of Protection frame for Transmission
          output reg   [6:0] mcsIndex0Tx,           // MCS Index 0 of PPDU for Transmission

          //$port_g H-Descriptor AMPDU with only One MPDU
          output wire        txSingleVHTMPDU,       // Flag of single VHT MPDU

          //$port_g H-Descriptor PHY Control / P-Table MCS Information
          output reg         preTypeProtTx,         // Preamble Type of Protection frame for Transmission
                                                    // 1'b0: SHORT
                                                    // 1'b1: LONG
          output reg         preTypeTx,             // Preamble Type of PPDU for Transmission
                                                    // Same coding than preTypeTx
          output wire  [8:0] partialAIDTx,          // Partial AID
          output wire  [5:0] groupIDTx,             // Group ID
          output wire        dozeNotAllowedTx,      // TXOP PS is not allowed
          output wire        dynBWTx,               // Dynamic Bandwidth for Transmission
          output wire        useBWSignalingTx,      // Use BW Signaling for Transmission
          output wire        smoothingProtTx,       // Smoothing of Protection frame for Transmission
          output wire        smoothingTx,           // Smoothing of PPDU for Transmission
          output wire        soundingTx,            // Sounding Protection frame for Transmission
         
          //$port_g H-Descriptor MAC Control Information 1
          output wire [15:0] protFrmDur,            // Protection Frame Duration
          output wire        writeACK,              // Indicate SW expects the ACK frame for this frame 
                                                    // to be passed to it when received.
          output wire        lowRateRetry,          // Lower Rate on Retries
          output wire        lstpProt,              // L-SIG TXOP Protection for protection frame
          output wire        lstp,                  // L-SIG TXOP Protection
          output wire  [1:0] expectedAck,           // Expected Acknowledgement
                                                    // 2'b00: No acknowledgement.
                                                    // 2'b01: Normal ACK.
                                                    // 2'b10: BA.
                                                    // 2'b11: Compressed BA.
          output reg   [2:0] navProtFrmEx,          // NAV Protection Frame Exchange
                                                    // 3'b000: No protection
                                                    // 3'b001: Self-CTS
                                                    // 3'b010: RTS/CTS with intended receiver of this PPDU
                                                    // 3'b011: RTS/CTS with QAP 
                                                    // 3'b100: STBC protection
                                                    
          //$port_g H-Descriptor MAC Control Information 2
          output wire        dontGenerateMH,        // Indicates that HW should not generate the MAC Header by itself
          output wire        dontEncrypt,           // Indicates that HW should bypassed the encryption operation during tx.
          output wire        dontTouchFC,           // Indicates that HW should not update the Frame Control field,
          output wire        dontTouchDur,          // Indicates that HW should not update the Duration field
          output wire        dontTouchQoS,          // Indicates that HW should not update the QoS field 
          output wire        dontTouchHTC,          // Indicates that HW should not update the HTC field 
          output wire        dontTouchTSF,          // Indicates that HW should not update the TSF field 
          output wire        dontTouchDTIM,         // Indicates that HW should not update the DTIM Count field
          output wire        dontTouchFCS,          // Indicates that HW should not update the FCS field
          output wire        underBASetup,          // Indicates whether BA has been setup for this MPD
          output reg         aMPDUOut,              // Indicates whether this Transmit Header Descriptor belong to an A-MPDU
          output wire  [1:0] whichDescriptor,       // Indicates what kind of a descriptor this is
          output wire  [9:0] nBlankMDelimiters,     // Indicates the number of blank MPDU delimiters that are inserted
          output wire        interruptEnTx,         // Interrupt Enable for Transmit DMA
          output wire  [3:0] fcSubtype,             // Indicates the fcSubtype field of the Frame Control field of the MPDU.
          output wire  [1:0] fcType,                // Indicates the fcType field of the Frame Control field of the MPDU
          output wire        tsValid,               // Indicates if the fcType and fcSubtype fields have been populated correctly

          //$port_g Debug Port
          output wire [15:0] debugPortTxParametersCache // Debug Port of the TX Parameter Cache

    );

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

// hDescriptorManagement FSM states definition
//$fsm_sd hDescriptorManagement
localparam 
              HD_IDLE  =  4'd0,
            HD_LENGTH  =  4'd1,
               HD_PHY  =  4'd2,
      HD_OPT_LENGTH20  =  4'd3,
      HD_OPT_LENGTH40  =  4'd4,
      HD_OPT_LENGTH80  =  4'd5,
              HD_MAC1  =  4'd6,
              HD_MAC2  =  4'd7,
              HD_STAT  =  4'd8,
              HD_TIME  =  4'd9,
              HD_BUSY  =  4'd10;

// pTableManagement FSM states definition
//$fsm_sd pTableManagement
localparam 
              PT_IDLE   =  4'd0,
              PT_PHY1   =  4'd1,
              PT_PHY2   =  4'd2,
              PT_MAC1   =  4'd3,
              PT_MAC2   =  4'd4,
              PT_RATE1  =  4'd5,
              PT_RATE2  =  4'd6,
              PT_RATE3  =  4'd7,
              PT_RATE4  =  4'd8,
              PT_POWER1 =  4'd9,
              PT_POWER2 =  4'd10,
              PT_POWER3 =  4'd11,
              PT_POWER4 =  4'd12,
              PT_BUSY   =  4'd13;
  

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

//Header Descriptor Information Set 1
reg [19:0] hDescFrameLengthSet1;        //H-Descriptor Frame Length Set 1
reg [31:0] hDescPHYCntrlInfSet1;        //H-Descriptor PHY Control Information Set 1
reg [19:0] hDescOptFrameLength20Set1;   //H-Descriptor Optional Frame Length drop to 20 Mhz Set 1
reg [19:0] hDescOptFrameLength40Set1;   //H-Descriptor Optional Frame Length drop to 40 Mhz Set 1
reg [19:0] hDescOptFrameLength80Set1;   //H-Descriptor Optional Frame Length drop to 80 Mhz Set 1
reg [31:0] hDescMACCntrlInf1Set1;       //H-Descriptor MAC Control Information 1 Set 1
reg [31:0] hDescMACCntrlInf2Set1;       //H-Descriptor MAC Control Information 2 Set 1
reg [31:0] hDescStatusInfSet1;          //H-Descriptor Status Information Set 1
reg [31:0] hDescMdmTimeUsedSet1;        //H-Descriptor Medium Time Used Set 1

//Header Descriptor Information Set 2
reg [19:0] hDescFrameLengthSet0;        //H-Descriptor Frame Length Set 2
reg [31:0] hDescPHYCntrlInfSet0;        //H-Descriptor PHY Control Information Set 2
reg [19:0] hDescOptFrameLength20Set0;   //H-Descriptor Optional Frame Length drop to 20 Mhz Set 2
reg [19:0] hDescOptFrameLength40Set0;   //H-Descriptor Optional Frame Length drop to 40 Mhz Set 2
reg [19:0] hDescOptFrameLength80Set0;   //H-Descriptor Optional Frame Length drop to 80 Mhz Set 2
reg [31:0] hDescMACCntrlInf1Set0;       //H-Descriptor MAC Control Information 1 Set 2
reg [31:0] hDescMACCntrlInf2Set0;       //H-Descriptor MAC Control Information 2 Set 2
reg [31:0] hDescStatusInfSet0;          //H-Descriptor Status Information Set 2
reg [31:0] hDescMdmTimeUsedSet0;        //H-Descriptor Medium Time Used Set 2

//Policy Table Information Set 1
reg [31:0] pTablePHYCntrlInf1Set1;  //P-Table PHY Control Information 1 Set 1
reg [31:0] pTablePHYCntrlInf2Set1;  //P-Table PHY Control Information 2 Set 1
reg [31:0] pTableMACCntrlInf1Set1;  //P-Table MAC Control Information 1 Set 1
reg [31:0] pTableMACCntrlInf2Set1;  //P-Table MAC Control Information 2 Set 1
reg [31:0] pTableRateCntrlInf1Set1; //P-Table Rate Information Set 1
reg [31:0] pTableRateCntrlInf2Set1; //P-Table Rate Information Set 1
reg [31:0] pTableRateCntrlInf3Set1; //P-Table Rate Information Set 1
reg [31:0] pTableRateCntrlInf4Set1; //P-Table Rate Information Set 1
reg [31:0] pTablePowerCntrlInf1Set1;//P-Table Power Control Information 1 Set 1
reg [31:0] pTablePowerCntrlInf2Set1;//P-Table Power Control Information 2 Set 1
reg [31:0] pTablePowerCntrlInf3Set1;//P-Table Power Control Information 3 Set 1
reg [31:0] pTablePowerCntrlInf4Set1;//P-Table Power Control Information 4 Set 1

//Policy table Information Set 2
reg [31:0] pTablePHYCntrlInf1Set0; //P-Table PHY Control Information 1 Set 2
reg [31:0] pTablePHYCntrlInf2Set0; //P-Table PHY Control Information 2 Set 2
reg [31:0] pTableMACCntrlInf1Set0; //P-Table MAC Control Information 1 Set 2
reg [31:0] pTableMACCntrlInf2Set0; //P-Table MAC Control Information 2 Set 2
reg [31:0] pTableRateCntrlInf1Set0;//P-Table Rate Information 1 Set 2
reg [31:0] pTableRateCntrlInf2Set0;//P-Table Rate Information 2 Set 2
reg [31:0] pTableRateCntrlInf3Set0;//P-Table Rate Information 3 Set 2
reg [31:0] pTableRateCntrlInf4Set0;//P-Table Rate Information 4 Set 2
reg [31:0] pTablePowerCntrlInf1Set0;//P-Table Power Control Information 1 Set 2
reg [31:0] pTablePowerCntrlInf2Set0;//P-Table Power Control Information 2 Set 2
reg [31:0] pTablePowerCntrlInf3Set0;//P-Table Power Control Information 3 Set 2
reg [31:0] pTablePowerCntrlInf4Set0;//P-Table Power Control Information 4 Set 2

//P-Table RATE Control Information 1
wire  [2:0] nRetryRC1;             // Number of trial for this rate control
wire  [2:0] formatModProtTxRC1;    // Format and Modulation for Tx Protection frame (RTS/CTS)
wire  [1:0] bwProtTxRC1;           // Bandwidth for protection frame
wire  [6:0] mcsIndexProtTxRC1;     // MCS index forProtection frame Tx
wire  [2:0] navProtFrmExRC1;       // NAV Protection Frame Exchange
wire  [2:0] formatModTxRC1;        // Format and Modulation for Tx PPDU
wire        preTypeTxRC1;          // Preamble Type for Tx frame
wire        shortGITxRC1;          // Short Guard Interval
wire  [1:0] bwTxRC1;               // Bandwidth for PPDU
wire  [6:0] mcsIndexTxRC1;         // MCS index for PPDU frame Tx

//P-Table Power Control Information 1
wire  [7:0] txPwrLevelRC1;
wire  [7:0] txPwrLevelProtRC1;

//P-Table RATE Control Information 2
wire  [2:0] nRetryRC2;             // Number of trial for this rate control
wire  [2:0] formatModProtTxRC2;    // Format and Modulation for Tx Protection frame (RTS/CTS)
wire  [1:0] bwProtTxRC2;           // Bandwidth for protection frame
wire  [6:0] mcsIndexProtTxRC2;     // MCS index forProtection frame Tx
wire  [2:0] navProtFrmExRC2;       // NAV Protection Frame Exchange
wire  [2:0] formatModTxRC2;        // Format and Modulation for Tx PPDU
wire        preTypeTxRC2;          // Preamble Type for Tx frame
wire        shortGITxRC2;          // Short Guard Interval
wire  [1:0] bwTxRC2;               // Bandwidth for PPDU
wire  [6:0] mcsIndexTxRC2;         // MCS index for PPDU frame Tx

//P-Table Power Control Information 2
wire  [7:0] txPwrLevelRC2;
wire  [7:0] txPwrLevelProtRC2;

//P-Table RATE Control Information 3
wire  [2:0] nRetryRC3;             // Number of trial for this rate control
wire  [2:0] formatModProtTxRC3;    // Format and Modulation for Tx Protection frame (RTS/CTS)
wire  [1:0] bwProtTxRC3;           // Bandwidth for protection frame
wire  [6:0] mcsIndexProtTxRC3;     // MCS index forProtection frame Tx
wire  [2:0] navProtFrmExRC3;       // NAV Protection Frame Exchange
wire  [2:0] formatModTxRC3;        // Format and Modulation for Tx PPDU
wire        preTypeTxRC3;          // Preamble Type for Tx Protection frame
wire        shortGITxRC3;          // Short Guard Interval
wire  [1:0] bwTxRC3;               // Bandwidth for PPDU
wire  [6:0] mcsIndexTxRC3;         // MCS index for PPDU frame Tx

//P-Table Power Control Information 3
wire  [7:0] txPwrLevelRC3;
wire  [7:0] txPwrLevelProtRC3;

//P-Table RATE Control Information 4
//wire  [2:0] nRetryRC4;             // Number of trial for this rate control
wire  [2:0] formatModProtTxRC4;    // Format and Modulation for Tx Protection frame (RTS/CTS)
wire  [1:0] bwProtTxRC4;           // Bandwidth for protection frame
wire  [6:0] mcsIndexProtTxRC4;     // MCS index forProtection frame Tx
wire  [2:0] navProtFrmExRC4;       // NAV Protection Frame Exchange
wire  [2:0] formatModTxRC4;        // Format and Modulation for Tx PPDU
wire        preTypeTxRC4;          // Preamble Type for Tx Protection frame
wire        shortGITxRC4;          // Short Guard Interval
wire  [1:0] bwTxRC4;               // Bandwidth for PPDU
wire  [6:0] mcsIndexTxRC4;         // MCS index for PPDU frame Tx

//P-Table Power Control Information 4
wire  [7:0] txPwrLevelRC4;
wire  [7:0] txPwrLevelProtRC4;

// Variables used to mux the RATE output
wire  [7:0] retryRC2Limit;
wire  [7:0] retryRC3Limit;
wire        retryRTSRC1;
wire        retryRTSRC2;
wire        retryRTSRC3;
wire        retryMPDURC1;
wire        retryMPDURC2;
wire        retryMPDURC3;

// Detect if the header descriptor has not set ampdu and format mode is VHT and whichDescriptor is 0
reg         ampduVHTSingleMpdu;

// Signal used for VHT single MPDU
wire  [19:0]  aMPDUFrameLengthTxGen;
wire  [19:0]  aMPDUOptFrameLength20TxGen;
wire  [19:0]  aMPDUOptFrameLength40TxGen;
wire  [19:0]  aMPDUOptFrameLength80TxGen;

wire          aMPDU;

wire  [19:0]  hDescFrameLengthSet;
wire  [19:0]  hDescOptFrameLength20Set;
wire  [19:0]  hDescOptFrameLength40Set;
wire  [19:0]  hDescOptFrameLength80Set;

// HD and PT Sets Read and Write Pointers
reg currentWriteHDSet;             // Indicates if the Header Descriptor Set1 is active
reg currentReadHDSet;              // Indicates if the Header Descriptor Set0 is active
reg currentWritePTSet;             // Indicates if the Policy Table Set1 is free
reg currentReadPTSet;              // Indicates if the Header Descriptor Set1 is full
reg currentReadHDAMPDUSet;         // Indicates if the Header Descriptor Set0 for AMPDU is active

reg [1:0] nFilledHDSets;           // Indicates the number of HD Sets already filled.
reg [1:0] nFilledPTSets;           // Indicates the number of PT Sets already filled.

reg partOfAMPDU;                   // Indicates if the MPDU are part of an A-MPDU

reg txCtrlRegHD_ff1;               // txCtrlRegHD delayed of one clock cycle
reg txCtrlRegPT_ff1;               // txCtrlRegPT delayed of one clock cycle

// hDescriptorManagement FSM signals definition
reg [3:0] hDescriptorManagementCs; // hDescriptorManagement FSM Current State
reg [3:0] hDescriptorManagementNs; // hDescriptorManagement FSM Next State

// pTableManagement FSM signals definition
reg [3:0] pTableManagementCs;      // pTableManagement FSM Current State
reg [3:0] pTableManagementNs;      // pTableManagement FSM Next State

wire hDescFrameLength_p;           // Indicates that the received data is H-Descriptor Frame Length
wire hDescPHYCntrlInf_p;           // Indicates that the received data is H-Descriptor PHY Control Information
wire hDescOptFrameLength20_p;      // Indicates that the received data is H-Descriptor Optional Frame Length drop to 20 Mhz
wire hDescOptFrameLength40_p;      // Indicates that the received data is H-Descriptor Optional Frame Length drop to 40 Mhz
wire hDescOptFrameLength80_p;      // Indicates that the received data is H-Descriptor Optional Frame Length drop to 80 Mhz
wire hDescMACCntrlInf1_p;          // Indicates that the received data is H-Descriptor MAC Control Information 1
wire hDescMACCntrlInf2_p;          // Indicates that the received data is H-Descriptor MAC Control Information 2
wire hDescStatusInf_p;             // Indicates that the received data is H-Descriptor Status Information
wire hDescMdmTimeUsed_p;           // Indicates that the received data is H-Descriptor Medium Time Used
reg  hDescMdmTimeUsedFF1_p;        // hDescMdmTimeUsed_p delayed of 1cc
`ifdef RW_THD_V2
reg  hDescStatusInfFF1_p;          // hDescStatusInf_p delayed of 1cc
`endif // RW_THD_V2

wire pTablePHYCntrlInf1_p;         // Indicates that the received data is P-Table PHY Control Information 1
wire pTablePHYCntrlInf2_p;         // Indicates that the received data is P-Table PHY Control Information 2
wire pTableMACCntrlInf1_p;         // Indicates that the received data is P-Table MAC Control Information 1
wire pTableMACCntrlInf2_p;         // Indicates that the received data is P-Table MAC Control Information 2
wire pTableRATECntrlInf1_p;        // Indicates that the received data is P-Table RATE Control Information 1
wire pTableRATECntrlInf2_p;        // Indicates that the received data is P-Table RATE Control Information 2
wire pTableRATECntrlInf3_p;        // Indicates that the received data is P-Table RATE Control Information 3
wire pTableRATECntrlInf4_p;        // Indicates that the received data is P-Table RATE Control Information 4
wire pTablePOWERCntrlInf1_p;       // Indicates that the received data is P-Table POWER Control Information 1
wire pTablePOWERCntrlInf2_p;       // Indicates that the received data is P-Table POWER Control Information 2
wire pTablePOWERCntrlInf3_p;       // Indicates that the received data is P-Table POWER Control Information 3
wire pTablePOWERCntrlInf4_p;       // Indicates that the received data is P-Table POWER Control Information 4

wire txCtrlRegHD_p;                // Indicates a rising edge on txCtrlRegHD
wire txCtrlRegPT_p;                // Indicates a rising edge on txCtrlRegPT

reg         txParameterHDReady;         // Indicates if the Header Descriptor fields are usable 
reg         txParameterPTReady;         // Indicates if the Policy Table fields are usable
wire        txParameterNextPTReady;     // Indicates if a second policy table has already been loaded
reg         txParameterHDReadyDelay;    // txParameterHDReadyIn delayed of one clock cycle
reg         txParameterPTReadyDelay;    // txParameterPTReady delayed of one clock cycle
reg         txParameterNextPTReadyDelay;// txParameterNextPTReady delayed of one clock cycle

`ifdef RW_SIMU_ON
  // These two signals are defined to ease the simulation and waveform analysis.
  // String definition to display hDescriptorManagement current state
  reg [15*8:0] hDescriptorManagementCs_str;
  // String definition to display pTableManagement current state
  reg [10*8:0] pTableManagementCs_str;
`endif // RW_SIMU_ON

//////////////////////////////////////////////////////////////////////////////
// Beginning of Logic part
//////////////////////////////////////////////////////////////////////////////

// This process generates two pulses indicating when the 
// DMA Engine starts a Header Descriptor transfer or a
// Policy Table transfer
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    txCtrlRegHD_ff1 <= 1'b0;
    txCtrlRegPT_ff1 <= 1'b0;
  end
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
  // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
  begin
    txCtrlRegHD_ff1 <= 1'b0; 
    txCtrlRegPT_ff1 <= 1'b0; 
  end
  else
  begin
    txCtrlRegHD_ff1 <= txCtrlRegHD; 
    txCtrlRegPT_ff1 <= txCtrlRegPT; 
  end
end

assign txCtrlRegHD_p = !txCtrlRegHD_ff1 && txCtrlRegHD;
assign txCtrlRegPT_p = !txCtrlRegPT_ff1 && txCtrlRegPT;


// Header Descriptor Management FSM
///////////////////////////////////

// hDescriptorManagement FSM Current State Logic 
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    hDescriptorManagementCs <= HD_IDLE;
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
  // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
    hDescriptorManagementCs <= HD_IDLE; 
  else
    hDescriptorManagementCs <= hDescriptorManagementNs; 
end


// hDescriptorManagement FSM Next State Logic.
//always @(hDescriptorManagementCs, txCtrlRegHD, txCtrlRegWr, freeHD1, freeHD2)
always @*
begin
  case(hDescriptorManagementCs)

    HD_IDLE:
      //$fsm_s In HD_IDLE state, the state machine waits for a 
      //Header descriptor fields transfer from the DMA Engine
      if (txCtrlRegHD_p) 
        //$fsm_t When txCtrlRegPT is received, the state machine goes to HD_LENGTH state
        hDescriptorManagementNs = HD_LENGTH;
      else
        //$fsm_t If txCtrlRegPT is low, the state machine stays in HD_IDLE state
        hDescriptorManagementNs = HD_IDLE;

    HD_LENGTH:
      //$fsm_s In HD_LENGTH state, the state machine waits for the reception of 
      //H-Descriptor Frame Length from the DMA Engine
      if (txCtrlRegWr) 
        //$fsm_t When txCtrlRegWr is received, the state machine goes to HD_PHY state
        hDescriptorManagementNs = HD_PHY; 
      else if (!txCtrlRegHD) 
        //$fsm_t If txCtrlRegHD goes low, the state machine moves to HD_IDLE state
        hDescriptorManagementNs = HD_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in HD_LENGTH state
        hDescriptorManagementNs = HD_LENGTH;

    HD_PHY:
      //$fsm_s In HD_PHY state, the state machine waits for the reception of 
      //PHY Control Information from the DMA Engine
      if (txCtrlRegWr) 
        //$fsm_t When txCtrlRegWr is received, the state machine goes to HD_MAC1 state
      `ifdef RW_THD_V2
        hDescriptorManagementNs = HD_MAC1; 
      `else // RW_THD_V2
        hDescriptorManagementNs = HD_OPT_LENGTH20; 
      `endif // RW_THD_V2
      else if (!txCtrlRegHD) 
        //$fsm_t If txCtrlRegHD goes low, the state machine moves to HD_IDLE state
        hDescriptorManagementNs = HD_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in HD_PHY state
        hDescriptorManagementNs = HD_PHY;

    HD_OPT_LENGTH20:
      //$fsm_s In HD_OPT_LENGTH20 state, the state machine waits for the reception of 
      //H-Descriptor Optional Frame Length 20 from the DMA Engine
      if (txCtrlRegWr) 
        //$fsm_t When txCtrlRegWr is received, the state machine goes to HD_OPT_LENGTH40 state
        hDescriptorManagementNs = HD_OPT_LENGTH40; 
      else if (!txCtrlRegHD) 
        //$fsm_t If txCtrlRegHD goes low, the state machine moves to HD_IDLE state
        hDescriptorManagementNs = HD_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in HD_OPT_LENGTH20 state
        hDescriptorManagementNs = HD_OPT_LENGTH20;

    HD_OPT_LENGTH40:
      //$fsm_s In HD_OPT_LENGTH40 state, the state machine waits for the reception of 
      //H-Descriptor Optional Frame Length 40 from the DMA Engine
      if (txCtrlRegWr) 
        //$fsm_t When txCtrlRegWr is received, the state machine goes to HD_OPT_LENGTH80 state
        hDescriptorManagementNs = HD_OPT_LENGTH80; 
      else if (!txCtrlRegHD) 
        //$fsm_t If txCtrlRegHD goes low, the state machine moves to HD_IDLE state
        hDescriptorManagementNs = HD_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in HD_OPT_LENGTH40 state
        hDescriptorManagementNs = HD_OPT_LENGTH40;

    HD_OPT_LENGTH80:
      //$fsm_s In HD_OPT_LENGTH80 state, the state machine waits for the reception of 
      //H-Descriptor Optional Frame Length 80 from the DMA Engine
      if (txCtrlRegWr) 
        //$fsm_t When txCtrlRegWr is received, the state machine goes to HD_MAC1 state
        hDescriptorManagementNs = HD_MAC1; 
      else if (!txCtrlRegHD) 
        //$fsm_t If txCtrlRegHD goes low, the state machine moves to HD_IDLE state
        hDescriptorManagementNs = HD_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in HD_OPT_LENGTH20 state
        hDescriptorManagementNs = HD_OPT_LENGTH80;

    HD_MAC1:
      //$fsm_s In HD_MAC1 state, the state machine waits for the reception of 
      //H-Descriptor MAC Control Information 1 from the DMA Engine
      if (txCtrlRegWr) 
        //$fsm_t When txCtrlRegWr is received, the state machine goes to HD_MAC2 state
        hDescriptorManagementNs = HD_MAC2; 
      else if (!txCtrlRegHD) 
        //$fsm_t If txCtrlRegHD goes low, the state machine moves to HD_IDLE state
        hDescriptorManagementNs = HD_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in HD_MAC1 state
        hDescriptorManagementNs = HD_MAC1;

    HD_MAC2:
      //$fsm_s In HD_MAC2 state, the state machine waits for the reception of 
      //H-Descriptor MAC Control Information 2 from the DMA Engine
      if (txCtrlRegWr) 
        //$fsm_t When txCtrlRegWr is received, the state machine goes to HD_STAT state
        hDescriptorManagementNs = HD_STAT; 
      else if (!txCtrlRegHD) 
        //$fsm_t If txCtrlRegHD goes low, the state machine moves to HD_IDLE state
        hDescriptorManagementNs = HD_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in HD_MAC2 state
        hDescriptorManagementNs = HD_MAC2;

    HD_STAT:
      //$fsm_s In HD_STAT state, the state machine waits for the reception of 
      //H-Descriptor Status Information from the DMA Engine
      if (txCtrlRegWr) 
          //$fsm_t When txCtrlRegWr is received, the state machine moves to HD_BUSY state
      `ifdef RW_THD_V2
          hDescriptorManagementNs = HD_BUSY;
      `else // RW_THD_V2
          hDescriptorManagementNs = HD_TIME; 
      `endif // RW_THD_V2
      else if (!txCtrlRegHD) 
        //$fsm_t If txCtrlRegHD goes low, the state machine moves to HD_IDLE state
        hDescriptorManagementNs = HD_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in HD_STAT state
        hDescriptorManagementNs = HD_STAT;
          
    HD_TIME:
      //$fsm_s In HD_TIME state, the state machine waits for the reception of 
      //H-Descriptor Medium Time Used from the DMA Engine
      if (txCtrlRegWr) 
          //$fsm_t When txCtrlRegWr is received, the state machine moves to HD_BUSY state
          hDescriptorManagementNs = HD_BUSY; 
      else if (!txCtrlRegHD) 
        //$fsm_t If txCtrlRegHD goes low, the state machine moves to HD_IDLE state
        hDescriptorManagementNs = HD_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in HD_TIME state
        hDescriptorManagementNs = HD_TIME;
    HD_BUSY:
      //$fsm_s In HD_BUSY state, the state machine waits and the txCtrlReg is busy
      if (nFilledHDSets != 2'd2)
        //$fsm_t If one of the Header Descriptor Set becomes free, 
        //the state machine goes back to HD_IDLE state and is ready to receive 
        //another Header Descriptor
        hDescriptorManagementNs = HD_IDLE; 
      else
        //$fsm_t If none of the Header Descriptor Set is free, the state machine stays 
        //in HD_BUSY state
        hDescriptorManagementNs = HD_BUSY;

     // Disable coverage on the default state because it cannot be reached.
     // pragma coverage block = off 
     default:   
        hDescriptorManagementNs = HD_IDLE; 
     // pragma coverage block = on 
  endcase
end


// Header Descriptor Triggers
/////////////////////////////
// When the DMA Engine transfer a new part of the Header Descriptor, a pulse according to the 
// type of data currently transfered (based on the hDescriptorManagement FSM current state) is generated. 
// These pulses are used to stored the coming data to the right location into the HD Sets. 
assign hDescFrameLength_p       = ((hDescriptorManagementCs == HD_LENGTH)       && txCtrlRegWr) ? 1'b1 : 1'b0;
assign hDescPHYCntrlInf_p       = ((hDescriptorManagementCs == HD_PHY)          && txCtrlRegWr) ? 1'b1 : 1'b0;
assign hDescOptFrameLength20_p  = ((hDescriptorManagementCs == HD_OPT_LENGTH20) && txCtrlRegWr) ? 1'b1 : 1'b0;
assign hDescOptFrameLength40_p  = ((hDescriptorManagementCs == HD_OPT_LENGTH40) && txCtrlRegWr) ? 1'b1 : 1'b0;
assign hDescOptFrameLength80_p  = ((hDescriptorManagementCs == HD_OPT_LENGTH80) && txCtrlRegWr) ? 1'b1 : 1'b0;
assign hDescMACCntrlInf1_p      = ((hDescriptorManagementCs == HD_MAC1)         && txCtrlRegWr) ? 1'b1 : 1'b0;
assign hDescMACCntrlInf2_p      = ((hDescriptorManagementCs == HD_MAC2)         && txCtrlRegWr) ? 1'b1 : 1'b0;
assign hDescStatusInf_p         = ((hDescriptorManagementCs == HD_STAT)         && txCtrlRegWr) ? 1'b1 : 1'b0;
assign hDescMdmTimeUsed_p       = ((hDescriptorManagementCs == HD_TIME)         && txCtrlRegWr) ? 1'b1 : 1'b0;



always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    hDescMdmTimeUsedFF1_p   <= 1'b0;
  else 
    hDescMdmTimeUsedFF1_p   <= hDescMdmTimeUsed_p;
end    

`ifdef RW_THD_V2
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    hDescStatusInfFF1_p   <= 1'b0;
  else 
    hDescStatusInfFF1_p   <= hDescStatusInf_p;
end    
`endif // RW_THD_V2

// Policy Table Management FSM
//////////////////////////////

// pTableManagement FSM Current State Logic 
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    pTableManagementCs <= PT_IDLE; 
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
  // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
    pTableManagementCs <= PT_IDLE;
  else
    pTableManagementCs <= pTableManagementNs; 
end


// pTableManagement FSM Next State Logic.
always @* 
begin
  case(pTableManagementCs)

    PT_IDLE:
      //$fsm_s In PT_IDLE state, the state machine waits for a 
      //Policy table fields transfer from the DMA Engine
      if (txCtrlRegPT_p) 
        //$fsm_t When txCtrlRegPT is received, the state machine goes to PT_PHY1 state
        pTableManagementNs = PT_PHY1;
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_IDLE state
        pTableManagementNs = PT_IDLE;

    PT_PHY1:
      //$fsm_s In PT_PHY1 state, the state machine waits for the reception of 
      //P-Table PHY Control Information 1 from the DMA Engine
      if (txCtrlRegWr) 
        //$fsm_t When txCtrlRegWr is received, the state machine goes to PT_PHY2 state
        pTableManagementNs = PT_PHY2; 
      else if (!txCtrlRegPT) 
        //$fsm_t If txCtrlRegPT goes low, the state machine moves to PT_IDLE state
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_PHY1 state
        pTableManagementNs = PT_PHY1; 

    PT_PHY2:
      //$fsm_s In PT_PHY2 state, the state machine waits for the reception of 
      //P-Table PHY Control Information 2 from the DMA Engine
      if (txCtrlRegWr) 
        //$fsm_t When txCtrlRegWr is received, the state machine goes to PT_MAC1 state
        pTableManagementNs = PT_MAC1; 
      else if (!txCtrlRegPT) 
        //$fsm_t If txCtrlRegPT goes low, the state machine moves to PT_IDLE state
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_PHY2 state
        pTableManagementNs = PT_PHY2; 

    PT_MAC1:
      //$fsm_s In PT_MAC1 state, the state machine waits for the reception of 
      //P-Table MAC Control Information 1 from the DMA Engine
      if (txCtrlRegWr) 
        //$fsm_t When txCtrlRegWr is received, the state machine goes to PT_MAC2 state
        pTableManagementNs = PT_MAC2;
      else if (!txCtrlRegPT) 
        //$fsm_t If txCtrlRegPT goes low, the state machine moves to PT_IDLE state
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_MAC1 state
        pTableManagementNs = PT_MAC1; 

    PT_MAC2:
      //$fsm_s In PT_MAC2 state, the state machine waits for the reception of 
      //P-Table MAC Control Information 2 from the DMA Engine
      if (txCtrlRegWr) 
        //$fsm_t When txCtrlRegWr is received, the state machine goes to PT_RATE1 state
        pTableManagementNs = PT_RATE1;
      else if (!txCtrlRegPT) 
        //$fsm_t If txCtrlRegPT goes low, the state machine moves to PT_IDLE state
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_MAC2 state
        pTableManagementNs = PT_MAC2; 

    PT_RATE1:
      //$fsm_s In PT_RATE1 state, the state machine waits for the reception of 
      //P-Table PT_RATE1 Information from the DMA Engine
      if (txCtrlRegWr) 
          //$fsm_t When txCtrlRegWr is received, the state machine moves to PT_RATE2 state
          pTableManagementNs = PT_RATE2; 
      else if (!txCtrlRegPT) 
        //$fsm_t If txCtrlRegPT goes low, the state machine moves to PT_IDLE state
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_RATE1 state
        pTableManagementNs = PT_RATE1; 

    PT_RATE2:
      //$fsm_s In PT_RATE2 state, the state machine waits for the reception of 
      //P-Table PT_RATE2 Information from the DMA Engine
      if (txCtrlRegWr) 
          //$fsm_t When txCtrlRegWr is received, the state machine moves to PT_RATE3 state
          pTableManagementNs = PT_RATE3; 
      else if (!txCtrlRegPT) 
        //$fsm_t If txCtrlRegPT goes low, the state machine moves to PT_IDLE state
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_RATE2 state
        pTableManagementNs = PT_RATE2; 

    PT_RATE3:
      //$fsm_s In PT_RATE3 state, the state machine waits for the reception of 
      //P-Table PT_RATE3 Information from the DMA Engine
      if (txCtrlRegWr) 
          //$fsm_t When txCtrlRegWr is received, the state machine moves to PT_RATE3 state
          pTableManagementNs = PT_RATE4; 
      else if (!txCtrlRegPT) 
        //$fsm_t If txCtrlRegPT goes low, the state machine moves to PT_IDLE state
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_RATE3 state
        pTableManagementNs = PT_RATE3; 

    PT_RATE4:
      //$fsm_s In PT_RATE4 state, the state machine waits for the reception of 
      //P-Table PT_RATE4 Information from the DMA Engine
      if (txCtrlRegWr) 
          //$fsm_t When txCtrlRegWr is received, the state machine moves to PT_BUSY state
          pTableManagementNs = PT_POWER1; 
      else if (!txCtrlRegPT) 
        //$fsm_t If txCtrlRegPT goes low, the state machine moves to PT_IDLE state
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_RATE4 state
        pTableManagementNs = PT_RATE4; 

    PT_POWER1:
      //$fsm_s In PT_POWER1 state, the state machine waits for the reception of 
      //P-Table PT_POWER1 Information from the DMA Engine
      if (txCtrlRegWr) 
          //$fsm_t When txCtrlRegWr is received, the state machine moves to PT_POWER2 state
          pTableManagementNs = PT_POWER2; 
      else if (!txCtrlRegPT) 
        //$fsm_t If txCtrlRegPT goes low, the state machine moves to PT_IDLE state
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_POWER1 state
        pTableManagementNs = PT_POWER1; 

    PT_POWER2:
      //$fsm_s In PT_POWER2 state, the state machine waits for the reception of 
      //P-Table PT_POWER2 Information from the DMA Engine
      if (txCtrlRegWr) 
          //$fsm_t When txCtrlRegWr is received, the state machine moves to PT_POWER3 state
          pTableManagementNs = PT_POWER3; 
      else if (!txCtrlRegPT) 
        //$fsm_t If txCtrlRegPT goes low, the state machine moves to PT_IDLE state
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_POWER2 state
        pTableManagementNs = PT_POWER2; 

    PT_POWER3:
      //$fsm_s In PT_POWER3 state, the state machine waits for the reception of 
      //P-Table PT_POWER3 Information from the DMA Engine
      if (txCtrlRegWr) 
          //$fsm_t When txCtrlRegWr is received, the state machine moves to PT_POWER3 state
          pTableManagementNs = PT_POWER4; 
      else if (!txCtrlRegPT) 
        //$fsm_t If txCtrlRegPT goes low, the state machine moves to PT_IDLE state
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_POWER3 state
        pTableManagementNs = PT_POWER3; 

    PT_POWER4:
      //$fsm_s In PT_POWER4 state, the state machine waits for the reception of 
      //P-Table PT_POWER4 Information from the DMA Engine
      if (txCtrlRegWr) 
          //$fsm_t When txCtrlRegWr is received, the state machine moves to PT_BUSY state
          pTableManagementNs = PT_BUSY; 
      else if (!txCtrlRegPT) 
        //$fsm_t If txCtrlRegPT goes low, the state machine moves to PT_IDLE state
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If txCtrlRegWr is low, the state machine stays in PT_POWER4 state
        pTableManagementNs = PT_POWER4; 

    PT_BUSY:
      //$fsm_s In PT_BUSY state, the state machine waits and the txCtrlReg is busy
      if (nFilledPTSets != 2'd2)
        //$fsm_t If one of the Policy Table Set becomes free, 
        //the state machine goes back to PT_IDLE state and is ready to receive 
        //another Policy table
        pTableManagementNs = PT_IDLE; 
      else
        //$fsm_t If none of the Policy Table Set is free, the state machine stays in 
        //PT_BUSY state
        pTableManagementNs = PT_BUSY; 

     // Disable coverage on the default state because it cannot be reached.
     // pragma coverage block = off 
     default:   
        pTableManagementNs = PT_IDLE; 
     // pragma coverage block = on 
  endcase
end

// Policy Table Triggers
////////////////////////
// When the DMA Engine transfer a new part of the Policy Table, a pulse according to the 
// type of data currently transfered (based on the pTableManagement FSM current state) is generated. 
// These pulses are used to stored the coming data to the right location into the PT Sets. 
assign pTablePHYCntrlInf1_p   = ((pTableManagementCs == PT_PHY1)   && txCtrlRegWr) ? 1'b1 : 1'b0;
assign pTablePHYCntrlInf2_p   = ((pTableManagementCs == PT_PHY2)   && txCtrlRegWr) ? 1'b1 : 1'b0;
assign pTableMACCntrlInf1_p   = ((pTableManagementCs == PT_MAC1)   && txCtrlRegWr) ? 1'b1 : 1'b0;
assign pTableMACCntrlInf2_p   = ((pTableManagementCs == PT_MAC2)   && txCtrlRegWr) ? 1'b1 : 1'b0;
assign pTableRATECntrlInf1_p  = ((pTableManagementCs == PT_RATE1)  && txCtrlRegWr) ? 1'b1 : 1'b0;
assign pTableRATECntrlInf2_p  = ((pTableManagementCs == PT_RATE2)  && txCtrlRegWr) ? 1'b1 : 1'b0;
assign pTableRATECntrlInf3_p  = ((pTableManagementCs == PT_RATE3)  && txCtrlRegWr) ? 1'b1 : 1'b0;
assign pTableRATECntrlInf4_p  = ((pTableManagementCs == PT_RATE4)  && txCtrlRegWr) ? 1'b1 : 1'b0;
assign pTablePOWERCntrlInf1_p = ((pTableManagementCs == PT_POWER1) && txCtrlRegWr) ? 1'b1 : 1'b0;
assign pTablePOWERCntrlInf2_p = ((pTableManagementCs == PT_POWER2) && txCtrlRegWr) ? 1'b1 : 1'b0;
assign pTablePOWERCntrlInf3_p = ((pTableManagementCs == PT_POWER3) && txCtrlRegWr) ? 1'b1 : 1'b0;
assign pTablePOWERCntrlInf4_p = ((pTableManagementCs == PT_POWER4) && txCtrlRegWr) ? 1'b1 : 1'b0;

// Busy Indication to DMA Engine generation
///////////////////////////////////////////
// As soon as the two HD Sets are fulled, the TX Parameters Cache generates a busy 
// indication to the DMA Engine via the signal txCtrlRegBusy
// However, in case of Singleton MPDU, this signal must not go high as soon as the 
// second HD Sets is filled because the DMA has to feed the PT.
// But in case of A-MPDU, the busy indication must be set on the Header descriptor 
// because no Policy table will be transfer.
// This is what the partOfAMPDU is created indicating when the txCtrlRegBusy has to
// be set on the hDescriptorManagement FSM BUSY state or on the pTableManagement 
// FSM BUSY state
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    partOfAMPDU   <= 1'b0;
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
  // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
    partOfAMPDU   <= 1'b0;
  else
  begin
    if (pTablePOWERCntrlInf4_p )
    begin
    // At this end of the Policy Table transfer, the partOfAMPDU is set with the aMPDU
    // value contained in MAC Control Information 2. A selection of the right HD set is
    // required in this case.
      if (currentWriteHDSet)
      begin
        if (hDescMACCntrlInf2Set0[21] && hDescMACCntrlInf2Set0[20:19] == 2'b00)
          partOfAMPDU   <= 1'b1;
        else
          partOfAMPDU   <= 1'b0;
      end
      else
      begin    
        if (hDescMACCntrlInf2Set1[21] && hDescMACCntrlInf2Set1[20:19] == 2'b00)   
          partOfAMPDU   <= 1'b1;
        else
          partOfAMPDU   <= 1'b0;
      end   
    end             
`ifdef RW_THD_V2
    else if (hDescStatusInf_p)
`else // RW_THD_V2
    else if (hDescMdmTimeUsed_p)
`endif // RW_THD_V2
    begin
    // At this end of the Policy Table transfer, the partOfAMPDU is set with the aMPDU
    // value contained in MAC Control Information 2. A selection of the right HD set is
    // required in this case.
      if (currentWriteHDSet)
      begin
        if (hDescMACCntrlInf2Set1[21] && hDescMACCntrlInf2Set1[20:19] == 2'b11)
          partOfAMPDU   <= 1'b0;
      end
      else
      begin    
        if (hDescMACCntrlInf2Set0[21] && hDescMACCntrlInf2Set0[20:19] == 2'b11)   
          partOfAMPDU   <= 1'b0;
      end   
    end             
  end    
end


// txCtrlRegBusy generation
///////////////////////////
// If none of the HD Sets or PT Sets is free, the txCtrlRegBusy signal is raised
//assign txCtrlRegBusy = (((partOfAMPDU == 1'b1) && (hDescriptorManagementCs == HD_BUSY)) || (pTableManagementCs == PT_BUSY)) ? 1'b1 : 1'b0;
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    txCtrlRegBusy <= 1'b0;
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
    txCtrlRegBusy <= 1'b0;
  else
  begin
    if (toggleHDSet_p || discardPrevHD_p || (hDescriptorManagementCs == HD_IDLE))
      txCtrlRegBusy <= 1'b0;
    else if (pTableManagementCs == PT_BUSY)  
      txCtrlRegBusy <= 1'b1;
`ifdef RW_THD_V2
    else if ((hDescriptorManagementCs == HD_BUSY) && aMPDU && (whichDescriptor != 2'b11) && hDescStatusInfFF1_p)
`else // RW_THD_V2
    else if ((hDescriptorManagementCs == HD_BUSY) && aMPDU && (whichDescriptor != 2'b11) && hDescMdmTimeUsedFF1_p)
`endif // RW_THD_V2
      txCtrlRegBusy <= 1'b1;
  end      
end

                       
// Header Descriptor Sets Management
////////////////////////////////////
// This process manages the Header Descriptor Set Read and Write pointers 
// as well as the number of filled HD Sets
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    nFilledHDSets     <= 2'b00;
    currentReadHDSet  <= 1'b0;
    currentWriteHDSet <= 1'b0;
    currentReadHDAMPDUSet <= 1'b0;
  end
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
  // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
  begin
    nFilledHDSets     <= 2'b00;
    currentReadHDSet  <= 1'b0;
    currentWriteHDSet <= 1'b0;
    currentReadHDAMPDUSet <= 1'b0;
  end
  else
  begin
    if (discardPrevHD_p)
    // In case of Discard Previous Header Descriptor pulse received from the DMA Engine,
    // The nFilledHDSets and currentWriteHDSet need to be adjusted to cancel the last Header 
    // descriptor reception.
    // To avoid problem, two cases have been defined.
    // 1- If the MAC Controller requests a toggle of the HD Sets simultaneously
    // 2- If the MAC Controller does not request a toggle of the HD Sets simultaneously
    begin
      if ((toggleHDSet_p) || (nFilledHDSets == 2'b00))
      // 1- If the MAC Controller requests a toggle of the HD Sets simultaneously,
      // This case can happen only if nFilledHDSets is equals to 2 (1 for the 
      // pending toggle request and 1 for the HD which has to be discarded
      // So,the number of Filled HD Set is reset to zero.
      // See also the cover point countDiscardHDEnd
      begin
        nFilledHDSets     <= 2'b00;
        currentReadHDSet  <= 1'b0;
        currentWriteHDSet <= 1'b0;
        currentReadHDAMPDUSet <= 1'b0;
      end   
      else
      // 2- If the MAC Controller does not request a toggle of the HD Sets simultaneously,
      // This case can happen if nFilledHDSets is equals to 2 (1 for a 
      // pending toggle request and 1 for the HD which has to be discarded) or 1
      // (1 for the HD which has to be discarded
      // In this case, the number of Filled HD set is descreased of 1
      begin
        nFilledHDSets     <= nFilledHDSets - 2'b1;
        currentWriteHDSet <= ~currentWriteHDSet;
      end
    end    
    else
    // If HD Set discard is not requested, there is three different cases 
    // depending if the MAC Controller requests a toggle of the HD Sets 
    // and if the DMA has completed the Header Descriptor transfer. 
    // Both events can happen simultaniously.
    begin
    `ifdef RW_THD_V2
      if (toggleHDSet_p && hDescStatusInf_p)
    `else // RW_THD_V2
      if (toggleHDSet_p && hDescMdmTimeUsed_p)
    `endif // RW_THD_V2
      // 1- When the DMA has completed the HD transfer and the MAC Controller 
      // requests a toggle at the same time.
      // In this case, the number of Filled HD Set does not change (+1 due to 
      // the DMA HD transfer and -1 due to the MAC COntroller toggle request)
      // and both currentWriteHDSet and currentReadHDSet pointers toggle.
      // See also the cover point countToggleHDEnd
      begin
        nFilledHDSets     <= nFilledHDSets;
        currentReadHDSet  <= ~currentReadHDSet;
        currentWriteHDSet <= ~currentWriteHDSet;
        if (!aMPDU || (whichDescriptor == 2'b11))
          currentReadHDAMPDUSet <= ~currentReadHDSet;
      end   
      else if (toggleHDSet_p)
      // 2- When the MAC Controller requests a toggle.
      // In this case, the number of Filled HD Set is decremented (-1 due to 
      // the MAC COntroller toggle request) and the currentReadHDSet pointer
      // toggles.
      begin
        nFilledHDSets     <= nFilledHDSets - 2'b1;
        currentReadHDSet  <= ~currentReadHDSet;
        if (!aMPDU || (whichDescriptor == 2'b11))
          currentReadHDAMPDUSet <= ~currentReadHDSet;
      end   
    `ifdef RW_THD_V2
      else if (hDescStatusInf_p)
    `else // RW_THD_V2
      else if (hDescMdmTimeUsed_p)
    `endif // RW_THD_V2
      // 3- When the DMA has completed the Header Descriptor transfer.
      // In this case, the number of Filled HD Set is incremented (+1 due to 
      // the DMA HD transfer) and the currentWriteHDSet pointer toggles.
      begin
        nFilledHDSets     <= nFilledHDSets + 2'b1;
        currentWriteHDSet <= ~currentWriteHDSet;
      end   
    end 
  end
end





// Policy Table Sets Management
///////////////////////////////
// This process manages the  Policy Table Set Read and Write pointers 
// as well as the number of filled PT Sets
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    nFilledPTSets     <= 2'b00;
    currentReadPTSet  <= 1'b0;
    currentWritePTSet <= 1'b0;
  end
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
  // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
  begin
    nFilledPTSets     <= 2'b00;
    currentReadPTSet  <= 1'b0;
    currentWritePTSet <= 1'b0;
  end
  else
  // There is three different cases depending if the MAC Controller requests 
  // a toggle of the PT Sets and if the DMA has completed the Policy Table transfer. 
  // Both events can happen simultaneously.
  begin
    if (togglePTSet_p && pTablePOWERCntrlInf4_p)
    // 1- When the DMA has completed the PT transfer and the MAC Controller 
    // requests a toggle at the same time.
    // In this case, the number of Filled PT Set does not change (+1 due to 
    // the DMA Policy Table transfer and -1 due to the MAC COntroller toggle request)
    // and both currentWritePTSet and currentReadPTSet pointers toggle.
    // See also the cover point countTogglePTEnd
    begin
      nFilledPTSets     <= nFilledPTSets;
      currentReadPTSet  <= ~currentReadPTSet;
      currentWritePTSet <= ~currentWritePTSet;
    end   
    else if (togglePTSet_p)
    // 2- When the MAC Controller requests a toggle.
    // In this case, the number of Filled PT Set is decremented (-1 due to 
    // the MAC COntroller toggle request) and the currentReadPTSet pointer
    // toggles.
    begin
      nFilledPTSets     <= nFilledPTSets - 2'b1;
      currentReadPTSet  <= ~currentReadPTSet;
    end   
    else if (pTablePOWERCntrlInf4_p)
    // 3- When the DMA has completed the Policy Table transfer.
    // In this case, the number of Filled PT Set is incremented (+1 due to 
    // the DMA PT transfer) and the currentWritePTSet pointer toggles.
    begin
      nFilledPTSets     <= nFilledPTSets + 2'b1;
      currentWritePTSet <= ~currentWritePTSet;
    end   
  end
end

// always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
// begin
//   if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
//     currentReadHDAMPDUSet <= 1'b0;
//   else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
//   // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
//     currentReadHDAMPDUSet <= 1'b0;
//   else
//     if (!partOfAMPDU)
//       currentReadHDAMPDUSet <= currentReadHDSet;
// end      


// Header Descriptor Sets Update 
////////////////////////////////
// This process fills the HD Sets with the data comming from the DMA Engine
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    hDescFrameLengthSet1      <= 20'b0;
    hDescPHYCntrlInfSet1      <= 32'b0;
    hDescOptFrameLength20Set1 <= 20'b0;
    hDescOptFrameLength40Set1 <= 20'b0;
    hDescOptFrameLength80Set1 <= 20'b0;
    hDescMACCntrlInf1Set1     <= 32'b0;
    hDescMACCntrlInf2Set1     <= 32'b0;
    hDescStatusInfSet1        <= 32'b0;
    hDescMdmTimeUsedSet1      <= 32'b0;

    hDescFrameLengthSet0      <= 20'b0;
    hDescPHYCntrlInfSet0      <= 32'b0;
    hDescOptFrameLength20Set0 <= 20'b0;
    hDescOptFrameLength40Set0 <= 20'b0;
    hDescOptFrameLength80Set0 <= 20'b0;
    hDescMACCntrlInf1Set0     <= 32'b0;
    hDescMACCntrlInf2Set0     <= 32'b0;
    hDescStatusInfSet0        <= 32'b0;
    hDescMdmTimeUsedSet0      <= 32'b0;
  end
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
  // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
  begin
    hDescFrameLengthSet1      <= 20'b0;
    hDescPHYCntrlInfSet1      <= 32'b0;
    hDescOptFrameLength20Set1 <= 20'b0;
    hDescOptFrameLength40Set1 <= 20'b0;
    hDescOptFrameLength80Set1 <= 20'b0;
    hDescMACCntrlInf1Set1     <= 32'b0;
    hDescMACCntrlInf2Set1     <= 32'b0;
    hDescStatusInfSet1        <= 32'b0;
    hDescMdmTimeUsedSet1      <= 32'b0;

    hDescFrameLengthSet0      <= 20'b0;
    hDescPHYCntrlInfSet0      <= 32'b0;
    hDescOptFrameLength20Set0 <= 20'b0;
    hDescOptFrameLength40Set0 <= 20'b0;
    hDescOptFrameLength80Set0 <= 20'b0;
    hDescMACCntrlInf1Set0     <= 32'b0;
    hDescMACCntrlInf2Set0     <= 32'b0;
    hDescStatusInfSet0        <= 32'b0;
    hDescMdmTimeUsedSet0      <= 32'b0;
  end
  else
    if (currentWriteHDSet)
    // If the current HD Set write pointer is 1, the HD Set 1 fields
    // are updated with the data comming from the DMA Engine. The field of
    // the HD Set 1 is selected based on the pulses generated by the FSM
    begin
      // Received H-Descriptor Frame Length data
      if (hDescFrameLength_p)
        hDescFrameLengthSet1 <= txCtrlRegData[19:0];

      // Received H-Descriptor PHY Control Information data
      else if (hDescPHYCntrlInf_p)
      begin
        if (!partOfAMPDU)
          hDescPHYCntrlInfSet1 <= txCtrlRegData;
        else
          hDescPHYCntrlInfSet1 <= hDescPHYCntrlInfSet0;
      end
      
      // Received H-Descriptor Optional Frame Length drop to 20 Mhz data
      else if (hDescOptFrameLength20_p)
        hDescOptFrameLength20Set1 <= txCtrlRegData[19:0];
        
      // Received H-Descriptor Optional Frame Length drop to 40 Mhz data
      else if (hDescOptFrameLength40_p)
        hDescOptFrameLength40Set1 <= txCtrlRegData[19:0];
        
      // Received H-Descriptor Optional Frame Length drop to 80 Mhz data
      else if (hDescOptFrameLength80_p)
        hDescOptFrameLength80Set1 <= txCtrlRegData[19:0];
        
      // Received H-Descriptor MAC Control Information 1 data
      else if (hDescMACCntrlInf1_p)
      begin
      	if (!partOfAMPDU)
          hDescMACCntrlInf1Set1 <= txCtrlRegData;
        else  
          hDescMACCntrlInf1Set1 <= hDescMACCntrlInf1Set0;
      end
      
      // Received H-Descriptor MAC Control Information 2 data
      else if (hDescMACCntrlInf2_p)
        hDescMACCntrlInf2Set1 <= txCtrlRegData;

      // Received H-Descriptor Status Information data
      else if (hDescStatusInf_p)
        hDescStatusInfSet1 <= txCtrlRegData;
        
      // Received H-Descriptor Medium Time Used data
      else if (hDescMdmTimeUsed_p)
      begin
        if (!partOfAMPDU)
          hDescMdmTimeUsedSet1 <= txCtrlRegData;
        else
          hDescMdmTimeUsedSet1 <= hDescMdmTimeUsedSet0;
      end
    end  
    else 
    // If the current HD Set write pointer is 0, the HD Set 0 fields
    // are updated following the same mechanism than for HD Set 1 previously
    // described
    begin
      // Received H-Descriptor Frame Length data
      if (hDescFrameLength_p)
        hDescFrameLengthSet0 <= txCtrlRegData[19:0];

      // Received H-Descriptor PHY Control Information data
      else if (hDescPHYCntrlInf_p)
      begin
      	if (!partOfAMPDU)
          hDescPHYCntrlInfSet0 <= txCtrlRegData;
        else
          hDescPHYCntrlInfSet0 <= hDescPHYCntrlInfSet1;
      end
      
      // Received H-Descriptor Optional Frame Length drop to 20 Mhz data
      else if (hDescOptFrameLength20_p)
        hDescOptFrameLength20Set0 <= txCtrlRegData[19:0];
        
      // Received H-Descriptor Optional Frame Length drop to 40 Mhz data
      else if (hDescOptFrameLength40_p)
        hDescOptFrameLength40Set0 <= txCtrlRegData[19:0];
        
      // Received H-Descriptor Optional Frame Length drop to 80 Mhz data
      else if (hDescOptFrameLength80_p)
        hDescOptFrameLength80Set0 <= txCtrlRegData[19:0];

      // Received H-Descriptor MAC Control Information 1 data
      else if (hDescMACCntrlInf1_p)
      begin
      	if (!partOfAMPDU)
      	  hDescMACCntrlInf1Set0 <= txCtrlRegData;
      	else
      	  hDescMACCntrlInf1Set0 <= hDescMACCntrlInf1Set1;  
      end
      
      // Received H-Descriptor MAC Control Information 2 data
      else if (hDescMACCntrlInf2_p)
        hDescMACCntrlInf2Set0 <= txCtrlRegData;

      // Received H-Descriptor Status Information data
      else if (hDescStatusInf_p)
        hDescStatusInfSet0 <= txCtrlRegData;
        
      // Received H-Descriptor Medium Time Used data
      else if (hDescMdmTimeUsed_p)
      begin
        if (!partOfAMPDU)
          hDescMdmTimeUsedSet0 <= txCtrlRegData;
        else
          hDescMdmTimeUsedSet0 <= hDescMdmTimeUsedSet1;
      end
    end  
end


// Policy Table Sets Update
///////////////////////////
// This process fills the PT Sets with the data comming from the DMA Engine
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    pTablePHYCntrlInf1Set1   <= 32'b0;
    pTablePHYCntrlInf2Set1   <= 32'b0;
    pTableMACCntrlInf1Set1   <= 32'b0;
    pTableMACCntrlInf2Set1   <= 32'b0;
    pTableRateCntrlInf1Set1  <= 32'b0;
    pTableRateCntrlInf2Set1  <= 32'b0;
    pTableRateCntrlInf3Set1  <= 32'b0;
    pTableRateCntrlInf4Set1  <= 32'b0;
    pTablePowerCntrlInf1Set1 <= 32'b0;
    pTablePowerCntrlInf2Set1 <= 32'b0;
    pTablePowerCntrlInf3Set1 <= 32'b0;
    pTablePowerCntrlInf4Set1 <= 32'b0;

    pTablePHYCntrlInf1Set0   <= 32'b0;
    pTablePHYCntrlInf2Set0   <= 32'b0;
    pTableMACCntrlInf1Set0   <= 32'b0;
    pTableMACCntrlInf2Set0   <= 32'b0;
    pTableRateCntrlInf1Set0  <= 32'b0;
    pTableRateCntrlInf2Set0  <= 32'b0;
    pTableRateCntrlInf3Set0  <= 32'b0;
    pTableRateCntrlInf4Set0  <= 32'b0;
    pTablePowerCntrlInf1Set0 <= 32'b0;
    pTablePowerCntrlInf2Set0 <= 32'b0;
    pTablePowerCntrlInf3Set0 <= 32'b0;
    pTablePowerCntrlInf4Set0 <= 32'b0;
  end
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
  // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
  begin
    pTablePHYCntrlInf1Set1   <= 32'b0;
    pTablePHYCntrlInf2Set1   <= 32'b0;
    pTableMACCntrlInf1Set1   <= 32'b0;
    pTableMACCntrlInf2Set1   <= 32'b0;
    pTableRateCntrlInf1Set1  <= 32'b0;
    pTableRateCntrlInf2Set1  <= 32'b0;
    pTableRateCntrlInf3Set1  <= 32'b0;
    pTableRateCntrlInf4Set1  <= 32'b0;
    pTablePowerCntrlInf1Set1 <= 32'b0;
    pTablePowerCntrlInf2Set1 <= 32'b0;
    pTablePowerCntrlInf3Set1 <= 32'b0;
    pTablePowerCntrlInf4Set1 <= 32'b0;

    pTablePHYCntrlInf1Set0   <= 32'b0;
    pTablePHYCntrlInf2Set0   <= 32'b0;
    pTableMACCntrlInf1Set0   <= 32'b0;
    pTableMACCntrlInf2Set0   <= 32'b0;
    pTableRateCntrlInf1Set0  <= 32'b0;
    pTableRateCntrlInf2Set0  <= 32'b0;
    pTableRateCntrlInf3Set0  <= 32'b0;
    pTableRateCntrlInf4Set1  <= 32'b0;
    pTablePowerCntrlInf1Set0 <= 32'b0;
    pTablePowerCntrlInf2Set0 <= 32'b0;
    pTablePowerCntrlInf3Set0 <= 32'b0;
    pTablePowerCntrlInf4Set1 <= 32'b0;
  end
  else
    if (currentWritePTSet)
    // If the current PT Set write pointer is 1, the PT Set 1 fields
    // are updated with the data comming from the DMA Engine. The field of
    // the PT Set 1 is selected based on the pulses generated by the FSM
    begin
      // Received P-Table PHY Control Information 1 data
      if (pTablePHYCntrlInf1_p)
        pTablePHYCntrlInf1Set1 <= txCtrlRegData;

      // Received P-Table PHY Control Information 2 data
      else if (pTablePHYCntrlInf2_p)
        pTablePHYCntrlInf2Set1 <= txCtrlRegData;

      // Received P-Table MAC Control Information 1 data
      else if (pTableMACCntrlInf1_p)
        pTableMACCntrlInf1Set1 <= txCtrlRegData;

      // Received P-Table MAC Control Information 2 data
      else if (pTableMACCntrlInf2_p)
        pTableMACCntrlInf2Set1 <= txCtrlRegData;

      // Received P-Table RATE Control Information 1 data
      else if(pTableRATECntrlInf1_p)
        pTableRateCntrlInf1Set1 <= txCtrlRegData;

      // Received P-Table RATE Control Information 2 data
      else if(pTableRATECntrlInf2_p)
        pTableRateCntrlInf2Set1 <= txCtrlRegData;

      // Received P-Table RATE Control Information 3 data
      else if(pTableRATECntrlInf3_p)
        pTableRateCntrlInf3Set1 <= txCtrlRegData;

      // Received P-Table RATE Control Information 4 data
      else if(pTableRATECntrlInf4_p)
        pTableRateCntrlInf4Set1 <= txCtrlRegData;

      // Received P-Table POWER Control Information 1 data
      else if(pTablePOWERCntrlInf1_p)
        pTablePowerCntrlInf1Set1 <= txCtrlRegData;

      // Received P-Table POWER Control Information 2 data
      else if(pTablePOWERCntrlInf2_p)
        pTablePowerCntrlInf2Set1 <= txCtrlRegData;

      // Received P-Table POWER Control Information 3 data
      else if(pTablePOWERCntrlInf3_p)
        pTablePowerCntrlInf3Set1 <= txCtrlRegData;

      // Received P-Table POWER Control Information 4 data
      else if(pTablePOWERCntrlInf4_p)
        pTablePowerCntrlInf4Set1 <= txCtrlRegData;

    end  
    else
    // If the current PT Set write pointer is 0, the PT Set 0 fields
    // are updated following the same mechanism than for PT Set 1 previously
    // described
    begin
      // Received P-Table PHY Control Information 1 data
      if (pTablePHYCntrlInf1_p)
        pTablePHYCntrlInf1Set0 <= txCtrlRegData;

      // Received P-Table PHY Control Information 2 data
      else if (pTablePHYCntrlInf2_p)
        pTablePHYCntrlInf2Set0 <= txCtrlRegData;

      // Received P-Table MAC Control Information 1 data
      else if (pTableMACCntrlInf1_p)
        pTableMACCntrlInf1Set0 <= txCtrlRegData;

      // Received P-Table MAC Control Information 2 data
      else if (pTableMACCntrlInf2_p)
        pTableMACCntrlInf2Set0 <= txCtrlRegData;

      // Received P-Table RATE Control Information 1 data
      else if(pTableRATECntrlInf1_p)
        pTableRateCntrlInf1Set0 <= txCtrlRegData;

      // Received P-Table RATE Control Information 2 data
      else if(pTableRATECntrlInf2_p)
        pTableRateCntrlInf2Set0 <= txCtrlRegData;

      // Received P-Table RATE Control Information 3 data
      else if(pTableRATECntrlInf3_p)
        pTableRateCntrlInf3Set0 <= txCtrlRegData;

      // Received P-Table RATE Control Information 4 data
      else if(pTableRATECntrlInf4_p)
        pTableRateCntrlInf4Set0 <= txCtrlRegData;

      // Received P-Table POWER Control Information 1 data
      else if(pTablePOWERCntrlInf1_p)
        pTablePowerCntrlInf1Set0 <= txCtrlRegData;

      // Received P-Table POWER Control Information 2 data
      else if(pTablePOWERCntrlInf2_p)
        pTablePowerCntrlInf2Set0 <= txCtrlRegData;

      // Received P-Table POWER Control Information 3 data
      else if(pTablePOWERCntrlInf3_p)
        pTablePowerCntrlInf3Set0 <= txCtrlRegData;

      // Received P-Table POWER Control Information 4 data
      else if(pTablePOWERCntrlInf4_p)
        pTablePowerCntrlInf4Set0 <= txCtrlRegData;

    end  
end


// txParameter Ready indication generation
//////////////////////////////////////////
// This process generates the txParameterHDReady and txParameterPTReady
// indication flag. These two flags indicates to the MAC Controller when
// a HD Set or PT Set is avaible on the interface and can be read safetly.
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    txParameterHDReady   <= 1'b0;
    txParameterPTReady   <= 1'b0;
  end
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
  // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
  begin
    txParameterHDReady   <= 1'b0;
    txParameterPTReady   <= 1'b0;
  end
  else
  begin
    // When one of the HD Sets is filled (number of filled HD Sets not equal to zero)
    // the txParameterHDReady indication is set. However, this indication is not set during 
    // the HD set toggle clock cycle. This is prevented with toggleHDSet_p
    if (nFilledHDSets != 2'b00 && !toggleHDSet_p)
      txParameterHDReady   <= 1'b1;
    else
      txParameterHDReady   <= 1'b0;

    // When one of the PT Sets is filled (number of filled PT Sets not equal to zero)
    // the txParameterPTReady indication is set. However, this indication is not set during 
    // the PT set toggle clock cycle. This is prevented with togglePTSet_p
    if (nFilledPTSets != 2'b00 && !togglePTSet_p)
      txParameterPTReady   <= 1'b1;
    else
      txParameterPTReady   <= 1'b0;
  end    
end

assign txParameterNextPTReady = (nFilledPTSets == 2'b10) ? 1'b1 : 1'b0;


assign txParameterNextPTReady_p = txParameterNextPTReady && !txParameterNextPTReadyDelay;
assign txParameterHDReady_p     = txParameterHDReady && !txParameterHDReadyDelay;
assign txParameterPTReady_p     = txParameterPTReady && !txParameterPTReadyDelay;

always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    txParameterPTReadyDelay <= 1'b0; 
  else
    txParameterPTReadyDelay <= txParameterPTReady;
end

always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    txParameterHDReadyDelay <= 1'b0; 
  else
    txParameterHDReadyDelay <= txParameterHDReady;
end

always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    txParameterNextPTReadyDelay <= 1'b0; 
  else
    txParameterNextPTReadyDelay <= txParameterNextPTReady;
end


// aMPDUFrameLengthTx Generation
////////////////////////////////
// This process generates the aMPDUFrameLengthTx and keep it available 
// during the full A-MPDU transfert
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    aMPDUFrameLengthTx <= 20'b0;
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset  
    // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
    aMPDUFrameLengthTx <= 20'b0;
  else if (aMPDU && (whichDescriptor == 2'b0) && (nFilledHDSets != 2'b00))
  begin
    // The aMPDUFrameLengthTx is updated only when the Policy Table of a A-MPDU
    // is transfer.
    aMPDUFrameLengthTx <= hDescFrameLengthSet;
  end
  // Case if VHT single MPDU
  else if (!aMPDU && (formatModTx == 3'b100) && (hDescFrameLengthSet != 20'd0) && (nFilledHDSets != 2'b00))
  begin
    // The aMPDUFrameLengthTx is updated only when the Policy Table of a A-MPDU
    // is transfer.
    aMPDUFrameLengthTx <= aMPDUFrameLengthTxGen;
  end
end    

// This process generates the aMPDUOptFrameLength20Tx and keep it available 
// during the full A-MPDU transfert
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    aMPDUOptFrameLength20Tx <= 20'b0;
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset  
    // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
    aMPDUOptFrameLength20Tx <= 20'b0;
  else if (aMPDU && (whichDescriptor == 2'b0) && (nFilledHDSets != 2'b00))
  begin
    // The aMPDUOptFrameLength20Tx is updated only when the Policy Table of a A-MPDU
    // is transfer.
    aMPDUOptFrameLength20Tx <= hDescOptFrameLength20Set;
  end
  // Case if VHT single MPDU
  else if (!aMPDU && (formatModTx == 3'b100) && (hDescOptFrameLength20Set != 20'd0) && (nFilledHDSets != 2'b00))
  begin
    // The aMPDUOptFrameLength20Tx is updated only when the Policy Table of a A-MPDU
    // is transfer.
    aMPDUOptFrameLength20Tx <= aMPDUOptFrameLength20TxGen;
  end
end    

// This process generates the aMPDUOptFrameLength40Tx and keep it available 
// during the full A-MPDU transfert
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    aMPDUOptFrameLength40Tx <= 20'b0;
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset  
    // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
    aMPDUOptFrameLength40Tx <= 20'b0;
  else if (aMPDU && (whichDescriptor == 2'b0) && (nFilledHDSets != 2'b00))
  begin
    // The aMPDUOptFrameLength40Tx is updated only when the Policy Table of a A-MPDU
    // is transfer.
    aMPDUOptFrameLength40Tx <= hDescOptFrameLength40Set;
  end
  // Case if VHT single MPDU
  else if (!aMPDU && (formatModTx == 3'b100) && (hDescOptFrameLength40Set != 20'd0) && (nFilledHDSets != 2'b00))
  begin
    // The aMPDUOptFrameLength40Tx is updated only when the Policy Table of a A-MPDU
    // is transfer.
    aMPDUOptFrameLength40Tx <= aMPDUOptFrameLength40TxGen;
  end
end    

// This process generates the aMPDUOptFrameLength80Tx and keep it available 
// during the full A-MPDU transfert
always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    aMPDUOptFrameLength80Tx <= 20'b0;
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset  
    // In case of retry, the Tx Parameters Cache is cleared (synchronous reset).
    aMPDUOptFrameLength80Tx <= 20'b0;
  else if (aMPDU && (whichDescriptor == 2'b0) && (nFilledHDSets != 2'b00))
  begin
    // The aMPDUOptFrameLength80Tx is updated only when the Policy Table of a A-MPDU
    // is transfer.
    aMPDUOptFrameLength80Tx <= hDescOptFrameLength80Set;
  end
  // Case if VHT single MPDU
  else if (!aMPDU && (formatModTx == 3'b100) && (hDescOptFrameLength80Set != 20'd0) && (nFilledHDSets != 2'b00))
  begin
    // The aMPDUOptFrameLength80Tx is updated only when the Policy Table of a A-MPDU
    // is transfer.
    aMPDUOptFrameLength80Tx <= aMPDUOptFrameLength80TxGen;
  end
end    


// Length selection from header descriptor
assign hDescFrameLengthSet      = (currentReadHDSet) ? hDescFrameLengthSet1 : hDescFrameLengthSet0;
assign hDescOptFrameLength20Set = (currentReadHDSet) ? hDescOptFrameLength20Set1 : hDescOptFrameLength20Set0;
assign hDescOptFrameLength40Set = (currentReadHDSet) ? hDescOptFrameLength40Set1 : hDescOptFrameLength40Set0;
assign hDescOptFrameLength80Set = (currentReadHDSet) ? hDescOptFrameLength80Set1 : hDescOptFrameLength80Set0;

always @ (posedge macPITxClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    aMPDUOut  <= 1'b0;
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
    aMPDUOut  <= 1'b0;
  else
    aMPDUOut  <= (aMPDU || txSingleVHTMPDU);
end

// ampdu length generation for VHT single MPDU = mpdu length         + delimiter length + padding
//                                             = hDescFrameLengthSet + 4                + (4 - hDescFrameLengthSet % 4)
assign aMPDUFrameLengthTxGen = (hDescFrameLengthSet[1:0] == 2'b00) ? hDescFrameLengthSet + 20'd4                                   :
                                                                     hDescFrameLengthSet + 20'd8 - {18'd0,hDescFrameLengthSet[1:0]};
                                                                     
assign aMPDUOptFrameLength20TxGen = (hDescFrameLengthSet[1:0] == 2'b00) ? hDescOptFrameLength20Set + 20'd4                                   :
                                                                          hDescOptFrameLength20Set + 20'd8 - {18'd0,hDescFrameLengthSet[1:0]};
assign aMPDUOptFrameLength40TxGen = (hDescFrameLengthSet[1:0] == 2'b00) ? hDescOptFrameLength40Set + 20'd4                                   :
                                                                          hDescOptFrameLength40Set + 20'd8 - {18'd0,hDescFrameLengthSet[1:0]};
assign aMPDUOptFrameLength80TxGen = (hDescFrameLengthSet[1:0] == 2'b00) ? hDescOptFrameLength80Set + 20'd4                                   :
                                                                          hDescOptFrameLength80Set + 20'd8 - {18'd0,hDescFrameLengthSet[1:0]};

always @ (posedge macPITxClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    ampduVHTSingleMpdu     <= 1'b0;
  else if ((macPIClkSoftRst_n == 1'b0) || (clearSets_p == 1'b1))  // Synchronous Reset
    ampduVHTSingleMpdu     <= 1'b0;
  else
  begin
    if(!aMPDU && (formatModTx == 3'b100) && (hDescFrameLengthSet != 20'd0))
      ampduVHTSingleMpdu <= 1'b1;
    else
      ampduVHTSingleMpdu <= 1'b0;
  end
end

assign txSingleVHTMPDU = ampduVHTSingleMpdu;

// Header Descriptor Ouptuts Assigments
///////////////////////////////////////

// Header Descriptor
assign MPDUFrameLengthTx  = (currentReadHDSet) ? hDescFrameLengthSet1[15:0]   : hDescFrameLengthSet0[15:0];

// PHY Control Information fields assigment 
assign partialAIDTx       = (currentReadHDSet) ? hDescPHYCntrlInfSet1[30:22]  : hDescPHYCntrlInfSet0[30:22];
assign groupIDTx          = (currentReadHDSet) ? hDescPHYCntrlInfSet1[21:16]  : hDescPHYCntrlInfSet0[21:16];
assign useRIFSTx          = (currentReadHDSet) ? hDescPHYCntrlInfSet1[14]     : hDescPHYCntrlInfSet0[14];
assign continuousTx       = (currentReadHDSet) ? hDescPHYCntrlInfSet1[6]      : hDescPHYCntrlInfSet0[6];
assign dozeNotAllowedTx   = (currentReadHDSet) ? hDescPHYCntrlInfSet1[5]      : hDescPHYCntrlInfSet0[5];
assign dynBWTx            = (currentReadHDSet) ? hDescPHYCntrlInfSet1[4]      : hDescPHYCntrlInfSet0[4];
assign useBWSignalingTx   = (currentReadHDSet) ? hDescPHYCntrlInfSet1[3]      : hDescPHYCntrlInfSet0[3];
assign smoothingProtTx    = (currentReadHDSet) ? hDescPHYCntrlInfSet1[2]      : hDescPHYCntrlInfSet0[2];
assign smoothingTx        = (currentReadHDSet) ? hDescPHYCntrlInfSet1[1]      : hDescPHYCntrlInfSet0[1];
assign soundingTx         = (currentReadHDSet) ? hDescPHYCntrlInfSet1[0]      : hDescPHYCntrlInfSet0[0];

// MAC Control Information 1 fields assigment
assign protFrmDur         = (currentReadHDSet) ? hDescMACCntrlInf1Set1[31:16] : hDescMACCntrlInf1Set0[31:16];
assign writeACK           = (currentReadHDSet) ? hDescMACCntrlInf1Set1[14]    : hDescMACCntrlInf1Set0[14];
assign lowRateRetry       = (currentReadHDSet) ? hDescMACCntrlInf1Set1[13]    : hDescMACCntrlInf1Set0[13];
assign lstpProt           = (currentReadHDSet) ? hDescMACCntrlInf1Set1[12]    : hDescMACCntrlInf1Set0[12];
assign lstp               = (currentReadHDSet) ? hDescMACCntrlInf1Set1[11]    : hDescMACCntrlInf1Set0[11];
assign expectedAck        = (currentReadHDSet) ? hDescMACCntrlInf1Set1[10:9]  : hDescMACCntrlInf1Set0[10:9];

// MAC Control Information 2 fields assigment
assign dontGenerateMH     = (currentReadHDSet) ? hDescMACCntrlInf2Set1[31]    : hDescMACCntrlInf2Set0[31];
assign dontEncrypt        = (currentReadHDSet) ? hDescMACCntrlInf2Set1[30]    : hDescMACCntrlInf2Set0[30];
assign dontTouchFC        = (currentReadHDSet) ? hDescMACCntrlInf2Set1[29]    : hDescMACCntrlInf2Set0[29];
assign dontTouchDur       = (currentReadHDSet) ? hDescMACCntrlInf2Set1[28]    : hDescMACCntrlInf2Set0[28];
assign dontTouchQoS       = (currentReadHDSet) ? hDescMACCntrlInf2Set1[27]    : hDescMACCntrlInf2Set0[27];
assign dontTouchHTC       = (currentReadHDSet) ? hDescMACCntrlInf2Set1[26]    : hDescMACCntrlInf2Set0[26];
assign dontTouchTSF       = (currentReadHDSet) ? hDescMACCntrlInf2Set1[25]    : hDescMACCntrlInf2Set0[25];
assign dontTouchDTIM      = (currentReadHDSet) ? hDescMACCntrlInf2Set1[24]    : hDescMACCntrlInf2Set0[24];
assign dontTouchFCS       = (currentReadHDSet) ? hDescMACCntrlInf2Set1[23]    : hDescMACCntrlInf2Set0[23];
assign underBASetup       = (currentReadHDSet) ? hDescMACCntrlInf2Set1[22]    : hDescMACCntrlInf2Set0[22];
assign aMPDU              = (currentReadHDSet) ? hDescMACCntrlInf2Set1[21]    : hDescMACCntrlInf2Set0[21];
assign whichDescriptor    = (currentReadHDSet) ? hDescMACCntrlInf2Set1[20:19] : hDescMACCntrlInf2Set0[20:19];
assign nBlankMDelimiters  = (currentReadHDSet) ? hDescMACCntrlInf2Set1[18:9]  : hDescMACCntrlInf2Set0[18:9];
assign interruptEnTx      = (currentReadHDSet) ? hDescMACCntrlInf2Set1[8]     : hDescMACCntrlInf2Set0[8];
assign fcSubtype          = (currentReadHDSet) ? hDescMACCntrlInf2Set1[6:3]   : hDescMACCntrlInf2Set0[6:3];
assign fcType             = (currentReadHDSet) ? hDescMACCntrlInf2Set1[2:1]   : hDescMACCntrlInf2Set0[2:1];
assign tsValid            = (currentReadHDSet) ? hDescMACCntrlInf2Set1[0]     : hDescMACCntrlInf2Set0[0];

// Status Information fields assigment
assign lifetimeExpired    = (currentReadHDSet) ? hDescStatusInfSet1[17]    : hDescStatusInfSet0[17];
assign numMPDURetries     = (currentReadHDSet) ? hDescStatusInfSet1[15:8]  : hDescStatusInfSet0[15:8];
assign numRTSRetries      = (currentReadHDSet) ? hDescStatusInfSet1[7:0]   : hDescStatusInfSet0[7:0];

// Medium Time Used field assignment
assign mediumTimeUsed     = (currentReadHDSet) ? hDescMdmTimeUsedSet1   : hDescMdmTimeUsedSet0;

// Policy Table Ouptuts Assigments
//////////////////////////////////

// PHY Control Information 1 output assignment
assign nTxProtPT       = (currentReadPTSet) ? pTablePHYCntrlInf1Set1[19:17] :  pTablePHYCntrlInf1Set0[19:17];
assign nTxPT           = (currentReadPTSet) ? pTablePHYCntrlInf1Set1[16:14] :  pTablePHYCntrlInf1Set0[16:14];
assign stbcPT          = (currentReadPTSet) ? pTablePHYCntrlInf1Set1[8:7]   :  pTablePHYCntrlInf1Set0[8:7];
assign fecCodingPT     = (currentReadPTSet) ? pTablePHYCntrlInf1Set1[6]     :  pTablePHYCntrlInf1Set0[6];
assign numExtnSSPT     = (currentReadPTSet) ? pTablePHYCntrlInf1Set1[5:4]   :  pTablePHYCntrlInf1Set0[5:4];
assign bfFrmExPT       = (currentReadPTSet) ? pTablePHYCntrlInf1Set1[3]     :  pTablePHYCntrlInf1Set0[3];

// PHY Control Information 2
assign beamFormedPT    = (currentReadPTSet) ? pTablePHYCntrlInf2Set1[16]    :  pTablePHYCntrlInf2Set0[16];
assign smmIndexPT      = (currentReadPTSet) ? pTablePHYCntrlInf2Set1[15:8]  :  pTablePHYCntrlInf2Set0[15:8];
assign antennaSetPT    = (currentReadPTSet) ? pTablePHYCntrlInf2Set1[7:0]   :  pTablePHYCntrlInf2Set0[7:0];

// MAC Control Information 1
assign keySRAMIndexRA  = (currentReadPTSet) ? pTableMACCntrlInf1Set1[19:10] :  pTableMACCntrlInf1Set0[19:10];
assign keySRAMIndex    = (currentReadPTSet) ? pTableMACCntrlInf1Set1[9:0]   :  pTableMACCntrlInf1Set0[9:0];

// MAC Control Information 2
assign rtsThreshold    = (currentReadPTSet) ? pTableMACCntrlInf2Set1[27:16] :  pTableMACCntrlInf2Set0[27:16];
assign shortRetryLimit = (currentReadPTSet) ? pTableMACCntrlInf2Set1[15:8]  :  pTableMACCntrlInf2Set0[15:8];
assign longRetryLimit  = (currentReadPTSet) ? pTableMACCntrlInf2Set1[7:0]   :  pTableMACCntrlInf2Set0[7:0];

//RATE Control Information 1
assign nRetryRC1          = (currentReadPTSet) ? pTableRateCntrlInf1Set1[31:29]   :  pTableRateCntrlInf1Set0[31:29];
assign formatModProtTxRC1 = (currentReadPTSet) ? pTableRateCntrlInf1Set1[28:26]   :  pTableRateCntrlInf1Set0[28:26];
assign bwProtTxRC1        = (currentReadPTSet) ? pTableRateCntrlInf1Set1[25:24]   :  pTableRateCntrlInf1Set0[25:24];
assign mcsIndexProtTxRC1  = (currentReadPTSet) ? pTableRateCntrlInf1Set1[23:17]   :  pTableRateCntrlInf1Set0[23:17];
assign navProtFrmExRC1    = (currentReadPTSet) ? pTableRateCntrlInf1Set1[16:14]   :  pTableRateCntrlInf1Set0[16:14];
assign formatModTxRC1     = (currentReadPTSet) ? pTableRateCntrlInf1Set1[13:11]   :  pTableRateCntrlInf1Set0[13:11];
assign preTypeTxRC1       = (currentReadPTSet) ? pTableRateCntrlInf1Set1[10]      :  pTableRateCntrlInf1Set0[10];
assign shortGITxRC1       = (currentReadPTSet) ? pTableRateCntrlInf1Set1[9]       :  pTableRateCntrlInf1Set0[9];
assign bwTxRC1            = (currentReadPTSet) ? pTableRateCntrlInf1Set1[8:7]     :  pTableRateCntrlInf1Set0[8:7];
assign mcsIndexTxRC1      = (currentReadPTSet) ? pTableRateCntrlInf1Set1[6:0]     :  pTableRateCntrlInf1Set0[6:0];

//POWER Control Information 1
assign txPwrLevelRC1      = (currentReadPTSet) ? pTablePowerCntrlInf1Set1[7:0]   :  pTablePowerCntrlInf1Set0[7:0];
assign txPwrLevelProtRC1  = (currentReadPTSet) ? pTablePowerCntrlInf1Set1[15:8]  :  pTablePowerCntrlInf1Set0[15:8];

//RATE Control Information 2
assign nRetryRC2          = (currentReadPTSet) ? pTableRateCntrlInf2Set1[31:29]   :  pTableRateCntrlInf2Set0[31:29];
assign formatModProtTxRC2 = (currentReadPTSet) ? pTableRateCntrlInf2Set1[28:26]   :  pTableRateCntrlInf2Set0[28:26];
assign bwProtTxRC2        = (currentReadPTSet) ? pTableRateCntrlInf2Set1[25:24]   :  pTableRateCntrlInf2Set0[25:24];
assign mcsIndexProtTxRC2  = (currentReadPTSet) ? pTableRateCntrlInf2Set1[23:17]   :  pTableRateCntrlInf2Set0[23:17];
assign navProtFrmExRC2    = (currentReadPTSet) ? pTableRateCntrlInf2Set1[16:14]   :  pTableRateCntrlInf2Set0[16:14];
assign formatModTxRC2     = (currentReadPTSet) ? pTableRateCntrlInf2Set1[13:11]   :  pTableRateCntrlInf2Set0[13:11];
assign preTypeTxRC2       = (currentReadPTSet) ? pTableRateCntrlInf2Set1[10]      :  pTableRateCntrlInf2Set0[10];
assign shortGITxRC2       = (currentReadPTSet) ? pTableRateCntrlInf2Set1[9]       :  pTableRateCntrlInf2Set0[9];
assign bwTxRC2            = (currentReadPTSet) ? pTableRateCntrlInf2Set1[8:7]     :  pTableRateCntrlInf2Set0[8:7];
assign mcsIndexTxRC2      = (currentReadPTSet) ? pTableRateCntrlInf2Set1[6:0]     :  pTableRateCntrlInf2Set0[6:0];

//POWER Control Information 2
assign txPwrLevelRC2      = (currentReadPTSet) ? pTablePowerCntrlInf2Set1[7:0]   :  pTablePowerCntrlInf2Set0[7:0];
assign txPwrLevelProtRC2  = (currentReadPTSet) ? pTablePowerCntrlInf2Set1[15:8]  :  pTablePowerCntrlInf2Set0[15:8];

//RATE Control Information 3
assign nRetryRC3          = (currentReadPTSet) ? pTableRateCntrlInf3Set1[31:29]   :  pTableRateCntrlInf3Set0[31:29];
assign formatModProtTxRC3 = (currentReadPTSet) ? pTableRateCntrlInf3Set1[28:26]   :  pTableRateCntrlInf3Set0[28:26];
assign bwProtTxRC3        = (currentReadPTSet) ? pTableRateCntrlInf3Set1[25:24]   :  pTableRateCntrlInf3Set0[25:24];
assign mcsIndexProtTxRC3  = (currentReadPTSet) ? pTableRateCntrlInf3Set1[23:17]   :  pTableRateCntrlInf3Set0[23:17];
assign navProtFrmExRC3    = (currentReadPTSet) ? pTableRateCntrlInf3Set1[16:14]   :  pTableRateCntrlInf3Set0[16:14];
assign formatModTxRC3     = (currentReadPTSet) ? pTableRateCntrlInf3Set1[13:11]   :  pTableRateCntrlInf3Set0[13:11];
assign preTypeTxRC3       = (currentReadPTSet) ? pTableRateCntrlInf3Set1[10]      :  pTableRateCntrlInf3Set0[10];
assign shortGITxRC3       = (currentReadPTSet) ? pTableRateCntrlInf3Set1[9]       :  pTableRateCntrlInf3Set0[9];
assign bwTxRC3            = (currentReadPTSet) ? pTableRateCntrlInf3Set1[8:7]     :  pTableRateCntrlInf3Set0[8:7];
assign mcsIndexTxRC3      = (currentReadPTSet) ? pTableRateCntrlInf3Set1[6:0]     :  pTableRateCntrlInf3Set0[6:0];

//POWER Control Information 3
assign txPwrLevelRC3      = (currentReadPTSet) ? pTablePowerCntrlInf3Set1[7:0]   :  pTablePowerCntrlInf3Set0[7:0];
assign txPwrLevelProtRC3  = (currentReadPTSet) ? pTablePowerCntrlInf3Set1[15:8]  :  pTablePowerCntrlInf3Set0[15:8];

//RATE Control Information 4
//assign nRetryRC4          = (currentReadPTSet) ? pTableRateCntrlInf4Set1[31:29]   :  pTableRateCntrlInf4Set0[31:29];
assign formatModProtTxRC4 = (currentReadPTSet) ? pTableRateCntrlInf4Set1[28:26]   :  pTableRateCntrlInf4Set0[28:26];
assign bwProtTxRC4        = (currentReadPTSet) ? pTableRateCntrlInf4Set1[25:24]   :  pTableRateCntrlInf4Set0[25:24];
assign mcsIndexProtTxRC4  = (currentReadPTSet) ? pTableRateCntrlInf4Set1[23:17]   :  pTableRateCntrlInf4Set0[23:17];
assign navProtFrmExRC4    = (currentReadPTSet) ? pTableRateCntrlInf4Set1[16:14]   :  pTableRateCntrlInf4Set0[16:14];
assign formatModTxRC4     = (currentReadPTSet) ? pTableRateCntrlInf4Set1[13:11]   :  pTableRateCntrlInf4Set0[13:11];
assign preTypeTxRC4       = (currentReadPTSet) ? pTableRateCntrlInf4Set1[10]      :  pTableRateCntrlInf4Set0[10];
assign shortGITxRC4       = (currentReadPTSet) ? pTableRateCntrlInf4Set1[9]       :  pTableRateCntrlInf4Set0[9];
assign bwTxRC4            = (currentReadPTSet) ? pTableRateCntrlInf4Set1[8:7]     :  pTableRateCntrlInf4Set0[8:7];
assign mcsIndexTxRC4      = (currentReadPTSet) ? pTableRateCntrlInf4Set1[6:0]     :  pTableRateCntrlInf4Set0[6:0];

//POWER Control Information 4
assign txPwrLevelRC4      = (currentReadPTSet) ? pTablePowerCntrlInf4Set1[7:0]   :  pTablePowerCntrlInf4Set0[7:0];
assign txPwrLevelProtRC4  = (currentReadPTSet) ? pTablePowerCntrlInf4Set1[15:8]  :  pTablePowerCntrlInf4Set0[15:8];

//RATE Control output

assign retryRC2Limit = ({5'h0,nRetryRC1} + {5'h0,nRetryRC2});
assign retryRC3Limit = (retryRC2Limit    + {5'h0,nRetryRC3});

assign retryRTSRC1   = (numRTSRetries <=  {5'h0,nRetryRC1});
assign retryRTSRC2   = (numRTSRetries <=  retryRC2Limit);
assign retryRTSRC3   = (numRTSRetries <=  retryRC3Limit);

assign retryMPDURC1  = (numMPDURetries <=  {5'h0,nRetryRC1});
assign retryMPDURC2  = (numMPDURetries <=  retryRC2Limit);
assign retryMPDURC3  = (numMPDURetries <=  retryRC3Limit);

always @(*)
begin
  if(lowRateRetry)
  begin
    mcsIndex0ProtTx   = retryRTSRC1  ? mcsIndexProtTxRC1 :
                        retryRTSRC2  ? mcsIndexProtTxRC2 :
                        retryRTSRC3  ? mcsIndexProtTxRC3 :
                                       mcsIndexProtTxRC4 ;

    mcsIndex0Tx       = retryMPDURC1 ? mcsIndexTxRC1 :
                        retryMPDURC2 ? mcsIndexTxRC2 :
                        retryMPDURC3 ? mcsIndexTxRC3 :
                                       mcsIndexTxRC4 ;

    formatModProtTx   = retryRTSRC1  ? formatModProtTxRC1 :
                        retryRTSRC2  ? formatModProtTxRC2 :
                        retryRTSRC3  ? formatModProtTxRC3 :
                                       formatModProtTxRC4 ;

    formatModTx       = retryMPDURC1 ? formatModTxRC1 :
                        retryMPDURC2 ? formatModTxRC2 :
                        retryMPDURC3 ? formatModTxRC3 :
                                       formatModTxRC4 ;

    preTypeProtTx     = preTypeTx;
    
    preTypeTx         = retryMPDURC1 ? preTypeTxRC1 :
                        retryMPDURC2 ? preTypeTxRC2 :
                        retryMPDURC3 ? preTypeTxRC3 :
                                       preTypeTxRC4 ;

    bwProtTx          = retryRTSRC1  ? bwProtTxRC1 :
                        retryRTSRC2  ? bwProtTxRC2 :
                        retryRTSRC3  ? bwProtTxRC3 :
                                       bwProtTxRC4 ;

    bwTx              = retryMPDURC1 ? bwTxRC1 :
                        retryMPDURC2 ? bwTxRC2 :
                        retryMPDURC3 ? bwTxRC3 :
                                       bwTxRC4 ;

    navProtFrmEx     = retryRTSRC1  ? navProtFrmExRC1 :
                       retryRTSRC2  ? navProtFrmExRC2 :
                       retryRTSRC3  ? navProtFrmExRC3 :
                                      navProtFrmExRC4 ;

    shortGIPT        = retryMPDURC1  ? shortGITxRC1 :
                       retryMPDURC2  ? shortGITxRC2 :
                       retryMPDURC3  ? shortGITxRC3 :
                                       shortGITxRC4 ;

    txPwrLevelPT     = retryMPDURC1  ? txPwrLevelRC1 :
                       retryMPDURC2  ? txPwrLevelRC2 :
                       retryMPDURC3  ? txPwrLevelRC3 :
                                       txPwrLevelRC4 ;

    txPwrLevelProtPT = retryRTSRC1  ? txPwrLevelProtRC1 :
                       retryRTSRC2  ? txPwrLevelProtRC2 :
                       retryRTSRC3  ? txPwrLevelProtRC3 :
                                      txPwrLevelProtRC4 ;

  end
  else
  begin
    mcsIndex0ProtTx  = mcsIndexProtTxRC1;
    mcsIndex0Tx      = mcsIndexTxRC1;
    formatModProtTx  = formatModProtTxRC1;
    formatModTx      = formatModTxRC1;
    preTypeProtTx    = preTypeTxRC1;
    preTypeTx        = preTypeTxRC1;
    bwProtTx         = bwProtTxRC1;
    bwTx             = bwTxRC1;
    navProtFrmEx     = navProtFrmExRC1;
    shortGIPT        = shortGITxRC1;
    txPwrLevelPT     = txPwrLevelRC1;
    txPwrLevelProtPT = txPwrLevelProtRC1;
  end
end

// Debug Port assignment
assign debugPortTxParametersCache = {txCtrlRegWr,           
                                     txCtrlRegPT,          
                                     txCtrlRegHD,          
                                     discardPrevHD_p,      
                                     txCtrlRegBusy,        
                                     toggleHDSet_p,        
                                     togglePTSet_p,        
                                     clearSets_p,          
                                     txParameterHDReady_p,   
                                     txParameterPTReady_p,   
                                     txParameterNextPTReady_p,
                                     partOfAMPDU,
                                     currentReadPTSet,
                                     currentReadHDSet,
                                     currentWritePTSet,
                                     currentWriteHDSet};

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// Display FSM State in string for RTL simulation waveform
//////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
  // hDescriptorManagement FSM states displayed in a string to easy simulation and debug
  always @*
  begin
    case (hDescriptorManagementCs)
                HD_IDLE  :  hDescriptorManagementCs_str = {"HD_IDLE"};
              HD_LENGTH  :  hDescriptorManagementCs_str = {"HD_LENGTH"};
                 HD_PHY  :  hDescriptorManagementCs_str = {"HD_PHY"};
        HD_OPT_LENGTH20  :  hDescriptorManagementCs_str = {"HD_OPT_LENGTH20"};
        HD_OPT_LENGTH40  :  hDescriptorManagementCs_str = {"HD_OPT_LENGTH40"};
        HD_OPT_LENGTH80  :  hDescriptorManagementCs_str = {"HD_OPT_LENGTH80"};
                HD_MAC1  :  hDescriptorManagementCs_str = {"HD_MAC1"};
                HD_MAC2  :  hDescriptorManagementCs_str = {"HD_MAC2"};
                HD_STAT  :  hDescriptorManagementCs_str = {"HD_STAT"};
                HD_TIME  :  hDescriptorManagementCs_str = {"HD_TIME"};
                HD_BUSY  :  hDescriptorManagementCs_str = {"HD_BUSY"};
                default  :  hDescriptorManagementCs_str = {"XXXX"};
     endcase
  end
  
  // pTableManagement FSM states displayed in a string to easy simulation and debug
  always @*
  begin
    case (pTableManagementCs)
                PT_IDLE  :  pTableManagementCs_str = {"PT_IDLE"};
                PT_PHY1  :  pTableManagementCs_str = {"PT_PHY1"};
                PT_PHY2  :  pTableManagementCs_str = {"PT_PHY2"};
                PT_MAC1  :  pTableManagementCs_str = {"PT_MAC1"};
                PT_MAC2  :  pTableManagementCs_str = {"PT_MAC2"};
               PT_RATE1  :  pTableManagementCs_str = {"PT_RATE1"};
               PT_RATE2  :  pTableManagementCs_str = {"PT_RATE2"};
               PT_RATE3  :  pTableManagementCs_str = {"PT_RATE3"};
               PT_RATE4  :  pTableManagementCs_str = {"PT_RATE4"};
              PT_POWER1  :  pTableManagementCs_str = {"PT_POWER1"};
              PT_POWER2  :  pTableManagementCs_str = {"PT_POWER2"};
              PT_POWER3  :  pTableManagementCs_str = {"PT_POWER3"};
              PT_POWER4  :  pTableManagementCs_str = {"PT_POWER4"};
                PT_BUSY  :  pTableManagementCs_str = {"PT_BUSY"};
                default  :  pTableManagementCs_str = {"XXXX"};
     endcase
  end
`endif // RW_SIMU_ON


// System Verilog Assertions
////////////////////////////

`ifdef RW_ASSERT_ON
//$rw_sva Checks if the DMA Engine does not write when the txCtrlRegBusy is set 
// That guaranty the handshaking between DMA Engine and Tx Parameters Cache
property noWriteWhenBusyCheck_prop;
@(posedge macPITxClk)
    (txCtrlRegBusy == 1'b1) |-> txCtrlRegWr == 1'b0;
endproperty
noWriteWhenBusyCheck: assert property (noWriteWhenBusyCheck_prop); 

//$rw_sva Checks if the MAC Controller does not acknowledge a TX when the Tx Parameters Sets
// are empty. Each MAC Controller TX Acknorwedgement must follow a Tx Parameters Set
// reception from the DMA Engine
property noTxDoneWithHDSetEmpty_prop;
@(posedge macPITxClk)
    (toggleHDSet_p && !macPIClkSoftRst_n) |->  (nFilledHDSets != 2'b00) || (nFilledPTSets != 2'b00);
endproperty
noTxDoneWithHDSetEmpty: assert property (noTxDoneWithHDSetEmpty_prop); 

//$rw_sva Checks if the DMA Engine does not feed two Policy Tables in AMPDU mode.
property noTwoPTInAMPDUMode_prop;
@(posedge macPITxClk)
    ((partOfAMPDU == 1'b1) && (aMPDU == 1'b1) && (whichDescriptor != 2'b11) && (nFilledPTSets != 2'b00) && txCtrlRegPT) |=> !txCtrlRegWr;
endproperty
noTwoPTInAMPDUMode: assert property (noTwoPTInAMPDUMode_prop); 

//$rw_sva Checks if the DMA Engine does not write without either txCtrlRegPT or txCtrlRegHD high
property noWriteWithoutHDorPTInd_prop;
@(posedge macPITxClk)
    (txCtrlRegWr) |->  txCtrlRegHD || txCtrlRegPT;
endproperty
noWriteWithoutHDorPTInd: assert property (noWriteWithoutHDorPTInd_prop); 

//$rw_sva Checks if toggleHDSet_p is not triggered when nFilledHDSets = 0.
property noToggleHDSet_pIfnoFilledHDSets_prop;
@(posedge macPITxClk)
    (nFilledHDSets == 2'b00) |-> !toggleHDSet_p;
endproperty 
noToggleHDSet_pIfnoFilledHDSets: assert property (noToggleHDSet_pIfnoFilledHDSets_prop);

//$rw_sva Checks if togglePTSet_p is not triggered when nFilledPTSets = 0.
property noTogglePTSet_pIfnoFilledPTSets_prop;
@(posedge macPITxClk)
    (nFilledPTSets == 2'b00) |-> !togglePTSet_p;
endproperty 
noTogglePTSet_pIfnoFilledPTSets: assert property (noTogglePTSet_pIfnoFilledPTSets_prop);

// Cover Points Definitions
///////////////////////////

//$rw_sva This cover point checks if the case 1 described in the Header Descriptor Sets Management process
// has been tested
countToggleHDEnd: cover property (@(posedge macPITxClk) (toggleHDSet_p && hDescMdmTimeUsed_p));

//$rw_sva This cover point checks if the case where both Discard Previous HD and Clear Sets happen at 
// the same time
countDiscardRetry: cover property (@(posedge macPITxClk) (clearSets_p && discardPrevHD_p));

//$rw_sva This cover point checks if the case where both Discard Previous HD and toggleHDSet_p happen at 
// the same time
countDiscardHDEnd: cover property (@(posedge macPITxClk) (toggleHDSet_p && discardPrevHD_p));

`endif // RW_ASSERT_ON

endmodule