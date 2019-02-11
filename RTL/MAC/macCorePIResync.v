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
// Description      : This module contains all the signals resynchronization 
//                    circuitry required between macCoreClk clock domain and 
//                    macPIClk clock domain.
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

module macCorePIResync ( 
  ///////////////////////////////////////////////
  //$port_g Resets
  ///////////////////////////////////////////////
  input  wire         macPIClkHardRst_n,            // Active low hard reset signal synchronized to the macPIClk.
  input  wire         macCoreClkHardRst_n,          // Active low hard reset signal synchronized to the macCoreClk.
  input  wire         macCoreClkSoftRst_n,          // Active low soft reset signal synchronized to the macCoreClk.

  ///////////////////////////////////////////////
  //$port_g Clocks
  ///////////////////////////////////////////////
  input  wire         macPIClk,                     // Primary MAC Platform Interface Clock for TX
  input  wire         macPITxClk,                   // Secondary MAC Platform Interface Clock for TX
  input  wire         macCoreClk,                   // Primary MAC Core Clock
 
  ///////////////////////////////////////////////
  //$port_g MAC Timer Unit Interface
  ///////////////////////////////////////////////
  input  wire         tick1us_p,                    // Pulse generated every us.
  input  wire [63:0]  tsfTimer,                     // TSF Timer value

  ///////////////////////////////////////////////
  //$port_g CSReg Interface
  ///////////////////////////////////////////////
  input  wire         setac3HasData,                // set ac3 has data
  input  wire         setac2HasData,                // set ac2 has data
  input  wire         setac1HasData,                // set ac1 has data
  input  wire         setac0HasData,                // set ac0 has data
  input  wire         clearac3HasData,              // clear ac3 has data
  input  wire         clearac2HasData,              // clear ac2 has data
  input  wire         clearac1HasData,              // clear ac1 has data
  input  wire         clearac0HasData,              // clear ac0 has data
  input  wire [3:0]   nextStatePlClkReg,            // Next State Register indication
  input  wire         latchNextStatePlClk_p,        // Pulse to indicate the nextState Register has been updated
                      
  output wire         statussetac3HasData,          // ac3 has data status
  output wire         statussetac2HasData,          // ac2 has data status
  output wire         statussetac1HasData,          // ac1 has data status
  output wire         statussetac0HasData,          // ac0 has data status
  
  output reg  [31:0]  tsfTimerLowIn,                // TSF Timer value [31:0] on macPIClk
  output wire         tsfTimerLowInValid,           // Indicates that the tsfTimerLow register has to be updated with tsfTimerLowIn
  output reg  [31:0]  tsfTimerHighIn,               // TSF Timer value [63:32] on macPIClk
  output wire         tsfTimerHighInValid,          // Indicates that the tsfTimerHigh register has to be updated with tsfTimerHighIn
  
  output reg   [1:0]  txBWAfterDropResync,          // Transmission bandwidth after Drop synchronized to macPIClk
  
  ///////////////////////////////////////////////
  //$port_g MAC Controller Interface
  /////////////////////////////////////////////// 
  input  wire         toggleHDSet_p,                // Indicates that the Header Descriptor Set can be toggled
  input  wire         togglePTSet_p,                // Indicates that the Policy Table Set can be toggled
  input  wire         clearSets_p,                  // Indicates that the Sets have to be cleared.
  output reg          txParameterHDReady_p,         // Indicates that the Header Descriptor fields are usable 
  output reg          txParameterPTReady_p,         // Indicates that the Policy Table fields are usable
  output wire         txParameterNextPTReady_p,     // Indicates that a second policy table has already been loaded
  output reg  [3:0]   nextStateCoreClkReg,          // Next State Register indication
  input  wire         acBWDropTrigger,              // Interrupts signal for BW drop with AMPDU length change
  input  wire [1:0]   txBWAfterDrop,                // Transmission bandwidth after BW Drop

  ///////////////////////////////////////////////
  //$port_g Tx Parameter Cache Interface
  ///////////////////////////////////////////////
  output wire         txPCtoggleHDSet_p,            // Indicates that the Header Descriptor Set can be toggled
  output wire         txPCtogglePTSet_p,            // Indicates that the Policy Table Set can be toggled
  output wire         txPCclearSets_p,              // Indicates that the Sets have to be cleared.
  input  wire         txPCtxParameterHDReady_p,     // Indicates that the Header Descriptor fields are usable 
  input  wire         txPCtxParameterPTReady_p,     // Indicates that the Policy Table fields are usable
  input  wire         txPCtxParameterNextPTReady_p, // Indicates that a second policy table has already been loaded

          //$port_g P-Table PHY Control Information 1
          input  wire  [2:0] txPCnTxProtPT,             // Number of Transmit Chains for Protection Frame
          input  wire  [2:0] txPCnTxPT,                 // Number of Transmit Chains for PPDU
          input  wire        txPCshortGIPT,             // Short Guard Interval for Transmission
                                                        // When High, it indicates whether a short Guard Interval
          input  wire  [7:0] txPCtxPwrLevelPT,          // Transmit Power Level
          input  wire  [7:0] txPCtxPwrLevelProtPT,      // Transmit Power Level for Protection Frame
          input  wire  [1:0] txPCstbcPT,                // Space Time Block Coding
          input  wire        txPCfecCodingPT,           // FEC Coding
          input  wire  [1:0] txPCnumExtnSSPT,           // Number of Extension Spatial Streams
          input  wire        txPCbfFrmExPT,             // Beam Forming Frame Exchange
                                                    // 1'b0: QoS Null/ACK
                                                    // 1'b1: RTS/CTS
          //$port_g P-Table PHY Control Information 2
          input  wire        txPCbeamFormedPT,          // BeamFormed frame
          input  wire  [7:0] txPCsmmIndexPT,            // Spatial Map Matrix Index
          input  wire  [7:0] txPCantennaSetPT,          // Antenna Set

          //$port_g P-Table MAC Control Information 1
          input  wire  [9:0] txPCkeySRAMIndex,          // Key Storage RAM Index
          input  wire  [9:0] txPCkeySRAMIndexRA,        // Key Storage RAM Index for Receiver Address

          //$port_g P-Table MAC Control Information 2
          input  wire [11:0] txPCrtsThreshold,          // RTS Threshold
          input  wire  [7:0] txPCshortRetryLimit,       // Short Retry Limit
          input  wire  [7:0] txPClongRetryLimit,        // Long Retry Limit

          //$port_g H-Descriptor PHY Control Information 
          input  wire        txPCuseRIFSTx,             // Use RIFS for Transmission
          input  wire        txPCcontinuousTx,          // Enable continuous transmission for this frame 

          //$port_g H-Descriptor Frame Lenght
          input  wire [15:0] txPCMPDUFrameLengthTx,     // Length of the MPDU

          //$port_g H-Descriptor Status Information
          input  wire        txPClifetimeExpired,       // Indicates that the lifetime of this MPDU expired

          //$port_g P-Table RATE Control
          input  wire  [2:0] txPCformatModProtTx,       // Format and Modulation of Protection frame for Transmission
                                                    // 3'b000: NON-HT
                                                    // 3'b001: NON-HT-DUP-OFDM
                                                    // 3'b010: HT-MF
                                                    // 3'b011: HT-GF
                                                    // 3'b100: VHT
          input  wire  [2:0] txPCformatModTx,           // Format and Modulation of PPDU for Transmission
                                                    // Same coding than formatModProtTx
          input  wire  [1:0] txPCbwProtTx,              // Band Width of Protection frame for Transmission
          input  wire  [1:0] txPCbwTx,                  // Band Width of PPDU for Transmission
          //$port_g H-Descriptor Status Information
          input  wire  [7:0] txPCnumMPDURetries,        // Indicates the number of MPDU retries already done   
          input  wire  [7:0] txPCnumRTSRetries,         // Indicates the number of RTS retries already done  
          input  wire [31:0] txPCmediumTimeUsed,        // Indicates the medium Time Used for current TX transfer  

          //$port_g H-Descriptor Frame Lenght
          input  wire [19:0] txPCaMPDUFrameLengthTx,    // Length of the entire A-MPDU
          input  wire [19:0] txPCaMPDUOptFrameLength20Tx,    // Length of the entire A-MPDU
          input  wire [19:0] txPCaMPDUOptFrameLength40Tx,    // Length of the entire A-MPDU
          input  wire [19:0] txPCaMPDUOptFrameLength80Tx,    // Length of the entire A-MPDU

          //$port_g P-Table RATE Control
          input  wire  [6:0] txPCmcsIndex0ProtTx,       // MCS Index 0 of Protection frame for Transmission
          input  wire  [6:0] txPCmcsIndex0Tx,           // MCS Index 0 of PPDU for Transmission

          //$port_g H-Descriptor AMPDU with only One MPDU
          input  wire        txPCtxSingleVHTMPDU,       // Flag of single VHT MPDU

          //$port_g H-Descriptor PHY Control / P-Table MCS Information
          input  wire        txPCpreTypeProtTx,         // Preamble Type of Protection frame for Transmission
                                                    // 1'b0: SHORT
                                                    // 1'b1: LONG
          input  wire        txPCpreTypeTx,             // Preamble Type of PPDU for Transmission
                                                    // Same coding than preTypeTx
          input  wire  [8:0] txPCpartialAIDTx,          // Partial AID
          input  wire  [5:0] txPCgroupIDTx,             // Group ID
          input  wire        txPCdozeNotAllowedTx,      // TXOP PS is not allowed
          input  wire        txPCdynBWTx,               // Dynamic Bandwidth for Transmission
          input  wire        txPCuseBWSignalingTx,      // Use BW Signaling for Transmission
          input  wire        txPCsmoothingProtTx,       // Smoothing of Protection frame for Transmission
          input  wire        txPCsmoothingTx,           // Smoothing of PPDU for Transmission
          input  wire        txPCsoundingTx,            // Sounding Protection frame for Transmission
         
          //$port_g H-Descriptor MAC Control Information 1
          input  wire [15:0] txPCprotFrmDur,            // Protection Frame Duration
          input  wire        txPCwriteACK,              // Indicate SW expects the ACK frame for this frame 
                                                    // to be passed to it when received.
          input  wire        txPClowRateRetry,          // Lower Rate on Retries
          input  wire        txPClstpProt,              // L-SIG TXOP Protection for protection frame
          input  wire        txPClstp,                  // L-SIG TXOP Protection
          input  wire  [1:0] txPCexpectedAck,           // Expected Acknowledgement
                                                    // 2'b00: No acknowledgement.
                                                    // 2'b01: Normal ACK.
                                                    // 2'b10: BA.
                                                    // 2'b11: Compressed BA.
          input  wire  [2:0] txPCnavProtFrmEx,          // NAV Protection Frame Exchange
                                                    // 3'b000: No protection
                                                    // 3'b001: Self-CTS
                                                    // 3'b010: RTS/CTS with intended receiver of this PPDU
                                                    // 3'b011: RTS/CTS with QAP 
                                                    // 3'b100: STBC protection
          //$port_g H-Descriptor MAC Control Information 2
          input  wire        txPCdontGenerateMH,        // Indicates that HW should not generate the MAC Header by itself
          input  wire        txPCdontEncrypt,           // Indicates that HW should bypassed the encryption operation during tx.
          input  wire        txPCdontTouchFC,           // Indicates that HW should not update the Frame Control field,
          input  wire        txPCdontTouchDur,          // Indicates that HW should not update the Duration field
          input  wire        txPCdontTouchQoS,          // Indicates that HW should not update the QoS field 
          input  wire        txPCdontTouchHTC,          // Indicates that HW should not update the HTC field 
          input  wire        txPCdontTouchTSF,          // Indicates that HW should not update the TSF field 
          input  wire        txPCdontTouchDTIM,         // Indicates that HW should not update the DTIM Count field
          input  wire        txPCdontTouchFCS,          // Indicates that HW should not update the FCS field
          input  wire        txPCunderBASetup,          // Indicates whether BA has been setup for this MPD
          input  wire        txPCaMPDUOut,              // Indicates whether this Transmit Header Descriptor belong to an A-MPDU
          input  wire  [1:0] txPCwhichDescriptor,       // Indicates what kind of a descriptor this is
          input  wire  [9:0] txPCnBlankMDelimiters,     // Indicates the number of blank MPDU delimiters that are inserted
          input  wire        txPCinterruptEnTx,         // Interrupt Enable for Transmit DMA
          input  wire  [3:0] txPCfcSubtype,             // Indicates the fcSubtype field of the Frame Control field of the MPDU.
          input  wire  [1:0] txPCfcType,                // Indicates the fcType field of the Frame Control field of the MPDU
          input  wire        txPCtsValid,               // Indicates if the fcType and fcSubtype fields have been populated correctly

          //$port_g P-Table PHY Control Information 1
          output reg   [2:0] nTxProtPT,             // Number of Transmit Chains for Protection Frame
          output reg   [2:0] nTxPT,                 // Number of Transmit Chains for PPDU
          output reg         shortGIPT,             // Short Guard Interval for Transmission
                                                    // When High, it indicates whether a short Guard Interval
          output reg   [7:0] txPwrLevelPT,          // Transmit Power Level
          output reg   [7:0] txPwrLevelProtPT,      // Transmit Power Level for Protection Frame
          output reg   [1:0] stbcPT,                // Space Time Block Coding
          output reg         fecCodingPT,           // FEC Coding
          output reg   [1:0] numExtnSSPT,           // Number of Extension Spatial Streams
          output reg         bfFrmExPT,             // Beam Forming Frame Exchange
                                                    // 1'b0: QoS Null/ACK
                                                    // 1'b1: RTS/CTS
          //$port_g P-Table PHY Control Information 2
          output reg         beamFormedPT,          // BeamFormed frame
          output reg   [7:0] smmIndexPT,            // Spatial Map Matrix Index
          output reg   [7:0] antennaSetPT,          // Antenna Set

          //$port_g P-Table MAC Control Information 1
          output reg   [9:0] keySRAMIndex,          // Key Storage RAM Index
          output reg   [9:0] keySRAMIndexRA,        // Key Storage RAM Index for Receiver Address

          //$port_g P-Table MAC Control Information 2
          output reg  [11:0] rtsThreshold,          // RTS Threshold
          output reg   [7:0] shortRetryLimit,       // Short Retry Limit
          output reg   [7:0] longRetryLimit,        // Long Retry Limit

          //$port_g H-Descriptor PHY Control Information 
          output reg         useRIFSTx,             // Use RIFS for Transmission
          output reg         continuousTx,          // Enable continuous transmission for this frame 

          //$port_g H-Descriptor Frame Lenght
          output reg  [15:0] MPDUFrameLengthTx,     // Length of the MPDU

          //$port_g H-Descriptor Status Information
          output reg         lifetimeExpired,       // Indicates that the lifetime of this MPDU expired

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

          //$port_g H-Descriptor Status Information
          output reg   [7:0] numMPDURetries,        // Indicates the number of MPDU retries already done   
          output reg   [7:0] numRTSRetries,         // Indicates the number of RTS retries already done  
          output reg  [31:0] mediumTimeUsed,        // Indicates the medium Time Used for current TX transfer  

          //$port_g H-Descriptor Frame Lenght
          output reg  [19:0] aMPDUFrameLengthTx,    // Length of the entire A-MPDU
          output reg  [19:0] aMPDUOptFrameLength20Tx,    // Length of the entire A-MPDU
          output reg  [19:0] aMPDUOptFrameLength40Tx,    // Length of the entire A-MPDU
          output reg  [19:0] aMPDUOptFrameLength80Tx,    // Length of the entire A-MPDU

          //$port_g P-Table RATE Control
          output reg   [6:0] mcsIndex0ProtTx,       // MCS Index 0 of Protection frame for Transmission
          output reg   [6:0] mcsIndex0Tx,           // MCS Index 0 of PPDU for Transmission

          //$port_g H-Descriptor AMPDU with only One MPDU
          output reg         txSingleVHTMPDU,       // Flag of single VHT MPDU

          //$port_g H-Descriptor PHY Control / P-Table MCS Information
          output reg         preTypeProtTx,         // Preamble Type of Protection frame for Transmission
                                                    // 1'b0: SHORT
                                                    // 1'b1: LONG
          output reg         preTypeTx,             // Preamble Type of PPDU for Transmission
                                                    // Same coding than preTypeTx
          output reg   [8:0] partialAIDTx,          // Partial AID
          output reg   [5:0] groupIDTx,             // Group ID
          output reg         dozeNotAllowedTx,      // TXOP PS is not allowed
          output reg         dynBWTx,               // Dynamic Bandwidth for Transmission
          output reg         useBWSignalingTx,      // Use BW Signaling for Transmission
          output reg         smoothingProtTx,       // Smoothing of Protection frame for Transmission
          output reg         smoothingTx,           // Smoothing of PPDU for Transmission
          output reg         soundingTx,            // Sounding Protection frame for Transmission
         
          //$port_g H-Descriptor MAC Control Information 1
          output reg  [15:0] protFrmDur,            // Protection Frame Duration
          output reg         writeACK,              // Indicate SW expects the ACK frame for this frame 
                                                    // to be passed to it when received.
          output reg         lowRateRetry,          // Lower Rate on Retries
          output reg         lstpProt,              // L-SIG TXOP Protection for protection frame
          output reg         lstp,                  // L-SIG TXOP Protection
          output reg   [1:0] expectedAck,           // Expected Acknowledgement
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
          output reg         dontGenerateMH,        // Indicates that HW should not generate the MAC Header by itself
          output reg         dontEncrypt,           // Indicates that HW should bypassed the encryption operation during tx.
          output reg         dontTouchFC,           // Indicates that HW should not update the Frame Control field,
          output reg         dontTouchDur,          // Indicates that HW should not update the Duration field
          output reg         dontTouchQoS,          // Indicates that HW should not update the QoS field 
          output reg         dontTouchHTC,          // Indicates that HW should not update the HTC field 
          output reg         dontTouchTSF,          // Indicates that HW should not update the TSF field 
          output reg         dontTouchDTIM,         // Indicates that HW should not update the DTIM Count field
          output reg         dontTouchFCS,          // Indicates that HW should not update the FCS field
          output reg         underBASetup,          // Indicates whether BA has been setup for this MPD
          output reg         aMPDUOut,              // Indicates whether this Transmit Header Descriptor belong to an A-MPDU
          output reg   [1:0] whichDescriptor,       // Indicates what kind of a descriptor this is
          output reg   [9:0] nBlankMDelimiters,     // Indicates the number of blank MPDU delimiters that are inserted
          output reg         interruptEnTx,         // Interrupt Enable for Transmit DMA
          output reg   [3:0] fcSubtype,             // Indicates the fcSubtype field of the Frame Control field of the MPDU.
          output reg   [1:0] fcType,                // Indicates the fcType field of the Frame Control field of the MPDU
          output reg         tsValid,               // Indicates if the fcType and fcSubtype fields have been populated correctly





  
  ///////////////////////////////////////////////
  //$port_g Backoff Engine Interface
  /////////////////////////////////////////////// 
  input  wire         bckoffstatussetac3HasData,    // ac3 has data status
  input  wire         bckoffstatussetac2HasData,    // ac2 has data status
  input  wire         bckoffstatussetac1HasData,    // ac1 has data status
  input  wire         bckoffstatussetac0HasData,    // ac0 has data status
                      
  output wire         bckoffsetac3HasData,          // set ac3 has data
  output wire         bckoffsetac2HasData,          // set ac2 has data
  output wire         bckoffsetac1HasData,          // set ac1 has data
  output wire         bckoffsetac0HasData,          // set ac0 has data
  output wire         bckoffclearac3HasData,        // clear ac3 has data
  output wire         bckoffclearac2HasData,        // clear ac2 has data
  output wire         bckoffclearac1HasData,        // clear ac1 has data
  output wire         bckoffclearac0HasData         // clear ac0 has data
  );

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
wire        tick1usPI_p;                   // Pulse generated every us.
wire        latchNextStateCoreClk_p;       // latchNextState_p pulse synchronized to macCoreClk domain
wire        acBWDropTriggerPIClk;          // acBWDropTrigger interrupt signal synchornized to macPIClk domain

wire txParameterHDReadyInt_p;
wire txParameterPTReadyInt_p;
//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
///
/// TSF resynchronization
///
//////////////////////////////////////////////////////////////////////////////

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_tick1us_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_tick1us_p_synchro (
                .srcclk             (macCoreClk),
                .srcresetn          (macCoreClkHardRst_n),
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (tick1us_p),
                .dstdata            (tick1usPI_p)
                );

always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    tsfTimerHighIn <= 32'b0;
    tsfTimerLowIn  <= 32'b0;
  end
  else if (tick1usPI_p)
  begin
    tsfTimerHighIn <= tsfTimer[63:32];
    tsfTimerLowIn  <= tsfTimer[31:0];
  end
end

assign tsfTimerLowInValid  = tick1usPI_p;
assign tsfTimerHighInValid = tick1usPI_p;

//////////////////////////////////////////////////////////////////////////////
///
/// MAC Controller to TX Parameters Cache resyncronization
///
//////////////////////////////////////////////////////////////////////////////

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_toggleHDSet_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_toggleHDSet_p_synchro (
		.srcclk       (macCoreClk),
		.srcresetn    (macCoreClkHardRst_n),
		.dstclk       (macPITxClk),
		.dstresetn    (macPIClkHardRst_n),
		.srcdata      (toggleHDSet_p),
		.dstdata      (txPCtoggleHDSet_p)
		);

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_togglePTSet_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_togglePTSet_p_synchro (
		.srcclk       (macCoreClk),
		.srcresetn    (macCoreClkHardRst_n),
		.dstclk       (macPITxClk),
		.dstresetn    (macPIClkHardRst_n),
		.srcdata      (togglePTSet_p),
		.dstdata      (txPCtogglePTSet_p)
		);

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_clearSets_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_clearSets_p_synchro (
		.srcclk       (macCoreClk),
		.srcresetn    (macCoreClkHardRst_n),
		.dstclk       (macPITxClk),
		.dstresetn    (macPIClkHardRst_n),
		.srcdata      (clearSets_p),
		.dstdata      (txPCclearSets_p)
		);

//////////////////////////////////////////////////////////////////////////////
///
/// TX Parameters Cache to MAC Controller resyncronization
///
//////////////////////////////////////////////////////////////////////////////


// Instanciation of pulse2PulseSynchro
// Name of the instance : U_txParameterHDReady_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_txParameterHDReady_p_synchro (
		.srcclk       (macPITxClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (txPCtxParameterHDReady_p),
		.dstdata      (txParameterHDReadyInt_p)
		);

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_txPCtxParameterPTReady_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_txPCtxParameterPTReady_p_synchro (
		.srcclk       (macPITxClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (txPCtxParameterPTReady_p),
		.dstdata      (txParameterPTReadyInt_p)
		);

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_txPCtxParameterNextPTReady_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_txPCtxParameterNextPTReady_p_synchro (
		.srcclk       (macPITxClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (txPCtxParameterNextPTReady_p),
		.dstdata      (txParameterNextPTReady_p)
		);


always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    txParameterHDReady_p <= 1'b0;
    txParameterPTReady_p <= 1'b0;
  end
  else
  begin
    txParameterHDReady_p <= txParameterHDReadyInt_p;
    txParameterPTReady_p <= txParameterPTReadyInt_p;
  end
end



//////////////////////////////////////////////////////////////////////////////
///
/// CSReg to Backoff resyncronization
///
//////////////////////////////////////////////////////////////////////////////

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_setac3HasData_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_setac3HasData_synchro (
		.srcclk       (macPIClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (setac3HasData),
		.dstdata      (bckoffsetac3HasData)
		);

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_setac2HasData_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_setac2HasData_synchro (
		.srcclk       (macPIClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (setac2HasData),
		.dstdata      (bckoffsetac2HasData)
		);

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_setac1HasData_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_setac1HasData_synchro (
		.srcclk       (macPIClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (setac1HasData),
		.dstdata      (bckoffsetac1HasData)
		);

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_setac0HasData_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_setac0HasData_synchro (
		.srcclk       (macPIClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (setac0HasData),
		.dstdata      (bckoffsetac0HasData)
		);

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_clearac3HasData_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_clearac3HasData_synchro (
		.srcclk       (macPIClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (clearac3HasData),
		.dstdata      (bckoffclearac3HasData)
		);

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_clearac2HasData_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_clearac2HasData_synchro (
		.srcclk       (macPIClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (clearac2HasData),
		.dstdata      (bckoffclearac2HasData)
		);

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_clearac1HasData_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_clearac1HasData_synchro (
		.srcclk       (macPIClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (clearac1HasData),
		.dstdata      (bckoffclearac1HasData)
		);

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_clearac0HasData_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_clearac0HasData_synchro (
		.srcclk       (macPIClk),
		.srcresetn    (macPIClkHardRst_n),
		.dstclk       (macCoreClk),
		.dstresetn    (macCoreClkHardRst_n),
		.srcdata      (clearac0HasData),
		.dstdata      (bckoffclearac0HasData)
		);

// Instanciation of simpleSynchro
// Name of the instance : U_statussetac3HasData_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_statussetac3HasData_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (bckoffstatussetac3HasData),
                .dstdata            (statussetac3HasData)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_statussetac2HasData_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_statussetac2HasData_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (bckoffstatussetac2HasData),
                .dstdata            (statussetac2HasData)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_statussetac1HasData_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_statussetac1HasData_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (bckoffstatussetac1HasData),
                .dstdata            (statussetac1HasData)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_statussetac0HasData_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_statussetac0HasData_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (bckoffstatussetac0HasData),
                .dstdata            (statussetac0HasData)
                );


//////////////////////////////////////////////////////////////////////////////
///
/// CSReg to MAC Controller synchronization
///
//////////////////////////////////////////////////////////////////////////////
// Instanciation of pulse2PulseSynchro
// Name of the instance : U_latchNextStatePlClk_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_latchNextStatePlClk_p_synchro (
                .srcclk       (macPIClk),
                .srcresetn    (macPIClkHardRst_n),
                .dstclk       (macCoreClk),
                .dstresetn    (macCoreClkHardRst_n),
                .srcdata      (latchNextStatePlClk_p),
                .dstdata      (latchNextStateCoreClk_p)
                );

//Registering the nextState signals in macCore Clock domain.
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    nextStateCoreClkReg <= 0;
  else if (macCoreClkSoftRst_n == 1'b0)
    nextStateCoreClkReg <= 0;
  else if (latchNextStateCoreClk_p)
    nextStateCoreClkReg <= nextStatePlClkReg; 
end

//////////////////////////////////////////////////////////////////////////////
///
///  MAC Controller to CSReg synchronization
///
//////////////////////////////////////////////////////////////////////////////
// Instanciation of pulse2PulseSynchro
// Name of the instance : U_acBWDropTrigger_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_acBWDropTrigger_synchro (
                .srcclk       (macCoreClk),
                .srcresetn    (macCoreClkHardRst_n),
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (acBWDropTrigger),
                .dstdata      (acBWDropTriggerPIClk)
                );

//Registering the txBWAfterDrop signals in macPI Clock domain.
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
    txBWAfterDropResync <= 2'b0;
  else if (acBWDropTriggerPIClk)
    txBWAfterDropResync <= txBWAfterDrop; 
end


always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    nTxProtPT <= 3'd0;             // Number of Transmit Chains for Protection Frame
    nTxPT     <= 3'd0;                 // Number of Transmit Chains for PPDU
    shortGIPT <= 1'd0;             // Short Guard Interval for Transmission
    txPwrLevelPT <= 8'd0;          // Transmit Power Level
    txPwrLevelProtPT <= 8'd0;          // Transmit Power Level for Protection Frame
    stbcPT       <= 2'd0;                // Space Time Block Coding
    fecCodingPT  <= 1'd0;           // FEC Coding
    numExtnSSPT  <= 2'd0;           // Number of Extension Spatial Streams
    bfFrmExPT    <= 1'd0;             // Beam Forming Frame Exchange
    beamFormedPT <= 1'd0;          // BeamFormed frame
    smmIndexPT   <= 8'd0;            // Spatial Map Matrix Index
    antennaSetPT <= 8'd0;          // Antenna Set
    keySRAMIndex <= 10'd0;          // Key Storage RAM Index
    keySRAMIndexRA <= 10'd0;        // Key Storage RAM Index for Receiver Address
    rtsThreshold <= 12'd0;          // RTS Threshold
    shortRetryLimit <= 8'd0;       // Short Retry Limit
    longRetryLimit <= 8'd0;        // Long Retry Limit
    useRIFSTx <= 1'd0;             // Use RIFS for Transmission
    continuousTx <= 1'd0;          // Enable continuous transmission for this frame 
    MPDUFrameLengthTx <= 16'd0;     // Length of the MPDU
    lifetimeExpired <= 1'd0;       // Indicates that the lifetime of this MPDU expired
    formatModProtTx <= 3'd0;       // Format and Modulation of Protection frame for Transmission
    formatModTx <= 3'd0;           // Format and Modulation of PPDU for Transmission
    bwProtTx <= 2'd0;              // Band Width of Protection frame for Transmission
    bwTx <= 2'd0;                  // Band Width of PPDU for Transmission
    numMPDURetries <= 8'd0;        // Indicates the number of MPDU retries already done   
    numRTSRetries <= 8'd0;         // Indicates the number of RTS retries already done  
    aMPDUFrameLengthTx <= 20'd0;    // Length of the entire A-MPDU
    aMPDUOptFrameLength20Tx <= 20'd0;    // Length of the entire A-MPDU
    aMPDUOptFrameLength40Tx <= 20'd0;    // Length of the entire A-MPDU
    aMPDUOptFrameLength80Tx <= 20'd0;    // Length of the entire A-MPDU
    mcsIndex0ProtTx <= 7'd0;       // MCS Index 0 of Protection frame for Transmission
    mcsIndex0Tx <= 7'd0;           // MCS Index 0 of PPDU for Transmission
    txSingleVHTMPDU <= 1'd0;       // Flag of single VHT MPDU
    preTypeProtTx <= 1'd0;         // Preamble Type of Protection frame for Transmission
    preTypeTx <= 1'd0;             // Preamble Type of PPDU for Transmission
    partialAIDTx <= 9'd0;          // Partial AID
    groupIDTx <= 6'd0;             // Group ID
    dozeNotAllowedTx <= 1'd0;      // TXOP PS is not allowed
    dynBWTx <= 1'd0;               // Dynamic Bandwidth for Transmission
    useBWSignalingTx <= 1'd0;      // Use BW Signaling for Transmission
    smoothingProtTx <= 1'd0;       // Smoothing of Protection frame for Transmission
    smoothingTx <= 1'd0;           // Smoothing of PPDU for Transmission
    soundingTx <= 1'd0;            // Sounding Protection frame for Transmission
    protFrmDur <= 16'd0;            // Protection Frame Duration
    writeACK <= 1'd0;              // Indicate SW expects the ACK frame for this frame 
    lowRateRetry <= 1'd0;          // Lower Rate on Retries
    lstpProt <= 1'd0;              // L-SIG TXOP Protection for protection frame
    lstp <= 1'd0;                  // L-SIG TXOP Protection
    expectedAck <= 2'd0;           // Expected Acknowledgement
    navProtFrmEx <= 3'd0;          // NAV Protection Frame Exchange
    dontGenerateMH <= 1'd0;        // Indicates that HW should not generate the MAC Header by itself
    dontEncrypt <= 1'd0;           // Indicates that HW should bypassed the encryption operation during tx.
    dontTouchFC <= 1'd0;           // Indicates that HW should not update the Frame Control field;
    dontTouchDur <= 1'd0;          // Indicates that HW should not update the Duration field
    dontTouchQoS <= 1'd0;          // Indicates that HW should not update the QoS field 
    dontTouchHTC <= 1'd0;          // Indicates that HW should not update the HTC field 
    dontTouchTSF <= 1'd0;          // Indicates that HW should not update the TSF field 
    dontTouchDTIM <= 1'd0;         // Indicates that HW should not update the DTIM Count field
    dontTouchFCS <= 1'd0;          // Indicates that HW should not update the FCS field
    underBASetup <= 1'd0;          // Indicates whether BA has been setup for this MPD
    aMPDUOut <= 1'd0;              // Indicates whether this Transmit Header Descriptor belong to an A-MPDU
    whichDescriptor <= 2'd0;       // Indicates what kind of a descriptor this is
    nBlankMDelimiters <= 10'd0;     // Indicates the number of blank MPDU delimiters that are inserted
    interruptEnTx <= 1'd0;         // Interrupt Enable for Transmit DMA
    fcSubtype <= 4'd0;             // Indicates the fcSubtype field of the Frame Control field of the MPDU.
    fcType <= 2'd0;                // Indicates the fcType field of the Frame Control field of the MPDU
    tsValid <= 1'd0;               // Indicates if the fcType and fcSubtype fields have been populated correctly
  end
  else 
  begin
    if (txParameterPTReadyInt_p)
    begin
      nTxProtPT <= txPCnTxProtPT;
      nTxPT <= txPCnTxPT;
      shortGIPT <= txPCshortGIPT;
      txPwrLevelPT <= txPCtxPwrLevelPT;
      txPwrLevelProtPT <= txPCtxPwrLevelProtPT;
      stbcPT <= txPCstbcPT;
      fecCodingPT <= txPCfecCodingPT;
      numExtnSSPT <= txPCnumExtnSSPT;
      bfFrmExPT <= txPCbfFrmExPT;
      beamFormedPT <= txPCbeamFormedPT;
      smmIndexPT <= txPCsmmIndexPT;
      antennaSetPT <= txPCantennaSetPT;
      keySRAMIndex <= txPCkeySRAMIndex;
      keySRAMIndexRA <= txPCkeySRAMIndexRA;
      rtsThreshold <= txPCrtsThreshold;
      shortRetryLimit <= txPCshortRetryLimit;
      longRetryLimit <= txPClongRetryLimit;
  
      formatModProtTx <= txPCformatModProtTx;
      formatModTx <= txPCformatModTx;
      bwProtTx <= txPCbwProtTx;
      bwTx <= txPCbwTx;
      mcsIndex0ProtTx <= txPCmcsIndex0ProtTx;
      mcsIndex0Tx <= txPCmcsIndex0Tx;
      preTypeProtTx <= txPCpreTypeProtTx;
      preTypeTx <= txPCpreTypeTx;
      navProtFrmEx <= txPCnavProtFrmEx;
      aMPDUOut <= txPCaMPDUOut;
      txSingleVHTMPDU <= txPCtxSingleVHTMPDU;
      aMPDUFrameLengthTx <= txPCaMPDUFrameLengthTx;
      aMPDUOptFrameLength20Tx <= txPCaMPDUOptFrameLength20Tx;
      aMPDUOptFrameLength40Tx <= txPCaMPDUOptFrameLength40Tx;
      aMPDUOptFrameLength80Tx <= txPCaMPDUOptFrameLength80Tx;
      
    end
    if (txParameterHDReadyInt_p)
    begin
      useRIFSTx <= txPCuseRIFSTx;
      continuousTx <= txPCcontinuousTx;
      MPDUFrameLengthTx <= txPCMPDUFrameLengthTx;
      lifetimeExpired <= txPClifetimeExpired;
      numMPDURetries <= txPCnumMPDURetries;
      numRTSRetries <= txPCnumRTSRetries;
      mediumTimeUsed <= txPCmediumTimeUsed;
      aMPDUFrameLengthTx <= txPCaMPDUFrameLengthTx;
      aMPDUOptFrameLength20Tx <= txPCaMPDUOptFrameLength20Tx;
      aMPDUOptFrameLength40Tx <= txPCaMPDUOptFrameLength40Tx;
      aMPDUOptFrameLength80Tx <= txPCaMPDUOptFrameLength80Tx;

      partialAIDTx <= txPCpartialAIDTx;
      groupIDTx <= txPCgroupIDTx;
      dozeNotAllowedTx <= txPCdozeNotAllowedTx;
      dynBWTx <= txPCdynBWTx;
      useBWSignalingTx <= txPCuseBWSignalingTx;
      smoothingProtTx <= txPCsmoothingProtTx;
      smoothingTx <= txPCsmoothingTx;
      soundingTx <= txPCsoundingTx;
      protFrmDur <= txPCprotFrmDur;
      writeACK <= txPCwriteACK;
      lowRateRetry <= txPClowRateRetry;
      lstpProt <= txPClstpProt;
      lstp <= txPClstp;
      expectedAck <= txPCexpectedAck;
      dontGenerateMH <= txPCdontGenerateMH;
      dontEncrypt <= txPCdontEncrypt;
      dontTouchFC <= txPCdontTouchFC;
      dontTouchDur <= txPCdontTouchDur;
      dontTouchQoS <= txPCdontTouchQoS;
      dontTouchHTC <= txPCdontTouchHTC;
      dontTouchTSF <= txPCdontTouchTSF;
      dontTouchDTIM <= txPCdontTouchDTIM;
      dontTouchFCS <= txPCdontTouchFCS;
      underBASetup <= txPCunderBASetup;
      aMPDUOut <= txPCaMPDUOut;
      txSingleVHTMPDU <= txPCtxSingleVHTMPDU;
      whichDescriptor <= txPCwhichDescriptor;
      nBlankMDelimiters <= txPCnBlankMDelimiters;
      interruptEnTx <= txPCinterruptEnTx;
      fcSubtype <= txPCfcSubtype;
      fcType <= txPCfcType;
      tsValid <= txPCtsValid;
    end
  end
end  
endmodule
