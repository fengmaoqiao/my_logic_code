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
// Description      : MAC Controller TX Frame Exchange managemement
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
//
//   A false path should be defined bewteen numMPDURetries and macPIClk
//   A false path should be defined bewteen numRTSRetries  and macPIClk
//   As per design, these signals are static when the DMA Engine capture them.
//
// Application Note :                                                       
// Simulator        :                                                       
// Parameters       :                                                       
// Terms & concepts :                                                       
// Bugs             :                                                       
// Open issues and future enhancements :
// $todo STBC support                                    
// $todo 20/40MHz                               
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////


module macControllerTx (          
          //$port_g Clock and Reset interface
          input  wire        macCoreClk,             // MAC Core Clock
          input  wire        macCoreClkHardRst_n,    // Hard Reset of the MAC Core Clock domain 
                                                     // active low
          input  wire        macCoreClkSoftRst_n,    // Soft Reset of the MAC Core Clock domain 
          output wire        macCoreTxClkEnTxC,      // Enable TX Clocks
          
          //$port_g MAC Controller Master interface
          input  wire        txExchangeEnabled,      // Enables the TX frame exchange
          output wire        txExchangeCompleted_p,  // When the completion of a RX frame exchange
          output wire        mpifKeepRFonTx,         // Keep the RF On
          output wire        txRxnTxC,               // Indicates the mode between TX and Rx
                                                     //   0 : RX
                                                     //   1 : TX
          
          input  wire  [1:0] availableBW,            // Bandwidth available before the current transmission.

          //$port_g  MAC Controller Rate Selection interface
          input  wire  [6:0] mcsData,                // MCS Index for frame
          input  wire  [3:0] legRateData,            // Legacy Rate Index for Data frame
          input  wire  [6:0] mcsCFEND,               // MCS Index for CF-END
          input  wire  [3:0] legRateCFEND,           // Legacy Rate Index for CF-END
          input  wire  [6:0] mcsPROT,                // MCS Index for PROT frame
          input  wire  [3:0] legRatePROT,            // Legacy Rate Index for Data frame
          input  wire  [6:0] mcsRESP,                // MCS Index for response frame
          input  wire  [3:0] legRateRESP,            // Legacy Rate Index for response frame
          output wire        rateUpdateTxC_p,        // Request from the macControllerTx to update the rate
          output wire  [6:0] mcsIndex0Prot,          // MCS Index 0 of Protection frame for Transmission
          output wire  [1:0] bwDataTx,               // BW of PPDU for Transmission
          output wire  [1:0] stbcTx,                 // STBC for Transmission

          //$port_g Rx Controller interface
          output wire        rxAck,                  // Force receive only BA or ACK after Tx
          output wire        rxBA,                   // Force receive only BA after Tx
          output wire        rxCts,                  // Force receive only CTS after RTS Tx
          output wire        forceWriteACK,          // Force the RX to pass the ACK to the Softwrae
          
          input  wire        ackRcved_p,             // ACK received
          input  wire        rtsRcved_p,             // RTS received
          input  wire        ctsRcved_p,             // CTS received
          input  wire        cfEndRcved_p,           // CF-End received
          input  wire        baRcved_p,              // BA received 
          input  wire        barRcved_p,             // BAR received
          input  wire        needAckRcved_p,         // Data or management received with ACK needed
          input  wire        bcMcRcved_p,            // Broadcast/Multicast
          input  wire        bcnRcved_p,             // Beacon received
          input  wire        notMineRcved_p,         // Frame received but not mine
          input  wire        unknownRcved_p,         // Unknown frame received
          input  wire [47:0] rxAddr2,                // Receiver addr
          input  wire [15:0] rxFrameDuration,        // Frame duration

          input  wire        incorrectRcved_p,       // Frame not received correctly
          input  wire        correctRcved_p,         // Frame received correctly

          input  wire        rxCsIsIdle,             // Rx Controller is in idle state

          //$port_g Deaggregator interface
          input  wire  [1:0] rxChBW,                 // Bandwidth of received frame
          input  wire  [1:0] rxChBWInNonHT,          // Channel bandwidth in Non-HT extracted from the scrambler initialization sequence
          input  wire        ampduCorrectRcved_p,    // A-MPDU received correctly
          input  wire        ampduIncorrectRcved_p,  // A-MPDU not received correctly
          input  wire        rxEndOfFrame_p,         // Rx vector 2 is available

          output wire        startRxTxC_p,           // Start Rx
          output wire        stopRxTxC_p,            // Stop Rx

          //$port_g Tx Controller interface
          output reg         sendData_p,             // Indicates that data packet has to be sent
          output reg         sendRTS_p,              // Indicates that an RTS packet has to be sent
          output reg         sendCTSTxC_p,           // Indicates that a CTS packet has to be sent
          output reg         sendCFENDTxC_p,         // Indicates that a CF-END packet has to be sent
          output reg         sendOnSIFSTxC,          // If set, data is sent on tickSIFS else on tickSlot
          output wire        sendOnPIFSTxC,          // If set, data is sent on tickPIFS
          output reg         skipMPDU_p,             // Indication that MPDU in TX FIFO has to be discarded

          output wire [47:0] srcAddrTxC,             // Source address
          output reg  [47:0] destAddrTxC,            // Receiver address
          output reg  [15:0] durationTxC,            // Duration
          output wire        retry,                  // Indicates that the trame is a retry.
          output reg   [6:0] txMCSTxC,               // MCS (Only used for HT frame)
          output reg  [11:0] txLegLengthTxC,         // Legacy Length of the PPDU         
          output reg   [3:0] txLegRateTxC,           // Legacy Rate of the PPDU.         
          output reg   [1:0] txSTBCTxC,              // Transmit a Frame with Space Time Block Coding
          output reg   [1:0] txChBWTxC,              // Channel Bandwidth
          output reg         txDisambiguityBitTxC,   // Transmit a Frame with disambiguityBit
          output wire        txDynBWTxC,             // Transmission with Dynamic BW
          output wire        txBWSignalingTxC,       // Transmission with BW Signaling

          output reg  [19:0] txHTLengthTxC,          // Length of the HT PPDU
          output wire        txFecCoding,            // Transmit a frame with FEC Coding       
          output wire        txShortGI,              // Transmit a frame with Short GI
          output reg  [15:0] tsfDuration,            // Duration from the preamble until the first bit of TSF
          
          output wire        txFromReg,              // Transmit a HW generated frame based on Register
          output wire        txFromHD,               // Transmit a HW generated frame based on THD
          output wire        txFromFifo,             // Transmit a Frame from Tx FIFO
          output wire        txCFEND,                // Transmit a HW generated CFEND frame
          input  wire        txDone_p,               // Indicates that the transmission is completed
          input  wire        sentCFEND,              // Indicates that the transmitted frame is a CF-END
          input  wire        sentRTS,                // Indicates that the transmitted frame is a RTS
          input  wire        sentBAReq,              // Indicates that the transmitted frame is a BA-Request
          input  wire        startTx_p,              // Start Tx trigger                 
          input  wire        mpduDone_p,             // Indicates that the MPDU has been sent
          input  wire        skipMPDUDone_p,         // Indicates that MPDU contained in the TXFIFO has been discarded.

          //$port_g Interface with the Tx Parameters Cache
          output wire        toggleHDSet_p,          // Indicates that the Header Descriptor Set can be toggled
          output wire        togglePTSet_p,          // Indicates that the Policy Table Set can be toggled
          output wire        clearSetsTxC_p,         // Indicates that the Sets have to be cleared.
          input  wire        clearSets_p,            // loopback of clearSetsTxC_p || (macPhyIfRxCca && !txExchangeEnabled)
          input  wire        txParameterHDReady_p,     // Indicates that the Header Descriptor fields are usable 
          input  wire        txParameterPTReady_p,     // Indicates that the Policy Table fields are usable
          input  wire        txParameterNextPTReady_p, // Indicates that a second policy table has already been loaded
          input  wire [15:0] protFrmDur,             // Protection Frame Duration
          input  wire        writeACK,               // Indicates SW expects the ACK frame for this frame 
                                                     // to be passed to it when received.
          input  wire        lowRateRetry,           // Lower Rate on Retries
          input  wire        lstpProt,               // L-SIG TXOP Protection for protection frame
          input  wire        lstp,                   // L-SIG TXOP Protection
          input  wire        dontTouchDur,           // Indicates that HW should not update the Duration field
          input  wire  [1:0] expectedAck,            // Expected Acknowledgement
                                                     //   2'b00: No acknowledgement.
                                                     //   2'b01: Normal ACK.
                                                     //   2'b10: BA.
                                                     //   2'b11: Compressed BA.
          input  wire  [2:0] navProtFrmEx,           // NAV Protection Frame Exchange
                                                     //   3'b000: No protection
                                                     //   3'b001: Self-CTS
                                                     //   3'b010: RTS/CTS with intended receiver of this PPDU
                                                     //   3'b011: RTS/CTS with QAP 
                                                     //   3'b100: STBC protection
          input  wire        useRIFSTx,              // Use RIFS for Transmission
          input  wire        preTypeProtTx,          // Preamble Type of Protection frame for Transmission
                                                     //   1'b0: SHORT
                                                     //   1'b1: LONG
          input  wire        preTypeTx,              // Preamble Type of PPDU for Transmission
                                                     // Same coding than preTypeTx
          input  wire        dynBWTx,               // Dynamic Bandwidth for Transmission
          input  wire        useBWSignalingTx,      // Use BW Signaling for Transmission
          input  wire        smoothingProtTx,        // Smoothing of Protection frame for Transmission
          input  wire        smoothingTx,            // Smoothing of PPDU for Transmission
          input  wire        soundingTx,             // Sounding Protection frame for Transmission
          input  wire  [2:0] nTxProtPT,              // Number of Transmit Chains for Protection Frame
          input  wire  [2:0] nTxPT,                  // Number of Transmit Chains for PPDU
          input  wire        shortGIPT,              // Short Guard Interval for Transmission
                                                     // When High, it indicates whether a short Guard Interval
          input  wire        fecCodingPT,            // FEC Coding
          input  wire  [1:0] stbcPT,                 // Space Time Block Coding
          input  wire  [1:0] numExtnSSPT,            // Number of Extension Spatial Streams
          input  wire  [7:0] smmIndexPT,             // Spatial Map Matrix Index
          input  wire  [9:0] keySRAMIndex,           // Key Storage RAM Index
          input  wire  [9:0] keySRAMIndexRA,         // Key Storage RAM Index for Receiver Address
          input  wire        aMPDU,                  // Indicates whether this Transmit Header Descriptor belong to an A-MPDU
          input  wire        txSingleVHTMPDU,        // Flag of single VHT MPDU
          input  wire  [1:0] whichDescriptor,        // Indicates what kind of a descriptor this is
          input  wire  [3:0] fcSubtype,              // Indicates the fcSubtype field of the Frame Control field of the MPDU.
          input  wire  [1:0] fcType,                 // Indicates the fcType field of the Frame Control field of the MPDU
          input  wire        tsValid,                // Indicates if the fcType and fcSubtype fields have been populated correctly

          input  wire [11:0] rtsThreshold,           // RTS Threshold
          input  wire  [7:0] shortRetryLimit,        // Short Retry Limit
          input  wire  [7:0] longRetryLimit,         // Long Retry Limit

          input  wire [15:0] MPDUFrameLengthTx,      // Length of the MPDU

          input  wire  [2:0] formatModProtTx,        // Format and Modulation of Protection frame for Transmission
                                                     //   3'b000: NON-HT
                                                     //   3'b001: NON-HT-DUP-OFDM
                                                     //   3'b010: HT-MF
                                                     //   3'b011: HT-GF
                                                     //   3'b100: VHT
          input  wire  [2:0] formatModTx,            // Format and Modulation of PPDU for Transmission
                                                     // Same coding than formatModProtTx
          input  wire  [1:0] bwProtTx,               // Band Width of Protection frame for Transmission
          input  wire  [1:0] bwTx,                   // Band Width of PPDU for Transmission
          input  wire  [7:0] numMPDURetriesTPC,      // Indicates the number of MPDU retries already done   
          input  wire  [7:0] numRTSRetriesTPC,       // Indicates the number of RTS retries already done  
          input  wire [19:0] aMPDUFrameLengthTx,     // Length of the entire A-MPDU
          input  wire [19:0] aMPDUOptFrameLength20Tx,// Length of the entire A-MPDU BW drop 20Mhz
          input  wire [19:0] aMPDUOptFrameLength40Tx,// Length of the entire A-MPDU BW drop 40Mhz
          input  wire [19:0] aMPDUOptFrameLength80Tx,// Length of the entire A-MPDU BW drop 80Mhz
          input  wire  [6:0] mcsIndex0ProtTx,        // MCS Index 0 of Protection frame for Transmission
          input  wire  [6:0] mcsIndex0Tx,            // MCS Index 0 of PPDU for Transmission
          
          input  wire [31:0] mediumTimeUsedTPC,      // Medium Time Used for current TX transfer

          //$port_g Interface with the Key Search Engine
          input  wire [47:0] macAddressKSR,          // MAC Addr returned by Key Search Engine
          output wire        txKeySearchIndexTrig_p, // Trigs the Key Search Engine for a Key Research based on index.
          output reg   [9:0] txKeySearchIndex,       // Key Index used by the Key Search Engine for Research based on index.

          //$port_g Interface with the DMA Engine
          input  wire        statusUpdated_p,        // Indication from the DMA that status have been updated.
          output reg         updateDMAStatus_p,      // trigs the DMA Status update.
          output reg         swRTS_p,                // Asserted high if the current transmitted packet is a
                                                     // RTS frame prepared by SW
          output wire        txMpduDone_p,           // Asserted high after every transmission of MPDU in an 
                                                     // AMPDU frame
          output reg         ampduFrm_p,             // Asserted high if the transmitted packet was an AMPDU
                                                     // frame
          output reg         retryFrame_p,           // If the transmitted frame has to be retried then this
                                                     // signal is asserted.
          output reg         mpduSuccess_p,          // If the transmitted frame was successful. Not asserted
                                                     // for RTS frames
          output reg         mpduFailed_p,           // If the transmitted frame was not successful. Not asserted
                                                     // if the RTS frame failed
          output reg         rtsFailed_p,            // If the transmitted frame was a RTS frame and did not 
                                                     // receive a CTS frame within the CTS timeout
          output reg         rtsSuccess_p,           // If the transmitted frame was a RTS frame and successfully
                                                     // received a CTS in reponse.
          output reg         retryLimitReached_p,    // If the transmitted frame was not successful and has reached  
                                                     // the retry limit.Is asserted for both RTS and other MPDU's    
          
          output reg  [ 1:0] transmissionBW,         // Indicates whether the frame was transmitted with 20MHz, 40Mhz, 80MHz or 160MHz BW
          output reg  [ 3:0] whichDescriptorSW,      // Indicates the value of the partAMorMSDU field Controller
          output reg  [ 7:0] numRTSRetries,          // Updated value of the number of retries for this RTS. Valid when 
                                                     // rtsFailed_p rtsSuccess_p mpduSuccess_p mpduFailed_p or 
                                                     // retryLimitReached 
          output reg  [ 7:0] numMPDURetries,         // Updated value of the number of retries for this MPDU. Valid when 
                                                     // rtsFailed_p rtsSuccess_p mpduSuccess_p mpduFailed_p or 
                                                     // retryLimitReached 
                                                     
          output reg  [31:0] mediumTimeUsed,          // Updated value of medium time used for this MPDU or A-MPDU.

          //$port_g BackOff and AC Selection Module interface
          
          input  wire  [3:0] txDmaState,             // DMA state for the active channel.
          input  wire [15:0] txOpLimit,              // TXOP Limit of the active channel.
          input  wire        trigTxBcn,              // Trigger from the MAC Controller to indicate DMA to run use the Beacon Queue
          output wire [15:0] acMOT,                  // Current AC Medium Occupancy timer
          output wire        retryType,              // Indicates the type of retry
                                                     //   0 : Short Retry Limit
                                                     //   1 : Long Retry Limit
          output reg         retry_p,                // Indicates that the current frame has to be retried
          output reg         retryLTReached_p,       // Indicates that the retry limit has been reached
          output reg         txSuccessful_p,         // Indicates that the current frame has be correctly transmitted
          output wire        endOfTxOp,              // Indicates the end of the TX OP.

          //$port_g Timers Module interface
          input  wire        tick1us_p,              // Pulse generated every us.
          input  wire [15:0] impQICnt,               // Quiet interval counter in 32 us
          input  wire        sec20ChannelIdleFlag,   // Secondary 20MHz channel idle for PIFS flag
          input  wire        sec40ChannelIdleFlag,   // Secondary 40MHz channel idle for PIFS flag
          input  wire        sec80ChannelIdleFlag,   // Secondary 80MHz channel idle for PIFS flag
          input  wire  [7:0] sifsRemaining,          // us remaining before tick sifs pulse
          output reg         respTO_p,               // Indicates that the Time Out Counter has expired.

          //$port_g TXTIME calculator interface
          input  wire [15:0] timeOnAirMC,            // Time On Air result to MAC Controller
                                                     // This field gives the time taken for frame transmission in microseconds (us)
                                                     // computed from parameters given by the MAC Controller.
          input  wire        timeOnAirValidMC,       // Time On Air Valid to MAC Controller
                                                     // This field is set when the air time computation is completed.
          input  wire        disambiguityMC,         // Value of the disambiguityBit in case of VHT frame with shortGI computed by the TxTimeCalculator

          output reg   [1:0] ppduBWMCTx,             // PPDU Bandwidth from MAC Controller
                                                     // This field indicates that that the PPDU should be transmitted at 40 MHz.
          output reg   [2:0] ppduPreTypeMCTx,        // PPDU Preamble Type from MAC Controller
                                                     // This field indicates what type of preamble is transmitted for the frame.
                                                     // The encoding is as follows:
                                                     //   3'b000: Non-HT-Short
                                                     //   3'b001: Non-HT-Long
                                                     //   3'b010: HT-MF
                                                     //   3'b011: HT-GF
                                                     //   3'b100: VHT
          output reg  [19:0] ppduLengthMCTx,         // PPDU Length from MAC Controller
                                                     // This field gives the length of the PPDU for computing time on air.
          output reg   [6:0] ppduMCSIndexMCTx,       // PPDU LegRate or MCS Index from MAC Controller
                                                     // This field indicates the rate at which this PPDU is transmitted. 
          output wire  [1:0] ppduNumExtnSSMCTx,      // Number of Extension Spatial Streams      
          output wire  [1:0] ppduSTBCMCTx,           // Enable Space Time Block Coding          
          output reg         ppduShortGIMCTx,        // PPDU Short Guard Interval from MAC Controller
                                                     // Indicates that the frame should be transmitted with Short GI.
          output reg         startComputationMCTx_p, // Start Time on Air computation from MAC Controller
          
          //$port_g MAC PHY interface
          input  wire        mpIfTxErr_p,            // Tx error from MAC-PHY if. resynchronized
          input  wire        macPhyIfRxStart_p,      // Start of reception pulse
          input  wire        macPhyIfRxErr_p,        // Rx error from MAC-PHY if. resynchronized
          input  wire        macPhyIfRxEnd_p,        // Indicate the macPhy if is idle
          input  wire        macPHYIFUnderRun,       // Underrun from MAC-PHY if.

          //$port_g Interrupt Controller interface
          output reg         txopComplete,           // Indicates the completion of a TXOP
          output reg         acBWDropTrigger,        // Indicates BW drop with AMPDU length change
          
          //$port_g HW Error detected
          input  wire        hwErr,                  // HW error detected

        `ifdef RW_MAC_MIBCNTL_EN
          //$port_g MIB interface
          output wire        mibrw20MHzFailedTXOPCount,     // Counts the number of attempts made to acquire a 20 MHz TXOP.
          output wire        mibrw20MHzSuccessfulTXOPCount, // Counts the number of successful 20 MHz TXOPs.
          output wire        mibrw40MHzFailedTXOPCount,     // Counts the number of attempts made to acquire a 40 MHz TXOP.
          output wire        mibrw40MHzSuccessfulTXOPCount, // Counts the number of successful 40 MHz TXOPs.
          output wire        mibrw80MHzFailedTXOPCount,     // Counts the number of attempts made to acquire a 80 MHz TXOP.
          output wire        mibrw80MHzSuccessfulTXOPCount, // Counts the number of successful 80 MHz TXOPs.
          output wire        mibrw160MHzFailedTXOPCount,    // Counts the number of attempts made to acquire a 160 MHz TXOP.
          output wire        mibrw160MHzSuccessfulTXOPCount,// Counts the number of successful 160 MHz TXOPs.
          output wire        mibrwDynBWDropCount,      // Count the number of BW drop using dynamic BW management.
          output wire        mibrwStaBWFailedCount,    // Count the number of failure using static BW management.
        `endif // RW_MAC_MIBCNTL_EN

          //$port_g CSReg interface
          output reg   [4:0] macControllerTxFSMCs,   // State of the MAC Controller TX FSM     
          input  wire [47:0] macAddr,                // MAC Addr
          input  wire [47:0] bssID,                  // BSSID
          input  wire  [7:0] sifsDuration,           // Provide SIFS duration in us
          input  wire  [7:0] sifsA,                  // Provide SIFS A duration in us
          input  wire  [7:0] sifsB,                  // Provide SIFS B duration in us
          input  wire  [7:0] slotTime,               // Provide Slot duration in us
          input  wire  [7:0] rxStartDelayMIMO,       // Receive Start Delay for MIMO
          input  wire  [7:0] rxStartDelayShort,      // Receive Start Delay for DSSS/CCK Short preamble
          input  wire  [7:0] rxStartDelayLong,       // Receive Start Delay for DSSS/CCK Long preamble
          input  wire  [7:0] rxStartDelayOFDM,       // Receive Start Delay for OFDM
          input  wire        ap,                     // Indicates the type of device (0: STA, 1: AP)
          input  wire        startTxFrameExGated,    // Start Transmission from register gated (set only when the startTxAC won the medium) 
          output wire        startTxFrameExIn,       // Clear the start Transmission with Frame Exchange
          output wire        startTxFrameExInValid,  // Clear the start Transmission with Frame Exchange
          input  wire  [1:0] startTxFrmExType,       // Start Transmission with Frame Exchange Type
                                                     //   2'b00: self-CTS
                                                     //   2'b01: RTS/CTS with MAC address determined from startTxKSRIndex field
                                                     //   2'b10: RTS/CTS with AP
                                                     //   2'b11: RTS/Dual-CTS with AP as a non-AP STA
                                                     //   2'b11: CTS with MAC address determined from startTxKSRIndex field as AP
          input  wire  [9:0] startTxKSRIndex,        // Start Transmission with Key Storage RAM Index
          input  wire  [7:0] startTxMCSIndex0,       // Start Transmission with MCS Index 0
          input  wire  [2:0] startTxFormatMod,       // Start Transmission with Format and Modulation
          input  wire        startTxPreType,         // Start Transmission with preample Type
                                                     //   1'b0: SHORT
                                                     //   1'b1: LONG
          input  wire  [1:0] startTxBW,              // Start Transmission with Bandwidth
          input  wire [15:0] durControlFrm,          // Start Transmission with duration Control Frame
          input  wire  [1:0] startTxNumExtnSS,       // Start Transmission with Number of Extension Spacial Stream
          input  wire  [1:0] startTxSTBC,            // Start Transmission with Space Time Block Coding
          input  wire        startTxLSTP,            // Start Transmission with L-SIG TXOP
          input  wire        startTxShortGI,         // Start Transmission with short GI
          input  wire        startTxFecCoding,       // Start Transmission with FEC Coding

          input  wire        dynBWEn,                // Enable dynamic Bandwidth support
          input  wire        dropToLowerBW,          // Drop To Lower Bandwidth
          input  wire  [2:0] numTryBWAcquisition,    // Number of Tries for 40/80/160MHz TXOP Acquisition
          input  wire  [1:0] defaultBWTXOP,          // Indicates the default bandwidth for TXOP acquisition
          input  wire        defaultBWTXOPV,         // Indicates if the defaultBWTXOP setting is valid.
          input  wire  [7:0] aPPDUMaxTime,           // aPPDU Maximum Time on Air
          output  reg  [1:0] txBWAfterDrop,          // Transmission bandwidth after BW Drop
          

          input  wire        keepTXOPOpen,           // Keep TXOP Open
          input  wire        remTXOPInDurField,      // Remaining TXOP Indicated in Duration Field
          input  wire        sendCFEnd,              // Send CF-End
          input  wire        sendCFEndNow,           // Send CF-End Now
          output wire        sendCFEndNowInValid,    // Indicates that the sendCFEndNow register has to be updated with sendCFEndNowIn
          output wire        sendCFEndNowIn,         // Give the update value of sendCFEndNow

          //$port_g Debug interface
          output wire  [6:0] debugPortAMPDUMC,
          output wire [15:0] debugPortMACControllerTx// DebugPort of the MAC Controller Tx
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

// macControllerTxFSM FSM states definition
//$fsm_sd macControllerTxFSM
localparam 
                 IDLE  =  5'd0,  
             WAIT_DMA  =  5'd1,  
        COMP_DURATION  =  5'd2,  
           CHECK_TXOP  =  5'd3,  
            PHY_ERROR  =  5'd4,  
              TX_PROT  =  5'd5,  
         RX_PROT_RESP  =  5'd6,  
WAIT_RX_PROT_RESP_END  =  5'd7,  
              TX_DATA  =  5'd8,  
              RX_RESP  =  5'd9,  
     WAIT_RX_RESP_END  =  5'd10, 
        STATUS_UPDATE  =  5'd11, 
          CHECK_CFEND  =  5'd12, 
             TX_CFEND  =  5'd13 ,
         TRIG_BACKOFF  =  5'd14 ,
            SKIP_MPDU  =  5'd15, 
 DROPBW_LENGTH_UPDATE  =  5'd16; 



localparam
        `ifdef RW_SIMU_ON
          DMA_HALTED   = 4'b0001,
          DMA_DEAD     = 4'b1000,
        `endif // RW_SIMU_ON
          DMA_PASSIVE  = 4'b0010,
          DMA_ACTIVE   = 4'b0100;


// durationComputationFSM FSM states definition
//$fsm_sd durationComputationFSM
localparam 
             DUR_IDLE  =  3'd0,  
              DUR_RTS  =  3'd1,  
              DUR_CTS  =  3'd2,  
             DUR_DATA  =  3'd3,  
              DUR_ACK  =  3'd4,  
            DUR_CFEND  =  3'd5,  
              DUR_TSF  =  3'd6,  
        DUR_COMPLETED  =  3'd7;


localparam
              NO_PROT  = 3'd0,
             SELF_CTS  = 3'd1,
         RTSCTS_W_STA  = 3'd2,
          RTSCTS_W_AP  = 3'd3,
          RTS_DUALCTS  = 3'd4,
            CTS_W_STA  = 3'd5;

localparam
               NON_HT  = 3'd0,
      NON_HT_DUP_OFDM  = 3'd1,
                HT_MM  = 3'd2,
                HT_GF  = 3'd3,
                  VHT  = 3'd4;

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// macControllerTxFSM FSM signals definition
reg   [4:0] macControllerTxFSMNs;// macControllerTxFSM FSM Next State
reg   [4:0] macControllerTxFSMPs;// macControllerTxFSM FSM Previous State

// durationComputationFSM FSM signals definition
reg   [2:0] durationComputationFSMCs;  // durationComputationFSM FSM Current State
reg   [2:0] durationComputationFSMNs;  // durationComputationFSM FSM Next State

  
reg         notMineRcved;        // Frame not addressed to the device
reg         incorrectRcved;      // Frame not received correctly
reg         correctRcved;        // Frame received correctly
reg         baRcved;             // BA received flag
reg         ackRcved;            // ACK received flag
reg         ctsRcved;            // CTS received flag
reg         swRTS;               // Asserted high if the current transmitted packet is a
                                 // RTS frame prepared by SW
reg         retryFrame;          // If the transmitted frame has to be retried then this
                                 // signal is asserted.
reg         mpduSuccess;         // If the transmitted frame was successful. Not asserted
                                 // for RTS frames
reg         mpduFailed;          // If the transmitted frame was not successful. Not asserted
                                 // if the RTS frame failed
reg         rtsFailed;           // If the transmitted frame was a RTS frame and did not 
                                 // receive a CTS frame within the CTS timeout
reg         rtsSuccess;          // If the transmitted frame was a RTS frame and successfully
                                 // received a CTS in reponse.
wire [15:0] txLegLengthProt;     // Length of the transmitted protection frame.
                                 
reg  [19:0] aMPDUFrameLengthInt;   // aMPDUFrameLengthInt (opt 20/40/80) mux
wire [19:0] frameLengthTx;         // Length of the transmitted frame

wire        hasTXOPLimitNull;     // Indicates that the transfer has a null TXOP Limit

wire        expectProtResp;       // Indicates that a protection response is expected            
wire        expectResp;           // Indicates that a response (ack or BA) is expected           

wire  [7:0] retryLimit;           // Retry Limit depending on the frame length and RTS Threshold 

reg  [15:0] frmExDuration;        // Current Frame exchange duration (1us) 
wire [15:0] cfendTotalDuration;   // CF_END Frame exchange duration   
wire        frmExDurationDone_p;  // Indicates that the frame exchange duration computing is completed  
reg         compDurDelayDone_p;   // Indicates that the frame exchange duration computing is completed  
reg         txOpAcquired;         // Indicates that a TX OP has already been acquired.

wire        dmaStatusUpdateDone_p;// Indicates that the DMA Engine has updated the status

// Time Out Counter
reg  [9:0]  timeOutCnt;             // Time Out counter
reg         timeOutStarted;         // Indicates that the Time Out Counter is counting down.

reg   [2:0] protType;               // Indicates the type of protection
wire        timeOnAirDone_p;        // Indicates the end of the time on air computation
reg         timeOnAirValidMC_ff1;   // timeOnAirValidMC delayed of one clock cycle
reg         dataDisambiguity;       // Disambiguity Bit Computed for PPDU
reg  [15:0] rtsDuration;            // Duration of the RTS frame
reg  [15:0] ctsDuration;            // Duration of the CTS frame
reg  [15:0] ProtDuration;            // Duration of the RTS/CTS exchange
reg  [15:0] dataDuration;           // Duration of the DATA frame
reg  [15:0] ackDuration;            // Duration of the ACK frame
reg  [15:0] cfendDuration;          // Duration of the CF-END frame
reg  [20:0] extACMOT;               // Extended version of the AC MOT (unit 1us)
reg  [15:0] remainingTXOPDuration;  // Remaining time before the end of the TXOP
wire        remainingTXOP;          // Indicates that the remaining TXOP is not null
reg  [15:0] remainingFrmExDuration; // Remaining frame Exchange duration

reg  [15:0] currentFrmDuration;       // Duration of the current transmitted frame
reg  [15:0] maxAllowedDuration;       // Maximum duration allowed (unit 32us)
reg  [15:0] dontTouchDurFrmExDuration;// Frame Exchange Duration in case of dontTouchDur. (in us)

reg         txOpStarted;            // Indicates that a TX OP is started.
wire        crossQI;                // Indicates that the frame exchange will cross the Quit Interval


reg         txSuccessful;           // Captured value of txSuccessful_p 
reg         retryLimitReached;      // Captured value of retryLimitReached_p

reg         txParameterPTReadyInt;      // Indicates if the Policy Table fields are usable
reg         txAMPDU;                    // Indicates that the current transmission is an AMPDU

reg         respReceived;         // Indicates that the expected response frame has been received

wire        rxRespOnGoing;        // Indicates that a response is being received.
wire        rxProtRespOnGoing;    // Indicates that a Protection response is being received.

reg         frmExFitInTXOP;       // Indicates that the current frame Exchange fit in the remaining TXOP;

wire        txDMADataPending;     // Indicates that the DMA has data pending on its active queue

reg         respProtIsHT;         // Indicates if the protection response frame should be HT or NON-HT PPDU
reg         respIsHT;             // Indicates if the response frame should be HT or NON-HT PPDU

reg   [7:0] phyRxStartDelay;      // Receive Start Delay of the PHY

wire        nextIsCFEND;          // Indicates that the next MPDU contained in the TXFIFO is a CF-END.
wire        nextIsBAR;            // Indicates that the next MPDU contained in the TXFIFO is a Block Ack request.

reg  [15:0] legLengthComputed;    // Legacy Length computed for HT_MM
reg  [15:0] lSIGDuration;         // L-SIG Duration
wire [15:0] txTimeInt;            // Equal to TXTIME - signalExtension - 20
wire [15:0] lSIGDurationInt;      // Equal to lSIGDuration-signalExtension
wire        useLSTP;              // Indicates that the current transmition uses L-SIG TXOP protection
wire  [2:0] signalExtension;
reg   [2:0] txFormatMod;          // Start Transmission with Format and Modulation

wire        toggleHDSetForAMPDU_p;   // Pulse to indicate a toggle of Header Descriptor set in case of AMPDU
wire        toggleSetForSingleMPDU_p;// Pulse to indicate a toggle of Header Descriptor set in case of Singleton MPDU
          
reg         skipBAR;              // Indicates that the Block Ack Requested chained has to be skipped by the TX Controller

reg   [1:0] requiredBW;           // Indicates that the current transmission needs 40MHz BW
reg   [1:0] txOpBW;               // Indicates if the current TXOP is a 40MHz TXOP
reg         dropBW;               // Indicates that the currentftransmission can dropped to 20MHz if required
wire        currentTxBWdroppedto20;  // Indicates that the current transmission BW has been dropped to 20 Mhz
wire        currentTxBWdroppedto40;  // Indicates that the current transmission BW has been dropped to 40 Mhz
wire        currentTxBWdroppedto80;  // Indicates that the current transmission BW has been dropped to 80 Mhz
wire        currentTxBWdropped;   // Indicates that the current transmission BW has been dropped
wire  [1:0] currentBWPPDU;        // Indicates the bandwidth of the current PPDU
wire  [1:0] currentBWProt;        // Indicates the bandwidth of the current Protection
reg         failedChBW;           // Indicates that the frame which is going to be transmitted failed BW check
reg         failedBWSignaling;    // Indicates that the BW signaling failed. (i.e the BW received in the CTS is not 
                                  // the expected one and the dynBW is static) 
reg   [2:0] numTryBWDone;         // Indicates the number of tries already done for 40MHz TXOP Acquisition
wire  [1:0] bwProt;               // Band Width of Protection frame for Transmission

wire [15:0] protFrmDurInt;        // Protection Frame Duration
wire  [2:0] formatModProt;        // Format and Modulation of Protection frame for Transmission
                                  //   3'b000: NON-HT
                                  //   3'b001: NON-HT-DUP-OFDM
                                  //   3'b010: HT-MF
                                  //   3'b011: HT-GF
                                  //   3'b100: VHT
wire        preTypeProt;          // Preamble Type of Protection frame for Transmission
                                  //   1'b0: SHORT
                                  //   1'b1: LONG
wire        lstpProtInt;          // Indicates that the current transmition uses L-SIG TXOP protection
wire        curFrmIsSWRTS;        // Indicates that the current frame programmed in Tx Parameter Cache is a SW RTS.
wire        txErr;                // Indicates that a error occured during transmission
reg         macPhyIfRxEnd;        // Captured version of macPhyIfRxEnd_p
reg   [1:0] expectedAckCapt;      // Expected Acknowledgement
wire        isPSPOLL;             // Indicates that the current frame is a PS_POLL
wire        includeTSF;           // Indicates that the current frame includes a TSF field (BEACON or PROB_RESP)


reg         frmExDurationDone_CheckCFEnd; // Memorize the pulse frmExDurationDone_p until the state is out of CHECKCFEND

wire        frmExDurBiggerMaxAllDur; // Indicates that the current frame exchange is bigger than the max allowed duration

wire        useImpQI; // Indicates that the maxAllowedDuration is based on impQICnt instead of txOpLimit

reg         rxEndOfFrameFlag; // Flag used to remember rx end of frame pulse

reg         captureStatus_p;
reg         captureStatusDly_p;

reg         ignoreTxParameterPTReady; // This mask the txParameterPTReady_p caused by resync between clk domain
reg         txDmaActive;              // This is used to detect when Dma is going from passive to active
reg         txDmaActiveDly;           // This is used to detect when Dma is going from passive to active

wire        txopCompleteInt;          // internal signal for txopComplete logic


wire        backToIdle_p;             // internal signal indicating that the FSM moves back to IDLE
reg         firstExchangeOfTxOp;      // Flag indicating that the current frame exchange is the first of TXOP 

reg         updateDurationAfterDynBW; // Flag indicated that the duration need to be updated due to dynBW
reg   [1:0] whichDescriptorCapt;      // Indicates what kind of a descriptor this is


`ifdef RW_MAC_MIBCNTL_EN
wire        updateBWMib_p;            // Pulse indicating the update of the BW statistic MIB
`endif // RW_MAC_MIBCNTL_EN


`ifdef RW_SIMU_ON
// String definition to display macControllerTxFSM current state
reg [21*8-1:0] macControllerTxFSMCs_str;
// String definition to display durationComputationFSM current state
reg [13*8-1:0] durationComputationFSMCs_str;
// String definition to display protType 
reg [12*8-1:0] protType_str;
// String definition to display expectedAckCapt 
reg [13*8-1:0] expectedAck_str;
// String definition to display txDmaState 
reg [11*8-1:0] txDmaState_str;
// String definition to display retryLimitType
wire [18*8-1:0] retryLimitType_str;
// String definition to display txOpBW
reg [10*8-1:0]  txOpBW_str;
`endif // RW_SIMU_ON


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

assign macCoreTxClkEnTxC = ((macControllerTxFSMCs == IDLE) ||
                            (macControllerTxFSMCs == RX_PROT_RESP) ||
                            (macControllerTxFSMCs == WAIT_RX_PROT_RESP_END) ||
                            (macControllerTxFSMCs == RX_RESP) ||
                            (macControllerTxFSMCs == WAIT_RX_RESP_END)) ? 1'b0 : 1'b1;

// macControllerTxFSM FSM Current State Logic 
always @(posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macControllerTxFSMCs <= IDLE; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macControllerTxFSMCs <= IDLE; 
  else
    macControllerTxFSMCs <= macControllerTxFSMNs; 
end

// macControllerTxFSM FSM Previous State Logic 
always @(posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macControllerTxFSMPs <= IDLE; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macControllerTxFSMPs <= IDLE; 
  else
    macControllerTxFSMPs <= macControllerTxFSMCs; 
end



// macControllerTxFSM FSM Next State Logic.
always @* 
begin
  case(macControllerTxFSMCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits for a trigger from the macControllerMaster state machine to start a TXOP.
      if (txExchangeEnabled && startTxFrameExGated) 
        //$fsm_t When txExchangeEnabled is received indicating the begining of a TXOP and if startTxFrameExGated is set indicating 
        //that the protection frame is requested via the registers, the state machine goes to COMP_DURATION state.
        macControllerTxFSMNs = COMP_DURATION; 
      else if (txExchangeEnabled && !startTxFrameExGated) 
        //$fsm_t When txExchangeEnabled is received indicating the begining of a TXOP and if startTxFrameExGated is not set indicating 
        //that the protection frame if any is built based on THD, the state machine goes to WAIT_DMA state.
        macControllerTxFSMNs = WAIT_DMA; 
      else
        //$fsm_t While txExchangeEnabled is not received, the state machine stays in IDLE state.
        macControllerTxFSMNs = IDLE;

    WAIT_DMA:
      //$fsm_s In WAIT_DMA state, the state machine waits for the download of the Policy table in the TX Parameters Cache
      if (skipBAR) 
        //$fsm_t In case of A-MPDU, when the DMA has finished the status update and the BA has been received, the FSM checkes if the BAR needs to be skipped.
        // In this case, the BA Request is skipped. So, the state machine moves to SKIP_MPDU.
        macControllerTxFSMNs = SKIP_MPDU;
      else if (txParameterPTReadyInt) 
        //$fsm_t When txParameterPTReadyInt is received meaning that the PT has been completed loaded in the TX Parameters Cache, 
        //the state machine goes to COMP_DURATION state.
        macControllerTxFSMNs = COMP_DURATION; 
      else if (txOpAcquired && !remainingTXOP) 
        //$fsm_t If a TXOP has already been acquired and the remaining TXOP duration reaches zero, 
        //the state machine goes to TRIG_BACKOFF state.
        macControllerTxFSMNs = TRIG_BACKOFF; 
      else if ((!txOpAcquired || trigTxBcn) && !txDMADataPending)
        //$fsm_t If the DMA States moves to HALTED or DEAD and the TXOP has not already been acquired, 
        //the state machine goes to TRIG_BACKOFF state.
        macControllerTxFSMNs = TRIG_BACKOFF; 
      else if (txOpAcquired && !txDMADataPending)
        //$fsm_t If the DMA States moves to HALTED or DEAD and the TXOP has already been acquired, 
        //the state machine goes to CHECK_CFEND state.
        macControllerTxFSMNs = CHECK_CFEND; 
      else
        //$fsm_t While txParameterPTReadyInt are not received, the state machine stays in WAIT_DMA state.
        macControllerTxFSMNs = WAIT_DMA;
    

    COMP_DURATION:
      //$fsm_s In COMP_DURATION state, the state machine waits for the completion of the duration computation
      if (frmExDurationDone_p) 
        if (updateDurationAfterDynBW)
          //$fsm_t When frmExDurationDone_p is received meaning that the duration computation is finished, the state machine goes to CHECK_TXOP state.
          macControllerTxFSMNs = TX_DATA; 
        else
          //$fsm_t When frmExDurationDone_p is received meaning that the duration computation is finished, the state machine goes to CHECK_TXOP state.
          macControllerTxFSMNs = CHECK_TXOP; 
      else
        //$fsm_t While frmExDurationDone_p is not received, the state machine stays in COMP_DURATION state.
        macControllerTxFSMNs = COMP_DURATION;

    CHECK_TXOP:
      //$fsm_s In CHECK_TXOP state, the state machine checks if the current frame exchange fits into the current TXOP
      if (!txOpAcquired && startTxFrameExGated && ({5'd0,dontTouchDurFrmExDuration} > {maxAllowedDuration,5'h1f}))
        //$fsm_t When startTxFrameExGated is 1 and the TXOP has not been acquired yet and the frame exchange does not fit in 
        // the maxAllowedDuration (due to Quit interval Crossing), the state machime moves to TRIG_BACKOFF.
        macControllerTxFSMNs = TRIG_BACKOFF; 
      else if (!txOpAcquired && dontTouchDur && ({5'd0,dontTouchDurFrmExDuration} > {maxAllowedDuration,5'h1f}))
        //$fsm_t When dontTouchDur is 1 and the TXOP has not been acquired yet and the frame exchange does not fit in 
        // the maxAllowedDuration (due to Quit interval Crossing), the state machime moves to STATUS_UPDATE.
        macControllerTxFSMNs = STATUS_UPDATE; 
      else if (hasTXOPLimitNull && frmExDurBiggerMaxAllDur)
        //$fsm_t When TXOPLimit is 0 and the frame exchange does not fit in the maxAllowedDuration (due to Quit interval Crossing), 
        //the state machime moves to STATUS_UPDATE.
        macControllerTxFSMNs = STATUS_UPDATE; 
      else if (failedChBW)
        //$fsm_t When the current transmission needs a 40MHz bandwidth which is not available and the drop to 20MHz is not possible, 
        //the state machime moves to STATUS_UPDATE.
        macControllerTxFSMNs = STATUS_UPDATE;
      else if (!hasTXOPLimitNull && !txOpAcquired && (impQICnt < frmExDuration) && !isPSPOLL)
        //$fsm_t If the current TXOP limit is not 0 and the frame exchange does not fit into the remaining TXOP,
        // the state machine moves in STATUS_UPDATE state.
        macControllerTxFSMNs = STATUS_UPDATE;
      else if (!hasTXOPLimitNull && txOpAcquired && (frmExDurBiggerMaxAllDur || (remainingTXOPDuration < frmExDuration)) && !isPSPOLL)
        //$fsm_t If the current TXOP limit is not 0 and the frame exchange does not fit into the remaining TXOP,
        // the state machine moves in STATUS_UPDATE state.
        macControllerTxFSMNs = STATUS_UPDATE;
      else if (!txOpAcquired && !hasTXOPLimitNull && nextIsCFEND)
        //$fsm_t If the TXOP has not been acquired yet and the MPDU is a CFEND, 
        //the state machine moves to SKIP_MPDU state.
        macControllerTxFSMNs = SKIP_MPDU;
      else if (!txOpAcquired && (protType != NO_PROT) && currentTxBWdropped)
        //$fsm_t If the TXOP has not been acquired yet and the frame exchange duration fit and a protection is required, 
        //the state machine moves to TX_PROT state.
        macControllerTxFSMNs = DROPBW_LENGTH_UPDATE;
      else if (!txOpAcquired && (protType != NO_PROT) && !currentTxBWdropped)
        //$fsm_t If the TXOP has not been acquired yet and the frame exchange duration fit and a protection is required, 
        //the state machine moves to TX_PROT state.
        macControllerTxFSMNs = TX_PROT;
      else if (currentTxBWdropped)
        //$fsm_t If the frame exchange fits into the remaining TXOP and maxAllowedDuration and no protection is required, 
        //the state machine moves to TX_DATA state.
        macControllerTxFSMNs = DROPBW_LENGTH_UPDATE;
      else
        macControllerTxFSMNs = TX_DATA;
        
    DROPBW_LENGTH_UPDATE:
      //$fsm_s In DROPBW_LENGTH_UPDATE state, the controler generates the corresponding BWDrop protocol interrupt
      if (protType != NO_PROT)
        macControllerTxFSMNs = TX_PROT;
      else
        macControllerTxFSMNs = TX_DATA;
        

    TX_PROT:
      //$fsm_s In TX_PROT state, the state machine launches the protection frame transmission and waits until its completion
      if (txDone_p) 
        if ((protType == SELF_CTS) || (protType == CTS_W_STA))
          //$fsm_t When txDone_p is received and the protection does not expect any response, the state machine goes to TX_DATA state.
          macControllerTxFSMNs = TX_DATA; 
        else
          //$fsm_t When txDone_p is received and the protection expects a response, the state machine goes to RX_PROT_RESP state.
          macControllerTxFSMNs = RX_PROT_RESP; 
      else if (txErr) 
        if (startTxFrameExGated)
          //$fsm_t When txErr is received set meaning that a PHY error has been detected during the 
          //transmission of a protection frame requested by register, the state machine goes to TRIG_BACKOFF state.
          macControllerTxFSMNs = TRIG_BACKOFF; 
        else  
          //$fsm_t When txErr is received set meaning that a PHY error has been detected, 
          //the state machine goes to STATUS_UPDATE state.
          macControllerTxFSMNs = STATUS_UPDATE; 
      else 
        //$fsm_t While txDone_p is not received, the state machine stays in TX_PROT state.
        macControllerTxFSMNs = TX_PROT;

    RX_PROT_RESP:
      //$fsm_s In RX_PROT_RESP state, the state machine waits for an indication
      // from the RX Controller indicating that a protection frame response is being received.
      if (ctsRcved_p) 
        //$fsm_t When ctsRcved_p is received indicating that a CTS is being received, the state machine goes to WAIT_RX_PROT_RESP_END state.
        macControllerTxFSMNs = WAIT_RX_PROT_RESP_END; 
      else if (respTO_p || rxEndOfFrameFlag || macPhyIfRxErr_p) 
        //$fsm_t When respTO_p is received indicating that the CTS frame has not been received before the expiration of the CTS Timeout timer, 
        //the state machine goes to STATUS_UPDATE state.
        macControllerTxFSMNs = STATUS_UPDATE; 
      else
        //$fsm_t While ctsRcved_p or respTO_p are not received, the state machine stays in RX_PROT_RESP state.
        macControllerTxFSMNs = RX_PROT_RESP;

    WAIT_RX_PROT_RESP_END:
      //$fsm_s In WAIT_RX_PROT_RESP_END state, the state machine waits for the completion of the protection frame reception 
      if (rxEndOfFrameFlag && correctRcved && rxCsIsIdle && !failedBWSignaling)
      begin
        if (useBWSignalingTx && dynBWTx && dynBWEn)
          //$fsm_t When rxEndOfFrameFlag is received indicating the end of the reception and the frame has been succefully received 
          // (correctRcved received), the state machine goes to TX_DATA state.
          macControllerTxFSMNs = COMP_DURATION; 
        else
          macControllerTxFSMNs = TX_DATA; 
      end
      else if ((rxEndOfFrameFlag && (incorrectRcved || failedBWSignaling) || macPhyIfRxErr_p))
        //$fsm_t When rxEndOfFrameFlag is received indicating the end of the reception and the frame has not been succefully received 
        // (incorrectRcved received) or the bandwidth failed or a Rx Error has been received, 
        // the state machine goes to STATUS_UPDATE state.
        macControllerTxFSMNs = STATUS_UPDATE; 
      else
        //$fsm_t While rxEndOfFrame is not received, the state machine stays in WAIT_RX_PROT_RESP_END state.
        macControllerTxFSMNs = WAIT_RX_PROT_RESP_END;

    TX_DATA:
      //$fsm_s In TX_DATA state, the state machine launches the frame transmission and waits until its completion
      if (txErr) 
        //$fsm_t When txErr is received set meaning that a PHY error has been detected, 
        //the state machine goes to STATUS_UPDATE state.
        macControllerTxFSMNs = STATUS_UPDATE; 
      else if (txDone_p)
        if (swRTS)
          //$fsm_t When txDone_p is received and the transmitted frame was an RTS (swRTS set), the state machine goes to RX_PROT_RESP state.
          macControllerTxFSMNs = RX_RESP; 
        else if (expectedAckCapt == 2'b00) 
          //$fsm_t When txDone_p is received and the transmitted frame does not expect acknowledgment, the state machine goes to STATUS_UPDATE state.
          macControllerTxFSMNs = STATUS_UPDATE; 
        else  
          //$fsm_t When txDone_p is received and the transmitted frame expects acknowledgment, the state machine goes to RX_RESP state.
          macControllerTxFSMNs = RX_RESP; 
      else
        //$fsm_t While txDone_p is not received, the state machine stays in TX_DATA state.
        macControllerTxFSMNs = TX_DATA;

    RX_RESP:
      //$fsm_s In RX_RESP state, the state machine waits for an indication
      // from the RX Controller indicating that an acknowledgment frame is being received.
      if (macPhyIfRxErr_p) 
        //$fsm_t When macPhyIfRxErr_p is received, the state machine goes to PHY_ERROR state.
        macControllerTxFSMNs = PHY_ERROR; 
      else if (ackRcved_p || baRcved_p || (ctsRcved_p && swRTS)) 
        //$fsm_t When ackRcved_p or baRcved_p is received indicating that an ACK or Block Ack is being received, the state machine goes to WAIT_RX_RESP_END state.
        macControllerTxFSMNs = WAIT_RX_RESP_END; 
      else if (respTO_p || rxEndOfFrameFlag) 
        //$fsm_t When respTO_p is received indicating that the ACK frame has not been received before the expiration of the ACK Timeout timer, 
        //the state machine goes to STATUS_UPDATE state.
        macControllerTxFSMNs = STATUS_UPDATE; 
      else
        //$fsm_t While ackRcved_p, baRcved_p or respTO_p are not received, the state machine stays in RX_RESP state.
        macControllerTxFSMNs = RX_RESP;

    WAIT_RX_RESP_END:
      //$fsm_s In WAIT_RX_RESP_END state, the state machine waits for the completion of the acknowledgment frame reception 
      if (macPhyIfRxErr_p) 
        //$fsm_t When macPhyIfRxErr_p is received, the state machine goes to PHY_ERROR state.
        macControllerTxFSMNs = PHY_ERROR; 
      else if (rxEndOfFrameFlag && (incorrectRcved || correctRcved)) 
        //$fsm_t When rxEndOfFrameFlag is received, the state machine goes to STATUS_UPDATE state.
        macControllerTxFSMNs = STATUS_UPDATE; 
      else
        //$fsm_t While rxEndOfFrameFlag is not received, the state machine stays in WAIT_RX_RESP_END state.
        macControllerTxFSMNs = WAIT_RX_RESP_END;

    PHY_ERROR:
      //$fsm_s In PHY_ERROR state, the state machine waits for the completion of the rxErr recovery 
      if (macPhyIfRxEnd)
        //$fsm_t When macPhyIfRxEnd is received, the state machine goes to STATUS_UPDATE state.
        macControllerTxFSMNs = STATUS_UPDATE; 
      else
        //$fsm_t While macPhyIfRxEnd is not received, the state machine stays in PHY_ERROR state.
        macControllerTxFSMNs = PHY_ERROR;

    SKIP_MPDU:
      //$fsm_s In SKIP_MPDU state, the state machine launches the tx controller to discard the MPDU and waits until the completion
      if (skipMPDUDone_p)
        //$fsm_t When skipMPDUDone_p is received, the state machine goes to STATUS_UPDATE state.
        macControllerTxFSMNs = STATUS_UPDATE; 

      else
        //$fsm_t While skipMPDUDone_p is not received, the state machine stays in TX_DATA state.
        macControllerTxFSMNs = SKIP_MPDU;

    STATUS_UPDATE:
      //$fsm_s In STATUS_UPDATE state, the state machine waits for the completion of the status update on the DMA side.
      if (statusUpdated_p)
      begin
        if (trigTxBcn && txDMADataPending)
          //$fsm_t When the DMA has finished the status update, if the current DMA queue is the Beacon one and it still have data pending on this queue,
          // the state machine goes to WAIT_DMA state to transmit the remaining frames.
          macControllerTxFSMNs = WAIT_DMA;
        else if (hasTXOPLimitNull && ((correctRcved && respReceived) || (expectedAckCapt == 2'b00)) && (txAMPDU == 1'b0) && ((whichDescriptorCapt == 2'b01) || (whichDescriptorCapt == 2'b10))) 
          //$fsm_t When the DMA has finished the status update, and in case of fragmented MSDU with TXOpLimit = 0, if the first or 
          // intermediate fragment has been successfully transmitted, the state machine goes to WAIT_DMA state to transmit the remaining fragments.
          macControllerTxFSMNs = WAIT_DMA;
        else if (skipBAR) 
          //$fsm_t In case of A-MPDU, when the DMA has finished the status update and the BA has been received, the state machine moves to WAIT_DMA.
          macControllerTxFSMNs = WAIT_DMA;
        else if (!hasTXOPLimitNull && txOpAcquired && (!txDMADataPending || !frmExFitInTXOP || failedChBW)) 
          //$fsm_t When the DMA has finished the status update, if the current TXOP limit is not 0 and the DMA has not yet loaded a new PT in the TX parameter Cache
          // or that the current frame exchange does not fit in the remianing TXOP, the state machine moves in CHECK_CFEND state.
          macControllerTxFSMNs = CHECK_CFEND;
        else if (!hasTXOPLimitNull && txOpAcquired && ((correctRcved && respReceived) || (expectedAckCapt == 2'b00)) && txDMADataPending)
          //$fsm_t When the DMA has finished the status update, if the current TXOP limit is not 0 and the DMA has data (in PASSIVE state),
          // the state machine moves in WAIT_DMA state.
          macControllerTxFSMNs = WAIT_DMA;
        else if (swRTS && txOpAcquired && txDMADataPending)
          //$fsm_t When the DMA has finished the status update, if the current TXOP limit is not 0 and the DMA has data (in PASSIVE state),
          // the state machine moves in WAIT_DMA state.
          macControllerTxFSMNs = WAIT_DMA;
        else
          //$fsm_t When the DMA has finished the status update, and either the current TXOP limit is 0 or the DMA has no data
          // (in HALTED state), the state machine moves in TRIG_BACKOFF state.
          macControllerTxFSMNs = TRIG_BACKOFF;
      end
      else
        //$fsm_t While the DMA has not finished the status update, the state machine stays in STATUS_UPDATE state.
        macControllerTxFSMNs = STATUS_UPDATE;

    CHECK_CFEND:
      //$fsm_s In CHECK_CFEND state, the state machine checks if the duration of the CF-END transmission fits into the remaining TXOP
      if (!txOpAcquired || !remainingTXOP || (!keepTXOPOpen && !sendCFEnd && !sendCFEndNow))
          //$fsm_t If the remaining TXOP reaches 0 (extACMOT = 0), the state machine goes back to TRIG_BACKOFF state.
          // If the flag keepTXOPOpen indicating that the TXOP shall be kept open is not set and the CFEnd transmission is not requested, the state machine
          // goes back to TRIG_BACKOFF state even if the remaining TXOP duration is not null.
        macControllerTxFSMNs = TRIG_BACKOFF;
      else if (frmExDurationDone_CheckCFEnd && (sendCFEnd || sendCFEndNow))
      begin
        if (remainingTXOPDuration > {cfendTotalDuration + 16'd20})
          //$fsm_t If the CF-END frame exchange fits into the remaining TXOP, the state machine goes to TX_CFEND state.
          macControllerTxFSMNs = TX_CFEND; 
        else  
          //$fsm_t If the CF-END frame exchange does not fit into the remaining TXOP, the state machine goes to TRIG_BACKOFF state.
          macControllerTxFSMNs = TRIG_BACKOFF; 
      end    
      else if (frmExFitInTXOP && txDMADataPending && !failedChBW) 
        //$fsm_t If the DMA has data available and the previous frame Exchange fit into the TXOP 
        //(txDMADataPending and txDMADataPending set), the state machine goes to WAIT_DMA state.
        // This transition occurs if the DMAChannel became HALTED during a TXOP (txDMADataPending reset) and the software linked a new MPDU.
        macControllerTxFSMNs = WAIT_DMA;
      else 
        //$fsm_t If the CF-END frame exchange does not fit into the remaining TXOP, the state machine goes to IDLE state.
        macControllerTxFSMNs = CHECK_CFEND;

    TX_CFEND:
      //$fsm_s In TX_CFEND state, the state machine launches the frame transmissi
      if (txErr) 
        //$fsm_t When txErr is received set meaning that a PHY error has been detected, 
        //the state machine goes to IDLE state.
        macControllerTxFSMNs = TRIG_BACKOFF; 
      else if (txDone_p) 
        //$fsm_t When txDone_p is received, the state machine goes back to IDLE state.
        macControllerTxFSMNs = TRIG_BACKOFF; 
      else
        //$fsm_t While txDone_p is not received, the state machine stays in TX_CFEND state.
        macControllerTxFSMNs = TX_CFEND;

    TRIG_BACKOFF:
      //$fsm_s In TRIG_BACKOFF state, the state machine restarts the backoff module. 

      //$fsm_t The FSM stays only one clock cycle in this state and goes back to IDLE.
       macControllerTxFSMNs = IDLE;

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
     default:   
        macControllerTxFSMNs = IDLE; 
    // pragma coverage block = on 
  endcase
end

assign backToIdle_p = (macControllerTxFSMCs == TRIG_BACKOFF);


// Indicates that the reception of the response is on-going
assign rxRespOnGoing      = (macControllerTxFSMCs == RX_RESP) || (macControllerTxFSMCs == WAIT_RX_RESP_END);

// Indicates that the reception of the protection frame response is on-going
assign rxProtRespOnGoing  = (macControllerTxFSMCs == RX_PROT_RESP) || (macControllerTxFSMCs == WAIT_RX_PROT_RESP_END);
 
// Assign the Length of the transmitted frame
assign frameLengthTx = (txAMPDU || txSingleVHTMPDU) ? aMPDUFrameLengthInt : {4'b0,MPDUFrameLengthTx};

// aMPDU length selection in case of bandwidth drop 
always @*
  begin
    if( currentTxBWdroppedto20 && (aMPDUOptFrameLength20Tx != 20'd0) )
    begin
      aMPDUFrameLengthInt = aMPDUOptFrameLength20Tx;
    end
    else if( currentTxBWdroppedto40 && (aMPDUOptFrameLength40Tx != 20'd0) )
    begin
      aMPDUFrameLengthInt = aMPDUOptFrameLength40Tx;
    end
    else if( currentTxBWdroppedto80 && (aMPDUOptFrameLength80Tx != 20'd0) )
    begin
      aMPDUFrameLengthInt = aMPDUOptFrameLength80Tx;
    end
    else
    begin
      aMPDUFrameLengthInt = aMPDUFrameLengthTx;
    end
  end
//end

// acBWDrop interrupt in case of bandwidth drop 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    acBWDropTrigger = 1'b0;
  end
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    acBWDropTrigger = 1'b0;
  end
  else if (macControllerTxFSMCs == DROPBW_LENGTH_UPDATE)
  begin
    if( currentTxBWdroppedto20 && (aMPDUOptFrameLength20Tx != aMPDUFrameLengthTx) && (aMPDUOptFrameLength20Tx != 20'd0) )
    begin
      acBWDropTrigger = 1'b1;
    end
    else if( currentTxBWdroppedto40 && (aMPDUOptFrameLength40Tx != aMPDUFrameLengthTx) && (aMPDUOptFrameLength40Tx != 20'd0))
    begin
      acBWDropTrigger = 1'b1;
    end
    else if( currentTxBWdroppedto80 && (aMPDUOptFrameLength80Tx != aMPDUFrameLengthTx) && (aMPDUOptFrameLength80Tx != 20'd0))
    begin
      acBWDropTrigger = 1'b1;
    end
    else
    begin
      acBWDropTrigger = 1'b0;
    end
  end
  else 
      acBWDropTrigger = 1'b0;
end

// Capture  expectedAck coming from txParametersCache
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    expectedAckCapt <= 2'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    expectedAckCapt <= 2'b0;
  else if (txParameterHDReady_p)
    expectedAckCapt <= expectedAck;
end 
 
// Capture  expectedAck coming from txParametersCache
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    whichDescriptorCapt <= 2'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    whichDescriptorCapt <= 2'b0;
  else if (txParameterHDReady_p)
    whichDescriptorCapt <= whichDescriptor;
end 
 
 
 
////////////////////////////////////////////////////////////////////
////
//// TX OP Management
////
////////////////////////////////////////////////////////////////////

// Indicates that the TXOPLimit for this AC is zero
assign hasTXOPLimitNull = (txOpLimit == 16'b0) ? 1'b1 : 1'b0;

// Set frmExFitInTXOP when the frame Exchange fits in the remaining TXOP.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    frmExFitInTXOP <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || backToIdle_p)  // Synchronous Reset
    frmExFitInTXOP <= 1'b0;
  else
  begin
    if ((macControllerTxFSMCs == CHECK_TXOP))
    begin
      if (dontTouchDur && (remainingTXOPDuration >= dontTouchDurFrmExDuration))
        frmExFitInTXOP <= 1'b1;
      else if (remainingTXOPDuration >= frmExDuration)
        frmExFitInTXOP <= 1'b1;
      else  
        frmExFitInTXOP <= 1'b0;
    end    
//    if ((macControllerTxFSMCs == COMP_DURATION) && frmExDurationDone_p)
//    begin
//      if (dontTouchDur && (remainingTXOPDuration >= dontTouchDurFrmExDuration))
//        frmExFitInTXOP <= 1'b1;
//      else if ((remainingTXOPDuration >= frmExDuration) && !frmExDurBiggerMaxAllDur)
//        frmExFitInTXOP <= 1'b1;
//      else  
//        frmExFitInTXOP <= 1'b0;
//    end    
  end
end


// When a transmission is requested, currentFrmDuration gets the computed duration for this frame.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    currentFrmDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || backToIdle_p)  // Synchronous Reset
    currentFrmDuration <= 16'b0;
  else
  begin
    if (sendCTSTxC_p)
      currentFrmDuration <= ctsDuration;
    if (sendRTS_p)
      currentFrmDuration <= rtsDuration;
    if (sendData_p)
      currentFrmDuration <= dataDuration;
  end
end


// In case of TXOPLimit - 0, only the frame Exchange Duration is needed.
// Once computed, the remainingFrmExDuration is loaded with frmExDuration.
// Then the remainingFrmExDuration is updated in four different cases:
//   1- When a CTS is transmitted:
//      The duration of the transmitted CTS is removed from remainingFrmExDuration
//   2- When a RTS is transmitted:
//      The duration of the transmitted RTS is removed from remainingFrmExDuration
//   3- When a MPDU is transmitted, there is two cases:
//     3.1- With no protection:
//       The duration of the transmitted frame is removed from remainingFrmExDuration
//     3.2- With protection (i.e. a protection frame has been already sent):
//       The duration of the transmitted frame and the SIFS duration are removed from remainingFrmExDuration
//   4- When a CTS is received:
//      The duration of the received CTS and the SIFS duration are removed from remainingFrmExDuration
// 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    remainingFrmExDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || backToIdle_p)  // Synchronous Reset
    remainingFrmExDuration <= 16'b0;
  else
  begin
    // When the frmExDuration computation is completed, it is loaded in 
    // remainingFrmExDuration
    if (frmExDurationDone_p)
      remainingFrmExDuration <= frmExDuration;
    else
    begin
      if (sendCTSTxC_p)
        // Case 1- When a CTS is transmitted:
        //   The duration of the transmitted CTS is removed from remainingFrmExDuration
        remainingFrmExDuration <= remainingFrmExDuration - ctsDuration;
      else if (sendRTS_p)
        // Case 2- When a RTS is transmitted:
        //   The duration of the transmitted RTS is removed from remainingFrmExDuration
        remainingFrmExDuration <= remainingFrmExDuration - rtsDuration;
      else if (sendData_p)
      begin
        if (protType == NO_PROT)
         // Case 3.1- With no protection:
         //   The duration of the transmitted frame is removed from remainingFrmExDuration
          if (remainingFrmExDuration > dataDuration)
            remainingFrmExDuration <= remainingFrmExDuration - dataDuration;
          else
            remainingFrmExDuration <= 16'b0;  
        else  
          // Case 3.2- With protection (i.e. a protection frame has been already sent):
          //   The duration of the transmitted frame and the SIFS duration are removed 
          //   from remainingFrmExDuration
          if (remainingFrmExDuration > (dataDuration + {8'd0,sifsDuration}))
          begin
            if (updateDurationAfterDynBW)
              remainingFrmExDuration <= remainingFrmExDuration - dataDuration;
            else  
              remainingFrmExDuration <= remainingFrmExDuration - dataDuration - {8'd0,sifsDuration};
          end
          else
            remainingFrmExDuration <= 16'b0;  
      end
      else if (ctsRcved_p)
        // Case 4- When a CTS is received:
        //   The duration of the received CTS and the SIFS duration are removed from remainingFrmExDuration
        remainingFrmExDuration <= remainingFrmExDuration - ctsDuration - {8'd0,sifsDuration};
    end   
  end
end
  
// This process creates the txOpAcquired flag which indicates that a TX OP has been acquired.
// So, based on this flag, if a protection is requested in the THD but the TX OP has already been acquired, 
// this protection will be discarded. This flag is set when the first frame of the TXOP is successfully transmitted
// So, there is four cases:
//  1- Transmission of a protection frame which does not expect a response (SELF_CTS or CTS_W_STA)
//  2- Reception of the response of the protection frame
//  3- Transmission of a frame which does not have a protection and does not expect a response
//  3- Reception of the response of a frame which does not have a protection
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txOpAcquired <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE) || backToIdle_p || txErr)  // Synchronous Reset
    txOpAcquired <= 1'b0;
  else
  begin
    if (!txOpAcquired && !curFrmIsSWRTS)
    begin
      if (((protType == SELF_CTS) || (protType == CTS_W_STA)) && startTx_p && frmExFitInTXOP)
        txOpAcquired <= 1'b1;
      if ((protType != NO_PROT) && ctsRcved && correctRcved_p && frmExFitInTXOP && !failedBWSignaling)
        txOpAcquired <= 1'b1;
      if ((protType == NO_PROT) && (expectedAckCapt == 2'b00) && startTx_p && frmExFitInTXOP)
        txOpAcquired <= 1'b1;
      if ((protType == NO_PROT) && (expectedAckCapt != 2'b00) && (ackRcved || baRcved) && correctRcved_p && frmExFitInTXOP)
        txOpAcquired <= 1'b1;
    end    
    else if (curFrmIsSWRTS && ctsRcved && correctRcved_p && frmExFitInTXOP && !failedBWSignaling)
      txOpAcquired <= 1'b1;
  end
end  

// Indicates that the current frame programmed in Tx Parameter Cache is a SW RTS.
assign curFrmIsSWRTS = ((fcSubtype == 4'b1011) && (fcType == 2'b01) && tsValid) ? 1'b1 : 1'b0;

// txOpStarted indicates that a TX OP is started. Note that this flag is raised when the first
// frame of the TX OP is being transmitted. So, that does not mean that the TXOP has been acquired.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txOpStarted <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE) || backToIdle_p || txErr)  // Synchronous Reset
    txOpStarted <= 1'b0;
  else
  begin
    if (!txOpStarted && (!hasTXOPLimitNull || curFrmIsSWRTS) && !isPSPOLL)
      if (startTx_p)
        txOpStarted <= 1'b1;
  end
end  

// Generation of the endofTxOp indication. It is generated when the FSM moves back to IDLE and a 
// TXOP was aquired (txOpAcquired set).
assign endOfTxOp = (txOpAcquired && !hasTXOPLimitNull && (macControllerTxFSMCs == IDLE)) ? 1'b1 : 1'b0;


// Manage the remaining TXOP.
// When a CF-END is transmitted either because it was requested (sendCFENDTxC_p = 1) or linked by SW (sentCFEND = 1), the 
// remaining TXOP duration is reset.
// During CHECKTXOP state, the remainingTXOPDuration is loaded with protFrmDurInt if dontTouchDur was set or with maxAllowedDuration
// Note that maxAllowedDuration is in TU and remainingTXOPDuration in us.
// Then once the TXOP is acquired, the remainingTXOPDuration is decremented every us (on tick1us_p pulse) until it reaches zero.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    remainingTXOPDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || sendCFENDTxC_p || sentCFEND || backToIdle_p)  // Synchronous Reset
    remainingTXOPDuration <= 16'b0;
  else
  begin
    if (macControllerTxFSMNs == CHECK_TXOP)
    begin
      if (!txOpStarted)
      begin
        if (dontTouchDur || startTxFrameExGated)
          remainingTXOPDuration <= dontTouchDurFrmExDuration;
        else
          remainingTXOPDuration <= maxAllowedDuration<<16'd5;
      end    
    end
    else if (txOpStarted && tick1us_p && remainingTXOP)
      remainingTXOPDuration <= remainingTXOPDuration - 16'd1;
  end
end

// Indicates that the remainingTXOP is not null
assign remainingTXOP = (remainingTXOPDuration != 16'd0) ? 1'b1 : 1'b0;


// isPSPOLL indicates that the transmiting frame is a PS_POLL
assign isPSPOLL = ((tsValid == 1'b1) && (fcType == 2'b01) && (fcSubtype == 4'b1010));

// includeTSF indicates that the transmiting frame includes a TSF field (i.e. BEACON or PROB_RESP)
assign includeTSF = ((tsValid == 1'b1) && (fcType == 2'b00) && ((fcSubtype == 4'b1000) || (fcSubtype == 4'b0101)));
//assign includeTSF = 0;

// dontTouchDurFrmExDuration is to Frame exchange duration computed in case of dontTouchDur based on the protFrmDurInt + Time 
// on Air of the transmitted frame
always @ *
begin
  if (dontTouchDur)
  begin
    if (isPSPOLL)
      // In case of PS_POLL, the dontTouchDurFrmExDuration duration is equal to the duration of a RTS
      dontTouchDurFrmExDuration = rtsDuration;
    else if ((protType == SELF_CTS) || (protType == CTS_W_STA))
      dontTouchDurFrmExDuration = protFrmDurInt + ctsDuration;
    else if  (protType == NO_PROT) 
      dontTouchDurFrmExDuration = protFrmDurInt + dataDuration;
    else  
      dontTouchDurFrmExDuration = protFrmDurInt + rtsDuration;
  end
  else
    dontTouchDurFrmExDuration = 16'b0;
end  
  
// Estimate the max allowed duration for the transmission.
// This max allowed duration is the minimum remaining duration before the next Quiet interval (impQICnt)
// In case of non-zero TXOP Limit, the max allowed duration is the minimum of impQICnt and txOpLimit.
// Note that txOpLimit and impQICnt are in 32us
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    maxAllowedDuration <= 16'b0;
  else if (macCoreClkSoftRst_n == 1'b0 || backToIdle_p)  // Synchronous Reset
    maxAllowedDuration <= 16'b0;
  else // if (tick1us_p)
  begin
    if (useImpQI)
      maxAllowedDuration <= impQICnt;
    else  
      maxAllowedDuration <= txOpLimit;
  end
end

// Indicates that the maxAllowedDuration is based on impQICnt instead of txOpLimit
assign useImpQI = (hasTXOPLimitNull || ( impQICnt < txOpLimit)) ? 1'b1 : 1'b0;

// The   flag indicates the the computed frame Exchange Duration is bigger than the 
// max Allowed Duration
assign frmExDurBiggerMaxAllDur = {5'b0,frmExDuration} > {maxAllowedDuration,5'h1f};


// In AP mode, only one CF-END will be transmitted.
// In STA, two CF-END will be sent (one by the STA and one after SIFS by the AP in response of the first CF-END).
assign cfendTotalDuration = (ap) ? cfendDuration : {cfendDuration[14:0],1'b0} + {8'b0,sifsA}; //$todo in STBC

// For TXOPLimit = 0, if the next atomic frame exchange sequence 
// will cross into the next scheduled Quiet interval, the frame exchange sequence is not attempted.
assign crossQI = (hasTXOPLimitNull && frmExDurBiggerMaxAllDur) ? 1'b1 : 1'b0;

////////////////////////////////////////////////////////////////////
////
//// 20/40/80/160MHz bandwidth
////
////////////////////////////////////////////////////////////////////

// Indicates the bandwidth requested for the on-going transmission
always @ *
begin
  if (!txOpAcquired && (protType != NO_PROT))
    requiredBW = bwProt;
  else if (txOpAcquired || (protType == NO_PROT))
    requiredBW = bwTx;
  else if (startTxFrameExGated)
    requiredBW = startTxBW;
  else
    requiredBW = 2'b0;
end

// txOpBW indicates the bandwidth of the TXOP
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txOpBW <= 2'b0;
  else if (macCoreClkSoftRst_n == 1'b0 || backToIdle_p)  // Synchronous Reset
    txOpBW <= 2'b0;
  else
  begin
    if (!txOpAcquired)
    begin
      if (useBWSignalingTx && dynBWTx && (macControllerTxFSMCs == WAIT_RX_PROT_RESP_END))
      begin
        if (availableBW >= rxChBWInNonHT)
          txOpBW <= rxChBWInNonHT;
        else
          txOpBW <= availableBW;
      end
      else if (availableBW >= requiredBW)
        txOpBW <= requiredBW;
      else if (macControllerTxFSMCs == WAIT_DMA)
//      else if ( ((macControllerTxFSMCs != WAIT_DMA) && (macControllerTxFSMNs == WAIT_DMA)) || dropBW )
        txOpBW <= availableBW;
    end    
  end
end

// Indicates that the bandwidth for the current transmission can be dropped to lower bandwidth
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    dropBW <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0 || backToIdle_p)  // Synchronous Reset
    dropBW <= 1'b0;
  else if ((txParameterPTReady_p || startTxFrameExGated) && !txOpAcquired)
  begin
    if (dropToLowerBW && (numTryBWAcquisition != 3'd0))
    begin
      if (!txOpAcquired && (protType != NO_PROT) && ((numTryBWAcquisition - 3'd1) <= numTryBWDone))
        dropBW <= 1'b1;
      else if ((txOpAcquired || (protType == NO_PROT)) && ((numTryBWAcquisition - 3'd1) <= numTryBWDone))
        dropBW <= 1'b1;
      else
        dropBW <= 1'b0;
    end
    else
      dropBW <= 1'b0;
  end    
end

// Indicates if current transmission BW hsa been changed with drop mechanism
assign currentTxBWdroppedto20 = (dropBW && (txChBWTxC != requiredBW) && dropToLowerBW && (txChBWTxC == 2'd0)) ? 1'b1 : 1'b0 ;
assign currentTxBWdroppedto40 = (dropBW && (txChBWTxC != requiredBW) && dropToLowerBW && (txChBWTxC == 2'd1)) ? 1'b1 : 1'b0 ;
assign currentTxBWdroppedto80 = (dropBW && (txChBWTxC != requiredBW) && dropToLowerBW && (txChBWTxC == 2'd2)) ? 1'b1 : 1'b0 ;
assign currentTxBWdropped = currentTxBWdroppedto20 || currentTxBWdroppedto40 || currentTxBWdroppedto80;

// Indicates the bandwidth of the current PPDU
assign currentBWPPDU = (dropBW && (txOpBW < bwTx)) ? txOpBW : bwTx;

assign bwDataTx = currentBWPPDU;

// Indicates the bandwidth of the current Protection
assign currentBWProt = (dropBW && (availableBW < bwProt)) ? availableBW : bwProt;

// Check if the channelBW of the transmission is correct
always @ *
begin
  if (requiredBW > txOpBW)
  begin
    if (!dropBW)
      failedChBW = 1'b1;
    else if (dropBW && ({2'b0,frmExDuration} >= {aPPDUMaxTime,10'b0}))
      failedChBW = 1'b1;
    else  
      failedChBW = 1'b0;
  end
  else
    failedChBW = 1'b0;
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    numTryBWDone <= 3'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    numTryBWDone <= 3'b0;
  else
  begin
    if ((macControllerTxFSMCs == CHECK_TXOP) && failedChBW)
      numTryBWDone <= numTryBWDone + 3'd1;
    else if ((macControllerTxFSMCs == CHECK_TXOP) && !failedChBW)
      numTryBWDone <= 3'd0;
  end    
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    failedBWSignaling <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0 || backToIdle_p)  // Synchronous Reset
    failedBWSignaling <= 1'b0;
  else if (useBWSignalingTx && !dynBWTx && ctsRcved_p)
  begin
    if (rxChBW < bwProtTx)
      failedBWSignaling <= 1'b1;
    else
      failedBWSignaling <= 1'b0;
  end
  else if (macControllerTxFSMCs == TRIG_BACKOFF)
    failedBWSignaling <= 1'b0;
end  


always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    updateDurationAfterDynBW <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0 || backToIdle_p)  // Synchronous Reset
    updateDurationAfterDynBW <= 1'b0;
  else if (useBWSignalingTx && dynBWTx && ctsRcved_p)
    updateDurationAfterDynBW <= 1'b1;
  else if (macControllerTxFSMCs == COMP_DURATION && frmExDurationDone_p)
    updateDurationAfterDynBW <= 1'b0;
end  

// txBWAfterDrop logic
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txBWAfterDrop <= 2'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    txBWAfterDrop <= 2'b0;
  else
  begin
    if (macControllerTxFSMCs == DROPBW_LENGTH_UPDATE)
      txBWAfterDrop <= txChBWTxC;
  end    
end



`ifdef RW_MAC_MIBCNTL_EN

assign updateBWMib_p = (firstExchangeOfTxOp && updateDMAStatus_p);

assign mibrw20MHzFailedTXOPCount      = (updateBWMib_p && !mibrw20MHzSuccessfulTXOPCount) && (requiredBW == 2'd0) ? 1'b1 : 1'b0;
assign mibrw40MHzFailedTXOPCount      = (updateBWMib_p && !mibrw40MHzSuccessfulTXOPCount) && (requiredBW == 2'd1) ? 1'b1 : 1'b0;
assign mibrw80MHzFailedTXOPCount      = (updateBWMib_p && !mibrw80MHzSuccessfulTXOPCount) && (requiredBW == 2'd2) ? 1'b1 : 1'b0;
assign mibrw160MHzFailedTXOPCount     = (updateBWMib_p && !mibrw160MHzSuccessfulTXOPCount) && (requiredBW == 2'd3) ? 1'b1 : 1'b0;
assign mibrw20MHzSuccessfulTXOPCount  = (updateBWMib_p && txOpAcquired && (txOpBW == 2'd0))? 1'b1 : 1'b0;
assign mibrw40MHzSuccessfulTXOPCount  = (updateBWMib_p && txOpAcquired && (txOpBW == 2'd1))? 1'b1 : 1'b0;
assign mibrw80MHzSuccessfulTXOPCount  = (updateBWMib_p && txOpAcquired && (txOpBW == 2'd2))? 1'b1 : 1'b0;
assign mibrw160MHzSuccessfulTXOPCount = (updateBWMib_p && txOpAcquired && (txOpBW == 2'd3))? 1'b1 : 1'b0;
assign mibrwDynBWDropCount            = ctsRcved && correctRcved_p && useBWSignalingTx && dynBWTx && firstExchangeOfTxOp && (requiredBW > txOpBW);
assign mibrwStaBWFailedCount          = updateBWMib_p && failedBWSignaling; 

`endif // RW_MAC_MIBCNTL_EN

//
//assign txBWSignalingTxC = ((macControllerTxFSMCs == TX_PROT) && ((protType == RTSCTS_W_STA) || (protType == RTSCTS_W_AP))) ? useBWSignalingTx : 1'b0;
//
//// If the BW Signaling is used for the current transmission (in this case, RTS transmission), the flag dynBWTx coming from the Header Descriptor is 
//// provided to the Tx Controller 
//assign txDynBWTxC = (txBWSignalingTxC) ? dynBWTx : 1'b0;
//

////////////////////////////////////////////////////////////////////
////
//// TX Controller management
////
////////////////////////////////////////////////////////////////////

// The macControllerTx updates the durationId field (via durationTxC signal).
// In case of dontTouchDur set, the durationTxC gets the value provided in the THD
// (protFrmDurInt)
// In case of remTXOPInDurField = 0, the durationTxC gets the frame Exchange remaining duration
// In case of TXOPLimit null, the durationTxC gets the frame Exchange remaining duration
// In case of non-null TxOPLimit, the duration of the transmitted frame (Protection or not)
// is removed from the remainingTXOPDuration.
// To avoid overflow, the durationTxC is forced to zero if the duration of the transmitted
// frame is bigger than the remainingTXOPDuration.
// Note that the durationTxC is updated on startTx_p pulse. This is
// to provide an accurate durationId based on the preamble start and not when the TX Controller is triggered.
// Thanks to that, the time spent by the TX Controller waiting for tickSIFS does not disturb the duration computation.
// In case of CF-END transmission, the remainingTXOPDuration has already been reset. So, the durationTxC will get 0.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    durationTxC <= 16'b0;
  else if (macCoreClkSoftRst_n == 1'b0 || backToIdle_p)  // Synchronous Reset
    durationTxC <= 16'b0;
  else
  begin
    if (dontTouchDur || startTxFrameExGated)
      durationTxC <= protFrmDurInt;
    else if (!remTXOPInDurField)
      // When remTXOPInDurField = 0, it indicates that the duration field of the transmitted frame
      // does not contain the remaining TXOP duration but only the remaining frame exchange duration (ACK + SIFS duration for exemple).
      durationTxC <= remainingFrmExDuration;
    else if (hasTXOPLimitNull || (!txOpAcquired && frmExDurBiggerMaxAllDur))
      durationTxC <= remainingFrmExDuration;
    else
    begin
      if (startTx_p)
      begin
        if ({1'b0,remainingTXOPDuration} > {1'b0,currentFrmDuration})
          durationTxC <= remainingTXOPDuration - currentFrmDuration;
        else
          durationTxC <= 16'b0;  
      end

      // Only in case of send data the duration is calculated before start tx
      // since the tx controller start fetching on sendData_p
      if(sendData_p)
      begin
        if (!frmExFitInTXOP)
          durationTxC <= frmExDuration - dataDuration - {8'd0,sifsRemaining};
        else if ({1'b0,remainingTXOPDuration} > ({1'b0,dataDuration} + {9'd0,sifsRemaining}))
          durationTxC <= remainingTXOPDuration - dataDuration - {8'd0,sifsRemaining};
        else
          durationTxC <= 16'b0;
      end
    end
  end
end

// Assign the MAC Header retry bit
assign retry = (numMPDURetriesTPC == 8'b0000) ? 1'b0 : 1'b1;

// Assign the destination address
// In case of RTSCTS with a STA, the destination address comes from the KeySearch Engine
// In case of Self CTS, the destination address is the MAC Address
// Else, the destination address is the bssID
// Note that thiis destination address is only used for RTS, Self-CTS and TXDATA
// All the response frames are handled by the macControllerRx.  
always @*
begin
  if ((macControllerTxFSMCs == TX_PROT) && (protType == RTSCTS_W_STA))
    destAddrTxC = macAddressKSR;
  else if ((macControllerTxFSMCs == TX_PROT) && (protType == SELF_CTS))
    destAddrTxC = macAddr;
  else
    destAddrTxC = bssID;
end  

assign srcAddrTxC = macAddr; //$todo for multi SSID


assign txFromReg  = ((macControllerTxFSMCs == TX_PROT) && startTxFrameExGated)  ? 1'b1 : 1'b0;
assign txFromHD   = ((macControllerTxFSMCs == TX_PROT) && !startTxFrameExGated) ? 1'b1 : 1'b0;
assign txFromFifo =  (macControllerTxFSMCs == TX_DATA)  ? 1'b1 : 1'b0;
assign txCFEND    =  (macControllerTxFSMCs == TX_CFEND) ? 1'b1 : 1'b0;

// sendOnSIFSTxC generation process
// 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    sendOnSIFSTxC <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
    sendOnSIFSTxC <= 1'b0;
  else
  begin
    if (txDone_p)
      sendOnSIFSTxC <= 1'b1;
  end
end


assign sendOnPIFSTxC = 1'b0;


assign txRxnTxC = txFromFifo || txFromHD || txFromReg || (macControllerTxFSMCs == TX_CFEND);

// When the state machine goes back to IDLE state, the txExchangeCompleted_p pulse is generated to indicate to the macControllerMaster
// the end of the TX frame exchanges (end of the TXOP in case of TXOPLimit > 0).
assign txExchangeCompleted_p = ((macControllerTxFSMNs == IDLE) && (macControllerTxFSMCs != IDLE)) ? 1'b1 : 1'b0;

// Indicate if a response is expected for the protection. The response can be either CTS or Dual-CTS.
// It depends on startTxFrmExType if the protection transmission has been requested through registers (startTxFrameExGated set)
// or on protType if the protection transmission has been requested through the Transmit Header Descriptor  (startTxFrameExGated reset).
assign expectProtResp = ((protType == RTSCTS_W_STA) || (protType == RTSCTS_W_AP) || (protType == RTS_DUALCTS)) ? 1'b1 : 1'b0;

// Indicate if a response is expected for this frame. The response can be either ACK or BA and depends on the ACK Policy.
assign expectResp = ((expectedAckCapt != 2'b00) || swRTS) ? 1'b1 : 1'b0;


// sendCTSTxC_p generation process
// The sendCTSTxC_p pulse is generated when the FSM enters in TX_PROT state and if the
// protection required is Self-CTS.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    sendCTSTxC_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    sendCTSTxC_p <= 1'b0;
  else
  begin
    sendCTSTxC_p <= 1'b0;
    if ((macControllerTxFSMNs == TX_PROT) && (macControllerTxFSMCs != TX_PROT))
      if ((protType == SELF_CTS) || (protType == CTS_W_STA))
        sendCTSTxC_p <= 1'b1;
  end
end

// sendRTS_p generation process
// The sendRTS_p pulse is generated when the FSM enters in TX_PROT state and if the
// protection required is RTS/CTS or RTS/DualCTS.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    sendRTS_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    sendRTS_p <= 1'b0;
  else
  begin
    sendRTS_p <= 1'b0;
    if ((macControllerTxFSMNs == TX_PROT) && (macControllerTxFSMCs != TX_PROT))
      if ((protType == RTSCTS_W_STA) || (protType == RTSCTS_W_AP) || (protType == RTS_DUALCTS))
        sendRTS_p <= 1'b1;
  end
end

// sendData_p generation process
// The sendData_p pulse is generated when the FSM enters in TX_DATA state
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    sendData_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    sendData_p <= 1'b0;
  else
  begin
    sendData_p <= 1'b0;
    if ((macControllerTxFSMNs == TX_DATA) && (macControllerTxFSMCs != TX_DATA))
      sendData_p <= 1'b1;
  end
end

// sendCFENDTxC_p generation process
// The sendCFENDTxC_p pulse is generated when the FSM enters in TX_CFEND state
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    sendCFENDTxC_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    sendCFENDTxC_p <= 1'b0;
  else
  begin
    sendCFENDTxC_p <= 1'b0;
    if ((macControllerTxFSMNs == TX_CFEND) && (macControllerTxFSMCs != TX_CFEND))
      sendCFENDTxC_p <= 1'b1;
  end    
end

// skipMPDU_p generation process
// The skipMPDU_p pulse is generated when the FSM enters in SKIP_MPDU state
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    skipMPDU_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    skipMPDU_p <= 1'b0;
  else
  begin
    skipMPDU_p <= 1'b0;
    if ((macControllerTxFSMNs == SKIP_MPDU) && (macControllerTxFSMCs != SKIP_MPDU))
      skipMPDU_p <= 1'b1;
  end
end


// Indicates that a error occured during transmission
assign txErr = mpIfTxErr_p || macPHYIFUnderRun;

////////////////////////////////////////////////////////////////////
////
//// Rx Controller
////
////////////////////////////////////////////////////////////////////


// Capture the incorrectRcved_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    incorrectRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || 
           (macControllerTxFSMCs == IDLE) || 
           (macControllerTxFSMCs == TX_PROT) || 
           (macControllerTxFSMCs == TX_DATA))  // Synchronous Reset
    // In case of synchronous reset or if the state machine is not waiting for a response 
    //(i.e. neither in WAIT_RX_PROT_RESP_END nor WAIT_RX_RESP_END),
    // the incorrectRcved flag is reset 
    incorrectRcved <= 1'b0; 
  else
    if (incorrectRcved_p || notMineRcved_p)
      // When incorrectRcved_p is received, the flag incorrectRcved is set to capture the incorrectRcved_p pulse
      incorrectRcved <= 1'b1; 
end


// Capture the notMineRcved_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    notMineRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || 
           (macControllerTxFSMCs == IDLE) || 
           (macControllerTxFSMCs == TX_PROT) || 
           (macControllerTxFSMCs == TX_DATA))  // Synchronous Reset
    // In case of synchronous reset or if the state machine is not waiting for a response 
    //(i.e. neither in WAIT_RX_PROT_RESP_END nor WAIT_RX_RESP_END),
    // the incorrectRcved flag is reset 
    notMineRcved <= 1'b0; 
  else
    if (notMineRcved_p)
      // When incorrectRcved_p is received, the flag incorrectRcved is set to capture the incorrectRcved_p pulse
      notMineRcved <= 1'b1; 
end



// Capture the correctRcved_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    correctRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || 
           (macControllerTxFSMCs == IDLE) || 
           (macControllerTxFSMCs == TX_PROT) || 
           (macControllerTxFSMCs == TX_DATA))  // Synchronous Reset
    // In case of synchronous reset or if the state machine is not waiting for a response 
    //(i.e. neither in WAIT_RX_PROT_RESP_END nor WAIT_RX_RESP_END),
    // the correctRcved flag is reset 
    correctRcved <= 1'b0; 
  else
    if (correctRcved_p && !notMineRcved)
      // When correctRcved_p is received, the flag incorrectRcved is set to capture the correctRcved_p pulse
      correctRcved <= 1'b1; 
end

// Capture the rxEndOfFrame_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxEndOfFrameFlag <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || 
           (macControllerTxFSMCs == IDLE) || 
           (macControllerTxFSMCs == TX_PROT) || 
           (macControllerTxFSMCs == TX_DATA))  // Synchronous Reset
    rxEndOfFrameFlag <= 1'b0; 
  else
    if (rxEndOfFrame_p)
      rxEndOfFrameFlag <= 1'b1; 
end


// Capture the ctsRcved_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    ctsRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || 
           (macControllerTxFSMCs == IDLE) || 
           (macControllerTxFSMCs == TX_PROT) || 
           (macControllerTxFSMCs == TX_DATA))  // Synchronous Reset
    // In case of synchronous reset 
    ctsRcved <= 1'b0; 
  else
    if (notMineRcved_p)
      // When notMineRcved_p is received, the flag ctsRcved is reset 
      ctsRcved <= 1'b0; 
    else if (ctsRcved_p)
      // When ctsRcved_p is received, the flag ctsRcved is set to capture the ctsRcved_p pulse
      ctsRcved <= 1'b1; 
end

// Capture the ackRcved_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    ackRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || 
           (macControllerTxFSMCs == IDLE) || 
           (macControllerTxFSMCs == TX_PROT) || 
           (macControllerTxFSMCs == TX_DATA))  // Synchronous Reset
    // In case of synchronous reset 
    ackRcved <= 1'b0; 
  else
    if (notMineRcved_p)
      // When notMineRcved_p is received, the flag ackRcved is reset 
      ackRcved <= 1'b0; 
    else if (ackRcved_p && ((macControllerTxFSMCs == RX_RESP) || (macControllerTxFSMCs == WAIT_RX_RESP_END)))
      // When ackRcved_p is received, the flag ackRcved is set to capture the ackRcved_p pulse
      ackRcved <= 1'b1; 
end


// Capture the baRcved_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    baRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || 
           (macControllerTxFSMCs == IDLE) || 
           (macControllerTxFSMCs == TX_PROT) || 
           (macControllerTxFSMCs == TX_DATA))  // Synchronous Reset
    // In case of synchronous reset 
    baRcved <= 1'b0; 
  else
    if (notMineRcved_p)
      // When notMineRcved_p is received, the flag baRcved is reset 
      baRcved <= 1'b0; 
    else if (baRcved_p && ((macControllerTxFSMCs == RX_RESP) || (macControllerTxFSMCs == WAIT_RX_RESP_END)))
      // When baRcved_p is received, the flag baRcved is set to capture the correctRcved_p pulse
      baRcved <= 1'b1; 
end


assign rxAck = (rxRespOnGoing && !swRTS) ? 1'b1 : 1'b0;
assign rxBA  = (rxRespOnGoing && !swRTS) ? txAMPDU || nextIsBAR : 1'b0;
assign rxCts = (rxProtRespOnGoing || swRTS) ? 1'b1 : 1'b0;

assign forceWriteACK = (rxRespOnGoing && writeACK) ? 1'b1 : 1'b0;




////////////////////////////////////////////////////////////////////
////
//// Key Search Engine Control
////
////////////////////////////////////////////////////////////////////

// Select between keySRAMIndex for encryption and keySRAMIndexRA for RTS to STA MAC Address search
// When the protection is RTSCTS with STA and the txOP has not been already acquired, the RA of the RTS are picked from the keySRAM based on 
// keySRAMIndexRA or startTxKSRIndex (depending if the protectionis requested by register or not).
// For the encryption, the key and encryption parameters are picked from the keySRAM based on keySRAMIndex.
always @ *
begin
  if ((macControllerTxFSMNs == COMP_DURATION) && ((protType == RTSCTS_W_STA) || (protType == CTS_W_STA)) && !txOpAcquired)
    if (startTxFrameExGated)
      txKeySearchIndex = startTxKSRIndex;
    else
      txKeySearchIndex = keySRAMIndexRA;
  else
    txKeySearchIndex = keySRAMIndex;
end

// When the macControllerTxFSM moves to COMP_DURATION, the key Search Egine is trigged to return the encryption informations.
// In case of RTSCTS_W_STA, the research done during COMP_DURATION returns the RA for the RTS. So, the key Search Engine is trigged 
// a second time when the FSM moves to RX_PROT_RESP in order to retrun the encryption informations required for the MPDU.
//always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
//begin
//  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
//    txKeySearchIndexTrig_p <= 1'b0; 
//  else if (((macControllerTxFSMCs != COMP_DURATION) && (macControllerTxFSMNs == COMP_DURATION)) || 
//           ((macControllerTxFSMCs != RX_PROT_RESP) && (macControllerTxFSMNs == RX_PROT_RESP) && (protType == RTSCTS_W_STA)))
//    txKeySearchIndexTrig_p <= 1'b1;
//  else  
//    txKeySearchIndexTrig_p <= 1'b0;
//end
assign txKeySearchIndexTrig_p = ((macControllerTxFSMCs != COMP_DURATION) && (macControllerTxFSMNs == COMP_DURATION)) || 
                                ((macControllerTxFSMCs != RX_PROT_RESP) && (macControllerTxFSMNs == RX_PROT_RESP) && (protType == RTSCTS_W_STA));

////////////////////////////////////////////////////////////////////
////
//// DMA Status Update
////
////////////////////////////////////////////////////////////////////

// Indicate the first frame exchange of the TXOP
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    firstExchangeOfTxOp <= 1'b1; 
  else if ((macCoreClkSoftRst_n == 1'b0) || backToIdle_p)  // Synchronous Reset
    firstExchangeOfTxOp <= 1'b1; 
  else if (statusUpdated_p)
    firstExchangeOfTxOp <= 1'b0;
end





// Indicates that the DMA has data to be transmitted its the active queue
assign txDMADataPending = (txDmaState == DMA_ACTIVE) || (txDmaState == DMA_PASSIVE);

// Indicates when an ACK or BA is received
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    respReceived <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
    respReceived <= 1'b0; 
  else
  begin
    if (notMineRcved_p)
      respReceived <= 1'b0;
    else if (nextIsBAR == 1'b1)
    begin
      if ((expectedAckCapt == 2'b01) && ackRcved_p) // ACK and expected ACK
        respReceived <= 1'b1; 
      else if ((expectedAckCapt[1] == 1'b1) && baRcved_p)  // BA or CompressBA and expected BA or CompressBA
        respReceived <= 1'b1;
    end
    else if (!txAMPDU && (baRcved_p || ackRcved_p))
      respReceived <= 1'b1; 
    else if (!txAMPDU && ctsRcved_p && swRTS)
      respReceived <= 1'b1; 
    else if (txAMPDU && ((expectedAckCapt[1] == 1'b1) && baRcved_p)) // BA or CompressBA
      respReceived <= 1'b1; 
    else if (macControllerTxFSMCs == RX_RESP)
      respReceived <= 1'b0; 
  end    
end




// Indicates when the DMA Status has to be updated.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    updateDMAStatus_p <= 1'b0; 
    captureStatus_p  <= 1'b0; 
    captureStatusDly_p  <= 1'b0; 
  end
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    updateDMAStatus_p <= 1'b0; 
    captureStatus_p  <= 1'b0; 
    captureStatusDly_p  <= 1'b0; 
  end
  else
  begin
    captureStatusDly_p  <= captureStatus_p; 
    updateDMAStatus_p  <= captureStatusDly_p; 
    if ((macControllerTxFSMCs != STATUS_UPDATE) && (macControllerTxFSMNs == STATUS_UPDATE))
      captureStatus_p <= 1'b1; 
    else  
      captureStatus_p <= 1'b0;
  end     
end


// Indicates when the DMA has updated the status.
assign dmaStatusUpdateDone_p = ((macControllerTxFSMNs != STATUS_UPDATE) && (macControllerTxFSMCs == STATUS_UPDATE)); 


// If an RTS has been transmitted by the TX Controller from the TX FIFO, the flag swRTS is set.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    swRTS <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (dmaStatusUpdateDone_p))  // Synchronous Reset
    swRTS <= 1'b0; 
  else
    if ((macControllerTxFSMCs == TX_DATA) && (sentRTS))
      swRTS <= 1'b1; 
end

// DMA Status : MPDU part of an A-MPDU transmitted
assign txMpduDone_p = txAMPDU && mpduDone_p;


always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    swRTS_p             <= 1'b0; 
    ampduFrm_p          <= 1'b0;
    retryFrame_p        <= 1'b0;
    mpduSuccess_p       <= 1'b0;
    mpduFailed_p        <= 1'b0;
    rtsFailed_p         <= 1'b0;
    rtsSuccess_p        <= 1'b0;
    retryLimitReached_p <= 1'b0;
  end
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE) || statusUpdated_p)  // Synchronous Reset
  begin
    swRTS_p             <= 1'b0; 
    ampduFrm_p          <= 1'b0;
    retryFrame_p        <= 1'b0;
    mpduSuccess_p       <= 1'b0;
    mpduFailed_p        <= 1'b0;
    rtsFailed_p         <= 1'b0;
    rtsSuccess_p        <= 1'b0;
    retryLimitReached_p <= 1'b0;
  end
  else if (captureStatusDly_p)
  begin

    // DMA Status : RTS frame linked by SW
    swRTS_p        <= swRTS;

    // DMA Status : Transmitted frame was an A-MPDU
    ampduFrm_p     <= txAMPDU;

    // DMA Status : Transmitted frame has to be retried
    retryFrame_p   <= (retryFrame || 
                       crossQI || 
                       (txOpAcquired && !frmExFitInTXOP) || 
                       (!txAMPDU && !mpduSuccess && !rtsFailed && (numMPDURetriesTPC < retryLimit)) ||
                       (rtsFailed  && (numRTSRetriesTPC  < shortRetryLimit)));

    // DMA Status : frame has been successfully transmitted
    mpduSuccess_p  <= mpduSuccess;

    // DMA Status : frame has not been successfully transmitted
    mpduFailed_p   <= !rtsFailed && frmExFitInTXOP && (mpduFailed || ((txOpLimit != 16'b0) && txOpAcquired && !frmExFitInTXOP) && !nextIsCFEND);

    // DMA Status : protection frame has not been successfully transmitted
    rtsFailed_p    <= rtsFailed;

    // DMA Status : protection frame has been successfully transmitted
    rtsSuccess_p   <= rtsSuccess;

    // DMA Status : retry limit reached.
    // If the mpdu transfert has failed and the retry limit is reached or if the RTS transfert has failed and the numRTS Retries reaches the shortRetrylimit, 
    // the pulse retryLimitReached_p is generated during the updateDMAStatus.

    // Now even if the frame is not fit inside the txOP the retryLimitReached_p can be raised
    retryLimitReached_p  <= ((!txAMPDU && !mpduSuccess  &&  (frmExFitInTXOP || (!txOpAcquired && frmExDurBiggerMaxAllDur)) && !rtsFailed && (numMPDURetriesTPC >= retryLimit)) || 
                             (rtsFailed     &&  (frmExFitInTXOP || (!txOpAcquired && frmExDurBiggerMaxAllDur)) && (numRTSRetriesTPC >= shortRetryLimit)));
                             
  end
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    transmissionBW      <= 2'b0;
  end
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
  begin
    transmissionBW      <= 2'b0;
  end
  else if (startTx_p)
  begin
    // DMA Status : Bandwidth used for the transmission.
    transmissionBW <= txChBWTxC;
  end
end


// When the ACK Time Out is received but the retry limit has not been reached yet, 
// the flag retryFrame is set to restart the transmission.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    retryFrame <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
    retryFrame <= 1'b0; 
  else
  begin
    if (rxProtRespOnGoing && (numRTSRetriesTPC < shortRetryLimit) && 
          (respTO_p || incorrectRcved || macPhyIfRxErr_p || (correctRcved_p && !ctsRcved)) || failedChBW || failedBWSignaling)
      retryFrame <= 1'b1; 
    if (!txAMPDU && rxRespOnGoing && (numMPDURetriesTPC < retryLimit) && 
          (respTO_p || incorrectRcved || macPhyIfRxErr_p || (correctRcved_p && !respReceived)))
      retryFrame <= 1'b1; 
    if (txErr && (
        ((macControllerTxFSMCs == TX_PROT) && (numMPDURetriesTPC < retryLimit)) || 
        ((macControllerTxFSMCs == TX_DATA) && (numRTSRetriesTPC < shortRetryLimit))))
      retryFrame <= 1'b1; 
    else if (((macControllerTxFSMCs == TX_PROT) || (macControllerTxFSMCs == TX_DATA)) && txDone_p)
      retryFrame <= 1'b0; 

  end    
end
                    
// If the transmitted MPDU expected a response and received correctly this response or 
// if the frame does not expect response and completed the transmission,
// the flag mpduSuccess is set.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    mpduSuccess <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (dmaStatusUpdateDone_p))  // Synchronous Reset
    mpduSuccess <= 1'b0; 
  else
    if ((macControllerTxFSMCs == SKIP_MPDU) && skipMPDUDone_p)    
      mpduSuccess <= 1'b1; 
    else if (expectResp == 1'b1)
    begin
      if ((macControllerTxFSMCs == WAIT_RX_RESP_END) && correctRcved_p && respReceived)
        mpduSuccess <= 1'b1; 
    end 
    else    
    begin
      if ((macControllerTxFSMCs == TX_DATA) && txDone_p)    
        mpduSuccess <= 1'b1; 
    end
end
 
                    
// When the ACK Time Out is received and the retry limit has been reached, the flag mpduFailed is set
// to report a transmission failure.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    mpduFailed <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (dmaStatusUpdateDone_p))  // Synchronous Reset
    mpduFailed <= 1'b0; 
  else
  begin
    if (rxRespOnGoing && 
         (numMPDURetriesTPC <= retryLimit) && (respTO_p || incorrectRcved_p || macPhyIfRxErr_p || (correctRcved_p && !respReceived)))
      mpduFailed <= 1'b1; 
    else if ((macControllerTxFSMCs == RX_RESP) && correctRcved_p)
      mpduFailed <= 1'b1; 
    else if ((macControllerTxFSMCs == TX_DATA) && txErr)
      mpduFailed <= 1'b1; 
    else if (((protType == NO_PROT) || txOpAcquired) && (macControllerTxFSMNs == CHECK_TXOP) && failedChBW)
      mpduFailed <= 1'b1; 
  end    
end

                    
// If the Protection expected a response and the CTS was not correctly received (FCS error or CTSTO), the flag rtsFailed is set.                  
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rtsFailed <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || dmaStatusUpdateDone_p)  // Synchronous Reset
    rtsFailed <= 1'b0; 
  else
  begin
    if (rxProtRespOnGoing && 
         (respTO_p || incorrectRcved_p || macPhyIfRxErr_p || (correctRcved_p && !ctsRcved) || failedChBW || failedBWSignaling))
      rtsFailed <= 1'b1; 
    else if ((macControllerTxFSMCs == TX_PROT) && txErr)
      rtsFailed <= 1'b1; 
    else if (((protType != NO_PROT) && !txOpAcquired) && (macControllerTxFSMNs == CHECK_TXOP) && failedChBW)
      rtsFailed <= 1'b1; 
  end    
end


// If the Protection expected a response and the CTS was correctly received or if 
// the protection does not expect response and the transmission has been done successfully, the flag rtsSuccess is set.                
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rtsSuccess <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (dmaStatusUpdateDone_p))  // Synchronous Reset
    rtsSuccess <= 1'b0; 
  else
    if (expectProtResp == 1'b1)
    begin
      if ((macControllerTxFSMCs == WAIT_RX_PROT_RESP_END) && correctRcved_p && ctsRcved && !failedChBW && !failedBWSignaling)
        rtsSuccess <= 1'b1; 
    end 
end


// DMA Status : Number of RTS retry already done for this frame exchange
// assign numRTSRetries  = (rtsFailed && (numRTSRetriesTPC  != shortRetryLimit)) ? numRTSRetriesTPC  + 1'b1 : numRTSRetriesTPC;
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    numRTSRetries <= 8'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    numRTSRetries <= 8'b0; 
  else
  begin
    if (macControllerTxFSMCs == STATUS_UPDATE)
      numRTSRetries <= numRTSRetries; 
    else if ((rtsFailed || (rxProtRespOnGoing && (respTO_p || macPhyIfRxErr_p))) && (numRTSRetriesTPC != shortRetryLimit))
      numRTSRetries <= numRTSRetriesTPC  + 8'b1; 
    else if (txParameterHDReady_p) 
      numRTSRetries <= numRTSRetriesTPC; 
  end
end

// DMA Status : medium time used for this frame exchange
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    mediumTimeUsed <= 31'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    mediumTimeUsed <= 31'b0; 
  else
  begin
    if(txParameterHDReady_p && !txAMPDU)
      mediumTimeUsed <= mediumTimeUsedTPC;
    else if (compDurDelayDone_p && !rtsFailed)
      mediumTimeUsed <= mediumTimeUsedTPC + {21'd0,frmExDuration[15:5]};
    else if ( (rxProtRespOnGoing && (respTO_p || macPhyIfRxErr_p)) || (rtsFailed && captureStatus_p) )
      mediumTimeUsed <= mediumTimeUsedTPC + {21'd0,ProtDuration[15:5]};
    else if (skipMPDUDone_p || backToIdle_p 
             || (updateDMAStatus_p && txOpAcquired && !frmExFitInTXOP) )
      mediumTimeUsed <= 31'b0;
    
  end
end
// DMA Status : Number of retry already done for this frame
// assign numMPDURetries = (mpduFailed && !rtsFailed && (numMPDURetriesTPC != retryLimit)) ? numMPDURetriesTPC + 1'b1 : numMPDURetriesTPC;
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    numMPDURetries <= 8'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    numMPDURetries <= 8'b0; 
  else
  begin
    if (macControllerTxFSMCs == STATUS_UPDATE)
      numMPDURetries <= numMPDURetries; 
    else if (!rtsFailed && !txAMPDU && (mpduFailed || (rxRespOnGoing && (respTO_p || macPhyIfRxErr_p))) && (numMPDURetriesTPC != retryLimit))
      numMPDURetries <= numMPDURetriesTPC  + 8'b1; 
    else  
      numMPDURetries <= numMPDURetriesTPC; 
  end
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    whichDescriptorSW <= 4'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    whichDescriptorSW <= 4'b0; 
  else if (macControllerTxFSMCs == STATUS_UPDATE || txMpduDone_p)
    whichDescriptorSW <= {expectedAckCapt[1],txAMPDU,whichDescriptorCapt}; 
end

////////////////////////////////////////////////////////////////////
////
//// TX Parameter Cache Control
////
////////////////////////////////////////////////////////////////////
// Indicates that the next MPDU contained in the TXFIFO is a CF-END.
assign nextIsCFEND =  (tsValid && (fcType == 2'b01) && (fcSubtype[3:1] == 3'b111)) ? 1'b1: 1'b0;

// Indicates that the next MPDU contained in the TXFIFO is a Block Ack request.
assign nextIsBAR   =  (tsValid && (fcType == 2'b01) && (fcSubtype == 4'b1000)) ? 1'b1: 1'b0;


assign clearSetsTxC_p   = ((macControllerTxFSMCs == TRIG_BACKOFF) || ((macControllerTxFSMCs == STATUS_UPDATE) && retryFrame_p)) ? 1'b1 : 1'b0;
//assign toggleHDSet_p    = toggleHDSetForAMPDU_p || (!txAMPDU && toggleSetForSingleMPDU_p);
assign toggleHDSet_p    = toggleHDSetForAMPDU_p || toggleSetForSingleMPDU_p;

// togglePTSet_p is send to tx cache paramter only if the next state is not trig backoff: avoid receiving tx paramter PT pulse during the resync of the clearSetsTxC_p on platform domain
assign togglePTSet_p    = toggleSetForSingleMPDU_p && (macControllerTxFSMNs != TRIG_BACKOFF);
 
assign toggleHDSetForAMPDU_p       = txAMPDU && (sendData_p || mpduDone_p) && (whichDescriptorCapt != 2'b11);
//assign toggleSetForSingleMPDU_p    = ((macControllerTxFSMNs != STATUS_UPDATE) && (macControllerTxFSMNs != TRIG_BACKOFF) && (macControllerTxFSMCs == STATUS_UPDATE) && !retryFrame) ? 1'b1 : 1'b0;
assign toggleSetForSingleMPDU_p    = ((macControllerTxFSMCs == STATUS_UPDATE) && statusUpdated_p && !retryFrame_p) ? 1'b1 : 1'b0;

 
// Due to the clock domain crossing required for the signals between the MAC Controller and the TX Parameters Cache,
// it might happen that the txParameterPTReady and txParameterNextPTReady stay high for several clock cycles after a 
// toggle or clear set request.
// To avoid that, txParameterPTReadyInt and txParameterNextPTReadyInt are created in the 
// two following processes. 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    txParameterPTReadyInt    <= 1'b0;
  end 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    txParameterPTReadyInt    <= 1'b0; 
  end
  else
  begin
    if (clearSets_p)
      txParameterPTReadyInt <= 1'b0;
    else if ((txParameterPTReady_p == 1'b1) && (ignoreTxParameterPTReady == 1'b0))
      txParameterPTReadyInt <= 1'b1;
    else if (togglePTSet_p)
      txParameterPTReadyInt <= 1'b0;
  end
end

// ignoreTxParameterPTReady FF is used to mask false pulse from txParameterCache
// due to resynchronization (between TRIGG_BACKOFF and next TX) 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    ignoreTxParameterPTReady <= 1'b0;
    txDmaActive              <= 1'b0;
    txDmaActiveDly           <= 1'b0;
  end 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    ignoreTxParameterPTReady <= 1'b0;
    txDmaActive              <= 1'b0;
    txDmaActiveDly           <= 1'b0;
  end
  else
  begin
    txDmaActive      <= (txDmaState == DMA_ACTIVE);
    txDmaActiveDly   <= txDmaActive;

    if (clearSets_p)
      ignoreTxParameterPTReady <= 1'b1;
    else if (((txDmaActiveDly == 1'b0) && (txDmaActive == 1'b1)) || ((macControllerTxFSMCs == IDLE) && (macControllerTxFSMNs != IDLE)))
      ignoreTxParameterPTReady <= 1'b0;
  end
end

////////////////////////////////////////////////////////////////////
////
//// A-MPDU Control
////
////////////////////////////////////////////////////////////////////

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txAMPDU <= 1'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    txAMPDU <= 1'b0; 
  else
  begin
    if (txParameterPTReady_p == 1'b1)
      txAMPDU <= aMPDU && !txSingleVHTMPDU;
  end
end


// SkipBAR indicates that a BA has been successfully receive in response of a AMPDU  
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    skipBAR <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
    skipBAR <= 1'b0; 
  else
  begin
    if (txAMPDU && baRcved && correctRcved && rxEndOfFrameFlag && (macControllerTxFSMCs == WAIT_RX_RESP_END)) //WAIT_RX_RESP_END
      skipBAR <= 1'b1;
    if (skipBAR && (macControllerTxFSMCs == SKIP_MPDU))
      skipBAR <= 1'b0;
  end
end
 
 
////////////////////////////////////////////////////////////////////
////
//// BackOff & AC Selection Control
////
////////////////////////////////////////////////////////////////////


// Frames shorter than or equal to the RTS Threshold are subject to the Short Retry Limit.
// Frames longer than the RTS Threshold are subject to the Long Retry Limit.
// retryLimit takes either shortRetryLimit or longRetryLimit depending on the frame length
// and the RTS Threshold.
assign retryLimit = (frameLengthTx <= {8'b0,rtsThreshold}) ? shortRetryLimit : longRetryLimit;


always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    retryLimitReached <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
    retryLimitReached <= 1'b0; 
  else
    if (retryLimitReached_p == 1'b1)
      retryLimitReached <= 1'b1;
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txSuccessful <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
    txSuccessful <= 1'b0; 
  else
  begin
    if (!swRTS && mpduSuccess_p == 1'b1)
      txSuccessful <= 1'b1;
    else if (incorrectRcved_p || respTO_p || macPhyIfRxErr_p)
      txSuccessful <= 1'b0;
    else if ((macControllerTxFSMCs ==  WAIT_DMA) && (macControllerTxFSMNs ==  TRIG_BACKOFF))
      txSuccessful <= 1'b1;
    else if (!txOpAcquired && !frmExFitInTXOP && (macControllerTxFSMCs ==  STATUS_UPDATE))
      txSuccessful <= 1'b1;
    else if (txAMPDU)
      txSuccessful <= 1'b1;
  end  
end



// Indicates to the BackOff & AC Selection module the type of retry in order to update the status registers
// 0 : Short Retry Limit
// 1 : Long Retry Limit
assign retryType = ({8'b0,rtsThreshold} < frameLengthTx) ? 1'b1 : 1'b0;

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    retryLTReached_p <= 1'b0; 
    retry_p          <= 1'b0; 
    txSuccessful_p   <= 1'b0; 
  end
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
  begin
    retryLTReached_p <= 1'b0; 
    retry_p          <= 1'b0; 
    txSuccessful_p   <= 1'b0; 
  end
  else if (macControllerTxFSMCs ==  TRIG_BACKOFF)
  begin
    if (retryLimitReached)  
      // Indicates to the BackOff & AC Selection module that the retry limit has been reached
      retryLTReached_p <= 1'b1;
    else if (retryFrame && !retryLimitReached && !txSuccessful)
    // Indicates that the current frame has to be retried
      retry_p          <= 1'b1; 
    else  
      txSuccessful_p   <= 1'b1; 
  end    
end


//////////////////////////////
// 
//////////////////////////////


// Protection type 
//
// startTxFrmExType
// 2'b00: self-CTS
// 2'b01: RTS/CTS with MAC address determined from startTxKSRIndex field
// 2'b10: RTS/CTS with AP
// 2'b11: RTS/Dual-CTS with AP as a non-AP STA
// 2'b11: CTS with MAC address determined from startTxKSRIndex field as AP
//
// navProtFrmEx
// 3'b000: No protection                                                                                  
// 3'b001: Self-CTS                                                                                       
// 3'b010: RTS/CTS with intended receiver of this PPDU                                                    
// 3'b011: RTS/CTS with QAP                                                                               
// 3'b100: STBC protection                                                                                
always @ *
begin
  if (startTxFrameExGated  && !txOpAcquired)
  begin
    case (startTxFrmExType)
            2'd0 : protType = SELF_CTS;
            2'd1 : protType = RTSCTS_W_STA;
            2'd2 : protType = RTSCTS_W_AP;
            2'd3 : protType = (!ap) ? RTS_DUALCTS : CTS_W_STA;
      // Disable coverage on the default state because it cannot be reached.
      // pragma coverage block = off 
         default : protType = NO_PROT;
      // pragma coverage block = on 
    endcase
  end
  else
  begin
    case (navProtFrmEx)
            3'd0 : protType = NO_PROT;                         
            3'd1 : protType = SELF_CTS;                        
            3'd2 : protType = RTSCTS_W_STA;                    
            3'd3 : protType = RTSCTS_W_AP;                     
            3'd4 : protType = (!ap) ? RTS_DUALCTS : CTS_W_STA; 
         default : protType = NO_PROT;
    endcase
  
  end    
end

////////////////////////////////////////////////////////////////////
////
//// TX Vector Generation
////
////////////////////////////////////////////////////////////////////

assign rateUpdateTxC_p = ((macControllerTxFSMCs != COMP_DURATION) && (macControllerTxFSMNs == COMP_DURATION)) ? 1'b1 : 1'b0;

always @*
begin
  if (macControllerTxFSMCs == TX_CFEND) //$todo for 80MHz
    txChBWTxC = txOpBW;
  else if (macControllerTxFSMCs == TX_PROT)
    txChBWTxC = currentBWProt;
  else
    txChBWTxC = currentBWPPDU;
end    



// If the Protection is RTS/CTS, the flag useBWSignalingTx coming from the Header Descriptor is provided to the Tx Controller RTS 
assign txBWSignalingTxC = ((macControllerTxFSMCs == TX_PROT) && ((protType == RTSCTS_W_STA) || (protType == RTSCTS_W_AP))) ? useBWSignalingTx : 1'b0;

// If the BW Signaling is used for the current transmission (in this case, RTS transmission), the flag dynBWTx coming from the Header Descriptor is 
// provided to the Tx Controller 
assign txDynBWTxC = (txBWSignalingTxC) ? dynBWTx : 1'b0;


always @*
begin
  if (macControllerTxFSMCs == TX_CFEND)
    txMCSTxC = mcsCFEND;
  else if (!startTxFrameExGated && (macControllerTxFSMCs == TX_PROT))
    txMCSTxC = mcsPROT;
  else if (startTxFrameExGated && (macControllerTxFSMCs == TX_PROT))
    txMCSTxC = startTxMCSIndex0[6:0];
  else
    txMCSTxC = mcsData;
end    

always @*
begin
  if ((txFormatMod == HT_MM) || (txFormatMod == VHT)) 
    txLegRateTxC = 4'd4;
  else if (macControllerTxFSMCs == TX_CFEND)
    txLegRateTxC = legRateCFEND;
  else if (!startTxFrameExGated && (macControllerTxFSMCs == TX_PROT))
    txLegRateTxC = legRatePROT;
  else if (startTxFrameExGated && (macControllerTxFSMCs == TX_PROT))
    txLegRateTxC = startTxMCSIndex0[3:0];
  else
    txLegRateTxC = legRateData;
end    

always @*
begin
  if ((txFormatMod == HT_MM) || (txFormatMod == VHT)) 
    txLegLengthTxC = legLengthComputed[11:0];
  else
    txLegLengthTxC = txHTLengthTxC[11:0];
end    

always @*
begin
  if (macControllerTxFSMCs == TX_CFEND)
    txHTLengthTxC = 20'd20;
  else if (macControllerTxFSMCs == TX_PROT)
    txHTLengthTxC = {4'b0,txLegLengthProt};
  else
    txHTLengthTxC = frameLengthTx;
end    

// $todo txSTBCTxC should be updated in case of DualCTS Prot 
always @*
begin
  if ((txFormatMod == NON_HT) || (txFormatMod == NON_HT_DUP_OFDM)) 
    txSTBCTxC = 2'd0;
  else if (macControllerTxFSMCs == TX_CFEND)
    txSTBCTxC = stbcPT;
  else if (!startTxFrameExGated && (macControllerTxFSMCs == TX_PROT))
    txSTBCTxC = stbcPT;
  else if (startTxFrameExGated && (macControllerTxFSMCs == TX_PROT))
    txSTBCTxC = startTxSTBC;
  else
    txSTBCTxC = stbcPT;
end    

// Assign the STBC value used for the rate selection of the transmitted frame.
// If the startTxFrameExGated is set and the TX OP has not been acquired yet, the STBC of the next frame 
// comes from start TX registers (startTxSTBC) else it comes from the Policy Table (stbcPT)
assign stbcTx = (startTxFrameExGated && !txOpAcquired) ? startTxSTBC : stbcPT;


// If the protection is a CTS (Self-CTS or CTS with STA), the length of the protection frame is 14bytes else it is 20bytes (RTS)
assign txLegLengthProt  = ((protType == SELF_CTS) || (protType == CTS_W_STA))? 16'd14 : 16'd20;

// Depending of the transmission source (THD or register), the rate of the protection frame takes either startTxMCSIndex0 or mcsIndex0Pro
assign mcsIndex0Prot    = (startTxFrameExGated) ? startTxMCSIndex0[6:0] : mcsIndex0ProtTx;    // $todo might not be required

// Depending of the transmission source (THD or register), the bandwidth of the protection frame takes either startTxBW or bwProtTx.
assign bwProt           = (startTxFrameExGated) ? startTxBW : bwProtTx;

// Depending of the transmission source (THD or register), the duration of the protection frame takes either durControlFrm or protFrmDur.
assign protFrmDurInt    = (startTxFrameExGated) ? durControlFrm : protFrmDur;

// Depending of the transmission source (THD or register), the format Modulation of the protection frame
// takes either startTxFormatMod or formatModProtTx.
assign formatModProt    = (startTxFrameExGated) ? startTxFormatMod : formatModProtTx;

// Depending of the transmission source (THD or register), the preamble type of the protection frame
// takes either startTxPreType or preTypeProtTx.
assign preTypeProt      = (startTxFrameExGated) ? startTxPreType : preTypeProtTx;

// Depending of the transmission source (THD or register), the use of L-SIG duration for the protection frame
// takes either startTxLSTP or lstpProt.
assign lstpProtInt      = (startTxFrameExGated) ? startTxLSTP : lstpProt;

// Depending of the transmission source (THD or register), the use of Short Guard Interval for the protection frame
// takes either startTxShortGI or shortGIPT.
assign txShortGI        = (startTxFrameExGated) ? startTxShortGI : shortGIPT;


// Depending of the transmission source (THD or register), the use of FEC Coding for the protection frame
// takes either startTxfecCoding or fecCodingPT.
assign txFecCoding      = (startTxFrameExGated) ? startTxFecCoding : fecCodingPT;


always @*
begin
  if (macControllerTxFSMCs == TX_CFEND)
    txFormatMod = formatModProt; // In case of Protection, the CF-END is sent using the same format than the protection 
  else if (macControllerTxFSMCs == TX_PROT)
    txFormatMod = formatModProt;
  else
    txFormatMod = formatModTx;
end    

always @*
begin
  if ((macControllerTxFSMCs == TX_DATA) && (txFormatMod == VHT))
    txDisambiguityBitTxC = dataDisambiguity;
  else
    txDisambiguityBitTxC = 1'b0;
end    

////////////////////////////////////////////////////////////////////
////
//// MAC-PHY Interface
////
////////////////////////////////////////////////////////////////////
// Capture macPhyIfRxEnd_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPhyIfRxEnd <= 1'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macPhyIfRxEnd <= 1'b0; 
  else
  begin
    if (macPhyIfRxEnd_p)
      macPhyIfRxEnd <= 1'b1;
    else if (macPhyIfRxEnd && (macControllerTxFSMCs != PHY_ERROR))
      macPhyIfRxEnd <= 1'b0;
  end    
end

assign mpifKeepRFonTx = 1'b0; // $todo in case of RIFS (useRIFSTx)

assign startRxTxC_p = (((macControllerTxFSMCs == RX_RESP) && (macControllerTxFSMPs != RX_RESP)) ||
                       ((macControllerTxFSMCs == RX_PROT_RESP) && (macControllerTxFSMPs != RX_PROT_RESP)))? 1'b1 : 1'b0;

assign stopRxTxC_p  = (((macControllerTxFSMCs == TX_PROT)  && (macControllerTxFSMPs != TX_PROT)) ||
                       ((macControllerTxFSMCs == TX_DATA)  && (macControllerTxFSMPs != TX_DATA)) ||
                       ((macControllerTxFSMPs == RX_RESP)  && respTO_p) ||
                       ((macControllerTxFSMCs == TX_CFEND) && (macControllerTxFSMPs != TX_CFEND)) ||
                       ((macControllerTxFSMPs != IDLE) && macPhyIfRxErr_p)) ? 1'b1 : 1'b0;

////////////////////////////////////////////////////////////////////
////
//// L-SIG Length and Duration 
////
////////////////////////////////////////////////////////////////////
// L_LENGTH (legLengthComputed) and L_DATARATE determine the duration that non-HT STAs will not transmit, equal to the
// remaining duration of the HT PPDU or the L-SIG Duration when L-SIG TXOP protection is used as defined
// in 9.13.5, following the non-HT portion of the preamble of the HT-mixed format PPDU.
//
// The L_DATARATE parameter of the TXVECTOR shall be set to the value 6 Mb/s.
//
// A STA that is transmitting a PPDU with the FORMAT parameter of the TXVECTOR set to HT_MF, and that
// is not operating by the L-SIG TXOP protection rules described in 9.13.5 (lstp = 0) shall set the value of the L_LENGTH
// parameter to the value (in units of octets) given by Equation (9-1) :
//
// L_LENGTH = ((TXTIME - Signal Extension) - (aPreambleLength + aPLCPHeaderLength))*NOPS/aSymbolLength - (aPLCPServiceLength + aPLCPConvolutionalTailLength)/8
// 
// or
//
// L_LENGTH = [((TXTIME - Signal Extension) - 20)/4]*3 - 3
//
// A STA that is transmitting a PPDU with the FORMAT parameter of the TXVECTOR set to HT_MF, and that
// is not operating by the L-SIG TXOP protection rules described in 9.13.5 (lstp = 1) shall set the value of the L_LENGTH
// parameter to the value (in units of octets) given by Equation (9-1) :
//
// L_LENGTH = (lSIGDuration - signalExtension) * NOPS/aSymbolLength - (aPLCPServiceLength + aPLCPConvolutionalTailLength)/8 
//
// or
//
// L_LENGTH = [(lSIGDuration - signalExtension)/4] * 3 - 3
//
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    legLengthComputed <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
    legLengthComputed <= 16'b0;
  else
    if (useLSTP)
    begin
      if (lSIGDurationInt[1:0] != 2'b0)  // $todo As only legLengthComputed[11:0] is used, the following could be optimized
        // if lSIGDurationInt[1:0] !=0, the rounding is done by adding 3. So, the -3 disapear
        legLengthComputed <= {1'b0,lSIGDurationInt[15:2],1'b0} + {2'b0,lSIGDurationInt[15:2]}; 
      else  
        legLengthComputed <= {1'b0,lSIGDurationInt[15:2],1'b0} + {2'b0,lSIGDurationInt[15:2]} - 16'd3;
    end
    else
    begin
      if (txTimeInt[1:0] != 2'b0)
        // if txTimeInt[1:0] !=0, the rounding is done by adding 3. So, the -3 disapear
        legLengthComputed <= {1'b0,txTimeInt[15:2],1'b0} + {2'b0,txTimeInt[15:2]}; 
      else  
        legLengthComputed <= {1'b0,txTimeInt[15:2],1'b0} + {2'b0,txTimeInt[15:2]} - 16'd3;
    end
end

// Indicates that the current transmition uses L-SIG TXOP protection
assign useLSTP = ((((macControllerTxFSMCs == TX_PROT) && lstpProtInt && (formatModProt >= 3'd2)) || (macControllerTxFSMCs == TX_DATA) && lstp && (formatModTx >= 3'd2))) ? 1'b1 : 1'b0;

// txTimeInt is the result of (TXTIME - signalExtension - 20)
// It is used in the previous process to compute the L_LENGTH for the response
assign txTimeInt       = currentFrmDuration - {13'b0,signalExtension} - {9'b0,7'd20};

// lSIGDurationInt is the result of (lSIGDuration - signalExtension)
// It is used in the previous process to compute the L_LENGTH for the response
assign lSIGDurationInt = lSIGDuration - {13'b0,signalExtension};


// Under L-SIG TXOP Protection operation, the L-SIG Duration of the initial PPDU that establishes protection
// shall be:
// 
// L-SIG Duration = (TInit_PPDU - (aPreambleLength + aPLCPHeaderLength)) + SIFS + TRes_PPDU
// 
// When the initial PPDU that establishes protection requires no response (e.g., a CTS to self), the L-SIG Duration
// shall contain a value:
// 
// L-SIG Duration = (TInit_MACDur + TInit_PPDU - (aPreambleLength + aPLCPHeaderLength))
//
// Under L-SIG TXOP Protection operation, the L-SIG field with an HT-mixed format PHY preamble represents a duration value equivalent 
// (except in the case of the initial frame that establishes the TXOP, as described above) to the sum of:
// a) the value of Duration/ID field contained in the MAC header, and
// b) the duration remaining in the current packet after the L-SIG, which is equal to the duration of the
// current packet less (aPreambleLength + aPLCPHeaderLength).
// 
// L-SIG Duration = (T_MACDur + T_PPDU - (aPreambleLength + aPLCPHeaderLength))

always @ *
begin
  if (!txOpAcquired)
  begin
    if ((protType == SELF_CTS) || (protType == CTS_W_STA))
      lSIGDuration = durationTxC + ctsDuration - 16'd20;
    else if (protType != NO_PROT)
      lSIGDuration = ctsDuration  - 16'd20 + {8'd0,sifsA} + rtsDuration;
    else if (expectedAckCapt == 2'b00)
      lSIGDuration = durationTxC + dataDuration - 16'd20;
    else 
      lSIGDuration = dataDuration  - 16'd20 + {8'd0,sifsA} + ackDuration;
  end
  else
    lSIGDuration = durationTxC + currentFrmDuration - 16'd20;
end
assign signalExtension = 3'd0; //$todo.
 
////////////////////////////////////////////////////////////////////
////
//// Interrupt Generation
////
////////////////////////////////////////////////////////////////////

assign txopCompleteInt = ((macControllerTxFSMCs == TRIG_BACKOFF) && !hasTXOPLimitNull) ? 1'b1 : 1'b0;

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txopComplete <= 1'b0; 
  else if (macCoreClkSoftRst_n == 1'b0) // Synchronous Reset
    txopComplete <= 1'b0; 
  else
    txopComplete <= txopCompleteInt;
end


////////////////////////////////////////////////////////////////////
////
//// MOT
////
////////////////////////////////////////////////////////////////////


always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    extACMOT <= 21'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
    extACMOT <= {txOpLimit,5'b0}; 
  else
  begin
    // In case of TXOP Limit  != 0, if the FSM leaves the state CHECK_TXOP for TX_PROT or TX_DATA, the duration of the frame
    // exchange is removed from the extACMOT.
    if (!hasTXOPLimitNull && (macControllerTxFSMCs == CHECK_TXOP) && (macControllerTxFSMNs != CHECK_CFEND))
      extACMOT <= {5'b0,remainingTXOPDuration} - {5'b0,frmExDuration};
    // When the FSM is waiting in CHECK_CFEND, the extACMOT gets the remainingTXOPDuration.
    if (macControllerTxFSMCs == CHECK_CFEND)
      extACMOT <= {5'b0,remainingTXOPDuration};
  end    
end

assign acMOT = extACMOT[20:5];

////////////////////////////////////////////////////////////////////
////
//// Register Control
////
////////////////////////////////////////////////////////////////////
assign sendCFEndNowInValid = (sendCFEndNow && (macControllerTxFSMCs == TRIG_BACKOFF)) ? 1'b1 : 1'b0;
assign sendCFEndNowIn      = 1'b0;

assign startTxFrameExIn      = 1'b0;
assign startTxFrameExInValid = startTxFrameExGated && txDone_p;



////////////////////////////////////////////////////////////////////
////
//// Frame exchange duration computing part
////
////////////////////////////////////////////////////////////////////

/////////////////////////////
// TX TIME Calculator Control
/////////////////////////////


always @*
begin
  case (durationComputationFSMCs)
    DUR_RTS, DUR_CFEND  :  ppduLengthMCTx = 20'd20; 
               DUR_CTS  :  ppduLengthMCTx = 20'd14; 
              DUR_DATA  :  ppduLengthMCTx = frameLengthTx;
               DUR_TSF  :  ppduLengthMCTx = 20'd24;
               DUR_ACK  :  ppduLengthMCTx = (expectedAck[1]) ? 20'd32 : 20'd14;
               default  :  ppduLengthMCTx = 20'd14; 
  endcase    
end

always @*
begin
  case (durationComputationFSMCs)
     DUR_RTS, DUR_CTS  :  ppduPreTypeMCTx = (formatModProt >= 3'd2) ? formatModProt : (legRatePROT == 4'd0) ? 3'b01 : {2'b0,preTypeProt}; 
    DUR_DATA, DUR_TSF  :  ppduPreTypeMCTx = (formatModTx >= 3'd2)   ? formatModTx   : (legRateData == 4'd0) ? 3'b01 : {2'b0,preTypeTx}; 
               DUR_ACK :  ppduPreTypeMCTx =  respIsHT               ? (formatModTx == 3'd4) ? 3'd4 :3'd2  : (legRateRESP == 4'd0) ? 3'b01 : {2'b0,preTypeTx};
            DUR_CFEND  :  ppduPreTypeMCTx = 3'b0; 
     default           :  ppduPreTypeMCTx = 3'b0; 
  endcase    
end

always @*
begin
  case (durationComputationFSMCs)
           DUR_CFEND  :  ppduBWMCTx = txOpBW; 
    DUR_RTS, DUR_CTS  :  ppduBWMCTx = currentBWProt; 
   DUR_DATA, DUR_TSF  :  ppduBWMCTx = currentBWPPDU;
             DUR_ACK  :  ppduBWMCTx = currentBWPPDU;
             default  :  ppduBWMCTx = 2'd0; 
  endcase    
end    

always @*
begin
  case (durationComputationFSMCs)
           DUR_CFEND  :  ppduShortGIMCTx = txShortGI; 
    DUR_RTS, DUR_CTS  :  ppduShortGIMCTx = 1'd0; 
   DUR_DATA, DUR_TSF  :  ppduShortGIMCTx = txShortGI;
             DUR_ACK  :  ppduShortGIMCTx = txShortGI;
             default  :  ppduShortGIMCTx = 1'd0; 
  endcase    
end    

assign ppduNumExtnSSMCTx = numExtnSSPT;
assign ppduSTBCMCTx      = stbcPT;

always @*
begin
  case (durationComputationFSMCs)
     DUR_RTS, DUR_CTS :  ppduMCSIndexMCTx = (formatModProt >= 3'd2) ? mcsPROT : {3'b0,legRatePROT}; 
    DUR_DATA, DUR_TSF :  ppduMCSIndexMCTx = (formatModTx >= 3'd2)   ? mcsData : {3'b0,legRateData}; 
              DUR_ACK :  ppduMCSIndexMCTx = respIsHT                ? mcsRESP : {3'b0,legRateRESP};
            DUR_CFEND :  ppduMCSIndexMCTx = {3'b0,legRateCFEND};
     default          :  ppduMCSIndexMCTx = 7'b0; 
  endcase    
end

// Each time the durationComputationFSM moves to another state except to IDLE and DUR_COMPLETED, the startComputationMCTx_p is generated and it trigs the TX Time Calculation 
// unit for a new computing.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    startComputationMCTx_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    startComputationMCTx_p <= 1'b0; 
  else if ((durationComputationFSMNs != durationComputationFSMCs) && (durationComputationFSMNs != DUR_IDLE) && (durationComputationFSMNs != DUR_COMPLETED))
    startComputationMCTx_p <= 1'b1;
  else
    startComputationMCTx_p <= 1'b0;
end


// Delay the timeOnAirValidMC signal of one clock cycle
// This signal is used to detect the rising edge and create the timeOnAirDone_p pulse.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    timeOnAirValidMC_ff1 <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    timeOnAirValidMC_ff1 <= 1'b0; 
  else
    timeOnAirValidMC_ff1 <= timeOnAirValidMC; 
end

// Generation of timeOnAirDone_p pulse which indicated the completion of the TX Tim computing.
assign timeOnAirDone_p = timeOnAirValidMC && !timeOnAirValidMC_ff1;

//////////////////////////////////////
// Frame exchanges duration computing
//////////////////////////////////////

// durationComputationFSM FSM Current State Logic 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    durationComputationFSMCs <= DUR_IDLE;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE)) // Synchronous Reset
    durationComputationFSMCs <= DUR_IDLE; 
  else
    durationComputationFSMCs <= durationComputationFSMNs; 
end


// durationComputationFSM FSM Next State Logic.
always @* 
begin
  case (durationComputationFSMCs)

    DUR_IDLE:
      //$fsm_s In DUR_IDLE state, the state machine waits for a trigger 
      // which will launch the computing.
      if (macControllerTxFSMCs == COMP_DURATION)
      begin
        if (includeTSF == 1'b1)
          //$fsm_t If includeTSF is set indicating that the transmitted frame include a TSF, 
          //, the state machine goes to DUR_TSF state.
          durationComputationFSMNs = DUR_TSF;
        else if (!txOpAcquired && ((protType == RTSCTS_W_STA) || (protType == RTSCTS_W_AP) || (protType == RTS_DUALCTS)))
          //$fsm_t When the macControllerTxFSM moves to COMP_DURATION, a TXOP has not been acquired yet and the protection type 
          // requires a RTS frame, the state machine goes to DUR_RTS state.
          durationComputationFSMNs = DUR_RTS; 
        else if (!txOpAcquired && ((protType == SELF_CTS) || (protType == CTS_W_STA))) 
          //$fsm_t When the macControllerTxFSM moves to COMP_DURATION, a TXOP has not been acquired yet and the protection type 
          // does not requires a RTS frame but needs a CTS, the state machine goes to DUR_CTS state.
          durationComputationFSMNs = DUR_CTS; 
        else
          //$fsm_t When the macControllerTxFSM moves to COMP_DURATION and the no protection frame is required, 
          //the state machine goes to DUR_DATA state.
          durationComputationFSMNs = DUR_DATA; 
      end
      else if ((macControllerTxFSMCs != CHECK_CFEND) && (macControllerTxFSMNs == CHECK_CFEND))
        //$fsm_t When the macControllerTxFSM moves to CHECK_CFEND and the no protection frame is required, 
        //the state machine goes to DUR_CFEND state.
        durationComputationFSMNs = DUR_CFEND; 
      else
        //$fsm_t While macControllerTxFSM is not in COMP_DURATION, the state machine stays in DUR_IDLE state.
        durationComputationFSMNs = DUR_IDLE;
          
    DUR_RTS:
      //$fsm_s In DUR_RTS state, the state machine waits for the end of computation indication from the TX Time Calculator unit.
      // In this state, the duration of the RTS frame is computed.
      if (timeOnAirDone_p)
        //$fsm_t When timeOnAirDone_p is received indicating the end of the RTS computing , the state machine goes to DUR_CTS state.
        durationComputationFSMNs = DUR_CTS;
      else
        //$fsm_t While timeOnAirDone_p is not received, the state machine stays in DUR_RTS state.
        durationComputationFSMNs = DUR_RTS;

    DUR_CTS:
      //$fsm_s In DUR_CTS state, the state machine waits for the end of computation indication from the TX Time Calculator unit. 
      // In this state, the duration of the CTS frame is computed.
      if (timeOnAirDone_p) 
        //$fsm_t When timeOnAirDone_p is received indicating the end of the CTS computing , the state machine goes to DUR_DATA state.
        durationComputationFSMNs = DUR_DATA;
      else
        //$fsm_t While timeOnAirDone_p is not received, the state machine stays in DUR_CTS state.
        durationComputationFSMNs = DUR_CTS;

    DUR_TSF:
      //$fsm_s In DUR_TSF state, the state machine waits for the end of computation indication from the TX Time Calculator unit. 
      //In this state, the duration until the TSF (from the preamble to the first bit of TSF) is computed.
      if (timeOnAirDone_p)
      begin
          //$fsm_t When timeOnAirDone_p is received indicating the end of the TSF computing, 
          //the state machine goes to DUR_DATA state.
          durationComputationFSMNs = DUR_DATA; 
      end
      else
        //$fsm_t While timeOnAirDone_p is not received, the state machine stays in DUR_TSF state.
        durationComputationFSMNs = DUR_TSF;

    DUR_DATA:
      //$fsm_s In DUR_DATA state, the state machine waits for the end of computation indication from the TX Time Calculator unit. 
      //In this state, the duration of the DATA frame is computed.
      if (timeOnAirDone_p)
      begin
        if (expectedAckCapt == 2'b00)
          //$fsm_t When timeOnAirDone_p is received indicating the end of the DATA computing and no ACK is expected (expectedAckCapt == 2'b00), 
          //, the state machine goes to DUR_COMPLETED state.
          durationComputationFSMNs = DUR_COMPLETED; 
        else  
          //$fsm_t When timeOnAirDone_p is received indicating the end of the DATA computing  and an ACK is expected (expectedAckCapt != 2'b00), 
          //the state machine goes to DUR_ACK state.
          durationComputationFSMNs = DUR_ACK; 
      end
      else
        //$fsm_t While timeOnAirDone_p is not received, the state machine stays in DUR_DATA state.
        durationComputationFSMNs = DUR_DATA;


    DUR_ACK:
      //$fsm_s In DUR_ACK state, the state machine waits for the end of computation indication from the TX Time Calculator unit. 
      //In this state, the duration of the ACK frame is computed.
      if (timeOnAirDone_p) 
        //$fsm_t When timeOnAirDone_p is received indicating the end of the ACK computing , the state machine goes to DUR_COMPLETED state.
        durationComputationFSMNs = DUR_COMPLETED; 
      else
        //$fsm_t While timeOnAirDone_p is not received, the state machine stays in DUR_ACK state.
        durationComputationFSMNs = DUR_ACK;


    DUR_CFEND:
      //$fsm_s In DUR_CFEND state, the state machine waits for the end of computation indication from the TX Time Calculator unit. 
      //In this state, the duration of the CF-END frame is computed.
      if (timeOnAirDone_p) 
        //$fsm_t When timeOnAirDone_p is received indicating the end of the CF-END computing , the state machine goes to DUR_COMPLETED state.
        durationComputationFSMNs = DUR_COMPLETED; 
      else
        //$fsm_t While timeOnAirDone_p is not received, the state machine stays in DUR_CFEND state.
        durationComputationFSMNs = DUR_CFEND;

    DUR_COMPLETED:
      //$fsm_s In DUR_COMPLETED state, the state machine finalizes the computing of the duration before checking the TXOP.
      
      //$fsm_t the FSM moves to DUR_IDLE
      durationComputationFSMNs = DUR_IDLE; 


    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
     default:   
        durationComputationFSMNs = DUR_IDLE;  
    // pragma coverage block = on 
  endcase
end

// Generate a pulse and the frame exchange computation is completed (i.e. when the durationComputationFSM moves back to IDLE.)
assign frmExDurationDone_p = (durationComputationFSMCs == DUR_COMPLETED) ? 1'b1 : 1'b0;

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    frmExDurationDone_CheckCFEnd <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    frmExDurationDone_CheckCFEnd <= 1'b0;
  else
  begin
    if((frmExDurationDone_p == 1'b1) && (macControllerTxFSMCs == CHECK_CFEND))
      frmExDurationDone_CheckCFEnd <= 1'b1;
    else if((macControllerTxFSMCs == CHECK_CFEND) && (macControllerTxFSMNs != CHECK_CFEND))
      frmExDurationDone_CheckCFEnd <= 1'b0;
  end
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    compDurDelayDone_p <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (durationComputationFSMCs != DUR_COMPLETED))  // Synchronous Reset
    compDurDelayDone_p <= 1'b0;
  else
    compDurDelayDone_p <= ~compDurDelayDone_p;
end


// Frame Exchange duration 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    frmExDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || 
           (macControllerTxFSMCs == IDLE) || 
           ((macControllerTxFSMCs == STATUS_UPDATE) && (macControllerTxFSMNs != STATUS_UPDATE)) ||
           ((macControllerTxFSMCs == WAIT_RX_PROT_RESP_END) && (macControllerTxFSMNs == COMP_DURATION)))  // Synchronous Reset // keep the value until the end of STATUS_UPDATE for the signal frmExDurBiggerMaxAllDur which is used in retryLimitReached_p 
    frmExDuration <= 16'b0;
  else
    if ((timeOnAirDone_p) && (durationComputationFSMCs != DUR_IDLE) && (durationComputationFSMCs != DUR_COMPLETED) && (durationComputationFSMCs != DUR_CFEND) && (durationComputationFSMCs != DUR_TSF))
    begin
      if (durationComputationFSMNs == DUR_COMPLETED)
        frmExDuration <= frmExDuration + timeOnAirMC; 
      else  
        frmExDuration <= frmExDuration + timeOnAirMC + {8'd0,sifsDuration};
    end
end

// RTS frame duration 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rtsDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE) || (macControllerTxFSMCs == STATUS_UPDATE))  // Synchronous Reset
    rtsDuration <= 16'b0;
  else
    if ((timeOnAirDone_p) && (durationComputationFSMCs == DUR_RTS))
      rtsDuration <= timeOnAirMC; 
end

// CTS frame duration 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    ctsDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE) || (macControllerTxFSMCs == STATUS_UPDATE))  // Synchronous Reset
    ctsDuration <= 16'b0;
  else
    if ((timeOnAirDone_p) && (durationComputationFSMCs == DUR_CTS))
      ctsDuration <= timeOnAirMC; 
end

//Protection exchange Duration
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    ProtDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE) || (macControllerTxFSMCs == STATUS_UPDATE))  // Synchronous Reset
    ProtDuration <= 16'b0;
  else
  begin
    if ((timeOnAirDone_p) && (durationComputationFSMCs == DUR_DATA))
    begin
      if( (protType == SELF_CTS) || (protType == CTS_W_STA) )
        ProtDuration <= ctsDuration + {8'd0,sifsDuration}; 
      else if( (protType == RTSCTS_W_STA) || (protType == RTSCTS_W_AP) )
        ProtDuration <= rtsDuration + {8'd0,sifsDuration} + ctsDuration; 
      else if( (protType == RTS_DUALCTS) )
        ProtDuration <= rtsDuration + ({8'd0,sifsDuration} + ctsDuration) << 2; 
      else
        ProtDuration <= 16'b0;
    end
  end
end

// ACK frame duration 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    ackDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE) || (macControllerTxFSMCs == STATUS_UPDATE))  // Synchronous Reset
    ackDuration <= 16'b0;
  else
    if ((timeOnAirDone_p) && (durationComputationFSMCs == DUR_ACK))
      ackDuration <= timeOnAirMC; 
end

// DATA frame duration 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    dataDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE) || (macControllerTxFSMCs == STATUS_UPDATE))  // Synchronous Reset
    dataDuration <= 16'b0;
  else
    if ((timeOnAirDone_p) && (durationComputationFSMCs == DUR_DATA))
      dataDuration <= timeOnAirMC; 
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    dataDisambiguity <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE) || (macControllerTxFSMCs == STATUS_UPDATE))  // Synchronous Reset
    dataDisambiguity <= 1'b0;
  else
    if ((timeOnAirDone_p) && (durationComputationFSMCs == DUR_DATA))
      dataDisambiguity <= disambiguityMC; 
end

// TSF frame duration 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    tsfDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE) || (macControllerTxFSMCs == STATUS_UPDATE))  // Synchronous Reset
    tsfDuration <= 16'b0;
  else
    if ((timeOnAirDone_p) && (durationComputationFSMCs == DUR_TSF))
      tsfDuration <= timeOnAirMC; 
end

// CF-END frame duration 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    cfendDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE) || (macControllerTxFSMCs == STATUS_UPDATE))  // Synchronous Reset
    cfendDuration <= 16'b0;
  else
    if ((timeOnAirDone_p) && (durationComputationFSMCs == DUR_CFEND))
      cfendDuration <= timeOnAirMC; 
end

//////////////////////////////////////
// Expected Response Type
//////////////////////////////////////

// determine if the Prot response will be HT or NON-HT.
// A control response frame must be carried in an HT PPDU if it responds to a frame that:
//  1.	Was an RTS carried in an HT-PPDU
//  2.	Used STBC, and Dual CTS Protection is enabled
// Else, it must be carried in a non-HT PPDU.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    respProtIsHT <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
     respProtIsHT <= 1'b0;
  else
    if (((((protType == RTSCTS_W_STA) || (protType == RTSCTS_W_AP)) &&  ((txFormatMod == HT_MM) || (txFormatMod == HT_GF) || (txFormatMod == VHT))) || 
        (protType == RTS_DUALCTS)) && (macControllerTxFSMNs == TX_PROT))
      respProtIsHT <= 1'b1;
    else
      respProtIsHT <= 1'b0;
end

// determine if the response will be HT or NON-HT.
// A response frame must be carried in an HT PPDU if it responds to a frame that:
//  1.  Contains an L-SIG Duration value (lstp = 1)
//  2.	Contained TRQ = 1 and NDP announcement = 0 //$todo. Not supported yet.
// Else, it must be carried in a non-HT PPDU.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    respIsHT <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
     respIsHT <= 1'b0;
  else
    // response if HT only if lstp is set and the transmitted frame is HT or VHT
    if (lstp && (formatModTx == 3'd2))
      respIsHT <= 1'b1;
    else
      respIsHT <= 1'b0;
end

////////////////////////////////////////////////////////////////////
////
//// ACK and CTS TimeOut
////
////////////////////////////////////////////////////////////////////

// TimeOut counter shared for ACK and CTS TimeOut.
// The timeout timer is loaded with the SIFS + SLOT Time + RXStartDelay when the transmission is requested.
// When txDone_p is received, indicating the end of the transmission ($todo to be confirmed) 
// and a response is expected, the down counter is started.
// The down counter is decremented every us (on tick1us_p)
// When a CTS, a ACK or a BA is received, the down counter is stopped
// If the down counter reaches 0, it generates the respTO_p pulse which indicates a response time out.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    timeOutCnt      <= 10'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
    timeOutCnt      <= 10'b0;
  else
  begin
    if (txDone_p && ((macControllerTxFSMCs == TX_PROT) || (macControllerTxFSMCs == TX_DATA)))
      // The timeout timer is loaded with the SIFS + SLOT Time + RXStartDelay when the transmission is requested.
      timeOutCnt <= {2'b0,sifsDuration} + {2'b0,slotTime} + {2'b0,phyRxStartDelay}; 
    else if (timeOutStarted && tick1us_p)
      // The down counter is decremented every us (on tick1us_p)
      timeOutCnt <= timeOutCnt - 10'd1;
  end
end

// TimeOut counter shared for ACK and CTS TimeOut.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    timeOutStarted  <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0))  // Synchronous Reset
    timeOutStarted  <= 1'b0;
  else
  begin
    if (((macControllerTxFSMCs == RX_PROT_RESP) && ctsRcved_p) || ((macControllerTxFSMCs == RX_RESP) && (ackRcved_p || baRcved_p)))
      // When a CTS, a ACK or a BA is received, the down counter is stopped
      timeOutStarted <= 1'b0;
    else if (txDone_p && ((macControllerTxFSMCs == TX_PROT) || (macControllerTxFSMCs == TX_DATA)))
      // When txDone_p is received, indicating the end of the transmission ($todo to be confirmed) 
      // and a response is expected, the down counter is started.
      timeOutStarted <= 1'b1;
    else if (macPhyIfRxStart_p || stopRxTxC_p)
    // If the down counter is started and a new reception is launched or the current reception is aborted, the down counter is stopped.
      timeOutStarted  <= 1'b0;
    else if (timeOutStarted && (timeOutCnt == 10'd0))
    // If the down counter is started and reaches 0, it generates the respTO_p pulse which indicates a response time out.
      timeOutStarted  <= 1'b0;
    else if ((macControllerTxFSMCs != RX_PROT_RESP) && (macControllerTxFSMCs != RX_RESP))  
      timeOutStarted <= 1'b0;
  end
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    respTO_p  <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
    respTO_p  <= 1'b0;
  else
    if (timeOutStarted && (timeOutCnt == 10'd0))
      respTO_p  <= 1'b1;
    else  
      respTO_p  <= 1'b0;
end    

// Assign phyRxStartDelay duration based on the expected preamble time for the response frame.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    phyRxStartDelay      <= 8'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerTxFSMCs == IDLE))  // Synchronous Reset
    phyRxStartDelay      <= 8'b0;
  else
  begin
    if ((macControllerTxFSMCs == TX_PROT) || (macControllerTxFSMCs == TX_DATA))
    begin
      if (txLegRateTxC < 4'd4)
        phyRxStartDelay <= rxStartDelayLong;
      else    
        phyRxStartDelay <= rxStartDelayOFDM;
    end
  end
end


////////////////////////////////////////////////////////////////////////////////
// Debug Interface
////////////////////////////////////////////////////////////////////////////////
                                   
assign debugPortMACControllerTx = {correctRcved_p,
                                   txAMPDU,
                                   skipBAR,
                                   nextIsBAR,
                                   txOpAcquired,
                                   txDMADataPending,
                                   dontTouchDur,
                                   hasTXOPLimitNull,
                                   frmExDurBiggerMaxAllDur,
                                   frmExFitInTXOP,
                                   remainingTXOP,
                                   useImpQI,
                                   macControllerTxFSMCs};  //4


assign debugPortAMPDUMC = {txAMPDU,
                           skipBAR,
                           correctRcved_p,
                           mpduSuccess_p,
                           mpduFailed_p,
                           retryFrame_p,
                           retryLimitReached_p};
                            
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
// Disable coverage on the default state because it cannot be reached.
// pragma coverage block = off 


// macControllerTxFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (macControllerTxFSMCs)
                 IDLE  :  macControllerTxFSMCs_str = {"IDLE                 "};
             WAIT_DMA  :  macControllerTxFSMCs_str = {"WAIT_DMA             "};
 DROPBW_LENGTH_UPDATE  :  macControllerTxFSMCs_str = {"DROPBW_LENGTH_UPDATE "};
        COMP_DURATION  :  macControllerTxFSMCs_str = {"COMP_DURATION        "};
           CHECK_TXOP  :  macControllerTxFSMCs_str = {"CHECK_TXOP           "};
              TX_PROT  :  macControllerTxFSMCs_str = {"TX_PROT              "};
         RX_PROT_RESP  :  macControllerTxFSMCs_str = {"RX_PROT_RESP         "};
WAIT_RX_PROT_RESP_END  :  macControllerTxFSMCs_str = {"WAIT_RX_PROT_RESP_END"};
              TX_DATA  :  macControllerTxFSMCs_str = {"TX_DATA              "};
              RX_RESP  :  macControllerTxFSMCs_str = {"RX_RESP              "};
     WAIT_RX_RESP_END  :  macControllerTxFSMCs_str = {"WAIT_RX_RESP_END     "};
        STATUS_UPDATE  :  macControllerTxFSMCs_str = {"STATUS_UPDATE        "};
          CHECK_CFEND  :  macControllerTxFSMCs_str = {"CHECK_CFEND          "};
             TX_CFEND  :  macControllerTxFSMCs_str = {"TX_CFEND             "};
         TRIG_BACKOFF  :  macControllerTxFSMCs_str = {"TRIG_BACKOFF         "};
            SKIP_MPDU  :  macControllerTxFSMCs_str = {"SKIP_MPDU            "};
            PHY_ERROR  :  macControllerTxFSMCs_str = {"PHY_ERROR            "};
              default  :  macControllerTxFSMCs_str = {"XXX                  "};
   endcase
end

// durationComputationFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (durationComputationFSMCs)
             DUR_IDLE  :  durationComputationFSMCs_str = {"DUR_IDLE     "};
              DUR_RTS  :  durationComputationFSMCs_str = {"DUR_RTS      "};
              DUR_CTS  :  durationComputationFSMCs_str = {"DUR_CTS      "};
             DUR_DATA  :  durationComputationFSMCs_str = {"DUR_DATA     "};
              DUR_ACK  :  durationComputationFSMCs_str = {"DUR_ACK      "};
            DUR_CFEND  :  durationComputationFSMCs_str = {"DUR_CFEND    "};
              DUR_TSF  :  durationComputationFSMCs_str = {"DUR_TSF      "};
        DUR_COMPLETED  :  durationComputationFSMCs_str = {"DUR_COMPLETED"};
              default  :  durationComputationFSMCs_str = {"XXX          "};
   endcase
end

// protType displayed in a string to easy simulation and debug
always @*
begin
  case (protType)
              NO_PROT  : protType_str = {"NO_PROT     "};
             SELF_CTS  : protType_str = {"SELF_CTS    "};
         RTSCTS_W_STA  : protType_str = {"RTSCTS_W_STA"};
          RTSCTS_W_AP  : protType_str = {"RTSCTS_W_AP "};
          RTS_DUALCTS  : protType_str = {"RTS_DUALCTS "};
            CTS_W_STA  : protType_str = {"CTS_W_STA   "};
              default  : protType_str = {"XXX         "};
   endcase
end

// expectedAckCapt displayed in a string to easy simulation and debug
always @*
begin
  case (expectedAckCapt)
            0  : expectedAck_str = {"No ACK       "};
            1  : expectedAck_str = {"Normal ACK   "};
            2  : expectedAck_str = {"BA           "};
            3  : expectedAck_str = {"Compressed BA"};
      default  : expectedAck_str = {"XXX          "};
   endcase
end

// txDmaState displayed in a string to easy simulation and debug
always @*
begin
  case (txDmaState)
         DMA_HALTED  : txDmaState_str = {"DMA_HALTED "};
        DMA_PASSIVE  : txDmaState_str = {"DMA_PASSIVE"};
         DMA_ACTIVE  : txDmaState_str = {"DMA_ACTIVE "};
           DMA_DEAD  : txDmaState_str = {"DMA_DEAD   "};
   endcase
end

// txOpBW displayed in a string to easy simulation and debug
always @*
begin
  case (txOpBW)
         0  : txOpBW_str = {"20 MHz"};
         1  : txOpBW_str = {"40 MHz"};
         2  : txOpBW_str = {"80 MHz"};
         3  : txOpBW_str = {"160 MHz"};
   endcase
end

// Retry Limit Type displayed in a string to easy simulation and debug
assign retryLimitType_str = retryType ? {"Long Retry Limit"} : {"Short Retry Limit"};

// pragma coverage block = on 
`endif // RW_SIMU_ON


`ifdef RW_ASSERT_ON

// Assertion Definitions
///////////////////////////

//$rw_sva Checks if the MPDU retry limit has not been already reached before starting the transmission.
property retryMPDUlimitCheck_prop;
@(posedge macCoreClk)
    ((macControllerTxFSMCs == WAIT_DMA) && (txParameterPTReadyInt)) |=>  retryLimit >= numMPDURetriesTPC;
endproperty
retryMPDUlimitCheck: assert property (retryMPDUlimitCheck_prop); 

//$rw_sva Checks if the RTS retry limit has not been already reached before starting the transmission.
property retryRTSlimitCheck_prop;
@(posedge macCoreClk)
    ((macControllerTxFSMCs == WAIT_DMA) && (txParameterPTReadyInt)) |=>  shortRetryLimit >= numRTSRetriesTPC;
endproperty
retryRTSlimitCheck: assert property (retryRTSlimitCheck_prop); 

integer nSIFS_prot;
integer nSIFS_ack;
assign nSIFS_prot = ((protType == NO_PROT) || txOpAcquired) ? 0 : ((protType == CTS_W_STA) || (protType == SELF_CTS)) ? 1 : 2;
assign nSIFS_ack  = (expectedAckCapt == 2'b00) ? 0 : 1;

//$rw_sva Checks if the computed frame exchange duration is correct
property frmExchangeDurationCheck_prop;
@(posedge macCoreClk)
    ((frmExDurationDone_p && !updateDurationAfterDynBW) && !dontTouchDur && (txOpLimit === 0)) |=> (frmExDuration == rtsDuration + ctsDuration + dataDuration + ackDuration + (nSIFS_prot+nSIFS_ack)*sifsDuration);
endproperty
frmExchangeDurationCheck: assert property (frmExchangeDurationCheck_prop); 


//$rw_sva Checks if the computed frame exchange duration does not cross the Quiet Interval
property frmExchangeQICrossingCheck_prop;
@(posedge macCoreClk)
    ((macControllerTxFSMCs != IDLE) && (startTx_p)) |=> ({impQICnt,5'b11111} >= {5'b0,durationTxC});
endproperty
frmExchangeQICrossingCheck: assert property (frmExchangeQICrossingCheck_prop); 


//$rw_sva Checks if the computed frame exchange duration does not cross the Quiet Interval
property fsmMovesToTrigBackoff_prop;
@(posedge macCoreClk)
    ((macControllerTxFSMNs != macControllerTxFSMCs) && (macControllerTxFSMCs == STATUS_UPDATE) && !txOpAcquired && !skipBAR) |=> (macControllerTxFSMCs == TRIG_BACKOFF);
endproperty
fsmMovesToTrigBackoff: assert property (fsmMovesToTrigBackoff_prop); 

//$rw_sva Check if when the clearSetsTxC_p one cycle after the ignoreTxParameterPTReady is set
property ignoreTxParameterPTReadyRaise_prop;
@(posedge macCoreClk)
  disable iff ((macCoreClkSoftRst_n) || (macCoreClkHardRst_n)) 
 (clearSets_p) |=> (ignoreTxParameterPTReady);
endproperty
ignoreTxParameterPTReadyRaise: assert property (ignoreTxParameterPTReadyRaise_prop);

//$rw_sva Check if when one cycle after macControllerTx going out of IDLE or dma going to ACTIVE then ignoreTxParameterPTReady should be cleared
property ignoreTxParameterPTReadyFall_prop;
@(posedge macCoreClk)
  disable iff ((macCoreClkSoftRst_n) || (macCoreClkHardRst_n)) 
 (((!txDmaActiveDly) && (txDmaActive)) || ((macControllerTxFSMCs == IDLE) && (macControllerTxFSMNs != IDLE))) |=> (!ignoreTxParameterPTReady);
endproperty
ignoreTxParameterPTReadyFall: assert property (ignoreTxParameterPTReadyFall_prop);

// Cover Points Definitions
///////////////////////////

//$rw_sva This cover point checks if we have successfully transmitted an RTS Frame
countRTSSuccess: cover property (@(posedge macCoreClk) (rtsSuccess_p));

//$rw_sva This cover point checks if we have unsuccessfully transmitted an RTS Frame due to FCS error
countRTSFailedDuetoFCS: cover property (@(posedge macCoreClk) (rtsFailed_p && (timeOutCnt >= 0)));

//$rw_sva This cover point checks if we have unsuccessfully transmitted an RTS Frame due to CTS TimeOut
countRTSFailedDuetoTO: cover property (@(posedge macCoreClk) (rtsFailed_p && (timeOutCnt == 0)));

//$rw_sva This cover point checks if we have unsuccessfully transmitted a MPDU due to FCS error
countMPDUFailedDuetoFCS: cover property (@(posedge macCoreClk) (mpduFailed_p && (timeOutCnt >= 0)));

//$rw_sva This cover point checks if we have unsuccessfully transmitted a MPDU due to ACK TimeOut
countMPDUFailedDuetoTO: cover property (@(posedge macCoreClk) (mpduFailed_p && (timeOutCnt == 0)));

//$rw_sva This cover point checks if we have unsuccessfully transmitted a MPDU due to Quiet Interval Crossing
countMPDUFailedDuetoQICrossing: cover property (@(posedge macCoreClk) (retryFrame_p && ({6'b0,frmExDuration} > {1'b0,impQICnt,5'b0})));

//$rw_sva This cover point checks if we have successfully transmitted a MPDU
counMPDUSuccess: cover property (@(posedge macCoreClk) (mpduSuccess_p));

//$rw_sva This cover point checks if we have requested a retry of an MPDU
countRetryFrame: cover property (@(posedge macCoreClk) (retryFrame_p));

//$rw_sva This cover point checks if we have reached the retry limit of RTS
countRTSRetryLimitReached: cover property (@(posedge macCoreClk) ((numRTSRetries == shortRetryLimit) && retryLimitReached_p));

//$rw_sva This cover point checks if we have reached the retry limit of MPDU
countMPDURetryLimitReached: cover property (@(posedge macCoreClk) ((numMPDURetries == retryLimit) && retryLimitReached_p));

//$rw_sva This cover point checks if a RTS/CTS protection is required
countRTSCTSProtection: cover property (@(posedge frmExDurationDone_p) ((protType == RTSCTS_W_STA) || (protType == RTSCTS_W_STA)));

//$rw_sva This cover point checks if a RTS/DualCTS protection is required
countRTSDualCTSProtection: cover property (@(posedge frmExDurationDone_p) (protType == RTS_DUALCTS));

//$rw_sva This cover point checks if a RTS/DualCTS protection is required
countSTBCTxData: cover property (@(posedge sendData_p) (txSTBCTxC == 1));

//$rw_sva This cover point checks if no protection is required
countNoProtection: cover property (@(posedge frmExDurationDone_p) (protType == NO_PROT));

//$rw_sva This cover point checks if a Self-CTS or CTS With STA protection is required
countCTSProtection: cover property (@(posedge frmExDurationDone_p) ((protType == SELF_CTS) || (protType == CTS_W_STA)));

//$rw_sva This cover point checks a frame exchange duration bigger than the TXOPLimit
countFrmExDurationLongerThanTXOPLimit: cover property (@(posedge frmExDurationDone_p) ({6'b0,frmExDuration} > {1'b0,txOpLimit,5'b0}));

//$rw_sva This cover point checks if a software linked RTS has been sent
countSWLinkedRTS: cover property (@(posedge txDone_p) (sentRTS));

//$rw_sva This cover point checks if a software linked BAReq has been sent
countSWLinkedBAReq: cover property (@(posedge txDone_p) (sentBAReq));

//$rw_sva This cover point checks if a software linked CFEND has been sent
countSWLinkedCFEND: cover property (@(posedge txDone_p) (sentCFEND));

//$rw_sva This cover point checks if a MPDU has been skipped
countSkipMPDU: cover property (@(posedge skipMPDU_p) (1));

//$rw_sva This cover point checks if AMPDU frames have been transmitted
countAMPDUTransmitted: cover property (@(posedge txDone_p) (aMPDU));


`endif // RW_ASSERT_ON



endmodule