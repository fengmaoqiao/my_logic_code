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
// Description      : Top level of macController module
//                    
// Simulation Notes : 
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
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////


module macController( 
          //$port_g Clock and Reset interface
          input  wire         macCoreClk,            // MAC Core Transmit Clock
          input  wire         macCoreClkHardRst_n,   // Hard Reset of the MAC Core Clock domain 
                                                     // active low
          input  wire         macCoreClkSoftRst_n,   // Soft Reset of the MAC Core Clock domain 
                                                     // active low
          output wire         macCoreTxClkEn,        // Enable the MAC Core TX Clock.
          
          //$port_g Interface with the DMA Engine
          input  wire         statusUpdated_p,       // Indication from the DMA that status have been updated.
          output wire         updateDMAStatus_p,     // trigs the DMA Status update.
          output wire         swRTS_p,               // Asserted high if the current transmitted packet is a
                                                     // RTS frame prepared by SW
          output wire         txMpduDone_p,          // Asserted high after every transmission of MPDU in an 
                                                     // AMPDU frame
          output wire         ampduFrm_p,            // Asserted high if the transmitted packet was an AMPDU
                                                     // frame
          output wire         retryFrame_p,          // If the transmitted frame has to be retried then this
                                                     // signal is asserted.
          output wire         mpduSuccess_p,         // If the transmitted frame was successful. Not asserted
                                                     // for RTS frames
          output wire         mpduFailed_p,          // If the transmitted frame was not successful. Not asserted
                                                     // if the RTS frame failed
          output wire         rtsFailed_p,           // If the transmitted frame was a RTS frame and did not 
                                                     // receive a CTS frame within the CTS timeout
          output wire         rtsSuccess_p,          // If the transmitted frame was a RTS frame and successfully
                                                     // received a CTS in reponse.
          output wire         retryLimitReached_p,   // If the transmitted frame was not successful and has reached  
                                                     // the retry limit.Is asserted for both RTS and other MPDU's    
          output wire   [1:0] transmissionBW,        // Indicates whether the frame was transmitted with 20MHz, 40MHz, 80MHz or 160MHz BW
          output wire   [3:0] whichDescriptorSW,     // Indicates the value of the whichDescriptorSW field for Status in THD
          output wire   [7:0] numMPDURetries,        // Indicates the number of retries for this MPDU. Valid when 
                                                     // rtsFailed_p rtsSuccess_p mpduSuccess_p mpduFailed_p or 
                                                     // retryLimitReached 
          output wire   [7:0] numRTSRetries,         // Indicates the number of retries for this RTS. Valid when 
                                                     // rtsFailed_p rtsSuccess_p mpduSuccess_p mpduFailed_p or 
                                                     // retryLimitReached 
          output wire  [31:0] mediumTimeUsed,        // Indicates the medium Time Used for current transmission
                                                     // Valid when DMA status is being updated
          input  wire         rxFrmDiscard,          // Discard current frame

          //$port_g Interface with the Tx Parameters Cache
          input  wire         txParameterHDReady_p,    // Indicates that the Header Descriptor fields are usable 
          input  wire         txParameterPTReady_p,    // Indicates that the Policy Table fields are usable
          input  wire         txParameterNextPTReady_p,// Indicates that a second policy table has already been loaded
          output wire         toggleHDSet_p,         // Indicates that the Header Descriptor Set can be toggled
          output wire         togglePTSet_p,         // Indicates that the Policy Table Set can be toggled
          output wire         clearSets_p,           // Indicates that the Sets have to be cleared.
          input  wire  [15:0] protFrmDur,            // Protection Frame Duration
          input  wire         writeACK,              // Indicate SW expects the ACK frame for this frame
                                                     // to be passed to it when received.
          input  wire         lowRateRetry,          // Lower Rate on Retries
          input  wire         lstpProt,              // L-SIG TXOP Protection for protection frame
          input  wire         lstp,                  // L-SIG TXOP Protection
          input  wire         dontTouchDur,          // Indicates that HW should not update the Duration field
          input  wire   [1:0] expectedAck,           // Expected Acknowledgement
                                                     //   2'b00: No acknowledgement.
                                                     //   2'b01: Normal ACK.
                                                     //   2'b10: BA.
                                                     //   2'b11: Compressed BA.
          input  wire   [2:0] navProtFrmEx,          // NAV Protection Frame Exchange
                                                     //   3'b000: No protection
                                                     //   3'b001: Self-CTS
                                                     //   3'b010: RTS/CTS with intended receiver of this PPDU
                                                     //   3'b011: RTS/CTS with QAP 
                                                     //   3'b100: STBC protection
          input  wire         useRIFSTx,             // Use RIFS for Transmission
          input  wire         preTypeProtTx,         // Preamble Type of Protection frame for Transmission
                                                     //   1'b0: SHORT
                                                     //   1'b1: LONG
          input  wire         preTypeTx,             // Preamble Type of PPDU for Transmission
                                                     // Same coding than preTypeProtTx
          input  wire         dynBWTx,               // Dynamic Bandwidth for Transmission
          input  wire         useBWSignalingTx,      // Use BW Signaling for Transmission
          input  wire         smoothingProtTx,       // Smoothing of Protection frame for Transmission
          input  wire         smoothingTx,           // Smoothing of PPDU for Transmission
          input  wire         soundingTx,            // Sounding Protection frame for Transmission
          input  wire   [2:0] nTxProtPT,             // Number of Transmit Chains for Protection Frame
          input  wire   [2:0] nTxPT,                 // Number of Transmit Chains for PPDU
          input  wire         shortGIPT,             // Short Guard Interval for Transmission
                                                     // When High, it indicates whether a short Guard Interval
          input  wire         fecCodingPT,           // FEC Coding
          input  wire   [1:0] stbcPT,                // Space Time Block Coding
          input  wire   [1:0] numExtnSSPT,           // Number of Extension Spatial Streams
          input  wire   [7:0] smmIndexPT,            // Spatial Map Matrix Index
          input  wire   [9:0] keySRAMIndex,          // Key Storage RAM Index
          input  wire   [9:0] keySRAMIndexRA,        // Key Storage RAM Index for Receiver Address
          input  wire         aMPDU,                 // Indicates whether this Transmit Header Descriptor belong to an A-MPDU
          input  wire         txSingleVHTMPDU,       // Flag of single VHT MPDU
          input  wire   [1:0] whichDescriptor,       // Indicates what kind of a descriptor this is
          input  wire   [3:0] fcSubtype,             // Indicates the fcSubtype field of the Frame Control field of the MPDU.
          input  wire   [1:0] fcType,                // Indicates the fcType field of the Frame Control field of the MPDU
          input  wire         tsValid,               // Indicates if the fcType and fcSubtype fields have been populated correctly

          input  wire  [11:0] rtsThreshold,          // RTS Threshold
          input  wire   [7:0] shortRetryLimit,       // Short Retry Limit
          input  wire   [7:0] longRetryLimit,        // Long Retry Limit
          input  wire   [2:0] formatModProtTx,       // Format and Modulation of Protection frame for Transmission
                                                     //   3'b000: NON-HT
                                                     //   3'b001: NON-HT-DUP-OFDM
                                                     //   3'b010: HT-MF
                                                     //   3'b011: HT-GF
                                                     //   3'b100: VHT
          input  wire   [2:0] formatModTx,           // Format and Modulation of PPDU for Transmission
                                                     // Same coding than formatModProtTx

          input  wire   [1:0] bwProtTx,              // Band Width of Protection frame for Transmission
          input  wire   [1:0] bwTx,                  // Band Width of PPDU for Transmission
          input  wire   [7:0] numMPDURetriesTPC,     // Indicates the number of MPDU retries already done   
          input  wire   [7:0] numRTSRetriesTPC,      // Indicates the number of RTS retries already done  
          input  wire  [19:0] aMPDUFrameLengthTx,    // Length of the entire A-MPDU
          input  wire  [19:0] aMPDUOptFrameLength20Tx,// Length of the entire A-MPDU BW drop 20Mhz
          input  wire  [19:0] aMPDUOptFrameLength40Tx,// Length of the entire A-MPDU BW drop 40Mhz
          input  wire  [19:0] aMPDUOptFrameLength80Tx,// Length of the entire A-MPDU BW drop 80Mhz
          input  wire   [6:0] mcsIndex0ProtTx,       // MCS Index 0 of Protection frame for Transmission
          input  wire   [6:0] mcsIndex0Tx,           // MCS Index 0 of PPDU for Transmission

          input  wire  [15:0] MPDUFrameLengthTx,     // Length of the MPDU
          
          input  wire  [31:0] mediumTimeUsedTPC,        // Medium Time Used for current TX transfer

          //$port_g Tx Controller interface
          output wire         sendData_p,            // Indicates that data packet has to be sent
          output wire         sendRTS_p,             // Indicates that an RTS packet has to be sent
          output wire         sendCTS_p,             // Indicates that a CTS packet has to be sent
          output wire         sendACK_p,             // Indicates that an ACK packet has to be sent
          output wire         sendCFEND_p,           // Indicates that a CF-END packet has to be sent
          output wire         sendBA_p,              // Indicates that an Block ACK packet has to be sent
          output wire         sendOnSIFS,            // If set, data is sent on tickSIFS else on tickSlot
          output wire         sendOnPIFS,            // If set, data is sent on tickPIFS
          output wire         skipMPDU_p,            // Indication that MPDU in TX FIFO has to be discarded

          output wire  [47:0] srcAddr,               // Source address
          output wire  [47:0] destAddr,              // Receiver address
          output wire  [15:0] duration,              // Duration
          output wire         retry,                 // Indicates that the trame is a retry.
          output wire  [15:0] tsfDuration,           // Duration from the preamble until the first bit of TSF

          output wire   [6:0] txMCS,                 // MCS (Only used for HT frame)
          output wire  [11:0] txLegLength,           // Legacy Length of the PPDU         
          output wire  [ 3:0] txLegRate,             // Legacy Rate of the PPDU.         
          output wire  [19:0] txHTLength,            // Length of the HT PPDU
          output wire   [1:0] txSTBC,                // Transmit a Frame with Space Time Block Coding
          output wire         txDisambiguityBit,     // Transmit a Frame with disambiguityBit
          

          output wire   [1:0] txChBW,                // Transmit a Frame with Channel Bandwidth
          output wire         txBWSignaling,         // Transmission with BW Signaling
          output wire         txDynBW,               // Transmission with Dynamic BW
          output wire         txResp,                // Transmit a Response Frame
          output wire         txFromReg,             // Transmit a HW generated frame based on Register
          output wire         txFromHD,              // Transmit a HW generated frame based on THD
          output wire         txFromFifo,            // Transmit a Frame from Tx FIFO
          output wire         txCFEND,               // Transmit a HW generated CFEND frame
          output wire         txRxn,                 // Indicates the mode between TX and Rx
                                                     //   0 : RX
                                                     //   1 : TX
          output wire         txFecCoding,           // Transmit a frame with FEC Coding       
          output wire         txShortGI,             // Transmit a frame with Short GI
          input  wire         txDone_p,              // Indicates that the transmission is completed
          input  wire   [3:0] txTID,                 // TID of the transmitted frame
          input  wire   [1:0] typeTx,                // TYPE of the transmitted frame
          input  wire         typeTxValid,           // Indicates typeTx is valid and can be latched
          input  wire         txAMSDUPresent,        // Indicates than the transmitted frame is an A-MSDU
          input  wire         txBcMc,                // Indicates than the transmitted frame has a group address.
          input  wire         sentCFEND,             // Indicates that the transmitted frame is a CF-END
          input  wire         sentRTS,               // Indicates that the transmitted frame is a RTS
          input  wire         sentBAReq,             // Indicates that the transmitted frame is a BA-Request
          input  wire         startTx_p,             // Start Tx trigger                 
          input  wire         mpduDone_p,            // Indicates that the MPDU has been sent
          input  wire         skipMPDUDone_p,        // Indicates that MPDU contained in the TXFIFO has been discarded.

          output wire   [7:0] respTxAntennaSet,      // Response Transmission with Antenna Set
          output wire   [7:0] respTxSMMIndex,        // Response Transmission with Spatial Map Matrix Index
          output wire         respTxPreType,         // Response Transmission with Preamble Type
                                                     //   1'b0: SHORT
                                                     //   1'b1: LONG
          output wire   [2:0] respTxFormatMod,       // Response Transmission with Format and Modulation
                                                     //   3'd0: NON-HT
                                                     //   3'd1: NON-HT-DUP-OFDM
                                                     //   3'd2: HT-MF
                                                     //   3'd3: HT-GF
                                                     //   3'd4: VHT
          output wire   [1:0] respTxNumExtnSS,       // Response Transmission with Number of Extension Spatial Streams
          output wire         respTxFECCoding,       // Response Transmission with Low Density Partity Check       
          output wire   [2:0] respTxNTx,             // Response Transmission with Number of Transmit Chains for PPDU        
          output wire         respTxShortGI,         // Response Transmission with Short Guard Interval

          //$port_g Rx Controller interface
          output reg          stopRx_p,              // Stop Rx
          output wire         activeRx,              // Current state Master is active Rx and Rx FSM is not IDLE
          output wire         rxAck,                 // Force receive only ACK after Tx
          output wire         rxBA,                  // Force receive only BA after Tx
          output wire         rxCts,                 // Force receive only CTS after RTS Tx
          output wire         forceWriteACK,         // Force the RX to pass the ACK to the Software
          output wire         lSIGTXOPDetected,      // Flag indicates received packet is LSIG TXOP protected

          input  wire         dataFrame,             // Frame type received is DATA
          input  wire         reservedRcved,         // Frame type received is Reserved
          input  wire         ackRcved_p,            // ACK received
          input  wire         rtsRcved_p,            // RTS received
          input  wire         ctsRcved_p,            // CTS received
          input  wire         cfEndRcved_p,          // CF-End received
          input  wire         baRcved_p,             // BA received 
          input  wire         barRcved_p,            // BAR received
          input  wire         needAckRcved_p,        // Data or management received with ACK needed
          input  wire         bcMcRcved_p,           // Broadcast/Multicast
          input  wire         bcnRcved_p,            // Beacon received
          input  wire         probRespRcved_p,       // Prob Response received
          input  wire         notMineRcved_p,        // Frame received but not mine
          input  wire         notMineRtsRcved_p,     // Not mine RTS received
          input  wire         notMinePsPollRcved_p,  // Not mine PS-Poll received
          input  wire         unknownRcved_p,        // Unknown frame received
          input  wire         macHeaderCompleted,    // End of MAC Header reception
          input  wire   [1:0] rxFCType,              // Indicates the fcType field of the received frame

          input  wire         incorrectRcved_p,      // Frame not received correctly
          input  wire         correctRcved_p,        // Frame received correctly

          input  wire         rxCsIsIdle,            // Rx Controller is in idle state

          input  wire  [47:0] rxAddr1,               // Received addr1
          input  wire  [47:0] rxAddr2,               // Received addr2
          input  wire         rxMoreFrag,            // More Frag bit of the received frame
          input  wire   [1:0] rxAckPolicy,           // Ack policy (Ack, No Ack, BA)
          input  wire  [15:0] rxFrameDuration,       // Frame duration
          input  wire  [31:0] rxHTCtrl,              // HT control field of the received frame

          input  wire   [3:0] rxTID,                 // TID of the received frame
          input  wire         rxAMSDUPresent,        // Indicates than the received frame is an A-MSDU
          input  wire         rxRetry,               // Indicates than the received frame has its retry bit set.
          input  wire         bcMcRcved,             // Indicates than the received frame has a group address.
          input  wire         notMineRcved,          // Indicates than the received frame is not destined to this device.
          input  wire         rxBWSignalingTA,       // Indicate that the received frame has a Bandwidth Signaling TA

          //$port_g deaggregator interface
          input  wire  [11:0] rxLegLength,           // Legacy length
          input  wire  [15:0] rxHTLength,            // HT length
          input  wire   [3:0] rxLegRate,             // Legacy rate
          input  wire   [6:0] rxMCS,                 // MCS
          input  wire         rxPreType,             // Preamble type
          input  wire   [2:0] rxFormatMod,           // Format and modulation
          input  wire         rxDynBW,               // Dynamique Bandwidth
          input  wire   [1:0] rxSTBC,                // Space Time Block Coding
          input  wire   [1:0] rxChBW,                // Channel bandwidth
          input  wire   [1:0] rxChBWInNonHT,         // Channel bandwidth in Non-HT extracted from the scrambler initialization sequence
          input  wire         rxShortGI,             // Short Guard Interval
          input  wire         rxLSIGValid,           // L-SIG Valid of received frame
          input  wire   [1:0] rxNumExtnSS,           // Number of Extension Spatial Streams
          input  wire         rxFecCoding,           // Low Density Partity Check  of received frame  
          input  wire         rxAggregation,         // MPDU aggregate
          input  wire   [7:0] rxAntennaSet,          // Antenna set

          input  wire         ampduCorrectRcved_p,   // A-MPDU received correctly
          input  wire         ampduIncorrectRcved_p, // A-MPDU not received correctly
          input  wire         rxSingleVHTMPDU,       // Detect EOF bit in AMPDU delimiter for a Single VHT MPDU
          input  wire         rxVector1Valid_p,      // Rx vector 1 is available
          input  wire         rxEndOfFrame_p,        // Rx vector 2 is available
          input  wire         rxVector1Start_p,      // Indicate that the first byte of RX Vector has been received
          input  wire   [5:0] rxMPDUCnt,             // Count the number of MPDU detected
          input  wire   [7:0] incorrectDelCnt,       // Count the number of incorrect delimiter

          output reg          startRx,               // Start Rx

          //$port_g MAC-PHY interface                                                           
          input  wire         mpIfTxErr_p,           // Tx error from MAC-PHY if. resynchronized
          input  wire         macPhyIfRxCca,         // CCA trigger                   
          input  wire         macPhyIfRxStart_p,     // Start of reception pulse
          input  wire         macPhyIfRxErr_p,       // Rx error from MAC-PHY if. resynchronized
          input  wire         macPhyIfRxEnd_p,       // mpIF state machine is idle
          input  wire         macPhyIfRxFlush_p,     // Rx flush pulse
          input  wire         macPHYIFUnderRun,      // Underrun from MAC-PHY if.
          input  wire         macPhyIfRifsRxDetected,// RIFS detected indication                      
          input  wire         macPhyIfRxEndForTiming_p, // end of reception at the antenna                        
          output wire         mpifKeepRFon,          // Keep RF On

          //$port_g Interface with the Key Search Engine
          input  wire  [47:0] macAddressKSR,         // MAC Addr returned by Key Search Engine
          output wire         txKeySearchIndexTrig_p,// Trigs the Key Search Engine for a Key Research based on index.
          output wire   [9:0] txKeySearchIndex,      // Key Index used by the Key Search Engine for Research based on index.

          //$port_g BackOff and AC Selection Module interface
          input  wire   [3:0] txDmaState,            // DMA state for the active channel
          input  wire  [15:0] txOpLimit,             // TXOP Limit of the active channel
          input  wire         backOffDone_p,         // Indicates when a backOff has expired
          input  wire         trigTxBackoff,         // Indicate that the backoff won the medium
          input  wire         trigTxBcn,             // Trigger from the MAC Controller to indicate DMA to run use the Beacon Queue
          output wire  [15:0] acMOT,                 // Current AC Medium Occupancy timer
          output wire         retryType,             // Indicates the type of retry
                                                     //   0 : Short Retry Limit
                                                     //   1 : Long Retry Limit
          output wire         txSuccessful_p,        // Indicates that the current frame has be correctly transmitted
          output wire         retry_p,               // Indicates that the current frame has to be retried
          output wire         retryLTReached_p,      // Indicates that the retry limit has been reached
          output wire         txInProgress,          // Tx is ongoing
          output wire         endOfTxOp,             // Indicates the end of the TX OP.

          //$port_g TXTIME calculator interface
          input  wire  [15:0] timeOnAirMC,           // Time On Air result to MAC Controller
                                                     // This field gives the time taken for frame transmission in microseconds (us)
                                                     // computed from parameters given by the MAC Controller.
          input  wire         timeOnAirValidMC,      // Time On Air Valid to MAC Controller
                                                     // This field is set when the air time computation is completed.
          input  wire         disambiguityMC,        // Value of the disambiguityBit in case of VHT frame with shortGI computed by the TxTimeCalculator

          output reg    [2:0] ppduPreTypeMC,         // PPDU Preamble Type from MAC Controller
                                                     // This field indicates what type of preamble is transmitted for the frame.
                                                     // The encoding is as follows:
                                                     //   3'b000: Non-HT-Short
                                                     //   3'b001: Non-HT-Long
                                                     //   3'b010: HT-MF
                                                     //   3'b011: HT-GF
                                                     //   3'b100: VHT
          output reg   [19:0] ppduLengthMC,          // PPDU Length from MAC Controller
                                                     // This field gives the length of the PPDU for computing time on air.
          output reg    [6:0] ppduMCSIndexMC,        // PPDU LegRate or MCS Index from MAC Controller
                                                     // This field indicates the rate at which this PPDU is transmitted. 
          output reg    [1:0] ppduBWMC,              // PPDU Bandwidth from MAC Controller
                                                     // This field indicates that that the PPDU should be transmitted at 40 MHz.
          output reg    [1:0] ppduNumExtnSSMC,       // Number of Extension Spatial Streams      
          output reg    [1:0] ppduSTBCMC,            // Enable Space Time Block Coding          
          output reg          ppduShortGIMC,         // PPDU Short Guard Interval from MAC Controller
                                                     // Indicates that the frame should be transmitted with Short GI.
          output reg          woPreambleMC,          // Indicates that total duration should not include the preamble duration 
          output reg          startComputationMC_p,  // Start Time on Air computation from MAC Controller
          
          
          //$port_g Timers Module interface
          input  wire         tick1us_p,             // Pulse generated every us.
          input  wire  [15:0] impQICnt,              // Quiet interval counter in 32 us
          input  wire         sec20ChannelIdleFlag,  // Secondary 20MHz channel idle for PIFS flag
          input  wire         sec40ChannelIdleFlag,  // Secondary 40MHz channel idle for PIFS flag
          input  wire         sec80ChannelIdleFlag,  // Secondary 80MHz channel idle for PIFS flag
          input  wire         tickPIFS_p,            // A pulse to indicate the end of PIFS period
          input  wire         rifsTO_p,              // Pulse when RIFS timeout occurs
          input  wire  [7:0]  sifsRemaining,         // us remaining before tick sifs pulse
          output wire  [15:0] frmDurWithoutMH,       // Indicates the duration if the Beacon or Probe Response from the end of the MAC header
          output wire         respTO_p,              // Indicates that the Time Out Counter has expired.
          output wire         resetCommonCnt_p,      // Reset common count counter
          output wire         moveToActive_p,        // Core should now move to ACTIVE state
          output wire         moveToIdle_p,          // Indicates that the macControllerMasterFSM moves to IDLE state


          //$port_g NAV Module interface
          input  wire         channelBusy,           // Channel busy indicator
          output wire  [15:0] ctsDuration,           // Indicates the duration of a CTS frame response of the received RTS
          output wire         ctsDurationValid_p,    // Indicates that the ctsDuration is valid
          output wire  [15:0] ackDuration,           // Indicates the duration of a ACK frame response of the received PS-POLL
          output wire         ackDurationValid_p,    // Indicates that the ackDuration is valid
          output wire  [7:0]  phyRxStartDelay,       // Receive Start Delay of the PHY
          output wire  [15:0] navLsigDuration,       // Indicates the duration computed based on L_LENGTH and L_RATE in HT_MM

          //$port_g Doze Module interface
          input  wire         dozeWakeUp_p,          // Wake up the Mac Controller 
          output wire         moveToDoze_p,          // Move to Doze request

        `ifdef RW_MAC_MIBCNTL_EN
          //$port_g Interface with the MIB Controller
          output wire         mibdot11WEPExcludedCount,              // Counts the number of unencrypted frames that have been discarded.
          output wire         mibdot11FCSErrorCount,                 // Counts the receive FCS errors.
          output wire         mibrwRxPHYErrorCount,                  // Counts the number of PHY Errors reported during a receive transaction.
          output wire         mibrwRxFIFOOverflowCount,              // Counts the number of times the Receive FIFO has overflowed.
          output wire         mibrwTxUnderrunCount,                  // Counts the number of times underrun has occurred on the Transmit side
          output wire         mibrwQosUTransmittedMPDUCount,         // Counts the number of unicast MPDUs, not containing an A-MSDU, that were transmitted successfully without using BA policy.
          output wire         mibrwQosGTransmittedMPDUCount,         // Counts the number of group-addressed MPDUs, not containing an A-MSDU, that were transmitted successfully.
          output wire         mibdot11QosFailedCount,                // Counts the number of MSDUs or MMPDUs that were discarded because of retry-limit-reached condition.
          output wire         mibdot11QosRetryCount,                 // Counts the number of unfragmented MSDUs or unfragmented MMPDUs that were transmitted successfully after 1 or more retransmissions without using BA policy.
          output wire         mibdot11QosRTSSuccessCount,            // Counts the number of successful RTS frame transmissions.
          output wire         mibdot11QosRTSFailureCount,            // Counts the number of unsuccessful RTS frame transmissions
          output wire         mibrwQosACKFailureCount,               // Counts the number of MPDUs, not containing an A-MSDU, that did not receive an ACK frame successfully in response.
          output wire         mibrwQosUReceivedMPDUCount,            // Counts the number of unicast MPDUs, not containing an A-MSDU, received successfully, destined to this device.
          output wire         mibrwQosGReceivedMPDUCount,            // Counts the number of group-addressed MPDUs, not containing an A-MSDU, received successfully.
          output wire         mibrwQosUReceivedOtherMPDU,            // Counts the number of unicast MPDUs, not containing an A-MSDU, received successfully, not destined to this device.
          output wire         mibdot11QosRetriesReceivedCount,       // Counts the number of MPDUs that are received with the retry bit set.
          output wire         mibrwUTransmittedAMSDUCount,           // Counts the number of unicast A-MSDUs that were transmitted successfully without using BA policy. 
          output wire         mibrwGTransmittedAMSDUCount,           // Counts the number of group-addressed A-MSDUs that were transmitted successfully
          output wire         mibdot11FailedAMSDUCount,              // Counts the number of A-MSDUs that were discarded because of retry-limit-reached condition.
          output wire         mibdot11RetryAMSDUCount,               // Counts the number of A-MSDUs that were transmitted successfully after 1 or more retransmissions without using BA policy. 
          output wire  [15:0] mibdot11TransmittedOctetsInAMSDU,      // Counts the number of bytes in the frame body of an A-MSDU that was transmitted successfully without using BA policy
          output wire         mibdot11AMSDUAckFailureCount,          // Counts the number of A-MSDUs that did not receive an ACK frame successfully in response.
          output wire         mibrwUReceivedAMSDUCount,              // Counts the number of unicast A-MSDUs received successfully, destined to this device.
          output wire         mibrwGReceivedAMSDUCount,              // Counts the number of group-addressed A-MSDUs received successfully.
          output wire         mibrwUReceivedOtherAMSDU,              // Counts the number of unicast A-MSDUs received successfully, not destined to this device.
          output wire  [15:0] mibdot11ReceivedOctetsInAMSDUCount,    // Counts the number of bytes in the frame body of an A-MSDU that was received successfully.
          output wire         mibdot11TransmittedAMPDUCount,         // Counts the number of A-MPDUs that were transmitted.
          output wire         mibdot11TransmittedMPDUInAMPDUCount,   // Counts the number of MPDUs that were transmitted in an A-MPDU.
          output wire  [15:0] mibdot11TransmittedOctetsInAMPDUCount, // Counts the number of bytes in a transmitted A-MPDU.
          output wire         mibrwUAMPDUReceivedCount,              // Counts the number of unicast A-MPDUs received, destined to this device.
          output wire         mibrwGAMPDUReceivedCount,              // Counts the number of group-addressed A-MPDUs received.
          output wire         mibrwOtherAMPDUReceivedCount,          // Counts the number of unicast A-MPDUs received, not destined to this device.
          output wire         mibdot11MPDUInReceivedAMPDUCount,      // Counts the number of MPDUs that were received in an A-MPDU.
          output wire  [15:0] mibdot11ReceivedOctetsInAMPDUCount,    // Counts the number of bytes received in an A-MPDU.
          output wire   [7:0] mibdot11AMPDUDelimiterCRCErrorCount,   // Counts the number of CRC errors in MPDU Delimiter of an A-MPDU. An immediately repeated CRC error within an A-MPDU is not counted.
          output wire         mibdot11ImplicitBARFailureCount,       // Counts the number of Implicit BAR frames that did not receive the BA frame successfully in response.
          output wire         mibdot11ExplicitBARFailureCount,       // Counts the number of Explicit BAR frames that did not receive the BA frame successfully in response.
          output wire         mibdot1120MHzFrameTransmittedCount,    // Counts the number of frames transmitted at 20 MHz BW.
          output wire         mibdot1140MHzFrameTransmittedCount,    // Counts the number of frames transmitted at 40 MHz BW.
          output wire         mibdot1180MHzFrameTransmittedCount,    // Counts the number of frames transmitted at 80 MHz BW.
          output wire         mibdot11160MHzFrameTransmittedCount,   // Counts the number of frames transmitted at 160 MHz BW.
          output wire         mibdot1120MHzFrameReceivedCount,       // Counts the number of frames received at 20 MHz BW.
          output wire         mibdot1140MHzFrameReceivedCount,       // Counts the number of frames received at 40 MHz BW.
          output wire         mibdot1180MHzFrameReceivedCount,       // Counts the number of frames received at 80 MHz BW.
          output wire         mibdot11160MHzFrameReceivedCount,      // Counts the number of frames received at 160 MHz BW.
          output wire         mibrw20MHzFailedTXOPCount,             // Counts the number of attempts made to acquire a 20 MHz TXOP.
          output wire         mibrw20MHzSuccessfulTXOPCount,         // Counts the number of successful 20 MHz TXOPs.
          output wire         mibrw40MHzFailedTXOPCount,             // Counts the number of attempts made to acquire a 40 MHz TXOP.
          output wire         mibrw40MHzSuccessfulTXOPCount,         // Counts the number of successful 40 MHz TXOPs.
          output wire         mibrw80MHzFailedTXOPCount,             // Counts the number of attempts made to acquire a 80 MHz TXOP.
          output wire         mibrw80MHzSuccessfulTXOPCount,         // Counts the number of successful 80 MHz TXOPs.
          output wire         mibrw160MHzFailedTXOPCount,            // Counts the number of attempts made to acquire a 160 MHz TXOP.
          output wire         mibrw160MHzSuccessfulTXOPCount,        // Counts the number of successful 160 MHz TXOPs.
          output wire         mibrwDynBWDropCount,                   // Count the number of BW drop using dynamic BW management.
          output wire         mibrwStaBWFailedCount,                 // Count the number of failure using static BW management.
          output wire         mibdot11DualCTSSuccessCount,           // Counts the number of times the dual CTS fails. 
          output wire         mibdot11STBCCTSSuccessCount,           // Counts the number of times the AP does not detect a collision PIFS after transmitting a STBC CTS frame. 
          output wire         mibdot11STBCCTSFailureCount,           // Counts the number of times the AP detects a collision PIFS after transmitting a STBC CTS frame.
          output wire         mibdot11nonSTBCCTSSuccessCount,        // Counts the number of times the AP does not detect a collision PIFS after transmitting a non-STBC CTS frame.
          output wire         mibdot11nonSTBCCTSFailureCount,        // Counts the number of times the AP detects a collision PIFS after transmitting a non-STBC CTS frame.
          output wire   [2:0] mibTIDIndex,                           // If TIDN of the MIB is
                                                                     // set to one then in that case
                                                                     // address given out of RAM
                                                                     // shall be determined from 
                                                                     // tidIndex
          output wire         mibTrigger,                            // Trigger From MAC to latch
                                                                     // MIB fields at MIB-MAC interface
 
        `endif // RW_MAC_MIBCNTL_EN

          //$port_g Interrupt Controller interface
          output wire         txopComplete,          // Indicates the completion of a TXOP
          output wire         acBWDropTrigger,       // Indicates a BW drop with AMPDU length change
          output wire         idleInterrupt,         // Indicates that the Core has moved to IDLE state

          //$port_g HW Error interface
          input  wire         hwErr,                 // HW error detected

        `ifdef RW_WLAN_COEX_EN
          input  wire                            coexEnable,            // Enable Coex Feature
          input  wire [3:0]                      coexPTIBKData,         // PTI default value for Data frame transmitted on BK AC
          input  wire [3:0]                      coexPTIBEData,         // PTI default value for Data frame transmitted on BE AC
          input  wire [3:0]                      coexPTIVIData,         // PTI default value for Data frame transmitted on VI AC
          input  wire [3:0]                      coexPTIVOData,         // PTI default value for Data frame transmitted on VO AC
          input  wire [3:0]                      coexPTIBcnData,        // PTI default value for Data frame transmitted on Beacon AC
          input  wire [3:0]                      coexPTIMgt,            // PTI default value for Management frame
          input  wire [3:0]                      coexPTICntl,           // PTI default value for Control frames other than ACK and BA
          input  wire [3:0]                      coexPTIAck,            // PTI default value for ACK and BA
          output reg                             coexWlanTx,            // Indicates that a WLAN Transmission is on-going
          output reg                             coexWlanRx,            // Indicates that a WLAN Reception is on-going
          input  wire                            coexWlanTxAbort,       // Requests from external arbiter abort all on-going transmission 
          output reg  [3:0]                      coexWlanPTI,           // Indicates the priority of the on-going traffic
          output reg                             coexWlanPTIToggle,     // Indicates a new priority value
          output reg                             coexWlanChanBw,        // Indicates the BW of the on-going traffic
          input  wire                            trigTxAC0,             // Trigger from the MAC Controller to indicate DMA to 
                                                                        // start fetching frames associated with AC0
          input  wire                            trigTxAC1,             // Trigger from the MAC Controller to indicate DMA to
                                                                        // start fetching frames associated with AC1
          input  wire                            trigTxAC2,             // Trigger from the MAC Controller to indicate DMA to 
                                                                        // start fetching frames associated with AC2
          input  wire                            trigTxAC3,             // Trigger from the MAC Controller to indicate DMA to
                                                                        // start fetching frames associated with AC3
        `endif // RW_WLAN_COEX_EN

          //$port_g CSReg interface
          output wire   [3:0] currentState,          // Indicates the current state of the Core. The state encoding is as follows:
                                                     //   0000 - IDLE state. This is the default state.
                                                     //   0010 - DOZE state
                                                     //   0011 - ACTIVE state
                                                     //   0100 to 1111  - reserved
          input  wire   [3:0] nextState,             // Indicates the next state of the Core
          output wire   [3:0] nextStateIn,           // When the current state goes back to IDLE, the nextState is also set to IDLE
          output wire         nextStateInValid,      // Indicates that the nextStateIn value can be capture.
          input  wire  [11:0] bssBasicRateSet,       // BSS Basic Rate Set
          input  wire  [15:0] bssBasicHTMCSSetEM,    // BSS Basic HT MCS Set for Equal Modulation
          input  wire   [5:0] bssBasicHTMCSSetUM,    // BSS Basic HT MCS Set for Unequal Modulation
          input  wire  [15:0] bssBasicVHTMCSSet,     // BSS Basic VTH MCS
          input  wire   [7:0] slotTime,              // aSlotTime parameter
          input  wire   [7:0] rxStartDelayMIMO,      // Receive Start Delay for MIMO
          input  wire   [7:0] rxStartDelayShort,     // Receive Start Delay for DSSS/CCK Short preamble
          input  wire   [7:0] rxStartDelayLong,      // Receive Start Delay for DSSS/CCK Long preamble
          input  wire   [7:0] rxStartDelayOFDM,      // Receive Start Delay for OFDM
          input  wire         ap,                    // Indicates the type of device (0: STA, 1: AP)
          input  wire         bssType,               // Indicates the type of BSS (0: IBSS, 1: Infrastructure)
          input  wire         rxRIFSEn,              // Enable RIFS in RX    
          input  wire  [47:0] bssID,                 // BSSID
          input  wire  [47:0] macAddr,               // MAC Addr
          input  wire  [15:0] cfEndSTBCDur,          // CF-End STBC Duration
          input  wire   [7:0] ctsSTBCDur,            // CTS STBC Duration
          input  wire         dualCTSProt,           // Dual-CTS Protection
          input  wire   [6:0] basicSTBCMCS,          // Basic STBC MCS
          input  wire   [7:0] sifsA,                 // Provide SIFS A duration in us
          input  wire   [7:0] sifsB,                 // Provide SIFS B duration in us
          input  wire         startTxFrameExGated,   // Start Transmission from register gated (set only when the startTxAC won the medium) 
          output wire         startTxFrameExIn,      // Clear the start Transmission with Frame Exchange
          output wire         startTxFrameExInValid, // Clear the start Transmission with Frame Exchange
          input  wire   [1:0] startTxFrmExType,      // Start Transmission with Frame Exchange Type
          input  wire   [9:0] startTxKSRIndex,       // Start Transmission with Key Storage RAM Index
          input  wire   [2:0] startTxFormatMod,      // Start Transmission with Format and Modulation
                                                     //   3'b000: NON-HT
                                                     //   3'b001: NON-HT-DUP-OFDM
                                                     //   3'b010: HT-MF
                                                     //   3'b011: HT-GF
                                                     //   3'b100: VHT
          input  wire   [7:0] startTxMCSIndex0,      // Start Transmission with MCS Index 0
          input  wire         startTxPreType,        // Start Transmission with preample Type
                                                     //   1'b0: SHORT
                                                     //   1'b1: LONG
          input  wire   [1:0] startTxBW,             // Start Transmission with Bandwidth
          input  wire  [15:0] durControlFrm,         // Start Transmission with duration Control Frame
          input  wire   [1:0] startTxNumExtnSS,      // Start Transmission with Number of Extension Spacial Stream
          input  wire   [1:0] startTxSTBC,           // Start Transmission with Space Time Block Coding
          input  wire         startTxLSTP,           // Start Transmission with L-SIG TXOP
          input  wire         startTxShortGI,        // Start Transmission with short GI
          input  wire         startTxFecCoding,      // Start Transmission with FEC Coding

          input  wire         dynBWEn,               // Enable dynamic Bandwidth support
          input  wire         dropToLowerBW,         // Drop To Lower Bandwidth
          input  wire   [2:0] numTryBWAcquisition,   // Number of Tries for 40/80/160MHz TXOP Acquisition
          input  wire   [1:0] defaultBWTXOP,         // Indicates the default bandwidth for TXOP acquisition
          input  wire         defaultBWTXOPV,        // Indicates if the defaultBWTXOP setting is valid.
          input  wire   [7:0] aPPDUMaxTime,          // aPPDU Maximum Time on Air
          input  wire   [1:0] maxSupportedBW,        // max Supported BW
          output wire   [1:0] txBWAfterDrop,         // Transmission bandwidth after BW Drop

          input  wire         supportLSTP,           // Indicates that the HW supports L-SIG TXOP

          input  wire         activeClkGating,       // Active Clock Gating This bit is set by SW to turn on 
                                                     // active clock gating in HW. When reset, the HW does not 
                                                     // perform active clock gating, i.e. does not turn off 
                                                     // clocks to save power in ACTIVE state.
          input  wire         disableACKResp,        // Disable ACK Response This bit is set by SW to disable 
                                                     // the automatic ACK generation logic in HW.
          input  wire         disableCTSResp,        // Disable CTS Response This bit is set by SW to disable 
                                                     // the automatic CTS generation logic in HW.
          input  wire         disableBAResp,         // Disable BA Response This bit is set by SW to disable 
          input  wire         keepTXOPOpen,          // Keep TXOP Open
          input  wire         remTXOPInDurField,     // Remaining TXOP Indicated in Duration Field
          input  wire         sendCFEnd,             // Send CF-End
          input  wire         sendCFEndNow,          // Send CF-End Now
          output wire         sendCFEndNowInValid,   // Indicates that the sendCFEndNow register has to be updated with sendCFEndNowIn
          output wire         sendCFEndNowIn,        // Give the update value of sendCFEndNow
                                                     // the automatic BA generation logic in HW.

          //$port_g Debug interface
          output wire  [15:0] debugPortMACController1, // DebugPort 1 of the MAC Controller
          output wire  [15:0] debugPortMACControllerRx,// DebugPort of the MAC Controller Rx
          output wire  [15:0] debugPortMACControllerTx,// DebugPort of the MAC Controller Tx
          output wire  [15:0] debugPortBWManagement,   // DebugPort of BW Management
          output wire   [6:0] debugPortAMPDUMC,
          output wire   [7:0] macControlCs,           // State of the MAC Controller FSMs       
          output reg    [7:0] macControlLs            // State of the MAC Controller FSMs when the HW Error happened    
                 );

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
wire  rxExchangeEnabled;     // Enables the RX frame exchange
wire  rxExchangeCompleted_p; // When the completion of a RX frame exchange
wire  txExchangeEnabled;     // Enables the TX frame exchange
wire  txExchangeCompleted_p; // When the completion of a TX frame exchange

wire  mpifKeepRFonMaster;
reg   mpifKeepRFonRx;
wire  rxRIFSPossible;
wire  rxRIFSCancelled_p;
wire  mpifKeepRFonTx;

wire startRxMaster_p;
wire stopRxMaster_p;
wire startRxRxC_p;
wire startRxTxC_p;
wire stopRxRxC_p;
wire stopRxTxC_p;

wire txRxnTxC;
wire txRxnRxC;
wire sendCTSTxC_p;
wire sendCTSRxC_p;
wire sendCFENDTxC_p;
wire sendCFENDRxC_p;
wire sendOnSIFSTxC;
wire sendOnSIFSRxC;
wire sendOnPIFSTxC;
wire sendOnPIFSRxC;

wire  [6:0] txMCSTxC;                 // MCS (Only used for HT frame)
wire [11:0] txLegLengthTxC;           // Legacy Length of the PPDU         
wire [ 3:0] txLegRateTxC;             // Legacy Rate of the PPDU.         

wire [19:0] txHTLengthTxC;            // Length of the HT PPDU

wire  [6:0] txMCSRxC;                 // MCS (Only used for HT frame)
wire [11:0] txLegLengthRxC;           // Legacy Length of the PPDU         
wire [ 3:0] txLegRateRxC;             // Legacy Rate of the PPDU.         
wire [15:0] txHTLengthRxC;            // Length of the HT PPDU
wire [ 1:0] txSTBCRxC;                
wire [ 1:0] txSTBCTxC;                
wire [ 1:0] txChBWRxC;
wire        txDisambiguityBitTxC;                

wire [ 1:0] txChBWTxC;

wire        txBWSignalingTxC;       // Transmission with BW Signaling from MAC Controller TX 
wire        txBWSignalingRxC;       // Response Transmission with BW Signaling from MAC Controller RX
wire        txDynBWTxC;             // Transmission with Dynamic BW from MAC Controller TX 
wire        txDynBWRxC;             // Transmission with Dynamic BW from MAC Controller RX 


wire [15:0] durationTxC;           // Duration field from MAC Tx Controller
wire [15:0] durationRxC;           // Duration field from MAC Rx Controller
wire [47:0] destAddrTxC;           // Receiver address from MAC Tx Controller
wire [47:0] destAddrRxC;           // Receiver address from MAC Rx Controller
wire [47:0] srcAddrTxC;            // Source address from MAC Tx Controller
wire [47:0] srcAddrRxC;            // Source address from MAC Rx Controller

wire        rateUpdateTxC_p;       // Request from the macControllerTx to update the rate
wire  [6:0] mcsIndex0Prot;         // MCS Index 0 of Protection frame for Transmission

wire        rateUpdateRxC_p;       // Request from the macControllerTx to update the rate
wire        rateUpdateDone_p;      // Indicates the end of the rate processing
wire  [1:0] bwDataTx;              // BW of PPDU for Transmission


wire  [6:0] mcsData;               // MCS Index for PROT frame
wire  [3:0] legRateData;           // Legacy Rate Index for Data frame
wire  [6:0] mcsCFEND;              // MCS Index for CF-END
wire  [3:0] legRateCFEND;          // Legacy Rate Index for CF-END
wire  [6:0] mcsPROT;               // MCS Index for PROT frame
wire  [3:0] legRatePROT;           // Legacy Rate Index for Data frame
wire  [6:0] mcsRESP;               // MCS Index for response frame
wire  [3:0] legRateRESP;           // Legacy Rate Index for response frame



wire [15:0] ppduLengthMCRx;         // PPDU Length from MAC Controller
                                    // This field gives the length of the PPDU for computing time on air.
wire  [1:0] ppduBWMCRx;             // PPDU Bandwidth MHz from MAC Controller
                                    // This field indicates that that the PPDU should be transmitted at 40 MHz.
wire  [2:0] ppduPreTypeMCRx;        // PPDU Preamble Type from MAC Controller
                                    // This field indicates what type of preamble is transmitted for the frame.
                                    // The encoding is as follows:
                                    // 3'b000: Non-HT-Short
                                    // 3'b001: Non-HT-Long
                                    // 3'b010: HT-MF
                                    // 3'b011: HT-GF
                                    // 3'b100: VHT
wire  [1:0] ppduNumExtnSSMCRx;      // Number of Extension Spatial Streams      
wire  [1:0] ppduSTBCMCRx;           // Enable Space Time Block Coding          
wire        ppduShortGIMCRx;        // PPDU Short Guard Interval from MAC Controller
                                    // Indicates that the frame should be transmitted with Short GI.
wire  [7:0] ppduMCSIndexMCRx;       // PPDU LegRate or MCS Index from MAC Controller
                                    // This field indicates the rate at which this PPDU is transmitted. 
wire        woPreambleMCRx;         // Indicates that total duration should not include the preamble duration 
wire        startComputationMCRx_p; // Start Time on Air computation from MAC Controller

wire  [2:0] ppduPreTypeMCTx;        // PPDU Preamble Type from MAC Controller
                                    // This field indicates what type of preamble is transmitted for the frame.
                                    // The encoding is as follows:
                                    // 3'b000: Non-HT-Short
                                    // 3'b001: Non-HT-Long
                                    // 3'b010: HT-MF
                                    // 3'b011: HT-GF
                                    // 3'b100: VHT
wire [19:0] ppduLengthMCTx;         // PPDU Length from MAC Controller
                                    // This field gives the length of the PPDU for computing time on air.
wire  [1:0] ppduBWMCTx;             // PPDU bandwidth from MAC Controller
                                    // This field indicates that that the PPDU should be transmitted at 40 MHz.
wire  [1:0] ppduNumExtnSSMCTx;      // Number of Extension Spatial Streams      
wire  [1:0] ppduSTBCMCTx;           // Enable Space Time Block Coding          
wire        ppduShortGIMCTx;        // PPDU Short Guard Interval from MAC Controller
                                    // Indicates that the frame should be transmitted with Short GI.
wire  [6:0] ppduMCSIndexMCTx;       // PPDU LegRate or MCS Index from MAC Controller

wire        startComputationMCTx_p; // Start Time on Air computation from MAC Controller

wire  [1:0] rxChOffset;             // Channel Offset of received frame
wire  [7:0] rxSMMIndex;             // Spatial Map Matrix Index of received frame
wire  [2:0] rxNTx;                  // Number of Transmit Chains for PPDU   of received frame    

wire  [7:0] sifsDuration;


wire        macCoreTxClkEnTxC;      // Enable TX Clocks from MAC Controller TX
wire        macCoreTxClkEnRxC;      // Enable TX Clocks from MAC Controller RX

wire  [2:0] macControllerMasterFSMCs;  // State of the MAC Controller Master FSM when the HW Error happened          
wire  [4:0] macControllerTxFSMCs;      // State of the MAC Controller TX FSM when the HW Error happened          
wire  [3:0] macControllerRxFSMCs;      // State of the MAC Controller RX FSM when the HW Error happened          

wire [15:0] rxLength;               // length of the received frame.

reg         macPhyIfRxErrInt_p;     // Rx error from MAC-PHY if. delayed of one clock cycle
wire  [3:0] rxLegRateConv;          // Converted Rx Legacy rate

wire        clearSetsTxC_p;         // Indicates that the Sets have to be cleared from MAC Controller TX.
wire [ 1:0] stbcTx;                

reg   [1:0] txFrameType;            //Latched value of txType signal from TX Controller
reg         macPhyIfRxCcaInt;       //Delayed version of macPhyIfRxCca

reg   [1:0] availableBWInt;         // Bandwidth available before the current reception.
wire  [1:0] availableBW;            // Bandwidth available before the current reception considering the maxSupportedBW.

wire        frameCorrectlyRcved_p; // Indicate that a frame (AMPU or not has been correctly received.

`ifdef RW_MAC_MIBCNTL_EN
  reg         bcMcRcvedCapt;         // Indicates than the received frame has a group address (Captured on correctRcved for AMPDU stat).
  reg         notMineRcvedCapt;      // Indicates than the received frame is not destined to this device (Captured on correctRcved for AMPDU stat).
`endif // RW_MAC_MIBCNTL_EN


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////



//assign macCoreTxClkEn = (activeClkGating) ? (txExchangeEnabled) ? macCoreTxClkEnTxC : macCoreTxClkEnRxC : 1'b1;  
assign macCoreTxClkEn = (activeClkGating && macCoreClkSoftRst_n) ? (txExchangeEnabled) ? macCoreTxClkEnTxC : macCoreTxClkEnRxC : 1'b1;  


assign sifsDuration = 8'd16; // $todo with real SIFSA and SIFSB values coming from registers.

assign activeRx = (macControlCs[7:5] == 3'b011) && (macControlCs[3:0] != 4'b0000);

// Instanciation of macControllerMaster
// Name of the instance : U_macControllerMaster
// Name of the file containing this module : macControllerMaster.v
macControllerMaster U_macControllerMaster (
		.macCoreClk                       (macCoreClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (macCoreClkSoftRst_n),
		.mpIfTxErr_p                      (mpIfTxErr_p),
		.macPhyIfRxCca                    (macPhyIfRxCca),
		.macPhyIfRxErr_p                  (macPhyIfRxErr_p),
		.macPhyIfRxEnd_p                  (macPhyIfRxEnd_p),
		.mpifKeepRFonMaster               (mpifKeepRFonMaster),
		.rxVector1Start_p                 (rxVector1Start_p),
		.startRxMaster_p                  (startRxMaster_p),
		.stopRxMaster_p                   (stopRxMaster_p),
		.backOffDone_p                    (backOffDone_p),
		.trigTxBackoff                    (trigTxBackoff),    
		.rxExchangeCompleted_p            (rxExchangeCompleted_p),
		.rxExchangeEnabled                (rxExchangeEnabled),
		.txExchangeCompleted_p            (txExchangeCompleted_p),
		.txExchangeEnabled                (txExchangeEnabled),
		.resetCommonCnt_p                 (resetCommonCnt_p),
		.moveToActive_p                   (moveToActive_p),
    .moveToIdle_p                     (moveToIdle_p),
		.idleInterrupt                    (idleInterrupt),
		.dozeWakeUp_p                     (dozeWakeUp_p),
		.moveToDoze_p                     (moveToDoze_p),
		.hwErr                            (hwErr),
		.macControllerMasterFSMCs         (macControllerMasterFSMCs),
		.currentState                     (currentState),
		.nextState                        (nextState),
		.nextStateIn                      (nextStateIn),
		.nextStateInValid                 (nextStateInValid)
		);



// Instanciation of macControllerTx
// Name of the instance : U_macControllerTx
// Name of the file containing this module : macControllerTx.v
macControllerTx U_macControllerTx (
		.macCoreClk                       (macCoreClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (macCoreClkSoftRst_n),
		.macCoreTxClkEnTxC                (macCoreTxClkEnTxC),
		.txExchangeEnabled                (txExchangeEnabled),
		.txExchangeCompleted_p            (txExchangeCompleted_p),
		.mpifKeepRFonTx                   (mpifKeepRFonTx),
		.txRxnTxC                         (txRxnTxC),
		.availableBW                      (availableBW),
		.updateDMAStatus_p                (updateDMAStatus_p),
		.mcsData                          (mcsData),
		.legRateData                      (legRateData),
		.mcsCFEND                         (mcsCFEND),
		.legRateCFEND                     (legRateCFEND),
		.mcsPROT                          (mcsPROT),
		.legRatePROT                      (legRatePROT),
		.mcsRESP                          (mcsRESP),
		.legRateRESP                      (legRateRESP),
		.rateUpdateTxC_p                  (rateUpdateTxC_p),
		.mcsIndex0Prot                    (mcsIndex0Prot),
    .bwDataTx                         (bwDataTx),
    .stbcTx                           (stbcTx),
    .rxAck                            (rxAck),
    .rxBA                             (rxBA),
    .rxCts                            (rxCts),
		.forceWriteACK                    (forceWriteACK),
		.ackRcved_p                       (ackRcved_p),
		.rtsRcved_p                       (rtsRcved_p),
		.ctsRcved_p                       (ctsRcved_p),
		.cfEndRcved_p                     (cfEndRcved_p),
		.baRcved_p                        (baRcved_p),
		.barRcved_p                       (barRcved_p),
		.needAckRcved_p                   (needAckRcved_p),
		.bcMcRcved_p                      (bcMcRcved_p),
		.bcnRcved_p                       (bcnRcved_p),
		.notMineRcved_p                   (notMineRcved_p),
		.unknownRcved_p                   (unknownRcved_p),
		.rxAddr2                          (rxAddr2),
		.rxFrameDuration                  (rxFrameDuration),
		.incorrectRcved_p                 (incorrectRcved_p),
		.correctRcved_p                   (correctRcved_p),
		.rxCsIsIdle                       (rxCsIsIdle),
		.rxChBW                           (rxChBW),
		.rxChBWInNonHT                    (rxChBWInNonHT),
		.ampduCorrectRcved_p              (ampduCorrectRcved_p),
		.ampduIncorrectRcved_p            (ampduIncorrectRcved_p),
		.rxEndOfFrame_p                   (rxEndOfFrame_p),
		.startRxTxC_p                     (startRxTxC_p),
		.stopRxTxC_p                      (stopRxTxC_p),
		.sendData_p                       (sendData_p),
		.sendRTS_p                        (sendRTS_p),
		.sendCTSTxC_p                     (sendCTSTxC_p),
		.sendCFENDTxC_p                   (sendCFENDTxC_p),
		.sendOnSIFSTxC                    (sendOnSIFSTxC),
		.sendOnPIFSTxC                    (sendOnPIFSTxC),
		.skipMPDU_p                       (skipMPDU_p),
		.destAddrTxC                      (destAddrTxC),
		.srcAddrTxC                       (srcAddrTxC),
		.durationTxC                      (durationTxC),
		.retry                            (retry),
		.txMCSTxC                         (txMCSTxC),
		.txLegLengthTxC                   (txLegLengthTxC),
		.txLegRateTxC                     (txLegRateTxC),
		.txHTLengthTxC                    (txHTLengthTxC),
		.txSTBCTxC                        (txSTBCTxC),
		.txDisambiguityBitTxC             (txDisambiguityBitTxC),
		.txChBWTxC                        (txChBWTxC),
		.txDynBWTxC                       (txDynBWTxC),
		.txBWSignalingTxC                 (txBWSignalingTxC),
		.tsfDuration                      (tsfDuration),
		.txFromReg                        (txFromReg),
		.txFromHD                         (txFromHD),
		.txFromFifo                       (txFromFifo),
		.txCFEND                          (txCFEND),
		.txDone_p                         (txDone_p),
		.txFecCoding                      (txFecCoding),
		.txShortGI                        (txShortGI),
		.sentCFEND                        (sentCFEND),
		.sentRTS                          (sentRTS),
		.sentBAReq                        (sentBAReq),
		.startTx_p                        (startTx_p),
		.mpduDone_p                       (mpduDone_p),
		.skipMPDUDone_p                   (skipMPDUDone_p),
		.toggleHDSet_p                    (toggleHDSet_p),
		.togglePTSet_p                    (togglePTSet_p),
		.clearSetsTxC_p                   (clearSetsTxC_p),
		.clearSets_p                      (clearSets_p),
		.txParameterHDReady_p             (txParameterHDReady_p),
		.txParameterPTReady_p             (txParameterPTReady_p),
		.txParameterNextPTReady_p         (txParameterNextPTReady_p),
		.protFrmDur                       (protFrmDur),
		.writeACK                         (writeACK),
		.lowRateRetry                     (lowRateRetry),
		.lstpProt                         (lstpProt),
		.lstp                             (lstp),
		.dontTouchDur                     (dontTouchDur),
		.expectedAck                      (expectedAck),
		.navProtFrmEx                     (navProtFrmEx),
		.useRIFSTx                        (useRIFSTx),
		.formatModProtTx                  (formatModProtTx),
		.formatModTx                      (formatModTx),
		.preTypeProtTx                    (preTypeProtTx),
		.preTypeTx                        (preTypeTx),
		.bwProtTx                         (bwProtTx),
		.bwTx                             (bwTx),
		.dynBWTx                          (dynBWTx),
		.useBWSignalingTx                 (useBWSignalingTx),
		.smoothingProtTx                  (smoothingProtTx),
		.smoothingTx                      (smoothingTx),
		.soundingTx                       (soundingTx),
		.nTxProtPT                        (nTxProtPT),
		.nTxPT                            (nTxPT),
		.shortGIPT                        (shortGIPT),
		.fecCodingPT                      (fecCodingPT),
		.stbcPT                           (stbcPT),
		.numExtnSSPT                      (numExtnSSPT),
		.smmIndexPT                       (smmIndexPT),
		.keySRAMIndex                     (keySRAMIndex),
		.keySRAMIndexRA                   (keySRAMIndexRA),
		.aMPDU                            (aMPDU),
		.txSingleVHTMPDU                  (txSingleVHTMPDU),
		.whichDescriptor                  (whichDescriptor),
		.fcSubtype                        (fcSubtype),
		.fcType                           (fcType),
		.tsValid                          (tsValid),
		.rtsThreshold                     (rtsThreshold),
		.shortRetryLimit                  (shortRetryLimit),
		.longRetryLimit                   (longRetryLimit),
		.aMPDUFrameLengthTx               (aMPDUFrameLengthTx),
		.aMPDUOptFrameLength20Tx          (aMPDUOptFrameLength20Tx),
		.aMPDUOptFrameLength40Tx          (aMPDUOptFrameLength40Tx),
		.aMPDUOptFrameLength80Tx          (aMPDUOptFrameLength80Tx),
		.MPDUFrameLengthTx                (MPDUFrameLengthTx),
		.mcsIndex0ProtTx                  (mcsIndex0ProtTx),
		.mcsIndex0Tx                      (mcsIndex0Tx),
    .mediumTimeUsedTPC                (mediumTimeUsedTPC),
		.numMPDURetriesTPC                (numMPDURetriesTPC),
		.numRTSRetriesTPC                 (numRTSRetriesTPC),
		.macAddressKSR                    (macAddressKSR),
		.txKeySearchIndexTrig_p           (txKeySearchIndexTrig_p),
		.txKeySearchIndex                 (txKeySearchIndex),
		.statusUpdated_p                  (statusUpdated_p),
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
		.whichDescriptorSW                (whichDescriptorSW),
		.numMPDURetries                   (numMPDURetries),
		.numRTSRetries                    (numRTSRetries),
    .mediumTimeUsed                   (mediumTimeUsed),
		.txDmaState                       (txDmaState),
		.txOpLimit                        (txOpLimit),
		.trigTxBcn                        (trigTxBcn),
		.acMOT                            (acMOT),
		.retryType                        (retryType),
		.retry_p                          (retry_p),
		.retryLTReached_p                 (retryLTReached_p),
		.txSuccessful_p                   (txSuccessful_p),
		.endOfTxOp                        (endOfTxOp),
		.tick1us_p                        (tick1us_p),
		.impQICnt                         (impQICnt),
		.sec20ChannelIdleFlag             (sec20ChannelIdleFlag),
		.sec40ChannelIdleFlag             (sec40ChannelIdleFlag),
		.sec80ChannelIdleFlag             (sec80ChannelIdleFlag),
		.sifsRemaining                    (sifsRemaining),
		.respTO_p                         (respTO_p),
		.timeOnAirMC                      (timeOnAirMC),
		.timeOnAirValidMC                 (timeOnAirValidMC),
		.disambiguityMC                   (disambiguityMC),
		.ppduLengthMCTx                   (ppduLengthMCTx),
		.ppduBWMCTx                       (ppduBWMCTx),
		.ppduPreTypeMCTx                  (ppduPreTypeMCTx),
		.ppduNumExtnSSMCTx                (ppduNumExtnSSMCTx),
		.ppduSTBCMCTx                     (ppduSTBCMCTx),
		.ppduShortGIMCTx                  (ppduShortGIMCTx),
		.ppduMCSIndexMCTx                 (ppduMCSIndexMCTx),
		.startComputationMCTx_p           (startComputationMCTx_p),
		.mpIfTxErr_p                      (mpIfTxErr_p),
		.macPhyIfRxStart_p                (macPhyIfRxStart_p),
		.macPhyIfRxErr_p                  (macPhyIfRxErr_p),
		.macPhyIfRxEnd_p                  (macPhyIfRxEnd_p),
		.macPHYIFUnderRun                 (macPHYIFUnderRun),
		.txopComplete                     (txopComplete),
    .acBWDropTrigger                  (acBWDropTrigger),
		.hwErr                            (hwErr),
  `ifdef RW_MAC_MIBCNTL_EN
		.mibrw20MHzFailedTXOPCount        (mibrw20MHzFailedTXOPCount),
		.mibrw20MHzSuccessfulTXOPCount    (mibrw20MHzSuccessfulTXOPCount),
		.mibrw40MHzFailedTXOPCount        (mibrw40MHzFailedTXOPCount),
		.mibrw40MHzSuccessfulTXOPCount    (mibrw40MHzSuccessfulTXOPCount),
		.mibrw80MHzFailedTXOPCount        (mibrw80MHzFailedTXOPCount),
		.mibrw80MHzSuccessfulTXOPCount    (mibrw80MHzSuccessfulTXOPCount),
		.mibrw160MHzFailedTXOPCount       (mibrw160MHzFailedTXOPCount),
		.mibrw160MHzSuccessfulTXOPCount   (mibrw160MHzSuccessfulTXOPCount),
		.mibrwDynBWDropCount              (mibrwDynBWDropCount),
		.mibrwStaBWFailedCount            (mibrwStaBWFailedCount),
  `endif // RW_MAC_MIBCNTL_EN
		.macControllerTxFSMCs             (macControllerTxFSMCs),
		.macAddr                          (macAddr),
		.bssID                            (bssID),
		.sifsDuration                     (sifsDuration),
		.sifsA                            (sifsA),
		.sifsB                            (sifsB),
		.slotTime                         (slotTime),
		.rxStartDelayMIMO                 (rxStartDelayMIMO),
		.rxStartDelayShort                (rxStartDelayShort),
		.rxStartDelayLong                 (rxStartDelayLong),
		.rxStartDelayOFDM                 (rxStartDelayOFDM),
		.ap                               (ap),
		.startTxFrameExGated              (startTxFrameExGated),
		.startTxFrameExIn                 (startTxFrameExIn),
		.startTxFrameExInValid            (startTxFrameExInValid),
		.startTxFrmExType                 (startTxFrmExType),
		.startTxKSRIndex                  (startTxKSRIndex),
		.startTxMCSIndex0                 (startTxMCSIndex0),
		.startTxFormatMod                 (startTxFormatMod),
		.startTxPreType                   (startTxPreType),
		.startTxBW                        (startTxBW),
		.durControlFrm                    (durControlFrm),
		.startTxNumExtnSS                 (startTxNumExtnSS),
		.startTxSTBC                      (startTxSTBC),
		.startTxLSTP                      (startTxLSTP),
		.startTxShortGI                   (startTxShortGI),
		.startTxFecCoding                 (startTxFecCoding),
		.dynBWEn                          (dynBWEn),
		.dropToLowerBW                    (dropToLowerBW),
		.numTryBWAcquisition              (numTryBWAcquisition),
		.defaultBWTXOP                    (defaultBWTXOP),
		.defaultBWTXOPV                   (defaultBWTXOPV),
		.aPPDUMaxTime                     (aPPDUMaxTime),
    .txBWAfterDrop                    (txBWAfterDrop),
		.keepTXOPOpen                     (keepTXOPOpen),
		.remTXOPInDurField                (remTXOPInDurField),
		.sendCFEnd                        (sendCFEnd),
		.sendCFEndNow                     (sendCFEndNow),
		.sendCFEndNowInValid              (sendCFEndNowInValid),
		.sendCFEndNowIn                   (sendCFEndNowIn),
		.debugPortAMPDUMC                 (debugPortAMPDUMC),
		.debugPortMACControllerTx         (debugPortMACControllerTx)
		);



// Instanciation of macControllerRx
// Name of the instance : U_macControllerRx
// Name of the file containing this module : macControllerRx.v
macControllerRx U_macControllerRx (
		.macCoreClk                       (macCoreClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (macCoreClkSoftRst_n),
		.macCoreTxClkEnRxC                (macCoreTxClkEnRxC),
		.rxExchangeEnabled                (rxExchangeEnabled),
		.rxExchangeCompleted_p            (rxExchangeCompleted_p),
		.rxRIFSPossible                   (rxRIFSPossible),
		.rxRIFSCancelled_p                (rxRIFSCancelled_p),
		.txRxnRxC                         (txRxnRxC),
		.availableBW                      (availableBW),
		.mcsRESP                          (mcsRESP),
		.legRateRESP                      (legRateRESP),
		.rateUpdateRxC_p                  (rateUpdateRxC_p),
		.reservedRcved                    (reservedRcved),
		.ackRcved_p                       (ackRcved_p),
		.rtsRcved_p                       (rtsRcved_p),
		.ctsRcved_p                       (ctsRcved_p),
		.cfEndRcved_p                     (cfEndRcved_p),
		.baRcved_p                        (baRcved_p),
		.barRcved_p                       (barRcved_p),
		.needAckRcved_p                   (needAckRcved_p),
		.bcMcRcved_p                      (bcMcRcved_p),
		.bcnRcved_p                       (bcnRcved_p),
		.probRespRcved_p                  (probRespRcved_p),
		.notMineRtsRcved_p                (notMineRtsRcved_p),
		.notMinePsPollRcved_p             (notMinePsPollRcved_p),
		.notMineRcved_p                   (notMineRcved_p),
		.unknownRcved_p                   (unknownRcved_p),
		.macHeaderCompleted               (macHeaderCompleted),
		.rxAddr1                          (rxAddr1),
		.rxAddr2                          (rxAddr2),
		.rxMoreFrag                       (rxMoreFrag),
		.rxAckPolicy                      (rxAckPolicy),
		.rxHTCtrl                         (rxHTCtrl),
		.rxFrameDuration                  (rxFrameDuration),
		.incorrectRcved_p                 (incorrectRcved_p),
		.correctRcved_p                   (correctRcved_p),
		.rxBWSignalingTA                  (rxBWSignalingTA),
		.rxLegRateConv                    (rxLegRateConv),
		.rxMCS                            (rxMCS),
		.rxHTLength                       (rxHTLength),
		.rxLegLength                      (rxLegLength),
		.rxDynBW                          (rxDynBW),
		.rxSTBC                           (rxSTBC),
		.rxChBW                           (rxChBW),
		.rxChBWInNonHT                    (rxChBWInNonHT),
		.rxChOffset                       (rxChOffset),
		.rxLSIGValid                      (rxLSIGValid),
		.rxAntennaSet                     (rxAntennaSet),
		.rxSMMIndex                       (rxSMMIndex),
		.rxPreType                        (rxPreType),
		.rxFormatMod                      (rxFormatMod),
		.rxNumExtnSS                      (rxNumExtnSS),
		.rxFecCoding                      (rxFecCoding),
		.rxNTx                            (rxNTx),
		.rxShortGI                        (rxShortGI),
		.lSIGTXOPDetected                 (lSIGTXOPDetected),
		.ampduCorrectRcved_p              (ampduCorrectRcved_p),
		.ampduIncorrectRcved_p            (ampduIncorrectRcved_p),
		.rxSingleVHTMPDU                  (rxSingleVHTMPDU),
		.rxVector1Valid_p                 (rxVector1Valid_p),
		.rxEndOfFrame_p                   (rxEndOfFrame_p),
		.rxAggregation                    (rxAggregation),
		.startRxRxC_p                     (startRxRxC_p),
		.stopRxRxC_p                      (stopRxRxC_p),
		.txDone_p                         (txDone_p),
		.sendCTSRxC_p                     (sendCTSRxC_p),
		.sendACK_p                        (sendACK_p),
		.sendBA_p                         (sendBA_p),
		.sendCFENDRxC_p                   (sendCFENDRxC_p),
		.sendOnSIFSRxC                    (sendOnSIFSRxC),
		.sendOnPIFSRxC                    (sendOnPIFSRxC),
		.destAddrRxC                      (destAddrRxC),
		.srcAddrRxC                       (srcAddrRxC),
		.durationRxC                      (durationRxC),
		.txMCSRxC                         (txMCSRxC),
		.txLegLengthRxC                   (txLegLengthRxC),
		.txLegRateRxC                     (txLegRateRxC),
		.txHTLengthRxC                    (txHTLengthRxC),
		.txSTBCRxC                        (txSTBCRxC),
		.txResp                           (txResp),
		.txChBWRxC                        (txChBWRxC),
		.txBWSignalingRxC                 (txBWSignalingRxC),
		.txDynBWRxC                       (txDynBWRxC),
		.respTxAntennaSet                 (respTxAntennaSet),
		.respTxSMMIndex                   (respTxSMMIndex),
		.respTxPreType                    (respTxPreType),
		.respTxFormatMod                  (respTxFormatMod),
		.respTxNumExtnSS                  (respTxNumExtnSS),
		.respTxFECCoding                  (respTxFECCoding),
		.respTxNTx                        (respTxNTx),
		.respTxShortGI                    (respTxShortGI),
		.timeOnAirMC                      (timeOnAirMC),
		.timeOnAirValidMC                 (timeOnAirValidMC),
		.ppduLengthMCRx                   (ppduLengthMCRx),
		.ppduBWMCRx                       (ppduBWMCRx),
		.ppduPreTypeMCRx                  (ppduPreTypeMCRx),
		.ppduNumExtnSSMCRx                (ppduNumExtnSSMCRx),
		.ppduSTBCMCRx                     (ppduSTBCMCRx),
		.ppduShortGIMCRx                  (ppduShortGIMCRx),
		.ppduMCSIndexMCRx                 (ppduMCSIndexMCRx),
		.woPreambleMCRx                   (woPreambleMCRx),
		.startComputationMCRx_p           (startComputationMCRx_p),
		.channelBusy                      (channelBusy),
		.ctsDuration                      (ctsDuration),
		.ctsDurationValid_p               (ctsDurationValid_p),
		.ackDuration                      (ackDuration),
		.ackDurationValid_p               (ackDurationValid_p),
		.phyRxStartDelay                  (phyRxStartDelay),
		.navLsigDuration                  (navLsigDuration),
		.tickPIFS_p                       (tickPIFS_p),
		.frmDurWithoutMH                  (frmDurWithoutMH),
		.macPhyIfRxCca                    (macPhyIfRxCca),
		.mpIfTxErr_p                      (mpIfTxErr_p),
		.macPhyIfRxEnd_p                  (macPhyIfRxEnd_p),
		.macPhyIfRxErr_p                  (macPhyIfRxErr_p),
		.macPhyIfRxFlush_p                (macPhyIfRxFlush_p),
		.macPHYIFUnderRun                 (macPHYIFUnderRun),
		.hwErr                            (hwErr),
		.debugPortMACControllerRx         (debugPortMACControllerRx),
		.macControllerRxFSMCs             (macControllerRxFSMCs),
		.sifsA                            (sifsA),
		.sifsB                            (sifsB),
		.slotTime                         (slotTime),
		.ap                               (ap),
		.rxStartDelayMIMO                 (rxStartDelayMIMO),
		.rxStartDelayShort                (rxStartDelayShort),
		.rxStartDelayLong                 (rxStartDelayLong),
		.rxStartDelayOFDM                 (rxStartDelayOFDM),
		.disableACKResp                   (disableACKResp),
		.disableCTSResp                   (disableCTSResp),
		.disableBAResp                    (disableBAResp),
		.dynBWEn                          (dynBWEn),
		.supportLSTP                      (supportLSTP),
		.ctsSTBCDur                       (ctsSTBCDur),
		.dualCTSProt                      (dualCTSProt),
		.basicSTBCMCS                     (basicSTBCMCS)
		);





// Instanciation of rateSelection
// Name of the instance : U_rateSelection
// Name of the file containing this module : rateSelection.v
rateSelection U_rateSelection (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
		.mcsIndex0Tx            (mcsIndex0Tx),
		.formatModProtTx        (formatModProtTx),
		.formatModTx            (formatModTx),
		.bwDataTx               (bwDataTx),
		.stbcTx                 (stbcTx),
		.lowRateRetry           (lowRateRetry),
		.rxMCS                  (rxMCS),
		.rxLegRate              (rxLegRate),
		.rxFormatMod            (rxFormatMod),
		.rxSTBC                 (rxSTBC),
		.bssBasicRateSet        (bssBasicRateSet),
		.bssBasicHTMCSSetEM     (bssBasicHTMCSSetEM),
		.bssBasicHTMCSSetUM     (bssBasicHTMCSSetUM),
		.bssBasicVHTMCSSet      (bssBasicVHTMCSSet),
		.basicSTBCMCS           (basicSTBCMCS),
		.dualCTSProt            (dualCTSProt),
		.ap                     (ap),
		.rateUpdateTxC_p        (rateUpdateTxC_p),
		.mcsIndex0Prot          (mcsIndex0Prot),
		.rateUpdateRxC_p        (rateUpdateRxC_p),
		.txExchangeEnabled      (txExchangeEnabled),
		.rateUpdateDone_p       (rateUpdateDone_p),
		.rxLegRateConv          (rxLegRateConv),
		.mcsData                (mcsData),
		.legRateData            (legRateData),
		.mcsCFEND               (mcsCFEND),
		.legRateCFEND           (legRateCFEND),
		.mcsPROT                (mcsPROT),
		.legRatePROT            (legRatePROT),
		.mcsRESP                (mcsRESP),
		.legRateRESP            (legRateRESP)
		);






////////////////////////////////////////////////////////////////////
////
//// Muxing between MAC Controller Rx and Tx for TX Controller interface
////
////////////////////////////////////////////////////////////////////

assign sendCTS_p    = sendCTSRxC_p   || sendCTSTxC_p;
assign sendCFEND_p  = sendCFENDRxC_p || sendCFENDTxC_p;
assign mpifKeepRFon = mpifKeepRFonMaster || mpifKeepRFonRx || mpifKeepRFonTx;

reg [7:0] rxRIFSCnt;

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
	  mpifKeepRFonRx <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    mpifKeepRFonRx <= 1'b0;
  else if (rxRIFSEn)
  begin
    if (macPhyIfRxErr_p || rxRIFSCancelled_p)
      mpifKeepRFonRx <= 1'b0;
    else if (rxRIFSPossible)  	
      mpifKeepRFonRx <= 1'b1;
    else if (tick1us_p && rxRIFSCnt == 8'b1 && !macPhyIfRifsRxDetected)
      mpifKeepRFonRx <= 1'b0;
  end		
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxRIFSCnt <= 8'b0;
  else if(macCoreClkSoftRst_n == 1'b0 || !mpifKeepRFonRx)
    rxRIFSCnt <= 8'b0;
  else if (macPhyIfRxEndForTiming_p)
    rxRIFSCnt <= 8'd7;
  else if (tick1us_p && rxRIFSCnt != 8'b0)
    rxRIFSCnt <= rxRIFSCnt - 8'b1;
end



// assign startRx_p    = startRxMaster_p || startRxRxC_p || startRxTxC_p;

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    startRx <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    startRx <= 1'b0;
  else if (startRxMaster_p || startRxRxC_p || startRxTxC_p)
    startRx <= 1'b1;
  else if (stopRx_p)  
    startRx <= 1'b0;
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    stopRx_p <= 1'b0;
  else if (stopRxMaster_p  || stopRxRxC_p  || stopRxTxC_p)
    stopRx_p <= 1'b1;
  else  
    stopRx_p <= 1'b0;
end

 
assign txRxn        = txRxnTxC || txRxnRxC;

// If the txEnchange is enabled, the sendOnSIFS information coming from the MAC Controller TX FSM is taken into account,
// else this is the sendOnSIFS coming from the MAC Controller RX FSM
assign sendOnSIFS  = (txExchangeEnabled) ? sendOnSIFSTxC  : sendOnSIFSRxC;
assign sendOnPIFS  = (txExchangeEnabled) ? sendOnPIFSTxC  : sendOnPIFSRxC;

assign txMCS       = (txExchangeEnabled) ? txMCSTxC       : txMCSRxC;       
assign txLegLength = (txExchangeEnabled) ? txLegLengthTxC : txLegLengthRxC;
assign txLegRate   = (txExchangeEnabled) ? txLegRateTxC   : txLegRateRxC;  

assign txHTLength  = (txExchangeEnabled) ? txHTLengthTxC  : {4'b0,txHTLengthRxC};

assign txSTBC      = (txExchangeEnabled) ? txSTBCTxC      : txSTBCRxC; 

assign txDisambiguityBit = (txExchangeEnabled) ? txDisambiguityBitTxC : 1'b0;

assign txChBW      = (txExchangeEnabled) ? txChBWTxC      : txChBWRxC;

assign txBWSignaling = (txExchangeEnabled) ? txBWSignalingTxC : txBWSignalingRxC;

assign txDynBW     = (txExchangeEnabled) ? txDynBWTxC : txDynBWRxC;

assign duration    = (txExchangeEnabled) ? durationTxC    : durationRxC;
assign destAddr    = (txExchangeEnabled) ? destAddrTxC    : destAddrRxC;
assign srcAddr     = (txExchangeEnabled) ? srcAddrTxC     : srcAddrRxC;

// Indicate to the backoff and AC Selection Unit that the TX Exchange is on-going. 
// When set, the backoff are not counted down even if the CCA is idle
assign txInProgress = txExchangeEnabled; //$todo, in case of AP receiving non-STBC RTS with DualCTSProt enabled, the backoff shall be stop betwen the two CTS
                                         //because the second CTS will be received after PIFS and not SIFS

// assign clearSets_p = (txExchangeEnabled) ? clearSetsTxC_p : rxExchangeEnabled;
//assign clearSets_p = clearSetsTxC_p | (macPhyIfRxCca && !macPhyIfRxCcaInt && !txExchangeEnabled);
assign clearSets_p = clearSetsTxC_p | (macPhyIfRxCca && !txExchangeEnabled) | moveToIdle_p;

// Generation of macPhyIfRxCcaInt which is macPhyIfRxCca delayed of one clock cycle
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPhyIfRxCcaInt <= 1'b0;
  else
    macPhyIfRxCcaInt <= macPhyIfRxCca;
end

//


always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    availableBWInt <= 2'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    availableBWInt <= 2'b0;
  else
    if ((!macPhyIfRxCcaInt && macPhyIfRxCca) || backOffDone_p || (txExchangeEnabled && rxEndOfFrame_p))
      casex ({sec80ChannelIdleFlag,sec40ChannelIdleFlag,sec20ChannelIdleFlag})
	      3'b111 : availableBWInt <= 2'd3;
	      3'b011 : availableBWInt <= 2'd2;
	      3'bx01 : availableBWInt <= 2'd1;
	     default : availableBWInt <= 2'd0;
      endcase    
end

assign availableBW = (availableBWInt > maxSupportedBW) ? maxSupportedBW : availableBWInt;

////////////////////////////////////////////////////////////////////
////
//// Rx fields assignment
////
////////////////////////////////////////////////////////////////////
assign rxChOffset   = 2'b00;   //For to 0 as the modem knows which channel is the primary
assign rxSMMIndex   = 8'h00;   //$todo Don't know how to select that
assign rxNTx        = 3'b001;  //$todo Don't know how to select that always equal to 1.

////////////////////////////////////////////////////////////////////
////
//// Muxing between MAC Controller Rx and Tx for TX Time Calculator control signals
////
////////////////////////////////////////////////////////////////////

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    ppduLengthMC   <= 20'd0;
    ppduMCSIndexMC <= 6'd0;
    ppduPreTypeMC  <= 3'd0;
    ppduBWMC       <= 2'd0;
    ppduNumExtnSSMC<= 2'd0;
    ppduSTBCMC     <= 2'd0;
    ppduShortGIMC  <= 1'd0;
    woPreambleMC   <= 1'd0;
    startComputationMC_p <= 1'd0;
  end
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    ppduLengthMC   <= 20'd0;
    ppduMCSIndexMC <= 6'd0;
    ppduPreTypeMC  <= 3'd0;
    ppduBWMC       <= 2'd0;
    ppduNumExtnSSMC<= 2'd0;
    ppduSTBCMC     <= 2'd0;
    ppduShortGIMC  <= 1'd0;
    woPreambleMC   <= 1'd0;
    startComputationMC_p <= 1'd0;
  end
  else
    if (startComputationMCTx_p || startComputationMCRx_p)
    begin
      ppduLengthMC         <= (txExchangeEnabled) ? ppduLengthMCTx          : {4'b0,ppduLengthMCRx};
      ppduMCSIndexMC       <= (txExchangeEnabled) ? ppduMCSIndexMCTx        : ppduMCSIndexMCRx[6:0];  // TODO macController ppduMCSIndexMC when rXdesc Ac is ready
      ppduPreTypeMC        <= (txExchangeEnabled) ? ppduPreTypeMCTx         : ppduPreTypeMCRx;
      ppduBWMC             <= (txExchangeEnabled) ? ppduBWMCTx              : ppduBWMCRx;    
      ppduNumExtnSSMC      <= (txExchangeEnabled) ? ppduNumExtnSSMCTx       : ppduNumExtnSSMCRx;   
      ppduSTBCMC           <= (txExchangeEnabled) ? ppduSTBCMCTx            : ppduSTBCMCRx;        
      ppduShortGIMC        <= (txExchangeEnabled) ? ppduShortGIMCTx         : ppduShortGIMCRx;       
      woPreambleMC         <= (txExchangeEnabled) ? 1'b0                    : woPreambleMCRx;
      startComputationMC_p <= 1'b1;
    end
    else
      startComputationMC_p <= 1'b0;
    
end


`ifdef RW_WLAN_COEX_EN
////////////////////////////////////////////////////////////////////
////
//// WLAN Coex
////
////////////////////////////////////////////////////////////////////

reg macHeaderCompletedDly;

// Indicates that a WLAN Transmission is on-going
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    coexWlanTx <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    coexWlanTx <= 1'b0;
  else
    if ((startTx_p || sendRTS_p || sendCTS_p || sendACK_p || sendCFEND_p || sendBA_p) && !skipMPDU_p)
      coexWlanTx <= 1'b1;
    else if (txDone_p)
      coexWlanTx <= 1'b0;
end



always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    coexWlanRx <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    coexWlanRx <= 1'b0;
  else
    if ((txExchangeEnabled && startRxTxC_p) || rxVector1Start_p)
      coexWlanRx <= 1'b1;
    else if ((txExchangeEnabled && updateDMAStatus_p) || rxEndOfFrame_p || stopRx_p)
      coexWlanRx <= 1'b0;
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    coexWlanChanBw <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    coexWlanChanBw <= 1'b0;
  else
    if (rxVector1Valid_p)
      coexWlanChanBw <= rxChBW;
    else if (txExchangeEnabled && startRxTxC_p)
      coexWlanChanBw <= txChBW;
    else if ((startTx_p || sendRTS_p || sendCTS_p || sendACK_p || sendCFEND_p || sendBA_p) && !skipMPDU_p)
      coexWlanChanBw <= txChBW;
    else if ((txExchangeEnabled && updateDMAStatus_p) || txDone_p || rxEndOfFrame_p || stopRx_p)
      coexWlanChanBw <= 1'b0;
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    coexWlanPTI        <= 4'b0;
    coexWlanPTIToggle  <= 1'b0;
  end
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    coexWlanPTI        <= 4'b0;
    coexWlanPTIToggle  <= 1'b0;
  end
  else if (updateDMAStatus_p || rxEndOfFrame_p || txDone_p)
  begin
    coexWlanPTI        <= 4'b0;
    coexWlanPTIToggle  <= ~coexWlanPTIToggle;
  end
  else
  begin
    if (sendACK_p || sendBA_p || (startRxTxC_p && (rxAck || rxBA)))
    begin
      coexWlanPTI        <= coexPTIAck;
      coexWlanPTIToggle  <= ~coexWlanPTIToggle;
    end
    else if (sendRTS_p || sendCTS_p || (startRxTxC_p && rxCts))
    begin
      coexWlanPTI        <= coexPTICntl;
      coexWlanPTIToggle  <= ~coexWlanPTIToggle;
    end
    else if (txExchangeEnabled && startTx_p) 
    begin
      coexWlanPTIToggle  <= ~coexWlanPTIToggle;
      if (fcType == 2'b01)
        coexWlanPTI <= coexPTICntl;
      else if (fcType == 2'b00)
        coexWlanPTI <= coexPTIMgt;
      else if (fcType == 2'b10)
      begin
        case (txTID[2:0])
          3'd1,3'd2 : coexWlanPTI <= coexPTIBKData;
          3'd0,3'd3 : coexWlanPTI <= coexPTIBEData;
          3'd4,3'd5 : coexWlanPTI <= coexPTIVIData;
          3'd6,3'd7 : coexWlanPTI <= coexPTIVOData;
        endcase
      end
    end  
    else if (rxExchangeEnabled && macHeaderCompleted && !macHeaderCompletedDly && !notMineRcved) 
    begin
      coexWlanPTIToggle  <= ~coexWlanPTIToggle;
      if (rxFCType == 2'b01)
        coexWlanPTI <= coexPTICntl;
      else if (rxFCType == 2'b00)
        coexWlanPTI <= coexPTIMgt;
      else if (rxFCType == 2'b10)
      begin
        case (rxTID[2:0])
          3'd1,3'd2 : coexWlanPTI <= coexPTIBKData;
          3'd0,3'd3 : coexWlanPTI <= coexPTIBEData;
          3'd4,3'd5 : coexWlanPTI <= coexPTIVIData;
          3'd6,3'd7 : coexWlanPTI <= coexPTIVOData;
        endcase
      end
    end  
    else if (stopRx_p)
    begin
      coexWlanPTI        <= 4'b0;
      coexWlanPTIToggle  <= ~coexWlanPTIToggle;
    end
  end
end


always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macHeaderCompletedDly <= 1'b0;
  else
    macHeaderCompletedDly <= macHeaderCompleted;
end

`endif // RW_WLAN_COEX_EN


////////////////////////////////////////////////////////////////////
////
//// Muxing for HW Error
////
////////////////////////////////////////////////////////////////////
assign macControlCs = (txExchangeEnabled) ? {macControllerMasterFSMCs,macControllerTxFSMCs} : {macControllerMasterFSMCs,1'b0,macControllerRxFSMCs};

// Latch the current states of the MAC Controller FSMs in case of HW Error.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macControlLs <= 8'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macControlLs <= 8'b0;
  else
    if (hwErr)
      macControlLs <= macControlCs;
end

//
//  | macControlCs[6:4] | macControllerMasterFSM |    
//  |     0x0           |                 IDLE   |
//  |     0x2           |        WAIT_TXRX_TRIG  |
//  |     0x3           |             ACTIVE_RX  |
//  |     0x4           |             ACTIVE_TX  |
//
//  When macControlCs[7:5] = 0x3
//  | macControlCs[3:0] | macControllerRxFSM | 
//  |     0x0           |          IDLE      |
//  |     0x1           |      RX_FRAME      |
//  |     0x2           |   RX_DECISION      |
//  |     0x3           | COMP_DURATION      |
//  |     0x4           |   RX_WAIT_END      |
//  |     0x5           |       TX_RESP      |
//  |     0x6           |  TX_STBC_RESP      |
//
//  When macControlCs[7:5] = 0x4
//  | macControlCs[4:0] | macControllerTxFSM        |
//  |     0x0           |                   IDLE    |
//  |     0x1           |               WAIT_DMA    |
//  |     0x2           |   DROPBW_LENGTH_UPDATE    |
//  |     0x3           |          COMP_DURATION    |
//  |     0x4           |             CHECK_TXOP    |
//  |     0x5           |                TX_PROT    |
//  |     0x6           |           RX_PROT_RESP    |
//  |     0x7           |  WAIT_RX_PROT_RESP_END    |
//  |     0x8           |                TX_DATA    |
//  |     0x9           |                RX_RESP    |
//  |     0xA           |       WAIT_RX_RESP_END    |
//  |     0xB           |          STATUS_UPDATE    |
//  |     0xC           |            CHECK_CFEND    |
//  |     0xD           |               TX_CFEND    |
//  |     0xE           |           TRIG_BACKOFF    |
//  |     0xF           |              SKIP_MPDU    |
//  |     0x10          |              PHY_ERROR    |

                                                       
                                                       
assign debugPortBWManagement = {txChBW,           // 2 
                                rxChBW,           // 2 
                                availableBW,      // 2
                                bwTx,             // 2
                                bwProtTx,         // 2
                                txBWSignaling,    // 1
                                txDynBW,          // 1
                                rxDynBW,          // 1
                                rxChBWInNonHT,    // 2
                                rxBWSignalingTA}; // 1

`ifdef RW_MAC_MIBCNTL_EN

////////////////////////////////////////////////////////////////////
////
//// MIB Controller interface
////
////////////////////////////////////////////////////////////////////
//Latching TX Frame Type
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txFrameType <= 2'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    txFrameType <= 2'b0;
  else if (typeTxValid == 1'b1)
    txFrameType <= typeTx;
end



// Basic MIB set
assign mibdot11WEPExcludedCount = !rxFrmDiscard && incorrectRcved_p;
assign mibdot11FCSErrorCount = !rxFrmDiscard && incorrectRcved_p;
assign mibrwRxPHYErrorCount = macPhyIfRxErrInt_p;
assign mibrwRxFIFOOverflowCount = rxFrmDiscard && incorrectRcved_p;
assign mibrwTxUnderrunCount = 1'b0;

// EDCA MIB set 
assign mibrwQosUTransmittedMPDUCount = !txBcMc && !swRTS_p && mpduSuccess_p && ((txFrameType == 2'b00) || (txFrameType == 2'b10));
assign mibrwQosGTransmittedMPDUCount =  txBcMc && !swRTS_p && mpduSuccess_p && ((txFrameType == 2'b00) || (txFrameType == 2'b10));
assign mibdot11QosFailedCount = retryLimitReached_p;
assign mibdot11QosRetryCount = !txBcMc && !swRTS_p && mpduSuccess_p && ((txFrameType == 2'b00) || (txFrameType == 2'b10)) && (numMPDURetries != 8'd0);
assign mibdot11QosRTSSuccessCount = rtsSuccess_p;
assign mibdot11QosRTSFailureCount = rtsFailed_p;
assign mibrwQosACKFailureCount = (!txAMSDUPresent && (retryLimitReached_p || retryFrame_p) && !rtsFailed_p);
assign mibrwQosUReceivedMPDUCount = !txExchangeEnabled && !notMineRcved && !bcMcRcved && correctRcved_p;
assign mibrwQosGReceivedMPDUCount = !txExchangeEnabled && bcMcRcved && correctRcved_p;
assign mibrwQosUReceivedOtherMPDU = !txExchangeEnabled && notMineRcved && correctRcved_p;
assign mibdot11QosRetriesReceivedCount = !txExchangeEnabled && rxRetry && correctRcved_p;
// A-MSDU MIB set txAMSDUPresent,
assign mibrwUTransmittedAMSDUCount = txAMSDUPresent && mibrwQosUTransmittedMPDUCount;
assign mibrwGTransmittedAMSDUCount = txAMSDUPresent && mibrwQosGTransmittedMPDUCount;
assign mibdot11FailedAMSDUCount = txAMSDUPresent && mibdot11QosFailedCount;
assign mibdot11RetryAMSDUCount = txAMSDUPresent && mibdot11QosRetryCount;
assign mibdot11TransmittedOctetsInAMSDU = (txAMSDUPresent) ? MPDUFrameLengthTx : 16'b0;
assign mibdot11AMSDUAckFailureCount = txAMSDUPresent && mibrwQosACKFailureCount;
assign mibrwUReceivedAMSDUCount = rxAMSDUPresent && mibrwQosUReceivedMPDUCount;
assign mibrwGReceivedAMSDUCount = rxAMSDUPresent && mibrwQosGReceivedMPDUCount;
assign mibrwUReceivedOtherAMSDU = rxAMSDUPresent && mibrwQosUReceivedOtherMPDU;
assign mibdot11ReceivedOctetsInAMSDUCount = (rxAMSDUPresent && correctRcved_p) ? rxLength : 16'b0;
// A-MPDU MIB set
assign mibdot11TransmittedAMPDUCount = aMPDU && startTx_p;
assign mibdot11TransmittedMPDUInAMPDUCount = aMPDU && mpduDone_p;
assign mibdot11TransmittedOctetsInAMPDUCount = (aMPDU && mpduDone_p) ? MPDUFrameLengthTx : 16'b0;
assign mibrwUAMPDUReceivedCount = !notMineRcvedCapt && !bcMcRcvedCapt && ampduCorrectRcved_p;
assign mibrwGAMPDUReceivedCount = bcMcRcvedCapt && ampduCorrectRcved_p;
assign mibrwOtherAMPDUReceivedCount = notMineRcvedCapt && ampduCorrectRcved_p;
assign mibdot11MPDUInReceivedAMPDUCount = rxAggregation && correctRcved_p;
assign mibdot11ReceivedOctetsInAMPDUCount =  (rxAggregation && ampduCorrectRcved_p) ? rxLength : 16'b0;
assign mibdot11AMPDUDelimiterCRCErrorCount = (ampduCorrectRcved_p || ampduIncorrectRcved_p) ? incorrectDelCnt : 8'b0;
assign mibdot11ImplicitBARFailureCount = aMPDU && mpduFailed_p;
assign mibdot11ExplicitBARFailureCount = (tsValid && (fcType == 2'b01) && (fcSubtype == 4'b1000)) && retryFrame_p && statusUpdated_p;

// 20/40/80/160 MHz MIB set
assign mibdot1120MHzFrameTransmittedCount  = (txChBW == 2'd0) ? startTx_p : 1'b0;
assign mibdot1140MHzFrameTransmittedCount  = (txChBW == 2'd1) ? startTx_p : 1'b0;
assign mibdot1180MHzFrameTransmittedCount  = (txChBW == 2'd2) ? startTx_p : 1'b0;
assign mibdot11160MHzFrameTransmittedCount = (txChBW == 2'd3) ? startTx_p : 1'b0;
assign mibdot1120MHzFrameReceivedCount     = (rxChBW == 2'd0) ? frameCorrectlyRcved_p : 1'b0;
assign mibdot1140MHzFrameReceivedCount     = (rxChBW == 2'd1) ? frameCorrectlyRcved_p : 1'b0;
assign mibdot1180MHzFrameReceivedCount     = (rxChBW == 2'd2) ? frameCorrectlyRcved_p : 1'b0;
assign mibdot11160MHzFrameReceivedCount    = (rxChBW == 2'd3) ? frameCorrectlyRcved_p : 1'b0;

assign frameCorrectlyRcved_p = (!rxAggregation && correctRcved_p) || (rxAggregation && ampduCorrectRcved_p);

// STBC MIB set
assign mibdot11DualCTSSuccessCount = 1'b0;//$todo
assign mibdot11STBCCTSSuccessCount = 1'b0;//$todo
assign mibdot11STBCCTSFailureCount = 1'b0;//$todo
assign mibdot11nonSTBCCTSSuccessCount = 1'b0;//$todo
assign mibdot11nonSTBCCTSFailureCount = 1'b0;//$todo

// MIB Control
assign mibTIDIndex = (txExchangeEnabled) ? txTID[2:0] : rxTID[2:0];
assign mibTrigger = correctRcved_p || startTx_p || incorrectRcved_p || ampduCorrectRcved_p || updateDMAStatus_p || (aMPDU && mpduDone_p) || (!macPhyIfRxErr_p && macPhyIfRxErrInt_p);

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    notMineRcvedCapt <= 1'b0;
    bcMcRcvedCapt    <= 1'b0;
  end
  else if (correctRcved_p)
  begin
    notMineRcvedCapt <= notMineRcved;
    bcMcRcvedCapt    <= bcMcRcved;
  end
end

`endif // RW_MAC_MIBCNTL_EN

assign rxLength = ((rxFormatMod == 3'd2) || (rxFormatMod == 3'd3) || (rxFormatMod == 3'd4)) ? rxHTLength : {4'b0,rxLegLength};


// Generation of macPhyIfRxErrInt_p which is macPhyIfRxErr_p delayed of one clock cycle
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPhyIfRxErrInt_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macPhyIfRxErrInt_p <= 1'b0;
  else
    macPhyIfRxErrInt_p <= macPhyIfRxErr_p;
end


assign debugPortMACController1 = {txParameterHDReady_p,    
                                  txParameterPTReady_p,    
                                  txParameterNextPTReady_p,
                                  toggleHDSet_p,           
                                  togglePTSet_p,           
                                  clearSets_p,             
                                  statusUpdated_p,         
                                  swRTS_p,                 
                                  txMpduDone_p,            
                                  ampduFrm_p,              
                                  retryFrame_p,            
                                  rtsSuccess_p || mpduSuccess_p,
                                  rtsFailed_p || mpduFailed_p,
                                  retryLimitReached_p,
                                  txExchangeEnabled,
                                  txSuccessful_p || retry_p || retryLTReached_p // Backoff trigger
                                 }; 
                    

endmodule
                       