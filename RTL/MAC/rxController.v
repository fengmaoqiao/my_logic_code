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
// Description      : Top level of rxController module
//                    
// Simulation Notes : 
//    For simulation, two defines are available
//
//    RW_SIMU_ON    : which creates string signals to display the FSM states on  
//                 the waveform viewer.
//
//    RW_ASSERT_ON  : which enables System Verilog Assertions.
//
//    ENCRYPTION : which enables Encryption support.
//
// Synthesis Notes  :
// Application Note :                                                       
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


module rxController( 
            ///////////////////////////////////////////////
            //$port_g Clock and reset
            ///////////////////////////////////////////////
            input wire         macCoreRxClk,            // MAC Core Receive Clock
            input wire         macCoreClkHardRst_n,     // Hard Reset of the MAC Core Clock domain 
                                                        // active low
            input wire         macCoreClkSoftRst_n,     // Soft Reset of the MAC Core Clock domain
                                                        // active low
            ///////////////////////////////////////////////
            //$port_g DMA Engine
            ///////////////////////////////////////////////
            input wire         rxFrmDiscard,            // Discard current frame
            input wire         rxDescAvailable,         // Indicate that the DMA has all the needed desc for the current rxFrame

            ///////////////////////////////////////////////
            //$port_g MAC Controller
            ///////////////////////////////////////////////
            input wire         stopRx_p,                // Stop Rx

            input wire         activeRx,                // Current state Master is active Rx and Rx FSM is not IDLE
            input wire         rxAck,                   // Force receive only ACK after Tx
            input wire         rxCts,                   // Force receive only CTS after RTS Tx
            input wire         lSIGTXOPDetected,        // Flag indicates current received packet is LSIG TXOP protected
            input wire         txInProgress,            // Tx is ongoing
            
            output wire        dataFrame,               // Type of frame is data
            output wire        reservedRcved,           // Reserved received
            output wire        ackRcved_p,              // ACK received
            output wire        rtsRcved_p,              // RTS received
            output wire        ctsRcved_p,              // CTS received
            output wire        cfEndRcved_p,            // CF-End received
            output wire        baRcved_p,               // BA received
            output wire        barRcved_p,              // BAR received
            output wire        needAckRcved_p,          // Data or management received with ACK needed
            output wire        bcMcRcved_p,             // Broadcast/Multicast received
            output wire        bcnRcved_p,              // Beacon received
            output wire        probRespRcved_p,         // Probe response received
            output wire        notMineRcved_p,          // Frame received but not mine
            output wire        unknownRcved_p,          // Unknown frame received
            output wire        macHeaderCompleted,      // End of MAC Header reception
            output wire        notMinePsPollRcved_p,    // PS-Poll received but not mine
            output wire        notMineRtsRcved_p,       // RTS received but not mine
            output wire [1:0]  rxFCType,                // Indicates the fcType field of the received frame

            output wire        correctRcved_p,          // Frame received correctly
            output wire        incorrectRcved_p,        // Frame not received correctly
            
            output wire [47:0] rxAddr2,                 // Receiver addr
            output wire        rxAMSDUPresent,          // A-MSDU Present
            output wire [1:0]  rxAckPolicy,             // Ack policy (Ack, No Ack, BA)
            output wire [3:0]  rxTID,                   // TID
            output wire [31:0] rxHTCtrl,                // HT control
            output wire        rxMoreFrag,              // More fragment
            output wire        rxRetry,                 // Retry
            output wire        rxMoreData,              // More data
            output wire        rxOrder,                 // Order
            output wire        bcMcRcved,               // Broadcast/Multicast
            output wire        notMineRcved,            // Frame received but not mine
            output wire        rxBWSignalingTA,         // Indicate that the received frame has a Bandwidth Signaling TA
            
            ///////////////////////////////////////////////
            //$port_g Backoff Engine
            ///////////////////////////////////////////////
            input wire         backOffDone_p,           // Backoff completed
            input wire [2:0]   activeAC,                // Indicates which AC is currently selected.


            ///////////////////////////////////////////////
            //$port_g Doze controller
            ///////////////////////////////////////////////
            output wire        timWakeUp,               // AP has data -> wake-up
            output wire        timSleep,                // AP has no data -> sleep
            
            ///////////////////////////////////////////////
            //$port_g NAV
            ///////////////////////////////////////////////
            output wire        navClear_p,              // Clear NAV
            output wire        navUpdate_p,             // Update NAV with frame duration
            output wire [15:0] rxFrameDuration,         // Frame duration
            output wire        navCfpDurRemUpdate_p,    // Update NAV with CFP duration remaining
            output wire [15:0] cfpDurRemaining,         // CFP duration remaining
            output wire        navLsigUpdate_p,         // Update NAV with LSIG !!!
            
            ///////////////////////////////////////////////
            //$port_g MAC Timer unit
            ///////////////////////////////////////////////
            output wire        dtimUpdate_p,            // Update DTIM element
            output wire [7:0]  dtimCnt,                 // DTIM counter
            
            output wire        cfpUpdate_p,             // Update CFP element
            output wire [7:0]  cfpCnt,                  // CFP counter
            
            output wire        tsfUpdate_p,             // Update TSF
            output wire        tsfOffsetUpdate_p,       // Update TSF Offset
            output wire [63:0] timeStamp,               // Timestamp
            
            output wire        olbcUpdate_p,            // Update OLBC counter

            output wire        lastRxWrong,             // Last received packet wrong

            ///////////////////////////////////////////////
            //$port_g Encryption Engine
            ///////////////////////////////////////////////
            input wire         wepTkipPassed_p,         // Indicates WEP/TKIP decryption was a success
            input wire         wepTkipFailed_p,         // Indicates WEP/TKIP decryption was a failure
            input wire         ccmpPassed_p,            // Indicates CCMP description was a success
            input wire         ccmpFailed_p,            // Indicates CCMP description was a failure
`ifdef RW_WAPI_EN
            output wire        rxWAPI,                  // Flag indicating wapi encrypted frame reception
            input wire         wapiPassed_p,            // WAPI decryption succesfull pulse 
            input wire         wapiFailed_p,            // WAPI decryption failed pulse 
`endif //RW_WAPI_EN
            
            input wire [7:0]   plainDataOut,            // Decrypted data for writing into RX FIFO
            input wire         plainOutDataValid,       // Decrypted data valid
            
            input wire         plainOutDataEnd_p,       // End of Decrypted data pulse
            input wire         plainOutICVEnd_p,        // End of ICV field pulse
            input wire         plainOutFCSValid,        // FCS field valid

            input wire         encrBufferFull,          // Encryption Buffer full flag
            
            output wire        rxControlIdle,           // RX Controller FSM in idle
`ifdef RW_WAPI_EN
            output wire [15:0]  rxFrmCtrl,              // Frame control field      
            output wire [47:0]  rxAddr3,                // Address 3 field      
            output wire [47:0]  rxAddr4,                // Address 4 field                
            output wire [15:0]  rxQoSControl,           // QoS field
            output wire [15:0]  rxSeqCtrl,              // Sequence control
            output wire [7:0]   rxWAPIKeyIndex,         // WAPI key index field           
            output wire [127:0] rxWAPIPN,               // WAPI packet number(PN) field   
`endif //RW_WAPI_EN
            output wire [47:0] rxAddr1,                 // Addr1
            output wire [23:0] rxInitVector,            // IV
            output wire [47:0] rxTkipSeqCntr,           // TKIP Sequence Counter for TKIP decryption
            output wire [15:0] rxPayLoadLen,            // Frame length including ICV or MIC and FCS
            output wire        rxAddress4Pres,          // Rx flag indicating address 4 is present
            output wire        rxQoSFrame,              // Rx flag indicating the current frame is a QoS Frame
            output wire        rxFifoReady,             // Flow control for receiving decrypted data
            output wire        rxError_p,               // Indicates received frame can be discarded
            output wire        encrRxBufFlush_p,        // Flush after end of reception
            output wire        initEncrRxCntrl_p,       // Starting decryption sequence
            output wire        rxCryptoKeyValid,        // Validating Key
            output wire        nullKeyFound,            // Null Key found in RAM

            output wire        pushRxDataInBuffer,      // Write pulse to Encryption buffer
            output wire [7:0]  wrDataToEncrBuffer,      // Write data to Encryption buffer
            output wire        rxCCMPAADwrEn_p,         // Write enable to CCMP for AAD writing

            ///////////////////////////////////////////////
            //$port_g Key Search Engine
            ///////////////////////////////////////////////
            input wire         keyStorageValid_p,       // Key Storage Index Valid
            input wire         keyStorageError_p,       // Error indicating MAC address not found
           
            input wire [9:0]   rxKeyIndexReturn,        // Key Storage Index
            input wire [1:0]   sppKSR,                  // SPP from RAM
            input wire [2:0]   cTypeKSR,                // Cipher Type from RAM
            input wire [3:0]   vlanIDKSR,               // Virtual LAN ID from RAM
            input wire         useDefKeyKSR,            // Use Default Key from RAM

            output wire        indexSearchTrig_p,       // Trigger for searching index from MAC address
            output wire        rxKeySearchIndexTrig_p,  // Trigger for searching parameter from index
            output wire [9:0]  rxKeySearchIndex,        // RAM Index to be searched
            
            ///////////////////////////////////////////////
            //$port_g MAC-PHY interface
            ///////////////////////////////////////////////
            input wire         macPhyIfRxErr_p,         // Rx error from MAC-PHY if. resynchronized
            input wire         macPhyIfRxEndForTiming_p,// Rx end for timing from MAC-PHY if. resynchronized
            input wire         mpIfTxEn,                // Indicates that TX is in progress
            input wire         macPHYIFOverflow,        // Overflow Indication
            
            ///////////////////////////////////////////////
            //$port_g A-MPDU Deaggregator
            ///////////////////////////////////////////////
            input wire [11:0]  rxLegLength,             // Legacy length
            input wire [ 3:0]  rxLegRate,               // Legacy rate
            input wire [19:0]  rxHTLength,              // HT length
            input wire [ 6:0]  rxMCS,                   // MCS
            input wire         rxPreType,               // Preamble type
            input wire [ 2:0]  rxFormatMod,             // Format and modulation
            input wire [ 1:0]  rxChBW,                  // Channel bandwidth
            input wire         rxShortGI,               // Short Guard Interval
            input wire         rxSmoothing,             // Smoothing
            input wire         rxLSIGValid,             // L-SIG Valid
            input wire [ 1:0]  rxSTBC,                  // Space Time Block Coding
            input wire         rxSounding,              // Sounding
            input wire [ 1:0]  rxNumExtnSS,             // Number of Extension Spatial Streams
            input wire         rxAggregation,           // MPDU aggregate
            input wire         rxFecCoding,             // FEC Coding
            input wire [ 2:0]  rxReserved1,             // Reserved
            input wire [ 7:0]  rxAntennaSet,            // Antenna set
            input wire [ 2:0]  rxnSTS,                  // Number of STS       
            input wire         rxDynBW,                 // Dynamique Bandwidth 
            input wire         rxDozeNotAllowed,        // TXOP PS not allowed 
            input wire [ 8:0]  rxPartialAID,            // Partial AID         
            input wire [ 5:0]  rxGroupID,               // Group ID            
            input wire [ 7:0]  rxRSSI1,                 // RSSI for RxChain 1
            input wire [ 7:0]  rxRSSI2,                 // RSSI for RxChain 2
            input wire [ 7:0]  rxRSSI3,                 // RSSI for RxChain 3
            input wire [ 7:0]  rxRSSI4,                 // RSSI for RxChain 4
            input wire [ 7:0]  rxReserved2,             // Reserved
            input wire [ 7:0]  rxRCPI,                  // Receive Channel Power Indicator
            input wire [ 7:0]  rxEVM1,                  // Error Vector Magnitude for space time stream 1
            input wire [ 7:0]  rxEVM2,                  // Error Vector Magnitude for space time stream 2
            input wire [ 7:0]  rxEVM3,                  // Error Vector Magnitude for space time stream 3
            input wire [ 7:0]  rxEVM4,                  // Error Vector Magnitude for space time stream 4
            input wire [ 7:0]  rxReserved3,             // Reserved
            input wire [ 7:0]  rxReserved4,             // Reserved
            input wire [ 7:0]  rxReserved5,             // Reserved
            input wire         rxVector1Valid_p,        // Rx vector 1 is available
            input wire         rxVector2Valid_p,        // Rx vector 2 is available
            
            input wire [7:0]   rxData,                  // Rx data extracted from MAC-PHY interface FIFO
            input wire         rxDataValid,             // Rx data is valid
            input wire         rxDataStart_p,           // Start of data flow
            input wire         rxDataEnd_p,             // End of data flow
            input wire         rxDataError_p,           // Rx data error (incorrect length)
            input wire         rxEndOfFrame_p,          // End of frame information

            input wire         ampduIncorrectRcved_p,   // A-MPDU not received correctly
            
            input wire [15:0]  rxByteCnt,               // Rx byte counter
            input wire [15:0]  rxMpduLength,            // Rx MPDU full length
            input wire         rxNDP,                   // Indicate that the received frame is a Null Data Packet
            input wire         correctDelimiter,        // Indicate that correct delimiter is found

            input wire  [1:0]  rxAMPDUCnt,              // Counter incremented at each A-MPDU reception
            input wire  [5:0]  rxMPDUCnt,               // Count the number of MPDU detected
            output wire        rxCntrlReady,            // Rx controller ready to receive data
            
            ///////////////////////////////////////////////
            //$port_g BA Controller
            ///////////////////////////////////////////////
            output wire        psBitmapUpdate_p,        // Update Bitmap request
            output wire        psBitmapDiscard_p,       // Discard Bitmap update request
            output wire        rxQoSEnd_p,              // FSM QoS end pulse
            
            output wire        baEnable,                // Enable BA Controller procedure

            output wire        barRcved,                // BAR received
            
            output wire [11:0] rxSN,                    // Sequence Number
            output wire [11:0] rxBASSN,                 // BA Starting Sequence Number
            
            ///////////////////////////////////////////////
            //$port_g Control and Status Register
            ///////////////////////////////////////////////
            input wire [3:0]   currentState,            // Current state of the core
            
            input wire         bssType,                 // BSS Type
            input wire         ap,                      // Access Point
            input wire         tsfMgtDisable,           // Disable HW management of TSF
            
            input wire [31:0]  tsfTimerHigh,            // TSF[63:32]
            input wire [31:0]  tsfTimerLow,             // TSF[31:0]
            
            input wire [47:0]  macAddr,                 // MAC Addr
            input wire [47:0]  macAddrMask,             // MAC Addr mask
            
            input wire [47:0]  bssID,                   // BSSID
            input wire [47:0]  bssIDMask,               // BSSID Mask
            
            input wire         excUnencrypted,          // Exclude unencrypted frames
            input wire         dontDecrypt,             // Don't decrypt frames
            input wire         acceptMulticast,         // Accept Multicast frames
            input wire         acceptBroadcast,         // Accept Broadcast frames
            input wire         acceptOtherBSSID,        // Accept other BSSID frames
            input wire         acceptErrorFrames,       // Accept error frames
            input wire         acceptUnicast,           // Accept Unicast frames
            input wire         acceptMyUnicast,         // Accept frames directed to this device
            input wire         acceptProbeReq,          // Accept Probe Request frames
            input wire         acceptProbeResp,         // Accept Probe Response frames
            input wire         acceptBeacon,            // Accept Beacon frames
            input wire         acceptAllBeacon,         // Accept all Beacon frames 
            input wire         acceptDecryptErrorFrames,// Accept frames which failed decryption
            input wire         acceptOtherMgmtFrames,   // Accept other management frames
            input wire         acceptBAR,               // Accept Block Ack Request frames
            input wire         acceptBA,                // Accept Block Ack frames
            input wire         acceptNotExpectedBA,     // Accept Block Ack Request frames received after SIFS
            input wire         acceptPSPoll,            // Accept PS-Poll frames
            input wire         acceptRTS,               // Accept RTS frames
            input wire         acceptCTS,               // Accept CTS frames
            input wire         acceptACK,               // Accept ACK frames
            input wire         acceptCFEnd,             // Accept CF-End frames
            input wire         acceptOtherCntrlFrames,  // Accept other control frames
            input wire         acceptData,              // Accept Data frames
            input wire         acceptCFWOData,          // Accept CF WithOut Data frames
            input wire         acceptQData,             // Accept QoS Data frames
            input wire         acceptQCFWOData,         // Accept QoS CF WithOut Data frames
            input wire         acceptQoSNull,           // Accept QoS Null frames
            input wire         acceptOtherDataFrames,   // Accept other Data frames
            input wire         acceptUnknown,           // Accept unknown frames

            output wire [7:0]  quietCount1In,           // Quiet Count 1
            output wire [7:0]  quietPeriod1In,          // Quiet Period 1
            output wire [15:0] quietDuration1In,        // Quiet Duration 1
            output wire [15:0] quietOffset1In,          // Quiet Offset 1
            output wire        quietElement1InValid,    // Indicates that the Quiet 1 registers have to be updated with Quiet 1 In elements

            output wire [7:0]  quietCount2In,           // Quiet Count 2
            output wire [7:0]  quietPeriod2In,          // Quiet Period 2
            output wire [15:0] quietDuration2In,        // Quiet Duration 2
            output wire [15:0] quietOffset2In,          // Quiet Offset 2
            output wire        quietElement2InValid,    // Indicates that the Quiet 2 registers have to be updated with Quiet 2 In elements
            
            output wire [7:0]  dtimPeriodIn,            // DTIM period
            output wire        dtimPeriodInValid,       // Indicates that the dtimPeriod register has to be updated with dtimPeriodIn
            output wire [7:0]  cfpPeriodIn,             // CFP period
            output wire        cfpPeriodInValid,        // Indicates that the cfpPeriod register has to be updated with cfpPeriodIn
 
            input wire         dynBWEn,                 // Enable the Dynamic Bandwidth
            
            output wire [4:0]  rxControlLs,             // RX Controller latched state
            output wire [4:0]  rxControlCs,             // RX Controller current state
            
            ///////////////////////////////////////////////
            //$port_g RX FIFO
            ///////////////////////////////////////////////
            input wire         rxFIFOAlmostFull,        // RX FIFO is almost full
            input wire         rxFIFOFull,              // RX FIFO is full
            
            output wire [3:0]  rxFIFOWrTag,             // RX Tag FIFO write data
            output wire [31:0] rxFIFOWrData,            // RX FIFO write data
            output wire        rxFIFOWrite,             // RX FIFO write enable
            
            ///////////////////////////////////////////////
            //$port_g Interrupt Controller
            ///////////////////////////////////////////////
            output wire        rxFIFOOverFlow,          // RX FIFO overflow
            output wire        baRxTrigger,             // Block-ACK Receive interrupt
            
            ///////////////////////////////////////////////
            //$port_g HW Error detected
            ///////////////////////////////////////////////
            input wire         hwErr,                   // HW error detected
            
            ///////////////////////////////////////////////
            //$port_g FCS
            ///////////////////////////////////////////////
            input wire         fcsOk,                   // FCS is ok
            
            output wire        fcsStartRx_p,            // Start FCS calculation
            output wire        fcsEnableRx,             // Enable FCS

            ///////////////////////////////////////////////
            //$port_g txParameters Cache
            ///////////////////////////////////////////////
            input wire         rxBA,                    // Indicate current tx frame is a single VHT Mpdu

            ///////////////////////////////////////////////
            //$port_g Debug ports
            ///////////////////////////////////////////////
            output wire [15:0] debugPortRxController,    // Debug port for validation
            output wire  [6:0] debugPortAMPDURxC,
            output wire [15:0] debugPortRxFrameDebug1,   // Debug port for validation
            output wire [15:0] debugPortRxFrameDebug2,   // Debug port for validation
            output wire [15:0] debugPortrxFIFOCntrl,     // Debug port for validation
            output wire [15:0] debugPortDecryptFsm       // Debug port for validation
            );


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
wire [63:0]  tsf;                     // TSF

wire         mgmtNoEncryptFrame;      // Management frame without encryption
wire         mgmtFrame;               // Management frame
wire         ctrlFrame;               // Control frame
wire         qosFrame;                // QoS frame
wire         htcFrame;                // HT or VHT frame with HTC field

wire         bcnRcved;                // Beacon
wire         probRespRcved;           // Probe response

wire         ctrlWrapRcved;           // Control Wrapper
wire         baRcved;                 // BA
wire         psPollRcved;             // PS-Poll
wire         rtsRcved;                // RTS
wire         ctsRcved;                // CTS
wire         ackRcved;                // ACK
wire         cfEndRcved;              // CF-End

wire         ctrlWrapFlag;            // Control Wrapper flag

wire         dataRcved;               // Data
wire         qosDataRcved;            // QoS Data
wire         qosNullRcved;            // QoS null

wire         compressedBA;            // Compressed BA

wire         toDS;                    // To DS
wire         fromDS;                  // From DS
wire         pwrMgt;                  // Power management
wire         protectedBit;            // Protected bit

wire         acceptRcved;             // Accept current frame

wire         addr1Match;              // ADDR1 match
wire         bssIDMatch;              // BSSID match

wire         rxFrmCtrlEn;             // Frame control field
wire         rxDurationIdEn;          // Duration / ID field
wire         rxAddr1En;               // ADDR1 field
wire         rxAddr2En;               // ADDR2 field
wire         rxAddr3En;               // ADDR3 field
wire         rxQoSCtrlEn;             // QoS control field
wire         rxHTCtrlEn;              // HT control field
wire         rxSeqCtrlEn;             // Sequence control field
wire         rxBACtrlEn;              // BA control field
wire         rxBASeqCtrlEn;           // BA Sequence control field
wire         rxInitVectorEn;          // IV field
wire         rxExtInitVectorEn;       // Extended IV field
wire         rxDtimCntEn;             // DTIM counter field
wire         rxDtimPeriodEn;          // DTIM period field
wire         rxCfpCntEn;              // CFP counter field
wire         rxCfpPeriodEn;           // CFP period field
wire         rxCfpDurRemainingEn;     // CFP Duration remaining field
wire         rxTimeStampEn;           // Timestamp field
wire         rxQuietCount1En;         // Quiet Count 1 field
wire         rxQuietPeriod1En;        // Quiet Period 1 field
wire         rxQuietDuration1En;      // Quiet Duration 1 field
wire         rxQuietOffset1En;        // Quiet Offset 1 field
wire         rxQuietCount2En;         // Quiet Count 2 field
wire         rxQuietPeriod2En;        // Quiet Period 2 field
wire         rxQuietDuration2En;      // Quiet Duration 2 field
wire         rxQuietOffset2En;        // Quiet Offset 2 field

wire [7:0]   stateByteCnt;            // Byte counter by states

wire         fcsCheck_p;              // FSM FCS check pulse
wire         rxDurationIdEnd_p;       // FSM Duration / ID end pulse
wire         rxAddr1End_p;            // FSM ADDR1 end pulse
wire         rxAddr2End_p;            // FSM ADDR1 end pulse
wire         carFrameCtrlEnd_p;       // FSM Carried frame control end pulse
wire         rxAddr3End_p;            // FSM ADDR3 end pulse
wire         rxSeqCtrlEnd_p;          // FSM Sequence Control end pulse
wire         rxBARCtrlEnd_p;          // FSM BAR control end pulse

wire         rxFIFODone_p;            // RX FIFO status done
wire [3:0]   macHeaderCnt;            // MAC header counter
wire         endHeaderDone;           // End of the Header done
wire         rxEndOfFrame;            // RX end of frame holded

wire         decrStatusValid_p;        // Decryption status valid pulse

`ifdef RW_MPDU_AC
wire [15:0]  rxLengthSub;             // sub value according to encryption or not for the full rx pkt
`else
wire [15:0]  payloadBufferLength;     // Payload length in buffers
`endif
wire         frmSuccessfulRcved;      // Frame successful for RX DMA
wire         fcsErrorRcved;           // FCS Error
wire         phyErrorRcved;           // PHY Error
wire         undefErrorRcved;         // Undefined Error
wire         rxFIFOOverFlowError;     // RX FIFO overflow
wire [2:0]   decrStatus;              // Decryption status
wire         frmBody;                 // Frame body completion

wire         startMacHdr;             // Start of the MAC Header
wire         endHeader;               // End of the Header
wire         endPayload;              // End of the Payload
wire         discardFrm;              // End of frame with discard command

wire         writeTrailer;            // Write trailer info


wire         padding4BytesFIFOEn;     // Padding 4 bytes enable
wire         padding4BytesWriteEn;    // Padding 4 bytes write enable
wire         padding2BytesFIFOEn;     // Padding 2 bytes enable

wire         rxDataSelect;            // Select data from Encryption Engine
wire         encrPadding4BytesFIFOEn; // Encryption padding 4 bytes enable
wire         encrPadding4BytesWriteEn;// Encryption padding 4 bytes write enable
wire         encrPadding2BytesFIFOEn; // Encryption padding 2 bytes enable
wire         rxControlToError_p;      // RX FSM goes to error
wire         rxControlToFrmBody_p;    // RX FSM goes to frame body
wire         acceptProtected;         // Accept protected frame
wire         rxInitVectorEnd_p;       // FSM IV end pulse
wire         rxExtIV_p;               // indicate if there is a ExtIV field
wire         rxIndexSearchDone;       // Key search Engine done searching
wire         myFrameRcvedTrig_p;      // my Frame pulse trigger for KSR
wire [1:0]   rxDefKeyID;              // Default Key ID

wire [3:0]   subTypeFrame;            // Subtype
wire [1:0]   typeFrame;               // Type
wire         protocolError;           // Protocol error

`ifndef RW_WAPI_EN
wire [15:0]  rxSeqCtrl;               // Sequence control
`endif //RW_WAPI_EN

wire [31:0]  rxExtInitVector;         // Extended IV

wire         keyIndexCapture_p;       // Key Index returned by keySearch capture pulse

wire         fcsOknDiscard;             // FCS OK and no discard frame from DMA
wire         acceptErrorFramesnDiscard; // accept  Error frame and no discard frame from DMA

wire         txInProgressDly;         // captured of txInProgress on rxVector1_valid

wire         rxBADly;                 // capture of rxBA

wire         acceptError_p;           // Pulse to indicate that writeTrailer to accept Error frame (others than FCS error)


wire         rxCntrlReadyInt;         // Rx controller ready to receive data
wire         decryptCntrlReady;       // Indicate that the Crypto is ready to receive data

`ifdef RW_WAPI_EN
wire         rxAddr4En;               // ADDR4 field          
wire         rxWAPIKeyIdxEn;          // WAPI KeyIdx field    
wire         rxWAPIPNEn;              // WAPI PN field        

wire         rxAddr4End_p;               // FSM ADDR4 pulse        
wire         rxWAPIKeyIdxEnd_p;          // FSM WAPI KeyIdx pulse  
wire         rxWAPIPNEnd_p;              // FSM WAPI PN pulse      
`endif //RW_WAPI_EN

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

assign fcsOknDiscard             = (fcsOk && !rxFrmDiscard);
assign acceptErrorFramesnDiscard = (acceptErrorFrames && !rxFrmDiscard);

assign rxCntrlReady = decryptCntrlReady & rxCntrlReadyInt;

assign rxFCType = typeFrame;
  
// RX Control FSM
rxControllerFsm U_rxControllerFsm (
    // Clock and reset
		.macCoreRxClk             (macCoreRxClk),
		.macCoreClkHardRst_n      (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n      (macCoreClkSoftRst_n),
    // DMA Engine
		.rxFrmDiscard             (rxFrmDiscard),
		.rxDescAvailable          (rxDescAvailable),
    // MAC Controller
		.stopRx_p                 (stopRx_p),
		.lSIGTXOPDetected         (lSIGTXOPDetected),
		.rxCts                    (rxCts),
		.rxAck                    (rxAck),
		.correctRcved_p           (correctRcved_p),
		.incorrectRcved_p         (incorrectRcved_p),
    // Backoff Engine
		.backOffDone_p            (backOffDone_p),
    // Doze controller
		.timWakeUp                (timWakeUp),
		.timSleep                 (timSleep),
    // NAV
		.navClear_p               (navClear_p),
		.navUpdate_p              (navUpdate_p),
		.navCfpDurRemUpdate_p     (navCfpDurRemUpdate_p),
		.navLsigUpdate_p          (navLsigUpdate_p),
    // MAC Timer unit
		.dtimUpdate_p             (dtimUpdate_p),
		.cfpUpdate_p              (cfpUpdate_p),
		.tsfUpdate_p              (tsfUpdate_p),
		.tsfOffsetUpdate_p        (tsfOffsetUpdate_p),
		.lastRxWrong              (lastRxWrong),
    // Encryption Engine
		.wepTkipPassed_p          (wepTkipPassed_p),
		.wepTkipFailed_p          (wepTkipFailed_p),
		.ccmpPassed_p             (ccmpPassed_p),
		.ccmpFailed_p             (ccmpFailed_p),
`ifdef RW_WAPI_EN
    .rxWAPI                   (rxWAPI),
    .wapiPassed_p             (wapiPassed_p),
    .wapiFailed_p             (wapiFailed_p),
`endif //RW_WAPI_EN
		.plainOutFCSValid         (plainOutFCSValid),
		.rxPayLoadLen             (rxPayLoadLen),
		.rxCCMPAADwrEn_p          (rxCCMPAADwrEn_p),
    // Key Search Engine
		.sppKSR                   (sppKSR),
		.cTypeKSR                 (cTypeKSR),
    // Decryption FSM
		.rxDataSelect             (rxDataSelect),
		.encrPadding4BytesFIFOEn  (encrPadding4BytesFIFOEn),
		.nullKeyFound             (nullKeyFound),
		.rxControlToError_p       (rxControlToError_p),
		.rxControlToFrmBody_p     (rxControlToFrmBody_p),
		.decrStatusValid_p        (decrStatusValid_p),
		.acceptProtected          (acceptProtected),
		.rxInitVectorEnd_p        (rxInitVectorEnd_p),
		.rxExtIV_p                (rxExtIV_p),
		.rxIndexSearchDone        (rxIndexSearchDone),
    // MAC-PHY IF
		.mpIfTxEn                 (mpIfTxEn),
		.macPhyIfRxErr_p          (macPhyIfRxErr_p),
		.macPHYIFOverflow         (macPHYIFOverflow),
    // A-MPDU Deaggregator
		.rxFormatMod              (rxFormatMod),
		.rxLSIGValid              (rxLSIGValid),
		.rxAggregation            (rxAggregation),
		.rxData                   (rxData),
		.rxDataValid              (rxDataValid),
		.rxDataStart_p            (rxDataStart_p),
		.rxDataEnd_p              (rxDataEnd_p),
		.rxDataError_p            (rxDataError_p),
		.ampduIncorrectRcved_p    (ampduIncorrectRcved_p),
		.rxByteCnt                (rxByteCnt),
		.rxNDP                    (rxNDP),
		.rxCntrlReady             (rxCntrlReadyInt),
    // Frame decoder
		.protocolError            (protocolError),
		.mgmtNoEncryptFrame       (mgmtNoEncryptFrame),
		.mgmtFrame                (mgmtFrame),
		.ctrlFrame                (ctrlFrame),
		.dataFrame                (dataFrame),
		.qosFrame                 (qosFrame),
		.htcFrame                 (htcFrame),
		.bcMcRcved                (bcMcRcved),
		.bcnRcved                 (bcnRcved),
		.probRespRcved            (probRespRcved),
		.ctrlWrapRcved            (ctrlWrapRcved),
		.baRcved                  (baRcved),
		.barRcved                 (barRcved),
		.psPollRcved              (psPollRcved),
		.rtsRcved                 (rtsRcved),
		.ctsRcved                 (ctsRcved),
		.ackRcved                 (ackRcved),
		.cfEndRcved               (cfEndRcved),
		.ctrlWrapFlag             (ctrlWrapFlag),
		.dataRcved                (dataRcved),
		.qosDataRcved             (qosDataRcved),
		.qosNullRcved             (qosNullRcved),
		.reservedRcved            (reservedRcved),
		.toDS                     (toDS),
		.fromDS                   (fromDS),
		.protectedBit             (protectedBit),
		.rxAMSDUPresent           (rxAMSDUPresent),
		.compressedBA             (compressedBA),
		.acceptRcved              (acceptRcved),
		.addr1Match               (addr1Match),
		.bssIDMatch               (bssIDMatch),
		.rxFrmCtrlEn              (rxFrmCtrlEn),
		.rxDurationIdEn           (rxDurationIdEn),
		.rxAddr1En                (rxAddr1En),
		.rxAddr2En                (rxAddr2En),
		.rxAddr3En                (rxAddr3En),
`ifdef RW_WAPI_EN
    .rxAddr4En                (rxAddr4En),
    .rxWAPIKeyIdxEn           (rxWAPIKeyIdxEn),
    .rxWAPIPNEn               (rxWAPIPNEn),
`endif //RW_WAPI_EN
		.rxQoSCtrlEn              (rxQoSCtrlEn),
		.rxHTCtrlEn               (rxHTCtrlEn),
		.rxSeqCtrlEn              (rxSeqCtrlEn),
		.rxBACtrlEn               (rxBACtrlEn),
		.rxBASeqCtrlEn            (rxBASeqCtrlEn),
		.rxInitVectorEn           (rxInitVectorEn),
		.rxExtInitVectorEn        (rxExtInitVectorEn),
		.rxDtimCntEn              (rxDtimCntEn),
		.rxDtimPeriodEn           (rxDtimPeriodEn),
		.rxCfpCntEn               (rxCfpCntEn),
		.rxCfpPeriodEn            (rxCfpPeriodEn),
		.rxCfpDurRemainingEn      (rxCfpDurRemainingEn),
		.rxTimeStampEn            (rxTimeStampEn),
		.rxQuietCount1En          (rxQuietCount1En),
		.rxQuietPeriod1En         (rxQuietPeriod1En),
		.rxQuietDuration1En       (rxQuietDuration1En),
		.rxQuietOffset1En         (rxQuietOffset1En),
		.rxQuietCount2En          (rxQuietCount2En),
		.rxQuietPeriod2En         (rxQuietPeriod2En),
		.rxQuietDuration2En       (rxQuietDuration2En),
		.rxQuietOffset2En         (rxQuietOffset2En),
		.stateByteCnt             (stateByteCnt),
		.fcsCheck_p               (fcsCheck_p),
`ifdef RW_WAPI_EN
    .rxAddr4End_p             (rxAddr4End_p),     
    .rxWAPIKeyIdxEnd_p        (rxWAPIKeyIdxEnd_p),
    .rxWAPIPNEnd_p            (rxWAPIPNEnd_p),    
`endif //RW_WAPI_EN
		.rxDurationIdEnd_p        (rxDurationIdEnd_p),
		.rxAddr1End_p             (rxAddr1End_p),
		.rxAddr2End_p             (rxAddr2End_p),
		.carFrameCtrlEnd_p        (carFrameCtrlEnd_p),
		.rxAddr3End_p             (rxAddr3End_p),
		.rxSeqCtrlEnd_p           (rxSeqCtrlEnd_p),
		.rxQoSEnd_p               (rxQoSEnd_p),
		.rxBARCtrlEnd_p           (rxBARCtrlEnd_p),
		.macHeaderCompleted       (macHeaderCompleted),
		.rxControlIdle            (rxControlIdle),
    // BA Controller
		.psBitmapUpdate_p         (psBitmapUpdate_p),
		.psBitmapDiscard_p        (psBitmapDiscard_p),
		.baEnable                 (baEnable),
    // Control and Status Register
		.currentState             (currentState),
		.bssType                  (bssType),
		.ap                       (ap),
    .tsfMgtDisable            (tsfMgtDisable),
		.dontDecrypt              (dontDecrypt),
		.acceptErrorFrames        (acceptErrorFramesnDiscard),
		.acceptDecryptErrorFrames (acceptDecryptErrorFrames),
		.quietElement1InValid     (quietElement1InValid),
		.quietElement2InValid     (quietElement2InValid),
		.dtimPeriodInValid        (dtimPeriodInValid),
		.cfpPeriodInValid         (cfpPeriodInValid),
		.rxControlLs              (rxControlLs),
		.rxControlCs              (rxControlCs),
    // RX FIFO Interface Controller
		.rxFIFOOverFlow           (rxFIFOOverFlow),
		.rxFIFOFull               (rxFIFOFull),
		.rxFIFODone_p             (rxFIFODone_p),
		.rxFIFOWrite              (rxFIFOWrite),
		.macHeaderCnt             (macHeaderCnt),
 		.endHeaderDone            (endHeaderDone),
 		.rxEndOfFrame             (rxEndOfFrame),
 		.txInProgressDly          (txInProgressDly),
     `ifdef RW_MPDU_AC
		.rxLengthSub              (rxLengthSub),
    `else
		.payloadBufferLength      (payloadBufferLength),
    `endif
		.frmSuccessfulRcved       (frmSuccessfulRcved),
		.fcsErrorRcved            (fcsErrorRcved),
		.phyErrorRcved            (phyErrorRcved),
		.undefErrorRcved          (undefErrorRcved),
		.rxFIFOOverFlowError      (rxFIFOOverFlowError),
		.decrStatus               (decrStatus),
		.frmBody                  (frmBody),
		.startMacHdr              (startMacHdr),
		.endPayload               (endPayload),
		.discardFrm               (discardFrm),
		.acceptError_p            (acceptError_p),
		.writeTrailer             (writeTrailer),
		.padding4BytesFIFOEn      (padding4BytesFIFOEn),
		.padding4BytesWriteEn     (padding4BytesWriteEn),
		.padding2BytesFIFOEn      (padding2BytesFIFOEn),
    // HW Error detected
		.hwErr                    (hwErr),
    // Interrupt Controller
		.baRxTrigger              (baRxTrigger),
    // FCS
		.fcsOk                    (fcsOknDiscard),
		.fcsStartRx_p             (fcsStartRx_p),
		.fcsEnableRx              (fcsEnableRx)
		);


`ifdef ENCRYPTION
// Decryption FSM
decryptFsm U_decryptFsm (
    // Clock and reset
		.macCoreRxClk                     (macCoreRxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (macCoreClkSoftRst_n),
    // A-MPDU Deaggregator
		.rxData                           (rxData),
		.rxDataValid                      (rxDataValid),
		.decryptCntrlReady                (decryptCntrlReady),
    // Encryption Engine
		.plainOutDataValid                (plainOutDataValid),
		.plainOutDataEnd_p                (plainOutDataEnd_p),
		.plainOutICVEnd_p                 (plainOutICVEnd_p),
		.encrBufferFull                   (encrBufferFull),
		.rxFifoReady                      (rxFifoReady),
		.rxError_p                        (rxError_p),
		.encrRxBufFlush_p                 (encrRxBufFlush_p),
		.initEncrRxCntrl_p                (initEncrRxCntrl_p),
		.rxCryptoKeyValid                 (rxCryptoKeyValid),
		.nullKeyFound                     (nullKeyFound),
		.pushRxDataInBuffer               (pushRxDataInBuffer),
		.wrDataToEncrBuffer               (wrDataToEncrBuffer),
    // Key Search Engine
		.keyStorageValid_p                (keyStorageValid_p),
		.keyStorageError_p                (keyStorageError_p),
		.sppKSR                           (sppKSR),
		.cTypeKSR                         (cTypeKSR),
		.vlanIDKSR                        (vlanIDKSR),
		.useDefKeyKSR                     (useDefKeyKSR),
		.indexSearchTrig_p                (indexSearchTrig_p),
		.rxKeySearchIndexTrig_p           (rxKeySearchIndexTrig_p),
		.rxKeySearchIndex                 (rxKeySearchIndex),
    // RX Controller FSM
		.rxControlIdle                    (rxControlIdle),
		.rxControlToError_p               (rxControlToError_p),
		.rxControlToFrmBody_p             (rxControlToFrmBody_p),
		.decrStatusValid_p                (decrStatusValid_p),
		.acceptProtected                  (acceptProtected),
		.discardFrm                       (discardFrm),
		.rxFIFOOverFlowError              (rxFIFOOverFlowError),
		.rxInitVectorEnd_p                (rxInitVectorEnd_p),
		.rxExtIV_p                        (rxExtIV_p),
 		.rxIndexSearchDone                (rxIndexSearchDone),
    // Frame decoder
		.bcMcRcved                        (bcMcRcved),
		.ctrlFrame                        (ctrlFrame),
		.rxAMSDUPresent                   (rxAMSDUPresent),
		.barRcved_p                       (barRcved_p),
		.myFrameRcvedTrig_p               (myFrameRcvedTrig_p),
		.unknownRcved_p                   (unknownRcved_p),
		.rxDefKeyID                       (rxDefKeyID),
    // RX FIFO Interface Controller
		.endHeaderDone                    (endHeaderDone),
		.rxDataSelect                     (rxDataSelect),
		.encrPadding4BytesFIFOEn          (encrPadding4BytesFIFOEn),
		.encrPadding4BytesWriteEn         (encrPadding4BytesWriteEn),
		.encrPadding2BytesFIFOEn          (encrPadding2BytesFIFOEn),
		.keyIndexCapture_p                (keyIndexCapture_p),

		.debugPortDecryptFsm              (debugPortDecryptFsm)
		);
`endif


// Frame decoder
frameDecoder U_frameDecoder (
    // Clock and reset
		.macCoreRxClk             (macCoreRxClk),
		.macCoreClkHardRst_n      (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n      (macCoreClkSoftRst_n),
    // MAC Controller
		.activeRx                 (activeRx),
		.rxAck                    (rxAck),
		.rxCts                    (rxCts),
		.ackRcved_p               (ackRcved_p),
		.rtsRcved_p               (rtsRcved_p),
		.ctsRcved_p               (ctsRcved_p),
		.cfEndRcved_p             (cfEndRcved_p),
		.baRcved_p                (baRcved_p),
		.barRcved_p               (barRcved_p),
		.needAckRcved_p           (needAckRcved_p),
		.bcMcRcved_p              (bcMcRcved_p),
		.bcnRcved_p               (bcnRcved_p),
		.probRespRcved_p          (probRespRcved_p),
		.notMineRcved_p           (notMineRcved_p),
		.unknownRcved_p           (unknownRcved_p),
		.notMinePsPollRcved_p     (notMinePsPollRcved_p),
		.notMineRtsRcved_p        (notMineRtsRcved_p),
		.rxAddr2                  (rxAddr2),
		.notMineRcved             (notMineRcved),
    // NAV
		.rxFrameDuration          (rxFrameDuration),
		.cfpDurRemaining          (cfpDurRemaining),
    // MAC Timer unit
		.dtimCnt                  (dtimCnt),
		.cfpCnt                   (cfpCnt),
		.timeStamp                (timeStamp),
		.olbcUpdate_p             (olbcUpdate_p),
    // Encryption Engine
`ifdef RW_WAPI_EN
    .rxFrmCtrl                (rxFrmCtrl),
    .rxAddr3                  (rxAddr3),       
    .rxAddr4                  (rxAddr4),       
    .rxQoSControl             (rxQoSControl),
    .rxWAPIKeyIndex           (rxWAPIKeyIndex),
    .rxWAPIPN                 (rxWAPIPN),      
`endif //RW_WAPI_EN
		.rxAddr1                  (rxAddr1),
		.rxInitVector             (rxInitVector),
		.rxExtInitVector          (rxExtInitVector),
    // Decryption FSM
		.myFrameRcvedTrig_p       (myFrameRcvedTrig_p),
		.rxDefKeyID               (rxDefKeyID),
    // RX Controller FSM
		.rxFrmCtrlEn              (rxFrmCtrlEn),
		.rxDurationIdEn           (rxDurationIdEn),
		.rxAddr1En                (rxAddr1En),
		.rxAddr2En                (rxAddr2En),
		.rxAddr3En                (rxAddr3En),
`ifdef RW_WAPI_EN
    .rxAddr4En                (rxAddr4En),
    .rxWAPIKeyIdxEn           (rxWAPIKeyIdxEn),
    .rxWAPIPNEn               (rxWAPIPNEn),
`endif //RW_WAPI_EN
		.rxQoSCtrlEn              (rxQoSCtrlEn),
		.rxHTCtrlEn               (rxHTCtrlEn),
		.rxSeqCtrlEn              (rxSeqCtrlEn),
		.rxBACtrlEn               (rxBACtrlEn),
		.rxBASeqCtrlEn            (rxBASeqCtrlEn),
		.rxInitVectorEn           (rxInitVectorEn),
		.rxExtInitVectorEn        (rxExtInitVectorEn),
		.rxDtimCntEn              (rxDtimCntEn),
		.rxDtimPeriodEn           (rxDtimPeriodEn),
		.rxCfpCntEn               (rxCfpCntEn),
		.rxCfpPeriodEn            (rxCfpPeriodEn),
		.rxCfpDurRemainingEn      (rxCfpDurRemainingEn),
		.rxTimeStampEn            (rxTimeStampEn),
		.rxQuietCount1En          (rxQuietCount1En),
		.rxQuietPeriod1En         (rxQuietPeriod1En),
		.rxQuietDuration1En       (rxQuietDuration1En),
		.rxQuietOffset1En         (rxQuietOffset1En),
		.rxQuietCount2En          (rxQuietCount2En),
		.rxQuietPeriod2En         (rxQuietPeriod2En),
		.rxQuietDuration2En       (rxQuietDuration2En),
		.rxQuietOffset2En         (rxQuietOffset2En),
		.stateByteCnt             (stateByteCnt),
		.fcsCheck_p               (fcsCheck_p),
`ifdef RW_WAPI_EN
    .rxAddr4End_p             (rxAddr4End_p),     
    .rxWAPIKeyIdxEnd_p        (rxWAPIKeyIdxEnd_p),
    .rxWAPIPNEnd_p            (rxWAPIPNEnd_p),    
`endif //RW_WAPI_EN
		.rxDurationIdEnd_p        (rxDurationIdEnd_p),
		.rxAddr1End_p             (rxAddr1End_p),
		.rxAddr2End_p             (rxAddr2End_p),
		.carFrameCtrlEnd_p        (carFrameCtrlEnd_p),
		.rxAddr3End_p             (rxAddr3End_p),
		.rxSeqCtrlEnd_p           (rxSeqCtrlEnd_p),
		.rxQoSEnd_p               (rxQoSEnd_p),
		.rxBARCtrlEnd_p           (rxBARCtrlEnd_p),
		.rxControlIdle            (rxControlIdle),
		.mgmtNoEncryptFrame       (mgmtNoEncryptFrame),
		.mgmtFrame                (mgmtFrame),
		.ctrlFrame                (ctrlFrame),
		.dataFrame                (dataFrame),
		.qosFrame                 (qosFrame),
		.htcFrame                 (htcFrame),
		.bcMcRcved                (bcMcRcved),
		.bcnRcved                 (bcnRcved),
		.probRespRcved            (probRespRcved),
		.ctrlWrapRcved            (ctrlWrapRcved),
		.baRcved                  (baRcved),
		.barRcved                 (barRcved),
		.psPollRcved              (psPollRcved),
		.rtsRcved                 (rtsRcved),
		.ctsRcved                 (ctsRcved),
		.ackRcved                 (ackRcved),
		.cfEndRcved               (cfEndRcved),
		.ctrlWrapFlag             (ctrlWrapFlag),
		.dataRcved                (dataRcved),
		.qosDataRcved             (qosDataRcved),
		.qosNullRcved             (qosNullRcved),
		.reservedRcved            (reservedRcved),
		.toDS                     (toDS),
		.fromDS                   (fromDS),
		.rxMoreFrag               (rxMoreFrag),
		.rxRetry                  (rxRetry),
		.pwrMgt                   (pwrMgt),
		.rxMoreData               (rxMoreData),
		.protectedBit             (protectedBit),
		.rxOrder                  (rxOrder),
		.rxAMSDUPresent           (rxAMSDUPresent),
		.rxAckPolicy              (rxAckPolicy),
		.rxTID                    (rxTID),
		.rxBWSignalingTA          (rxBWSignalingTA),
		.rxHTCtrl                 (rxHTCtrl),
		.compressedBA             (compressedBA),
		.acceptRcved              (acceptRcved),
		.addr1Match               (addr1Match),
		.bssIDMatch               (bssIDMatch),
    // BA Controller
		.rxSeqCtrl                (rxSeqCtrl),
		.rxBASSN                  (rxBASSN),
    // A-MPDU Deaggregator
		.rxFormatMod              (rxFormatMod),
		.rxData                   (rxData),
		.rxDataValid              (rxDataValid),
    // Control and Status Register
		.macAddr                  (macAddr),
		.macAddrMask              (macAddrMask),
		.bssID                    (bssID),
		.bssIDMask                (bssIDMask),
		.excUnencrypted           (excUnencrypted),
		.acceptMulticast          (acceptMulticast),
		.acceptBroadcast          (acceptBroadcast),
		.acceptOtherBSSID         (acceptOtherBSSID),
		.acceptErrorFrames        (acceptErrorFramesnDiscard),
		.acceptUnicast            (acceptUnicast),
		.acceptMyUnicast          (acceptMyUnicast),
		.acceptProbeReq           (acceptProbeReq),
		.acceptProbeResp          (acceptProbeResp),
		.acceptBeacon             (acceptBeacon),
		.acceptAllBeacon          (acceptAllBeacon),
		.acceptOtherMgmtFrames    (acceptOtherMgmtFrames),
		.acceptBAR                (acceptBAR),
		.acceptBA                 (acceptBA),
		.acceptNotExpectedBA      (acceptNotExpectedBA),
		.acceptPSPoll             (acceptPSPoll),
		.acceptRTS                (acceptRTS),
		.acceptCTS                (acceptCTS),
		.acceptACK                (acceptACK),
		.acceptCFEnd              (acceptCFEnd),
		.acceptOtherCntrlFrames   (acceptOtherCntrlFrames),
		.acceptData               (acceptData),
		.acceptCFWOData           (acceptCFWOData),
		.acceptQData              (acceptQData),
		.acceptQCFWOData          (acceptQCFWOData),
		.acceptQoSNull            (acceptQoSNull),
		.acceptOtherDataFrames    (acceptOtherDataFrames),
		.acceptUnknown            (acceptUnknown),
		.quietCount1In            (quietCount1In),
		.quietPeriod1In           (quietPeriod1In),
		.quietDuration1In         (quietDuration1In),
		.quietOffset1In           (quietOffset1In),
		.quietCount2In            (quietCount2In),
		.quietPeriod2In           (quietPeriod2In),
		.quietDuration2In         (quietDuration2In),
		.quietOffset2In           (quietOffset2In),
		.dtimPeriodIn             (dtimPeriodIn),
		.cfpPeriodIn              (cfpPeriodIn),
		.dynBWEn                  (dynBWEn),
    // RX FIFO Controller
		.rxBADly                  (rxBADly),
		.subTypeFrame             (subTypeFrame),
		.typeFrame                (typeFrame),
		.protocolError            (protocolError)
		);


// RX FIFO Interface Controller
rxFIFOIfController U_rxFIFOIfController (
    // Clock and reset
		.macCoreRxClk             (macCoreRxClk),
		.macCoreClkHardRst_n      (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n      (macCoreClkSoftRst_n),
    // Timer unit
		.tsf                      (tsf),
    // Crypto Engine
		.plainDataOut             (plainDataOut),
		.plainOutDataValid        (plainOutDataValid),
    // Key Search Engine
		.keyStorageValid_p        (keyStorageValid_p),
		.rxKeyIndexReturn         (rxKeyIndexReturn),
    // Decryption FSM
		.rxDataSelect             (rxDataSelect),
		.encrPadding4BytesFIFOEn  (encrPadding4BytesFIFOEn),
		.encrPadding4BytesWriteEn (encrPadding4BytesWriteEn),
		.encrPadding2BytesFIFOEn  (encrPadding2BytesFIFOEn),
    // MAC-PHY interface
		.macPhyIfRxEndForTiming_p (macPhyIfRxEndForTiming_p),
		.macPhyIfRxErr_p          (macPhyIfRxErr_p),
    // A-MPDU Deaggregator
		.correctDelimiter         (correctDelimiter),
		.rxNDP                    (rxNDP),
		.rxLegLength              (rxLegLength),
		.rxLegRate                (rxLegRate),
		.rxHTLength               (rxHTLength),
		.rxMCS                    (rxMCS),
		.rxPreType                (rxPreType),
		.rxFormatMod              (rxFormatMod),
		.rxChBW                   (rxChBW),
		.rxShortGI                (rxShortGI),
		.rxSmoothing              (rxSmoothing),
		.rxLSIGValid              (rxLSIGValid),
		.rxSTBC                   (rxSTBC),
		.rxSounding               (rxSounding),
		.rxNumExtnSS              (rxNumExtnSS),
		.rxAggregation            (rxAggregation),
		.rxFecCoding              (rxFecCoding),
		.rxReserved1              (rxReserved1),
		.rxAntennaSet             (rxAntennaSet),
		.rxnSTS                   (rxnSTS),
		.rxDynBW                  (rxDynBW),
		.rxDozeNotAllowed         (rxDozeNotAllowed),
		.rxPartialAID             (rxPartialAID),
		.rxGroupID                (rxGroupID),
		.rxRSSI1                  (rxRSSI1),
		.rxRSSI2                  (rxRSSI2),
		.rxRSSI3                  (rxRSSI3),
		.rxRSSI4                  (rxRSSI4),
		.rxReserved2              (rxReserved2),
		.rxReserved3              (rxReserved3),
		.rxRCPI                   (rxRCPI),
		.rxEVM1                   (rxEVM1),
		.rxEVM2                   (rxEVM2),
		.rxEVM3                   (rxEVM3),
		.rxEVM4                   (rxEVM4),
		.rxReserved4              (rxReserved4),
		.rxReserved5              (rxReserved5),
 		.rxVector1Valid_p         (rxVector1Valid_p),
 		.rxVector2Valid_p         (rxVector2Valid_p),
		.rxData                   (rxData),
		.rxDataValid              (rxDataValid),
		.rxDataStart_p            (rxDataStart_p),
		.rxDataEnd_p              (rxDataEnd_p),
		.rxDataError_p            (rxDataError_p),
		.rxEndOfFrame_p           (rxEndOfFrame_p),
		.rxAMPDUCnt               (rxAMPDUCnt),
		.rxMPDUCnt                (rxMPDUCnt),
    // RX Controller FSM
		.rxControlIdle            (rxControlIdle),
		.rxMpduLength             (rxMpduLength),
    `ifdef RW_MPDU_AC
		.rxLengthSub              (rxLengthSub),
    `else
		.payloadBufferLength      (payloadBufferLength),
    `endif
		.frmSuccessfulRcved       (frmSuccessfulRcved),
		.fcsErrorRcved            (fcsErrorRcved),
		.phyErrorRcved            (phyErrorRcved),
		.undefErrorRcved          (undefErrorRcved),
		.rxFIFOOverFlowError      (rxFIFOOverFlowError),
		.decrStatus               (decrStatus),
		.frmBody                  (frmBody),
		.startMacHdr              (startMacHdr),
		.endPayload               (endPayload),
		.discardFrm               (discardFrm),
		.acceptError_p            (acceptError_p),
		.writeTrailer             (writeTrailer),
		.padding4BytesFIFOEn      (padding4BytesFIFOEn),
		.padding4BytesWriteEn     (padding4BytesWriteEn),
		.padding2BytesFIFOEn      (padding2BytesFIFOEn),
		.rxFIFODone_p             (rxFIFODone_p),
		.macHeaderCnt             (macHeaderCnt),
		.endHeader                (endHeader),
		.endHeaderDone            (endHeaderDone),
		.rxEndOfFrame             (rxEndOfFrame),
		.txInProgressDly          (txInProgressDly),
    // Frame decoder
		.subTypeFrame             (subTypeFrame),
		.typeFrame                (typeFrame),
		.ctrlFrame                (ctrlFrame),
		.addr1Match               (addr1Match),
		.acceptRcved              (acceptRcved),
		.bcMcRcved                (bcMcRcved),
		.rxBADly                  (rxBADly),
    // Decrypt FSM  
		.keyIndexCapture_p        (keyIndexCapture_p),
    // RX FIFO
		.rxFIFOAlmostFull         (rxFIFOAlmostFull),
		.rxFIFOWrTag              (rxFIFOWrTag),
		.rxFIFOWrData             (rxFIFOWrData),
		.rxFIFOWrite              (rxFIFOWrite),
    // MacController
		.txInProgress             (txInProgress),
    .rxBA                     (rxBA),
    // backoff
		.activeAC                 (activeAC),
    // Control and Status Register
		.acceptErrorFrames        (acceptErrorFramesnDiscard),
    // Interrupt Controller
		.rxFIFOOverFlow           (rxFIFOOverFlow),
    // Debug Port
		.debugPortrxFIFOCntrl     (debugPortrxFIFOCntrl)
		);

// Internal wires
assign tsf                  = {tsfTimerHigh, tsfTimerLow};

// Output ports
assign rxSN           = rxSeqCtrl[15:4];
assign rxTkipSeqCntr  = {rxExtInitVector, rxInitVector[7:0], rxInitVector[23:16]};
assign rxAddress4Pres = dataFrame && toDS && fromDS;
assign rxQoSFrame     = qosFrame;

// Debug ports
assign debugPortRxController =  {discardFrm,
                                 endPayload,
                                 endHeader,
                                 startMacHdr,
                                 addr1Match,
                                 bssIDMatch,
                                 acceptRcved,
                                 fcsOk,
                                 rxFIFOWrTag,
                                 rxFIFOWrite,
                                 rxFIFOAlmostFull,
                                 rxFIFOOverFlow,
                                 baRxTrigger
                                 };

assign debugPortRxFrameDebug1 = {correctRcved_p || incorrectRcved_p,
                                 rxSeqCtrl[3:0],
                                 protectedBit,
                                 pwrMgt,
                                 rxMoreFrag,
                                 rxMoreData,
                                 rxRetry,
                                 subTypeFrame,
                                 typeFrame
                                 };

assign debugPortRxFrameDebug2 = {correctRcved_p,
                                 rxSeqCtrl[9:4],
                                 addr1Match,
                                 rxAddr2[47:40]
                                 };

assign debugPortAMPDURxC = {baRcved,
                            acceptRcved,
                            addr1Match,
                            bssIDMatch,
                            discardFrm,
                            fcsOk,
                            baRxTrigger};


///////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////
// System Verilog Assertions
///////////////////////////////////////
`ifdef RW_ASSERT_ON

//$rw_sva This cover point checks if RX Controller have generated rxFIFOOverFlow
countRxFIFOOverFlow: cover property (@(posedge macCoreRxClk) (rxFIFOOverFlow));

`endif // RW_ASSERT_ON


endmodule
                 
