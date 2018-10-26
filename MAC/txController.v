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
// Description      : Top level of txController module
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


module txController( 
          //$port_g Clock and Reset interface
          input  wire        macCoreClk,            // MAC Core Clock
          input  wire        macCoreTxClk,          // MAC Core Transmit Clock
          input  wire        macCoreClkHardRst_n,   // Hard Reset of the MAC Core Clock domain 
                                                    // active low
          input  wire        macCoreTxClkSoftRst_n, // Soft Reset of the MAC Core Clock domain 
                                                    // active low
          //$port_g MAC Controller interface
          input  wire        sendData_p,            // Indication that data packet has to be sent
          input  wire        sendRTS_p,             // Indication that an RTS packet has to be sent
          input  wire        sendCTS_p,             // Indication that a CTS packet has to be sent
          input  wire        sendACK_p,             // Indication that an ACK packet has to be sent
          input  wire        sendCFEND_p,           // Indication that a CF-END packet has to be sent
          input  wire        sendBA_p,              // Indication that an Block ACK packet has to be sent
          input  wire        skipMPDU_p,            // Indication that MPDU in TX FIFO has to be discarded
          input  wire        sendOnSIFS,            // If set, data is sent on tickSIFS else on tickSlot
          input  wire        sendOnPIFS,            // If set, data is sent on tickPIFS

          input  wire [47:0] destAddr,              // Receiver address
          input  wire [47:0] srcAddr,               // Source address
          input  wire [15:0] duration,              // Duration
          input  wire        retry,                 // Indicates that the trame is a retry.
          input  wire [15:0] tsfDuration,           // Duration from the preamble until the first bit of TSF
          output wire  [3:0] txTID,                 // TID of the transmitted frame
          output wire  [1:0] typeTx,                // TYPE of the transmitted frame
          output wire        typeTxValid,           // Indicates the typeTx signal is valid
          output wire        txAMSDUPresent,        // Indicates than the transmitted frame is an A-MSDU
          output wire        txBcMc,                // Indicates than the transmitted frame has a group address.

          input  wire  [6:0] txMCS,                 // MCS (Only used for HT frame)
          input  wire [11:0] txLegLength,           // Legacy Length of the PPDU         
          input  wire [ 3:0] txLegRate,             // Legacy Rate of the PPDU.         
          input  wire  [1:0] txChBW,                // Transmit a Frame with Channel Bandwidth
          input  wire        txDynBW,               // Transmit a Frame with dynamic bandwidth
          input  wire        txBWSignaling,         // Transmit a Frame with BW signaling 
          input  wire [19:0] txHTLength,            // Length of the HT PPDU         
          input  wire  [1:0] txSTBC,                // Transmit a Frame with Space Time Block Coding
          input  wire        txDisambiguityBit,     // Transmit a Frame with disambiguityBit
          input  wire        txResp,                // Transmit a Response Frame
          input  wire        txFromReg,             // Transmit a HW generated frame based on Register
          input  wire        txFromHD,              // Transmit a HW generated frame based on THD
          input  wire        txFromFifo,            // Transmit a Frame from Tx FIFO
          input  wire        txCFEND,               // Transmit a HW generated CFEND frame
          output wire        txDone_p,              // Indicates the completion of the transmission
          output wire        mpduDone_p,            // Indicates that the MPDU has been sent
          output wire        sentCFEND,             // Indicates that the transmitted frame is a CF-END
          output wire        sentRTS,               // Indicates that the transmitted frame is a RTS
          output wire        sentBAReq,             // Indicates that the transmitted frame is a BA-Request
          output wire        skipMPDUDone_p,        // Indicates that MPDU contained in the TXFIFO has been discarded.

          //$port_g Key Search Engine interface
          input  wire  [2:0] cTypeRAM,              // Indicates the type of encryption
                                                    // 0 : No Key
                                                    // 1 : WEP
                                                    // 2 : TKIP
                                                    // 3 : CCMP

          //$port_g Encryption Engine interface
          
          // Shared by all encrypt mode
          output wire        txCsIsIdle,            // Indicates the FSM is out of IDLE
          output wire [15:0] txDataLength,          // Indicate the Tx Data to encrypted Length
          output wire        txCryptoKeyValid,      // Indicate that the key is valid
          output wire [47:0] txCCMPTKIPSeqCnt,      // Packet Number for TKIP and CCMP

          // Plain Data
          output wire  [7:0] txPlainData,           // Plain data out
          output wire        txPlainDataValid,      // Plain data valid
          output wire        txPlainDataEnd,        // Last byte valid

          // Encrypted Data
          input  wire  [7:0] txEncrData,            // Encrypted data in
          input  wire        txEncrDataValid,       // Encrypted data in Valid

          // WEP and TKIP SBOX Init
          output wire        txSBOXInit,            // Pulse to init the Encryption Engine SBOX for WEP and TKIP
          input  wire        txSBOXInitDone,        // Indicates that the initialisation of the Encryption Engine is completed for WEP and TKIP.
          output wire        txICVEnable,           // Pulse to start outputing ICV for WEP and TKIP

          // WEP Only
          output wire        txWEP,                 // WEP Mode
          output wire [23:0] txWEPIV,               // WEP IV
          output wire        txWEPIVValid,          // WEP IV Valid

          // TKIP Only
          output wire        txTKIP,                // TKIP Mode

          // CCMP Only
          input  wire        txCCMPBusy,            // High when aes is processing on Data
          input  wire        txCCMPMicDone,         // Get Mic Calculation Done
          output wire        txCCMP,                // CCMP Mode
          output wire        txCCMPStart,           // Start Data CCMP encrypt
          output wire        txCCMPHeaderValid,     // Plain Data is MAC Header
          output wire        txCCMPDataValid,       // Plain Data is Valid for CCMP ADD + Nonce + Data
          output wire        txCCMPAdd4Pres,        // Address 4 is present
          output wire        txCCMPQoSPres,         // Frame is QoS
          output wire [47:0] txCCMPAddr1,           // Address 1 Value
          output wire [47:0] txCCMPAddr2,           // Address 2 Value
          output wire        txCCMPHT,              // HT flag

`ifdef RW_WAPI_EN
          // WAPI Only
          output wire         txWAPI,                // WAPI Mode
          output wire         txWAPIStart,           // Start Data WAPI encrypt
          input  wire         txWAPIMicDone,         // Get WAPI Mic Calculation Done
          input  wire         txWAPIBusy,            // High when wpi is processing data
          
          output wire [15:0]  txWAPIFrameControl,    // MAC Header Frame Control Field
          output wire [47:0]  txWAPIAddr3,           // MAC Header Address 3 Field
          output wire [47:0]  txWAPIAddr4,           // MAC Header Address 4 Field
          output wire [15:0]  txWAPIQoSCF,           // MAC Header QoS Control Field
          output wire [15:0]  txWAPISeqControl,      // MAC Header Seauence Control Field
          output wire [7:0]   txWAPIKeyIdx,          // WAPI Header Key Index
          output wire [127:0] txWAPIPN,              // WAPI Header Packet Number (PN) Field
`endif //RW_WAPI_EN

          //$port_g FCS Block interface
          input  wire        fcsEnd_p,              // Indicates the end of the transmission
          input  wire        fcsBusy,               // Indicates that the FCS block is busy cannot accept new data.
          input  wire        fcsDOutValid,          // Indicates that the fcsDOut is valid.
          input  wire  [7:0] fcsDOut,               // Data from the FCS block
          
          output wire        fcsEnableTx,           // Indicates the begining of the transmission and enable the FCS block
          output wire        fcsStartTx_p,          // Indicates the begining of the transmission and enable the FCS block
          output wire        fcsShiftTx,            // Indicates FCS engine to append FCS calculated on data
          output wire        fcsDInValidTx,         // Indicates that the data on fcsDInTx is valid and can be processed.
          output reg   [7:0] fcsDInTx,              // Data to the FCS block
          output wire        fcsPauseTx,            // Indicates that the FCS block must stop the processing.
        
          //$port_g TX FIFO interface
          input  wire  [1:0] txFIFOMPDUDelimiters,  // MPDU delimiters from TX FIFO
          input  wire  [7:0] txFIFORdData,          // Read Data from TX FIFO
          input  wire        txFIFOEmpty,           // Indicates that the TX FIFO is empty
          input  wire        txFIFODataValid,       // Indicates when the txFIFORdData is Valid
          output wire        txFIFORead,            // Request a new byte from the TX FIFO
          output wire        txFIFOReadByFour,      // Read data by four bytes
          output wire        txFIFOReadByTwo,       // Read data by two bytes

          //$port_g Tx Parameters Cache interface
          input  wire        txParameterHDReady_p,  // Indicates if the Header Descriptor fields are usable 
          input  wire [15:0] MPDUFrameLengthTx,     // Indicates that a DATA packet has to be sent
          input  wire        useRIFSTx,             // Use RIFS for Transmission
          input  wire        preTypeProtTx,         // Preamble Type of Protection frame for Transmission
                                                    // 1'b0: SHORT
                                                    // 1'b1: LONG
          input  wire        preTypeTx,             // Preamble Type of PPDU for Transmission
                                                    // Same coding than preTypeTx
          input  wire  [2:0] formatModProtTx,       // Format and Modulation of Protection frame for Transmission
                                                    // 2'b00: NON-HT
                                                    // 2'b01: NON-HT-DUP-OFDM
                                                    // 2'b10: HT-MF
                                                    // 2'b11: HT-GF
          input  wire  [2:0] formatModTx,           // Format and Modulation of PPDU for Transmission
                                                    // Same coding than formatModProtTx
          input  wire  [7:0] txPwrLevelPT,          // Transmit Power Level
          input  wire  [7:0] txPwrLevelProtPT,      // Transmit Power Level for Protection Frame
          input  wire  [9:0] nBlankMDelimiters,     // Indicates the number of blank MPDU delimiters that are inserted
          input  wire  [8:0] partialAIDTx,          // Partial AID
          input  wire  [5:0] groupIDTx,             // Group ID
          input  wire        dozeNotAllowedTx,      // TXOP PS is not allowed
          input  wire        smoothingProtTx,       // Smoothing of Protection frame for Transmission
          input  wire        smoothingTx,           // Smoothing of PPDU for Transmission
          input  wire        soundingTx,            // Sounding Protection frame for Transmission
          input  wire  [2:0] nTxProtPT,             // Number of Transmit Chains for Protection Frame
          input  wire  [2:0] nTxPT,                 // Number of Transmit Chains for PPDU
          input  wire        txShortGI,             // Short Guard Interval for Transmission
                                                    // When High, it indicates whether a short Guard Interval
          input  wire  [1:0] stbcPT,                // Space Time Block Coding
          input  wire        txFecCoding,           // FEC Coding
          input  wire  [1:0] numExtnSSPT,           // Number of Extension Spatial Streams
          input  wire        beamFormedPT,          // BeamFormed frame
          input  wire  [7:0] smmIndexPT,            // Spatial Map Matrix Index
          input  wire  [7:0] antennaSetPT,          // Antenna Set
          input  wire        dontGenerateMH,        // Indicates that HW should not generate the MAC Header by itself
          input  wire        dontEncrypt,           // Indicates that HW should bypassed the encryption operation during tx.
          input  wire        dontTouchFC,           // Indicates that HW should not update the Frame Control field,
          input  wire        dontTouchDur,          // Indicates that HW should not update the Duration field
          input  wire        dontTouchQoS,          // Indicates that HW should not update the QoS field 
          input  wire        dontTouchHTC,          // Indicates that HW should not update the HTC field 
          input  wire        dontTouchTSF,          // Indicates that HW should not update the TSF field 
          input  wire        dontTouchDTIM,         // Indicates that HW should not update the DTIM Count field
          input  wire        dontTouchFCS,          // Indicates that HW should not update the FCS field
          input  wire        aMPDU,                 // Indicates whether this Transmit Header Descriptor belong to an A-MPDU
          input  wire  [1:0] whichDescriptor,       // Indicates what kind of a descriptor this is
          input  wire        txSingleVHTMPDU,        // Detect single MPDU in VHT

          //$port_g RX Controller interface
          input  wire  [7:0] respTxAntennaSet,      // Response Transmission with Antenna Set
          input  wire  [7:0] respTxSMMIndex,        // Response Transmission with Spatial Map Matrix Index

          input  wire        respTxPreType,         // Response Transmission with Preamble Type
                                                    // 1'b0: SHORT
                                                    // 1'b1: LONG

          input  wire  [2:0] respTxFormatMod,       // Response Transmission with Format and Modulation
                                                    // 3'b000: NON-HT
                                                    // 3'b001: NON-HT-DUP-OFDM
                                                    // 3'b010: HT-MF
                                                    // 3'b011: HT-GF
                                                    // 3'b100: VHT
          input  wire  [1:0] respTxNumExtnSS,       // Response Transmission with Number of Extension Spatial Streams
          input  wire        respTxFECCoding,       // Response Transmission with FEC Coding      
          input  wire  [2:0] respTxNTx,             // Response Transmission with Number of Transmit Chains for PPDU        
          input  wire        respTxShortGI,         // Response Transmission with Short Guard Interval
          input  wire  [3:0] rxTID,                 // TID of the received frame

          //$port_g BA Controller
          input  wire  [7:0] psBitmap,              // PS Bitmap field
          input  wire        psBitmapValid,         // PS Bitmap field valid          
          
          output wire        psBitmapReady,         // PS Bitmap field request

          //$port_g Timers Block interface
          input  wire [63:0] tsf,                   // TSF timer value
          input  wire        tickSIFS_p,            // A pulse to indicate the end of SIFS period
          input  wire        tickPIFS_p,            // A pulse to indicate the end of PIFS period
          input  wire        tickSlot_p,            // A pulse to indicate the end of a slot period
          input  wire  [7:0] dtimCnt,               // DTIM count maintained in hardware
          
          //$port_g MAC-PHY-IF Block interface
          input  wire        mpIfTxFifoFull,        // MAC-PHY FIFO status                      
          input  wire        mpIfTxErr_p,           // Transmit error 
          input  wire        mpIfTxEn,              // Transmit on-going indication 
          input  wire        macPhyIfRxCca,         // Receive on-going indication 

          output wire        startTx_p,             // Start Tx trigger                 
          output wire        stopTx_p,              // Stop Tx trigger                  

          output wire  [7:0] mpIfTxFifoData,        // Data to transmit                 
          output wire        mpIfTxFifoWrite,       // Data valid                       

          output wire  [7:0] txPwrLevel,            // Transmit power Level
          output wire  [1:0] chBW,                  // Channel Bandwidth        
          output wire  [1:0] chOffset,              // Channel Offset
                                                    //	0 - CH_OFF_20 - 20 MHz channel
                                                    //	1 - CH_OFF_40 - The entire 40 MHz channel
                                                    //	2 - CH_OFF_20U - Upper 20 MHz in 40 MHz
                                                    //	3 - CH_OFF_20L - Lower 20 MHz in 40 MHz
          output wire        smoothing,             // Smoothing Recommended or Not
          output wire        beamFormed,            // BeamFormed frame
          output wire  [7:0] antennaSet,            // Antenna Set
          output wire  [7:0] smmIndex,              // Spatial Map Matrix Index
          output wire  [6:0] mcs,                   // MCS (Only used for HT/VHT frame)
          output wire  [2:0] nSTS,                  // nSTS
          output wire        preType,               // Preamble Type
                                                    // 1'b0: SHORT
                                                    // 1'b1: LONG
          output wire  [2:0] formatMod,             // Format and Modulation         
                                                    // 3'b000: NON-HT
                                                    // 3'b001: NON-HT-DUP-OFDM
                                                    // 3'b010: HT-MF
                                                    // 3'b011: HT-GF
                                                    // 3'b100: VHT
          output wire  [1:0] numExtnSS,             // Number of Extension Spatial Streams         
          output wire  [1:0] stbc,                  // Space Time Block Coding         
          output wire        disambiguityBit,       // disambiguity Bit value
          output wire        fecCoding,             // FEC Coding
          output wire  [8:0] partialAID,            // Partial AID
          output wire  [5:0] groupID,               // Group ID
          output wire        dozeNotAllowed,        // TXOP PS is not allowed
          output wire        sounding,              // Indicates whether this PPDU is Sounding         
          output wire [11:0] legLength,             // Legacy Length of the PPDU         
          output wire [ 3:0] legRate,               // Legacy Rate of the PPDU.         
          output wire [15:0] service,               // Scrambler initialization
          output wire [19:0] htLength,              // Length of the HT PPDU         
          output wire [ 2:0] nTx,                   // Number of Transmit Chains         
          output wire        shortGI,               // Short Guard Interval         
          output wire        aggreation,            // MPDU Aggregate         

          //$port_g HW Error interface
          input  wire        hwErr,                 // HW error detected
          
          //$port_g CSReg Block interface
          input  wire [47:0] bssID,                 // BSS ID
          input  wire  [7:0] timOffset,             // Indicates to the HW the offset, from the first byte of the Beacon frame, 
                                                    // at which the first byte of the TIM field is located
          input  wire        pwrMgt,                // Power Management is enabled for the current
                                                    // transmission
          input  wire  [7:0] dsssMaxPwrLevel,       // Maximum Power Level for DSSS/CCK
          input  wire  [7:0] ofdmMaxPwrLevel,       // Maximum Power Level for OFDM frames
          input  wire        startTxSmoothing,      // Start Transmission with Smoothing
          input  wire  [7:0] startTxAntennaSet,     // Start Transmission with Antenna Set
          input  wire  [7:0] startTxSMMIndex,       // Start Transmission with Spatial Map Matrix Index
          input  wire        startTxPreType,        // Start Transmission with Preamble Type
                                                    // 1'b0: SHORT
                                                    // 1'b1: LONG
          input  wire  [2:0] startTxFormatMod,      // Start Transmission with Format and Modulation
                                                    // 3'b000: NON-HT
                                                    // 3'b001: NON-HT-DUP-OFDM
                                                    // 3'b010: HT-MF
                                                    // 3'b011: HT-GF
                                                    // 3'b100: VHT
          input  wire  [1:0] startTxNumExtnSS,      // Start Transmission with Number of Extension Spatial Streams
          input  wire [15:0] bbServiceA,            // Service field when the modulation is OFDM.
          input  wire [ 7:0] bbServiceB,            // Service field when the modulation is DSSS/CCK.
          input  wire [ 2:0] startTxNTx,            // Start Transmission with Number of Transmit Chains for PPDU        

          //$port_g Backoff interface
          input  wire  [2:0] activeAC,              // Indicates Access category which has currently won contention

          //$port_g Debug interface
          output reg   [8:0] txControlCs,           // Current state of the TX Controller FSM
          output reg   [8:0] txControlLs,           // State of the TX Controller FSM captured when the HW Error happened
          output reg  [15:0] debugPortTxFrameDebug1,// Tx Frame Debug 1
          output reg  [15:0] debugPortTxFrameDebug2 // Tx Frame Debug 2
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

wire        ctsDone_p;
wire        ctsTxStart_p;
wire        ctsFCSEnable;
wire        ctsFCSStart_p;
wire        ctsFCSShiftTx;
wire  [7:0] ctsFCSDInTx;    
wire        ctsFCSDInValidTx;

wire        rtsDone_p;
wire        rtsTxStart_p;
wire        rtsFCSEnable;
wire        rtsFCSStart_p;
wire        rtsFCSShiftTx;
wire  [7:0] rtsFCSDInTx;    
wire        rtsFCSDInValidTx;

wire        ackDone_p;
wire        ackTxStart_p;
wire        ackFCSEnable;
wire        ackFCSStart_p;
wire        ackFCSShiftTx;
wire  [7:0] ackFCSDInTx;    
wire        ackFCSDInValidTx;

wire        cfendDone_p;
wire        cfendTxStart_p;
wire        cfendFCSEnable;
wire        cfendFCSStart_p;
wire        cfendFCSShiftTx;
wire  [7:0] cfendFCSDInTx;    
wire        cfendFCSDInValidTx;

wire        baDone_p;
wire        baTxStart_p;
wire        baFCSEnable;
wire        baFCSStart_p;
wire        baFCSShiftTx;
wire  [7:0] baFCSDInTx;    
wire        baFCSDInValidTx;

wire        qosnullDone_p;
wire        qosnullTxStart_p;

wire        mpduTxStart_p;
wire        mpduFCSEnable;
wire        mpduFCSStart_p;
wire        mpduFCSShiftTx;
wire  [7:0] mpduFCSDInTx;    
wire        mpduFCSDInValidTx;

wire        sendMPDU_p;
wire        aMPDUPaddingStart_p;
wire        aMPDUDelimiterStart_p;
wire        addBlankDelimiter;
wire        aMPDUDelimiterDone_p;
wire        aMPDUPaddingDone_p;

wire  [7:0] aMPDUDelimiterData;  
wire        aMPDUDelimiterWriteEn;  

wire  [2:0] formatACKFSMCs;         // formatACKFSM FSM Current State
wire  [3:0] formatBAFSMCs;          // formatBAFSM FSM Current State
wire  [1:0] formatAMPDUDelFSMCs;    // formatAMPDUDelFSM FSM Current State
wire  [3:0] formatCFENDFSMCs;       // formatCFENDFSM FSM Current State
wire  [2:0] formatCTSFSMCs;         // formatCTSFSM FSM Current State
wire  [4:0] formatMPDUFSMCs;        // formatMPDUFSM FSM Current State
wire  [3:0] formatRTSFSMCs;         // formatRTSFSM FSM Current State
wire  [3:0] txControlMainFSMCs;     // txControlMainFSM FSM Current State
//reg   [3:0] txControlMainFSMCapt;   // txControlMainFSM FSM Current State capture when the transmission is done

wire        mpduSeqCtrlDone_p;      // Indicates that the sequence number has been transmitted

wire [14:0] formatMPDUFrameDebug1; // frame Debug 1 from formatMPDU module
wire [14:0] formatMPDUFrameDebug2; // frame Debug 2 from formatMPDU module

reg         tickSIFS;              // Captured version of tickSIFS_p
reg         tickSlot;              // Captured version of tickSlot_p
reg         tickPIFS;              // Captured version of tickPIFS_p

wire        stopTxInt_p;           // Stop Tx;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// TBD
assign qosnullDone_p = 1'b0;
assign qosnullTxStart_p = 1'b0;

// Force the macPhyIF to stop the transmission in case of error.
assign stopTx_p = stopTxInt_p || hwErr;

// Instanciation of txControllerMainFSM
// Name of the instance : U_txControllerMainFSM
// Name of the file containing this module : txControllerMainFSM.v
txControllerMainFSM U_txControllerMainFSM (
		.macCoreTxClk                     (macCoreTxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreTxClkSoftRst_n            (macCoreTxClkSoftRst_n),
		.sendData_p                       (sendData_p),
		.sendRTS_p                        (sendRTS_p),
		.sendCTS_p                        (sendCTS_p),
		.sendACK_p                        (sendACK_p),
		.sendCFEND_p                      (sendCFEND_p),
		.sendBA_p                         (sendBA_p),
		.sendOnSIFS                       (sendOnSIFS),
		.txDone_p                         (txDone_p),
		.txParameterHDReady_p             (txParameterHDReady_p),
		.aMPDU                            (aMPDU),
		.txSingleVHTMPDU                  (txSingleVHTMPDU),
		.MPDUFrameLengthTx                (MPDUFrameLengthTx),
		.nBlankMDelimiters                (nBlankMDelimiters),
		.whichDescriptor                  (whichDescriptor),
		.tickSlot                         (tickSlot),
		.tickSIFS                         (tickSIFS),
		.rtsDone_p                        (rtsDone_p),
		.ctsDone_p                        (ctsDone_p),
		.ackDone_p                        (ackDone_p),
		.cfendDone_p                      (cfendDone_p),
		.baDone_p                         (baDone_p),
		.qosnullDone_p                    (qosnullDone_p),
		.mpduDone_p                       (mpduDone_p),
		.rtsTxStart_p                     (rtsTxStart_p),
		.ctsTxStart_p                     (ctsTxStart_p),
		.ackTxStart_p                     (ackTxStart_p),
		.cfendTxStart_p                   (cfendTxStart_p),
		.baTxStart_p                      (baTxStart_p),
		.qosnullTxStart_p                 (qosnullTxStart_p),
		.mpduTxStart_p                    (mpduTxStart_p),
		.aMPDUDelimiterDone_p             (aMPDUDelimiterDone_p),
		.aMPDUPaddingDone_p               (aMPDUPaddingDone_p),
		.aMPDUPaddingStart_p              (aMPDUPaddingStart_p),
		.aMPDUDelimiterStart_p            (aMPDUDelimiterStart_p),
		.addBlankDelimiter                (addBlankDelimiter),
		.sendMPDU_p                       (sendMPDU_p),
		.mpIfTxErr_p                      (mpIfTxErr_p),
		.mpIfTxEn                         (mpIfTxEn),
		.startTx_p                        (startTx_p),
		.stopTx_p                         (stopTxInt_p),
		.txControlMainFSMCs               (txControlMainFSMCs)
		);

// Instanciation of formatACK
// Name of the instance : U_formatACK
// Name of the file containing this module : formatACK.v
formatACK U_formatACK (
		.macCoreTxClk                     (macCoreTxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreTxClkSoftRst_n            (macCoreTxClkSoftRst_n),
		.destAddr                         (destAddr),
		.duration                         (duration),
		.sendACK_p                        (sendACK_p),
		.ackDone_p                        (ackDone_p),
		.ackTxStart_p                     (ackTxStart_p),
		.fcsEnd_p                         (fcsEnd_p),
		.fcsBusy                          (fcsBusy),
		.ackFCSEnable                     (ackFCSEnable),
		.ackFCSStart_p                    (ackFCSStart_p),
		.ackFCSShiftTx                    (ackFCSShiftTx),
		.ackFCSDInTx                      (ackFCSDInTx),
		.ackFCSDInValidTx                 (ackFCSDInValidTx),
		.tickSIFS                         (tickSIFS),
		.pwrMgt                           (pwrMgt),
		.formatACKFSMCs                   (formatACKFSMCs)
		);

// Instanciation of formatAMPDUDelimiter
// Name of the instance : U_formatAMPDUDelimiter
// Name of the file containing this module : formatAMPDUDelimiter.v
formatAMPDUDelimiter U_formatAMPDUDelimiter (
		.macCoreTxClk                     (macCoreTxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreTxClkSoftRst_n            (macCoreTxClkSoftRst_n),
		.aMPDUPaddingStart_p              (aMPDUPaddingStart_p),
		.aMPDUDelimiterStart_p            (aMPDUDelimiterStart_p),
		.addBlankDelimiter                (addBlankDelimiter),
		.aMPDUDelimiterDone_p             (aMPDUDelimiterDone_p),
		.aMPDUPaddingDone_p               (aMPDUPaddingDone_p),
		.MPDUFrameLengthTx                (MPDUFrameLengthTx),
		.nBlankMDelimiters                (nBlankMDelimiters),
		.txSingleVHTMPDU                  (txSingleVHTMPDU),
		.formatModTx                      (formatModTx),
		.mpIfTxFifoFull                   (mpIfTxFifoFull),
		.aMPDUDelimiterData               (aMPDUDelimiterData),
		.aMPDUDelimiterWriteEn            (aMPDUDelimiterWriteEn),
		.formatAMPDUDelFSMCs              (formatAMPDUDelFSMCs)
		);

// Instanciation of formatCFEND
// Name of the instance : U_formatCFEND
// Name of the file containing this module : formatCFEND.v
formatCFEND U_formatCFEND (
		.macCoreTxClk                     (macCoreTxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreTxClkSoftRst_n            (macCoreTxClkSoftRst_n),
		.sendCFEND_p                      (sendCFEND_p),
		.cfendDone_p                      (cfendDone_p),
		.cfendTxStart_p                   (cfendTxStart_p),
		.fcsEnd_p                         (fcsEnd_p),
		.fcsBusy                          (fcsBusy),
		.cfendFCSEnable                   (cfendFCSEnable),
		.cfendFCSStart_p                  (cfendFCSStart_p),
		.cfendFCSShiftTx                  (cfendFCSShiftTx),
		.cfendFCSDInTx                    (cfendFCSDInTx),
		.cfendFCSDInValidTx               (cfendFCSDInValidTx),
		.tickSIFS                         (tickSIFS),
		.bssID                            (bssID),
		.pwrMgt                           (pwrMgt),
		.formatCFENDFSMCs                 (formatCFENDFSMCs)
		);

// Instanciation of formatCTS
// Name of the instance : U_formatCTS
// Name of the file containing this module : formatCTS.v
formatCTS U_formatCTS (
		.macCoreTxClk                     (macCoreTxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreTxClkSoftRst_n            (macCoreTxClkSoftRst_n),
		.destAddr                         (destAddr),
		.duration                         (duration),
		.sendCTS_p                        (sendCTS_p),
		.sendOnPIFS                       (sendOnPIFS),
		.sendOnSIFS                       (sendOnSIFS),
		.ctsDone_p                        (ctsDone_p),
		.ctsTxStart_p                     (ctsTxStart_p),
		.fcsEnd_p                         (fcsEnd_p),
		.fcsBusy                          (fcsBusy),
		.ctsFCSEnable                     (ctsFCSEnable),
		.ctsFCSStart_p                    (ctsFCSStart_p),
		.ctsFCSShiftTx                    (ctsFCSShiftTx),
		.ctsFCSDInTx                      (ctsFCSDInTx),
		.ctsFCSDInValidTx                 (ctsFCSDInValidTx),
		.tickSIFS                         (tickSIFS),
		.tickSlot_p                       (tickSlot_p),
		.tickPIFS                         (tickPIFS),
		.pwrMgt                           (pwrMgt),
		.formatCTSFSMCs                   (formatCTSFSMCs)
		);

// Instanciation of formatMPDU
// Name of the instance : U_formatMPDU
// Name of the file containing this module : formatMPDU.v
formatMPDU U_formatMPDU (
		.macCoreTxClk                     (macCoreTxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreTxClkSoftRst_n            (macCoreTxClkSoftRst_n),
		.skipMPDU_p                       (skipMPDU_p),
		.duration                         (duration),
		.retry                            (retry),
		.tsfDuration                      (tsfDuration),
		.sendOnSIFS                       (sendOnSIFS),
		.txTID                            (txTID),
		.typeTx                           (typeTx),
		.typeTxValid                      (typeTxValid),
		.txAMSDUPresent                   (txAMSDUPresent),
		.txBcMc                           (txBcMc),
		.sentCFEND                        (sentCFEND),
		.sentRTS                          (sentRTS),
		.sentBAReq                        (sentBAReq),
		.skipMPDUDone_p                   (skipMPDUDone_p),
		.mpIfTxEn                         (mpIfTxEn),
		.sendMPDU_p                       (sendMPDU_p),
		.mpduDone_p                       (mpduDone_p),
		.mpduTxStart_p                    (mpduTxStart_p),
		.MPDUFrameLengthTx                (MPDUFrameLengthTx),
		.useRIFSTx                        (useRIFSTx),
		.dontGenerateMH                   (dontGenerateMH),
		.dontEncrypt                      (dontEncrypt),
		.dontTouchFC                      (dontTouchFC),
		.dontTouchDur                     (dontTouchDur),
		.dontTouchQoS                     (dontTouchQoS),
		.dontTouchHTC                     (dontTouchHTC),
		.dontTouchTSF                     (dontTouchTSF),
		.dontTouchDTIM                    (dontTouchDTIM),
		.dontTouchFCS                     (dontTouchFCS),
		.aMPDU                            (aMPDU),
		.txFIFOEmpty                      (txFIFOEmpty),
		.txFIFORdData                     (txFIFORdData),
		.txFIFOMPDUDelimiters             (txFIFOMPDUDelimiters),
		.txFIFODataValid                  (txFIFODataValid),
		.txFIFORead                       (txFIFORead),
		.txFIFOReadByFour                 (txFIFOReadByFour),
		.txFIFOReadByTwo                  (txFIFOReadByTwo),
		.cTypeRAM                         (cTypeRAM),
		.formatMod                        (formatModTx),
		.txCsIsIdle                       (txCsIsIdle),
		.txDataLength                     (txDataLength),
		.txCryptoKeyValid                 (txCryptoKeyValid),
		.txCCMPTKIPSeqCnt                 (txCCMPTKIPSeqCnt),
		.txPlainData                      (txPlainData),
		.txPlainDataValid                 (txPlainDataValid),
		.txPlainDataEnd                   (txPlainDataEnd),
		.txEncrData                       (txEncrData),
		.txEncrDataValid                  (txEncrDataValid),
		.txSBOXInit                       (txSBOXInit),
		.txSBOXInitDone                   (txSBOXInitDone),
 		.txICVEnable                      (txICVEnable),
		.txWEP                            (txWEP),
		.txWEPIV                          (txWEPIV),
		.txWEPIVValid                     (txWEPIVValid),
		.txTKIP                           (txTKIP),
		.txCCMPBusy                       (txCCMPBusy),
		.txCCMPMicDone                    (txCCMPMicDone),
		.txCCMP                           (txCCMP),
		.txCCMPStart                      (txCCMPStart),
		.txCCMPHeaderValid                (txCCMPHeaderValid),
		.txCCMPDataValid                  (txCCMPDataValid),
		.txCCMPAdd4Pres                   (txCCMPAdd4Pres),
		.txCCMPQoSPres                    (txCCMPQoSPres),
		.txCCMPAddr1                      (txCCMPAddr1),
		.txCCMPAddr2                      (txCCMPAddr2),
		.txCCMPHT                         (txCCMPHT),
		.fcsEnd_p                         (fcsEnd_p),
		.fcsBusy                          (fcsBusy),
    `ifdef RW_WAPI_EN
    .txWAPI                           (txWAPI),            
    .txWAPIStart                      (txWAPIStart),       
    .txWAPIMicDone                    (txWAPIMicDone),     
    .txWAPIBusy                       (txWAPIBusy),        
    .txWAPIFrameControl               (txWAPIFrameControl),
    .txWAPIAddr3                      (txWAPIAddr3),       
    .txWAPIAddr4                      (txWAPIAddr4),       
    .txWAPIQoSCF                      (txWAPIQoSCF),       
    .txWAPISeqControl                 (txWAPISeqControl),  
    .txWAPIKeyIdx                     (txWAPIKeyIdx),      
    .txWAPIPN                         (txWAPIPN),          
`endif //RW_WAPI_EN
		.mpduFCSEnable                    (mpduFCSEnable),
		.mpduFCSStart_p                   (mpduFCSStart_p),
		.mpduFCSShiftTx                   (mpduFCSShiftTx),
		.mpduFCSDInTx                     (mpduFCSDInTx),
		.mpduFCSDInValidTx                (mpduFCSDInValidTx),
		.tickSIFS                         (tickSIFS),
		.tickSlot                         (tickSlot),
		.dtimCnt                          (dtimCnt),
		.tsf                              (tsf),
		.timOffset                        (timOffset),
		.pwrMgt                           (pwrMgt),
		.activeAC                         (activeAC),
		.formatMPDUFSMCs                  (formatMPDUFSMCs),
		.mpduSeqCtrlDone_p                (mpduSeqCtrlDone_p),
		.formatMPDUFrameDebug1            (formatMPDUFrameDebug1),
		.formatMPDUFrameDebug2            (formatMPDUFrameDebug2)
		);



// Instanciation of formatRTS
// Name of the instance : U_formatRTS
// Name of the file containing this module : formatRTS.v
formatRTS U_formatRTS (
		.macCoreTxClk                     (macCoreTxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreTxClkSoftRst_n            (macCoreTxClkSoftRst_n),
		.destAddr                         (destAddr),
		.srcAddr                          (srcAddr),
		.duration                         (duration),
		.txBWSignaling                    (txBWSignaling),
		.sendRTS_p                        (sendRTS_p),
		.sendOnPIFS                       (sendOnPIFS),
		.sendOnSIFS                       (sendOnSIFS),
		.rtsDone_p                        (rtsDone_p),
		.rtsTxStart_p                     (rtsTxStart_p),
		.fcsEnd_p                         (fcsEnd_p),
		.fcsBusy                          (fcsBusy),
		.rtsFCSEnable                     (rtsFCSEnable),
		.rtsFCSStart_p                    (rtsFCSStart_p),
		.rtsFCSShiftTx                    (rtsFCSShiftTx),
		.rtsFCSDInTx                      (rtsFCSDInTx),
		.rtsFCSDInValidTx                 (rtsFCSDInValidTx),
		.tickSIFS                         (tickSIFS),
		.tickPIFS_p                       (tickPIFS_p),
		.tickSlot_p                       (tickSlot_p),
		.pwrMgt                           (pwrMgt),
		.formatRTSFSMCs                   (formatRTSFSMCs)
		);

// Instanciation of formatBA
// Name of the instance : U_formatBA
// Name of the file containing this module : formatBA.v
formatBA U_formatBA (
		.macCoreTxClk                     (macCoreTxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreTxClkSoftRst_n            (macCoreTxClkSoftRst_n),
		.destAddr                         (destAddr),
		.srcAddr                          (srcAddr),
		.duration                         (duration),
		.sendBA_p                         (sendBA_p),
		.baDone_p                         (baDone_p),
		.baTxStart_p                      (baTxStart_p),
		.rxTID                            (rxTID),
		.fcsEnd_p                         (fcsEnd_p),
		.fcsBusy                          (fcsBusy),
		.baFCSEnable                      (baFCSEnable),
		.baFCSStart_p                     (baFCSStart_p),
		.baFCSShiftTx                     (baFCSShiftTx),
		.baFCSDInTx                       (baFCSDInTx),
		.baFCSDInValidTx                  (baFCSDInValidTx),
		.psBitmap                         (psBitmap),
		.psBitmapValid                    (psBitmapValid),
		.psBitmapReady                    (psBitmapReady),
		.tickSIFS                         (tickSIFS),
		.pwrMgt                           (pwrMgt),
		.formatBAFSMCs                    (formatBAFSMCs)
		);



// Instanciation of txVectorSel
// Name of the instance : U_txVectorSel
// Name of the file containing this module : txVectorSel.v
txVectorSel U_txVectorSel (
		.macCoreTxClk           (macCoreTxClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.startTx_p              (startTx_p),
		.txMCS                  (txMCS),
		.txLegLength            (txLegLength),
		.txLegRate              (txLegRate),
		.txHTLength             (txHTLength),
		.txResp                 (txResp),
		.txFromReg              (txFromReg),
		.txFromHD               (txFromHD),
		.txSTBC                 (txSTBC),
		.txDisambiguityBit      (txDisambiguityBit),
		.txChBW                 (txChBW),
		.txDynBW                (txDynBW),
		.txBWSignaling          (txBWSignaling),
		.txFromFifo             (txFromFifo),
		.txCFEND                (txCFEND),
		.formatModProtTx        (formatModProtTx),
		.formatModTx            (formatModTx),
		.preTypeProtTx          (preTypeProtTx),
		.preTypeTx              (preTypeTx),
		.smoothingProtTx        (smoothingProtTx),
		.partialAIDTx           (partialAIDTx),
		.groupIDTx              (groupIDTx),
		.dozeNotAllowedTx       (dozeNotAllowedTx),
		.smoothingTx            (smoothingTx),
		.soundingTx             (soundingTx),
		.nTxProtPT              (nTxProtPT),
		.nTxPT                  (nTxPT),
		.txShortGI              (txShortGI),
		.txPwrLevelPT           (txPwrLevelPT),
		.txPwrLevelProtPT       (txPwrLevelProtPT),
		.stbcPT                 (stbcPT),
		.txFecCoding            (txFecCoding),
		.numExtnSSPT            (numExtnSSPT),
		.beamFormedPT           (beamFormedPT),
		.smmIndexPT             (smmIndexPT),
		.antennaSetPT           (antennaSetPT),
		.aMPDU                  (aMPDU),
		.dsssMaxPwrLevel        (dsssMaxPwrLevel),
		.ofdmMaxPwrLevel        (ofdmMaxPwrLevel),
		.startTxSmoothing       (startTxSmoothing),
		.startTxAntennaSet      (startTxAntennaSet),
		.startTxSMMIndex        (startTxSMMIndex),
		.startTxPreType         (startTxPreType),
		.startTxFormatMod       (startTxFormatMod),
		.startTxNumExtnSS       (startTxNumExtnSS),
		.pRandom                (tsf[2:0]),
		.bbServiceA             (bbServiceA),
		.bbServiceB             (bbServiceB),
		.startTxNTx             (startTxNTx),
		.respTxAntennaSet       (respTxAntennaSet),
		.respTxSMMIndex         (respTxSMMIndex),
		.respTxPreType          (respTxPreType),
		.respTxFormatMod        (respTxFormatMod),
		.respTxNumExtnSS        (respTxNumExtnSS),
		.respTxFECCoding        (respTxFECCoding),
		.respTxNTx              (respTxNTx),
		.respTxShortGI          (respTxShortGI),
		.txPwrLevel             (txPwrLevel),
		.chBW                   (chBW),
		.chOffset               (chOffset),
		.partialAID             (partialAID),
		.groupID                (groupID),
		.dozeNotAllowed         (dozeNotAllowed),
		.smoothing              (smoothing),
		.antennaSet             (antennaSet),
		.beamFormed             (beamFormed),
		.smmIndex               (smmIndex),
		.mcs                    (mcs),
		.nSTS                   (nSTS),
		.preType                (preType),
		.formatMod              (formatMod),
		.numExtnSS              (numExtnSS),
		.stbc                   (stbc),
		.disambiguityBit        (disambiguityBit),
		.fecCoding              (fecCoding),
		.sounding               (sounding),
		.legLength              (legLength),
		.legRate                (legRate),
		.service                (service),
		.htLength               (htLength),
		.nTx                    (nTx),
		.shortGI                (shortGI),
		.aggreation             (aggreation)
		);



assign fcsPauseTx     = mpIfTxFifoFull;
assign fcsStartTx_p   = ctsFCSStart_p    || rtsFCSStart_p    || ackFCSStart_p    || cfendFCSStart_p    || baFCSStart_p    || mpduFCSStart_p  ;
assign fcsShiftTx     = ctsFCSShiftTx    || rtsFCSShiftTx    || ackFCSShiftTx    || cfendFCSShiftTx    || baFCSShiftTx    || mpduFCSShiftTx  ;
assign fcsDInValidTx  = ctsFCSDInValidTx || rtsFCSDInValidTx || ackFCSDInValidTx || cfendFCSDInValidTx || baFCSDInValidTx || mpduFCSDInValidTx ; 
assign fcsEnableTx    = ctsFCSEnable     || rtsFCSEnable     || ackFCSEnable     || cfendFCSEnable     || baFCSEnable     || mpduFCSEnable  ;



always @*
begin
  case ({mpduFCSDInValidTx, baFCSDInValidTx, cfendFCSDInValidTx, ackFCSDInValidTx, ctsFCSDInValidTx, rtsFCSDInValidTx})
    6'b000001 :  fcsDInTx     = rtsFCSDInTx;

    6'b000010 :  fcsDInTx     = ctsFCSDInTx;
    
    6'b000100 :  fcsDInTx     = ackFCSDInTx;
    
    6'b001000 :  fcsDInTx     = cfendFCSDInTx;
    
    6'b010000 :  fcsDInTx     = baFCSDInTx;
    
    6'b100000 :  fcsDInTx     = mpduFCSDInTx;
    
     default  :  fcsDInTx     =  8'b0;
  endcase
end


assign mpIfTxFifoData    = (fcsDOutValid) ? fcsDOut      : aMPDUDelimiterData;
assign mpIfTxFifoWrite   = (txResp || txFromReg || txFromHD || txFromFifo || txCFEND) ?  
                           (fcsDOutValid) ? fcsDOutValid : aMPDUDelimiterWriteEn
                           : 1'b0;


// tickSIFS_p capture
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    tickSIFS <= 1'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || hwErr) // Synchronous Reset
    tickSIFS <= 1'b0; 
  else if (startTx_p || macPhyIfRxCca)   
    tickSIFS <= 1'b0; 
  else if (tickSIFS_p)
    tickSIFS <= 1'b1;
end

// tickPIFS_p capture
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    tickPIFS <= 1'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || hwErr) // Synchronous Reset
    tickPIFS <= 1'b0; 
  else if (startTx_p || macPhyIfRxCca)   
    tickPIFS <= 1'b0; 
  else if (tickPIFS_p)
    tickPIFS <= 1'b1;
end

// tickSlot capture
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    tickSlot <= 1'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || hwErr) // Synchronous Reset
    tickSlot <= 1'b0; 
  else if (startTx_p || macPhyIfRxCca)   
    tickSlot <= 1'b0; 
  else if (tickSlot_p)
    tickSlot <= 1'b1;
end



////////////////////////////////////////////////////////////////////////////////
//
// Debug logic.
//
////////////////////////////////////////////////////////////////////////////////

// This process merges together the state of the different FSM based on the txControlMain
// current state
always @*
begin
  case (txControlMainFSMCs)
      4'd2  : txControlCs = {txControlMainFSMCs,3'b0,formatAMPDUDelFSMCs}; // TX_AMPDU_DLM
      4'd3  : txControlCs = {txControlMainFSMCs,formatMPDUFSMCs};          // TX_FRAME
      4'd5  : txControlCs = {txControlMainFSMCs,3'b0,formatAMPDUDelFSMCs}; // TX_AMPDU_PAD
      4'd6  : txControlCs = {txControlMainFSMCs,1'b0,formatCFENDFSMCs};    // TX_CFEND
      4'd7  : txControlCs = {txControlMainFSMCs,1'b0,formatRTSFSMCs};      // TX_RTS
      4'd8  : txControlCs = {txControlMainFSMCs,2'b0,formatCTSFSMCs};      // TX_CTS
      4'd9  : txControlCs = {txControlMainFSMCs,2'b0,formatACKFSMCs};      // TX_ACK
      4'd10 : txControlCs = {txControlMainFSMCs,1'b0,formatBAFSMCs};       // TX_BACK
      4'd11 : txControlCs = {txControlMainFSMCs,5'b0};                     // TX_QOSNULL
    default : txControlCs = {txControlMainFSMCs,5'b0};                 
  endcase
end                                                                        

// | *txControlCs[8:5]* | *txControllerMainFSMCs*  |
// |  0x0               |                  IDLE    |
// |  0x1               | WAIT_FOR_SIFS_OR_SLOT    |
// |  0x2               |          TX_AMPDU_DLM    |
// |  0x3               |              TX_FRAME    |
// |  0x4               |        WAIT_HD_TOGGLE    |
// |  0x5               |          TX_AMPDU_PAD    |
// |  0x6               |              TX_CFEND    |
// |  0x7               |                TX_RTS    |
// |  0x8               |                TX_CTS    |
// |  0x9               |                TX_ACK    |
// |  0xA               |               TX_BACK    |
// |  0xB               |            TX_QOSNULL    |
// |  0xC               |           TX_WAIT_END    |
//
// | *txControlCs[4:0]* | *TX_AMPDU_DLM*  |    *TX_FRAME*      |  *TX_AMPDU_PAD* | *TX_CFEND*           |     *TX_RTS*       | *TX_CTS*           | *TX_ACK*           |    *TX_BACK*     |
// |  0x0               |            IDLE |                    |            IDLE |           CFEND_IDLE |           RTS_IDLE |           CTS_IDLE |           ACK_IDLE |          BA_IDLE |
// |  0x1               | INSERT_BLANKDEL |            FD_IDLE | INSERT_BLANKDEL |           CFEND_WAIT |           RTS_WAIT |           CTS_WAIT |           ACK_WAIT |          BA_WAIT |
// |  0x2               |      INSERT_DEL |      FD_INITCRYPTO |      INSERT_DEL |        CFEND_STARTTX |        RTS_STARTTX |        CTS_STARTTX |        ACK_STARTTX |       BA_STARTTX |
// |  0x3               |      INSERT_PAD |         FD_STARTTX |      INSERT_PAD | CFEND_FRMCNTRL_BYTE1 | RTS_FRMCNTRL_BYTE1 | CTS_FRMCNTRL_BYTE1 | ACK_FRMCNTRL_BYTE1 |BA_FRMCNTRL_BYTE1 |
// |  0x4               |                 |  FD_FRMCNTRL_BYTE1 |                 | CFEND_FRMCNTRL_BYTE2 | RTS_FRMCNTRL_BYTE2 | CTS_FRMCNTRL_BYTE2 | ACK_FRMCNTRL_BYTE2 |BA_FRMCNTRL_BYTE2 |
// |  0x5               |                 |  FD_FRMCNTRL_BYTE2 |                 |     CFEND_DURATIONID |     RTS_DURATIONID |     CTS_DURATIONID |     ACK_DURATIONID |    BA_DURATIONID |
// |  0x6               |                 |      FD_DURID_DATA |                 |             CFEND_RA |             RTS_RA |             CTS_RA |             ACK_RA |            BA_RA |
// |  0x7               |                 |           FD_ADDR1 |                 |          CFEND_BSSID |             RTS_TA |            CTS_FCS |            ACK_FCS |            BA_TA |
// |  0x8               |                 |           FD_ADDR2 |                 |            CFEND_FCS |            RTS_FCS |                    |                    |       BA_CONTROL |
// |  0x9               |                 |           FD_ADDR3 |                 |                      |                    |                    |                    |          BA_INFO |
// |  0xA               |                 |        FD_SQNCNTRL |                 |                      |                    |                    |                    |           BA_FCS |
// |  0xB               |                 |           FD_ADDR4 |                 |                      |                    |                    |                    |                  |
// |  0xC               |                 |        FD_QOSCNTRL |                 |                      |                    |                    |                    |                  |
// |  0xD               |                 |         FD_CFCNTRL |                 |                      |                    |                    |                    |                  |
// |  0xE               |                 |         FD_HTCNTRL |                 |                      |                    |                    |                    |                  |
// |  0xF               |                 |             FD_TSF |                 |                      |                    |                    |                    |                  |
// |  0x10              |                 |              FD_IV |                 |                      |                    |                    |                    |                  |
// |  0x11              |                 |           FD_EXTIV |                 |                      |                    |                    |                    |                  |
// |  0x12              |                 |       FD_MPDUSTART |                 |                      |                    |                    |                    |                  |
// |  0x13              |                 |        FD_FRM_BODY |                 |                      |                    |                    |                    |                  |
// |  0x14              |                 |             FD_ICV |                 |                      |                    |                    |                    |                  |
// |  0x15              |                 | FD_WAITCCMPMICDONE |                 |                      |                    |                    |                    |                  |
// |  0x16              |                 |         FD_CCMPMIC |                 |                      |                    |                    |                    |                  |
// |  0x17              |                 |             FD_FCS |                 |                      |                    |                    |                    |                  |
// |  0x18              |                 |     FD_FLUSHTXFIFO |                 |                      |                    |                    |                    |                  |


// TX Controller FSMs current states latched when an HW error happened
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txControlLs <= 9'b0; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    txControlLs <= 9'b0; 
  else
    if (hwErr)
      txControlLs <= txControlCs; 
end

// Capture the information about the frame which has been transmitted
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    debugPortTxFrameDebug1 <= 16'b0;
    debugPortTxFrameDebug2 <= 16'b0;
  end
  else
  begin
    if (txDone_p)
    begin
      debugPortTxFrameDebug1 <= 16'b0;
      debugPortTxFrameDebug2 <= 16'b0;
    end  
    if (mpduSeqCtrlDone_p || ctsTxStart_p || rtsTxStart_p || ackTxStart_p || cfendTxStart_p || baTxStart_p)
    begin
      case (txControlMainFSMCs)
          4'd3  : debugPortTxFrameDebug1 <= {1'b1,formatMPDUFrameDebug1};            // TX_FRAME
          4'd5  : debugPortTxFrameDebug1 <= {1'b1,5'b0,pwrMgt,3'b0,6'b111001};       // TX_CFEND
          4'd6  : debugPortTxFrameDebug1 <= {1'b1,5'b0,pwrMgt,2'b0,retry,6'b101101}; // TX_RTS
          4'd7  : debugPortTxFrameDebug1 <= {1'b1,5'b0,pwrMgt,3'b0,6'b101101};       // TX_CTS
          4'd8  : debugPortTxFrameDebug1 <= {1'b1,5'b0,pwrMgt,3'b0,6'b101101};       // TX_ACK
          4'd9  : debugPortTxFrameDebug1 <= {1'b1,5'b0,pwrMgt,3'b0,6'b100101};       // TX_BACK
        default : debugPortTxFrameDebug1 <= 16'b0;                 
      endcase
      if (txControlMainFSMCs == 4'd3)
        debugPortTxFrameDebug2 <= {1'b0,formatMPDUFrameDebug2};   // TX_FRAME
      else
        debugPortTxFrameDebug2 <= {8'b0,destAddr[47:40]};         // Others TX_CFEND
    end
  end
end    



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////



// System Verilog Assertions
////////////////////////////

`ifdef RW_ASSERT_ON
//$rw_sva Checks if the Tx Controller does not write when the mpIfTxFifoFull is set 
// That guaranty the handshaking between Tx Controller and the MAC-PHY Interface
property noWriteWhenFiFoFullCheck_prop;
@(posedge macCoreTxClk)
    (mpIfTxFifoFull == 1'b1) |-> mpIfTxFifoWrite == 1'b0;
endproperty
noWriteWhenFiFoFullCheck: assert property (noWriteWhenFiFoFullCheck_prop); 

//$rw_sva Checks if the Tx Controller does not read when the TX FIFO is empty
// That guaranty the handshaking between Tx Controller and the TX FIFO
property noReadWhenFiFoEmptyCheck_prop;
@(posedge macCoreTxClk)
    (txFIFOEmpty == 1'b1) |-> txFIFORead == 1'b0;
endproperty
noReadWhenFiFoEmptyCheck: assert property (noReadWhenFiFoEmptyCheck_prop); 


`endif // RW_ASSERT_ON
endmodule
                 
