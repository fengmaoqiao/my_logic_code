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
// Description      : FSM of rxController module
//                    
// Simulation Notes : 
//    For simulation, two defines are available
//
//    RW_SIMU_ON   : which creates string signals to display the FSM states on  
//                the waveform viewer.
//
//    RW_ASSERT_ON : which enables System Verilog Assertions.
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


module rxControllerFsm( 
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
            input wire         lSIGTXOPDetected,        // Frame received is LSIG TXOP protected 
            input wire         rxCts,                   // Reception of a CTS is expected
            input wire         rxAck,                   // Reception of an ACK is expected

            output wire        correctRcved_p,          // Frame received correctly
            output wire        incorrectRcved_p,        // Frame not received correctly

            ///////////////////////////////////////////////
            //$port_g Backoff Engine
            ///////////////////////////////////////////////
            input wire         backOffDone_p,            // Backoff completed

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
            output wire        navCfpDurRemUpdate_p,    // Update NAV with CFP duration remaining
            output wire        navLsigUpdate_p,         // Update NAV with LSIG
            
            ///////////////////////////////////////////////
            //$port_g MAC Timer unit
            ///////////////////////////////////////////////
            output wire        dtimUpdate_p,            // Update DTIM element
            output wire        cfpUpdate_p,             // Update CFP element
            output wire        tsfUpdate_p,             // Update TSF
            output reg         tsfOffsetUpdate_p,       // Update TSF Offset calculation
            output reg         lastRxWrong,             // Last received packet wrong
            
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
            input wire         plainOutFCSValid,        // FCS field valid
            
            output wire [15:0] rxPayLoadLen,            // Frame length including MIC & FCS
            output reg         rxCCMPAADwrEn_p,         // write enable to CCMP for AAD writing
            
            ///////////////////////////////////////////////
            //$port_g Key Search Engine
            ///////////////////////////////////////////////
            input wire [1:0]   sppKSR,                  // SPP for RAM
            input wire [2:0]   cTypeKSR,                // Cipher Type for RAM
            
            ///////////////////////////////////////////////
            //$port_g Decryption FSM
            ///////////////////////////////////////////////
            input wire         rxDataSelect,            // Select data from Encryption Engine
            input wire         encrPadding4BytesFIFOEn, // Encryption padding 4 bytes enable
            input wire         nullKeyFound,            // Null Key found in RAM
            input wire         rxIndexSearchDone,       // Key Search Engine Done

            output wire        rxControlToError_p,      // RX FSM goes to error
            output wire        rxControlToFrmBody_p,    // RX FSM goes to frame body
            output wire        acceptProtected,         // Accept protected frame
            output reg         rxInitVectorEnd_p,       // FSM IV end pulse
            output reg         rxExtIV_p,               // Indicate if there is a extended IV
            output wire        decrStatusValid_p,       // Decryption status valid pulse
            
            ///////////////////////////////////////////////
            //$port_g MAC-PHY interface
            ///////////////////////////////////////////////
            input wire         macPhyIfRxErr_p,         // Rx error from MAC-PHY if. resynchronized
            input wire         mpIfTxEn,                // Indicates that TX is in progress
            input wire         macPHYIFOverflow,        // Overflow Indication
            
            ///////////////////////////////////////////////
            //$port_g A-MPDU Deaggregator
            ///////////////////////////////////////////////
            input wire [ 2:0]  rxFormatMod,             // Format and modulation
            input wire         rxLSIGValid,             // L-SIG Valid
            input wire         rxAggregation,           // MPDU aggregate
            
            input wire [ 7:0]  rxData,                  // Rx data read from MAC-PHY interface FIFO
            input wire         rxDataValid,             // Rx data is valid
            input wire         rxDataStart_p,           // Start of data flow
            input wire         rxDataEnd_p,             // End of data flow
            input wire         rxDataError_p,           // Rx data error (incorrect length)

            input wire         ampduIncorrectRcved_p,   // A-MPDU not received correctly
            
            input wire [15:0]  rxByteCnt,               // Rx byte counter
            input wire         rxNDP,                   // Indicate that the received frame is a Null Data Packet
            
            output wire        rxCntrlReady,            // Rx controller ready to receive data

            ///////////////////////////////////////////////
            //$port_g Frame decoder
            ///////////////////////////////////////////////
            input wire         protocolError,           // Protocol error
            
            input wire         mgmtNoEncryptFrame,      // Management frame without encryption
            input wire         mgmtFrame,               // Management frame
            input wire         ctrlFrame,               // Control frame
            input wire         dataFrame,               // Data frame
            input wire         qosFrame,                // QoS frame
            input wire         htcFrame,                // HT or VHT frame with HTC field
            
            input wire         bcMcRcved,               // Broadcast/Multicast
            
            input wire         bcnRcved,                // Beacon
            input wire         probRespRcved,           // Probe response
            
            input wire         ctrlWrapRcved,           // Control Wrapper
            input wire         baRcved,                 // BA
            input wire         barRcved,                // BAR
            input wire         psPollRcved,             // PS-Poll
            input wire         rtsRcved,                // RTS
            input wire         ctsRcved,                // CTS
            input wire         ackRcved,                // ACK
            input wire         cfEndRcved,              // CF-End
            
            input wire         ctrlWrapFlag,            // Control Wrapper flag
            
            input wire         dataRcved,               // Data
            input wire         qosDataRcved,            // QoS Data
            input wire         qosNullRcved,            // QoS null
            
            input wire         reservedRcved,           // Reserved
            
            input wire         toDS,                    // To DS
            input wire         fromDS,                  // From DS
            input wire         protectedBit,            // Protected bit
            
            input wire         rxAMSDUPresent,          // A-MSDU present
            
            input wire         compressedBA,            // Compressed BA

            input wire         acceptRcved,             // Accept current frame after filtering
            
            input wire         addr1Match,              // ADDR1 match
            input wire         bssIDMatch,              // BSSID match
            
            output wire        rxFrmCtrlEn,             // Frame control field
            output wire        rxDurationIdEn,          // Duration / ID field
            output wire        rxAddr1En,               // ADDR1 field
            output wire        rxAddr2En,               // ADDR2 field
            output wire        rxAddr3En,               // ADDR3 field
`ifdef RW_WAPI_EN
            output wire        rxAddr4En,               // ADDR4 field
            output wire        rxWAPIKeyIdxEn,          // WAPI KeyIdx field
            output wire        rxWAPIPNEn,              // WAPI PN field
`endif //RW_WAPI_EN
            output wire        rxQoSCtrlEn,             // QoS control field
            output wire        rxHTCtrlEn,              // HT control field
            output wire        rxSeqCtrlEn,             // Sequence control field
            output wire        rxBACtrlEn,              // BA control field
            output wire        rxBASeqCtrlEn,           // BA Sequence control field
            output wire        rxInitVectorEn,          // IV field
            output wire        rxExtInitVectorEn,       // Extended IV field

            output wire        rxDtimCntEn,             // DTIM counter field
            output wire        rxDtimPeriodEn,          // DTIM period field
            output wire        rxCfpCntEn,              // CFP counter field
            output wire        rxCfpPeriodEn,           // CFP period field
            output wire        rxCfpDurRemainingEn,     // CFP Duration remaining field
            output wire        rxTimeStampEn,           // Timestamp field
            
            output wire        rxQuietCount1En,         // Quiet Count 1 field
            output wire        rxQuietPeriod1En,        // Quiet Period 1 field
            output wire        rxQuietDuration1En,      // Quiet Duration 1 field
            output wire        rxQuietOffset1En,        // Quiet Offset 1 field
            output wire        rxQuietCount2En,         // Quiet Count 2 field
            output wire        rxQuietPeriod2En,        // Quiet Period 2 field
            output wire        rxQuietDuration2En,      // Quiet Duration 2 field
            output wire        rxQuietOffset2En,        // Quiet Offset 2 field
            
            output reg [7:0]   stateByteCnt,            // Byte counter by states

`ifdef RW_WAPI_EN
            output reg         rxAddr4End_p,            // FSM ADDR4 pulse
            output reg         rxWAPIKeyIdxEnd_p,       // FSM WAPI KeyIdx pulse
            output reg         rxWAPIPNEnd_p,           // FSM WAPI PN pulse
`endif //RW_WAPI_EN
            output wire        fcsCheck_p,              // FSM FCS check pulse
            output wire        rxDurationIdEnd_p,       // FSM Duration / ID end pulse
            output reg         rxAddr1End_p,            // FSM ADDR1 end pulse
            output reg         rxAddr2End_p,            // FSM ADDR2 end pulse
            output reg         carFrameCtrlEnd_p,       // FSM Carried frame control end pulse
            output reg         rxAddr3End_p,            // FSM ADDR3 end pulse
            output reg         rxSeqCtrlEnd_p,          // FSM Sequence Control end pulse
            output reg         rxQoSEnd_p,              // FSM QoS end pulse
            output wire        rxBARCtrlEnd_p,          // FSM BAR control end pulse
            output wire        macHeaderCompleted,      // End of MAC Header reception pulse

            output wire        rxControlIdle,           // FSM in idle
            
            ///////////////////////////////////////////////
            //$port_g BA Controller
            ///////////////////////////////////////////////
            output wire        psBitmapUpdate_p,        // Update Bitmap request
            output wire        psBitmapDiscard_p,       // Discard Bitmap update request
            output wire        baEnable,                // Enable BA Controller procedure
            
            ///////////////////////////////////////////////
            //$port_g Control and Status Register
            ///////////////////////////////////////////////
            input wire [3:0]   currentState,            // Current state of the core

            input wire         bssType,                 // BSS Type
            input wire         ap,                      // Access Point
            input wire         tsfMgtDisable,           // Disable HW management of TSF
            
            input wire         dontDecrypt,             // Don't decrypt frames
            input wire         acceptErrorFrames,       // Accept error frames
            input wire         acceptDecryptErrorFrames,// Accept frames which failed decryption

            output wire        quietElement1InValid,    // Indicates that the Quiet 1 registers have to be updated with Quiet 1 In elements
            output wire        quietElement2InValid,    // Indicates that the Quiet 2 registers have to be updated with Quiet 2 In elements
            output wire        dtimPeriodInValid,       // Indicates that the dtimPeriod register has to be updated with dtimPeriodIn
            output wire        cfpPeriodInValid,        // Indicates that the cfpPeriod register has to be updated with cfpPeriodIn
            
            output reg [ 4:0]  rxControlLs,             // RX Controller latched state
            output reg [ 4:0]  rxControlCs,             // RX Controller current state
            
            ///////////////////////////////////////////////
            //$port_g RX FIFO Interface Controller
            ///////////////////////////////////////////////
            input wire         rxFIFOOverFlow,          // RX FIFO overflow
            input wire         rxFIFOFull,              // RX FIFO is full
            input wire         rxFIFODone_p,            // RX FIFO status done
            input wire         rxFIFOWrite,             // RX FIFO write enable
            input wire [3:0]   macHeaderCnt,            // MAC header counter
            input wire         endHeaderDone,           // End of the Header done
            input wire         rxEndOfFrame,            // RX end of frame holded
            input wire         txInProgressDly,         // Captured of the txInProgress on rxVector1 valid
            
            `ifdef RW_MPDU_AC
            output wire [15:0] rxLengthSub,             // sub value according to encryption or not for the full rx pkt
            `else
            output wire [15:0] payloadBufferLength,     // Payload length in buffers (frame body only)
            `endif
            output wire        frmSuccessfulRcved,      // Frame successful for RX DMA
            output reg         fcsErrorRcved,           // FCS Error
            output reg         phyErrorRcved,           // PHY Error
            output reg         undefErrorRcved,         // Undefined Error
            output reg         rxFIFOOverFlowError,     // RX FIFO overflow
            output reg [2:0]   decrStatus,              // Decryption status
            output wire        frmBody,                 // Frame body completion

            output wire        startMacHdr,             // Start of the MAC Header
            output wire        endPayload,              // End of the Payload
            output wire        discardFrm,              // End of frame with discard command
            output wire        acceptError_p,           // Pulse to indicate that writeTrailer to accept Error frame (others than FCS error)
            
            output wire        writeTrailer,            // Write trailer info
            
            output wire        padding4BytesFIFOEn,     // Padding 4 bytes enable
            output wire        padding4BytesWriteEn,    // Padding 4 bytes write enable
            output wire        padding2BytesFIFOEn,     // Padding 2 bytes enable
            
            ///////////////////////////////////////////////
            //$port_g HW Error detected
            ///////////////////////////////////////////////
            input wire         hwErr,                   // HW error detected
            
            ///////////////////////////////////////////////
            //$port_g Interrupt Controller
            ///////////////////////////////////////////////
            output reg         baRxTrigger,             // Block-ACK Receive interrupt
            
            ///////////////////////////////////////////////
            //$port_g FCS
            ///////////////////////////////////////////////
            input wire         fcsOk,                   // FCS is ok
            
            output wire        fcsStartRx_p,            // Start FCS calculation
            output reg         fcsEnableRx              // Enable FCS
            );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

// rxControl FSM states definition
//$fsm_sd rxControl
parameter 
                 IDLE  =  5'd0,
          RX_FRM_CTRL  =  5'd1,
            RX_DUR_ID  =  5'd2,
             RX_ADDR1  =  5'd3,
             RX_ADDR2  =  5'd4,
             RX_ADDR3  =  5'd5,
             RX_ADDR4  =  5'd6,
          RX_SEQ_CTRL  =  5'd7,
          RX_QOS_CTRL  =  5'd8,
      RX_CAR_FRM_CTRL  =  5'd9,
           RX_HT_CTRL  =  5'd10,
     RX_IV_WAPIKEYIDX  =  5'd11,
      RX_EXTIV_WAPIPN  =  5'd12,
          RX_FRM_BODY  =  5'd13,
               RX_ICV  =  5'd14,
     RX_CCMP_WAPI_MIC  =  5'd15,
               RX_FCS  =  5'd16,
           RX_BA_CTRL  =  5'd17,
       RX_BA_SEQ_CTRL  =  5'd18,
         RX_BA_BITMAP  =  5'd19,
         RX_TIMESTAMP  =  5'd20,
        RX_BCN_INTRVL  =  5'd21,
        RX_CAPABILITY  =  5'd22,
        RX_ELEMENT_ID  =  5'd23,
       RX_ELEMENT_LEN  =  5'd24,
      RX_ELEMENT_BODY  =  5'd25,
            CHECK_FCS  =  5'd26,
           CHECK_ENCR  =  5'd27,
         WRITE_STATUS  =  5'd28,
             RX_ERROR  =  5'd29,
        DISCARD_FRAME  =  5'd30,
   WAIT_KEYSEARCHDONE  =  5'd31;



// Core current state
parameter 
    ACTIVE_STATE = 4'h3; // active state

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// rxControl FSM signals definition
reg [4:0] rxControlNs;  // rxControl FSM Next State
reg [4:0] rxControlPs;  // rxControl FSM Padding State

// Info element length
reg [7:0] infoElemLen;
reg [7:0] elementID;

// Payload length
reg [15:0] payloadLength;
`ifdef ENCRYPTION
reg [15:0] payloadLengthSub;
`else
wire [15:0] payloadLengthSub;
`endif

// CFP parameter found
reg       cfpParameterFound;
// DTIM parameter found
reg       dtimParameterFound;
// Quiet parameter found
reg       quietParameterFound;
// Quiet parameter toggle
reg       quietParameterToggle;

// Non encrypted status information check
reg       statusInfoCheck_p;

// FCS Ok status
reg       fcsOkRcved;

// Local frame status
wire      localCorrectRcved_p;
wire      localIncorrectRcved_p;

// Invalid protected packet length
reg       invalidProtectPktLen;

// Invalid packet
wire      invalidPkt;

// rxByteCnt trigger
wire      rxByteCntTrig;
reg       rxByteCntTrig_ff1;

reg       macHeaderCntDone;        // End of MAC Header reception pulse

//reg       rxDataEnd;               // End of data flow holded

// Flag indicating if the frame has to be discarded due to encryption failure.
wire      discardDecrypt;

// Padding logic
reg [3:0] paddingByteCnt;
reg       padding4BytesEn;          // Padding 4 bytes enable
reg       padding4BytesEn_ff1;      // Padding 4 bytes enable ff1
reg       padding4BytesEn_ff2;      // Padding 4 bytes enable ff2
reg       padding2BytesEn;          // Padding 2 bytes enable

reg       macPhyIfRxErrInt_p;       // Rx error from MAC-PHY if delayed of 1 cc

// Encryption Engine specific logic
reg       decrStatusValidHold;      // Decryption status valid registered

reg       protectedPld;             // Flag indicating a protected payload
wire      respError;                // Indicate that the type of the received frame is not an expected response.

`ifdef RW_WAPI_EN
wire      WAPIMode;
reg       wapiPassedHold;
reg       wapiFailedHold;
`endif //RW_WAPI_EN

`ifdef RW_SIMU_ON
// String definition to display rxControl current state
reg [20*8:0] rxControlCs_str;
reg [20*8:0] rxControlNs_str;
`endif // RW_SIMU_ON

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// WAPI specific logic
`ifdef RW_WAPI_EN
assign WAPIMode = (cTypeKSR == 3'b100) ? 1'b1 : 1'b0;
assign rxWAPI   = WAPIMode && (rxControlCs != IDLE);
`endif //RW_WAPI_EN
                 
// rxControl FSM Latched State Logic 
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxControlLs <= IDLE;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxControlLs <= IDLE;
  else if (hwErr)
    rxControlLs <= rxControlCs;
end


// rxControl FSM Current State Logic 
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxControlCs <= IDLE;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxControlCs <= IDLE;
  else if (!padding4BytesEn || stopRx_p)
    rxControlCs <= rxControlNs;
end


// rxControl FSM Padding State Logic 
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxControlPs <= IDLE;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxControlPs <= IDLE;
  else if (padding4BytesEn || padding2BytesEn)
    rxControlPs <= rxControlNs;
end

// rxControl FSM Next State Logic.
always @* 
begin
  // Default state
  rxControlNs = rxControlCs; 
  
  case(rxControlCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits start from A-MPDU Deaggregator
      if (rxDataStart_p)
      begin
        if (rxNDP && !txInProgressDly)
          //$fsm_t When rxDataStart_p and not txInProgress and rxNDP received, the state machine goes to WRITE_STATUS state
          rxControlNs = WRITE_STATUS;
        else if (rxNDP && txInProgressDly)
          //$fsm_t When rxDataStart_p and txInProgress and rxNDP received, the state machine goes to RX_ERROR state
          rxControlNs = RX_ERROR;
        else 
          //$fsm_t When rxDataStart_p is received, the state machine goes to RX_FRM_CTRL state
          rxControlNs = RX_FRM_CTRL;
      end 
      else
        //$fsm_t While rxDataStart_p is not received, the state machine stays in IDLE state
        rxControlNs = IDLE;

    RX_FRM_CTRL:
      //$fsm_s In RX_FRM_CTRL state, the state machine waits frame control field reception
      if (rxDataValid && stateByteCnt[0])
        //$fsm_t When rxDataValid is received after 2 bytes, the state machine goes to RX_DUR_ID state
        rxControlNs = RX_DUR_ID;
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_FRM_CTRL state
        rxControlNs = RX_FRM_CTRL;

    RX_DUR_ID:
      //$fsm_s In RX_DUR_ID state, the state machine waits frame duration field reception
      if (rxDataValid && stateByteCnt[0])
        //$fsm_t When frame is not reserved, the state machine goes to RX_ADDR1 state
        rxControlNs = RX_ADDR1;
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_DUR_ID state
        rxControlNs = RX_DUR_ID;

    RX_ADDR1:
      //$fsm_s In RX_ADDR1 state, the state machine waits ADDR1 field reception
      if (rxDataValid && (stateByteCnt == 8'h05))
      begin
        if (ackRcved || ctsRcved)
          //$fsm_t When ACK or CTS is received, the state machine goes to RX_FCS state
          rxControlNs = RX_FCS;
        else if (ctrlWrapRcved)
          //$fsm_t When Control Wrapper is received, the state machine goes to RX_CAR_FRM_CTRL state
          rxControlNs = RX_CAR_FRM_CTRL;
        else
          //$fsm_t When frame is not an ACK or CTS, the state machine goes to RX_ADDR2 state
          rxControlNs = RX_ADDR2;
      end
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_ADDR1 state
        rxControlNs = RX_ADDR1;

    RX_ADDR2:
      //$fsm_s In RX_ADDR2 state, the state machine waits ADDR2 field reception
      if (rxDataValid && (stateByteCnt == 8'h05))
      begin
        if (reservedRcved)
        begin
          if (rxByteCnt > 16'h0004)
            //$fsm_t When reserved frame is received, the state machine goes to RX_FRM_BODY state
            rxControlNs = RX_FRM_BODY;
          else
            //$fsm_t When reserved frame is received, the state machine goes to RX_FRM_BODY state
            rxControlNs = RX_FCS;
        end
        else if (baRcved || barRcved)
          //$fsm_t When BA or BAR is received, the state machine goes to RX_BA_CTRL state
          rxControlNs = RX_BA_CTRL;
        else if (ctrlFrame)
          //$fsm_t When a control frame is received, the state machine goes to RX_FCS state
          rxControlNs = RX_FCS;
        else
          //$fsm_t When frame is not a control frame, the state machine goes to RX_ADDR3 state
          rxControlNs = RX_ADDR3;
      end
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_ADDR2 state
        rxControlNs = RX_ADDR2;

    RX_ADDR3:
      //$fsm_s In RX_ADDR3 state, the state machine waits ADDR3 field reception
      if (rxDataValid && (stateByteCnt == 8'h05))
        //$fsm_t When rxDataValid is received after 21 bytes, the state machine goes to RX_SEQ_CTRL state
        rxControlNs = RX_SEQ_CTRL; 
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_ADDR3 state
        rxControlNs = RX_ADDR3;

    RX_SEQ_CTRL:
      //$fsm_s In RX_SEQ_CTRL state, the state machine waits Sequence control field reception
      if (rxDataValid && stateByteCnt[0])
      begin
        if (rxByteCnt < 16'h0005)
          //$fsm_t When frame body is null, the state machine goes to RX_FCS state
          rxControlNs = RX_FCS;
        else if ((rxByteCnt <= 16'h000d) && protectedBit && !qosFrame)
          //$fsm_t When frame is encrypted and length is less or equal to 13, the state machine goes to RX_FRM_BODY state
          rxControlNs = RX_FRM_BODY;
        else if (dataFrame && toDS && fromDS)
          //$fsm_t When frame is data with addr field, the state machine goes to RX_ADDR4 state
          rxControlNs = RX_ADDR4;
        else if ((bcnRcved || probRespRcved) && !htcFrame)
          //$fsm_t When frame is beacon or probe response, the state machine goes to RX_TIMESTAMP state
          rxControlNs = RX_TIMESTAMP;
`ifdef ENCRYPTION
        else if (protectedBit && !qosFrame && !htcFrame)
          //$fsm_t When frame is encrypted, the state machine goes to RX_IV_WAPIKEYIDX state
          rxControlNs = RX_IV_WAPIKEYIDX;
`endif
        else if (!qosFrame && !htcFrame)
          //$fsm_t When frame is not QoS and not HTC, the state machine goes to RX_FRM_BODY state
          rxControlNs = RX_FRM_BODY;
        else if (!qosFrame)
          //$fsm_t When frame contains HTC field, the state machine goes to RX_HT_CTRL state
          rxControlNs = RX_HT_CTRL;
        else
          //$fsm_t When frame is QoS, the state machine goes to RX_QOS_CTRL state
          rxControlNs = RX_QOS_CTRL;
      end
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_SEQ_CTRL state
        rxControlNs = RX_SEQ_CTRL;

    RX_ADDR4:
      //$fsm_s In RX_ADDR4 state, the state machine waits ADDR4 field reception
      if (rxDataValid && (stateByteCnt == 8'h05))
      begin
        if (rxByteCnt < 16'h0005)
          //$fsm_t When frame body is null, the state machine goes to RX_FCS state
          rxControlNs = RX_FCS;
        else if ((rxByteCnt <= 16'h000d) && protectedBit && !qosFrame)
          //$fsm_t When frame is encrypted and length is less or equal to 13, the state machine goes to RX_FRM_BODY state
          rxControlNs = RX_FRM_BODY;
`ifdef ENCRYPTION
        else if (protectedBit && !qosFrame)
          //$fsm_t When frame is encrypted, the state machine goes to RX_IV_WAPIKEYIDX state
          rxControlNs = RX_IV_WAPIKEYIDX;
`endif
        else if (!qosFrame)
          //$fsm_t When frame is not QoS, the state machine goes to RX_FRM_BODY state
          rxControlNs = RX_FRM_BODY;
        else
          //$fsm_t When frame is QoS, the state machine goes to RX_QOS_CTRL state
          rxControlNs = RX_QOS_CTRL;
      end
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_ADDR4 state
        rxControlNs = RX_ADDR4;

    RX_QOS_CTRL:
      //$fsm_s In RX_QOS_CTRL state, the state machine waits QoS Control field reception
      if (rxDataValid && stateByteCnt[0])
      begin
        if (rxByteCnt < 16'h0005)
          //$fsm_t When frame body is null, the state machine goes to RX_FCS state
          rxControlNs = RX_FCS;
        else if ((rxByteCnt <= 16'h000d) && protectedBit && !htcFrame)
          //$fsm_t When frame is encrypted and length is less or equal to 13, the state machine goes to RX_FRM_BODY state
          rxControlNs = RX_FRM_BODY;
`ifdef ENCRYPTION
        else if (protectedBit && !htcFrame)
          //$fsm_t When frame is encrypted, the state machine goes to RX_IV_WAPIKEYIDX state
          rxControlNs = RX_IV_WAPIKEYIDX;
`endif
        else if (!htcFrame)
          //$fsm_t When frame does not contain HTC field, the state machine goes to RX_FRM_BODY state
          rxControlNs = RX_FRM_BODY;
        else
          //$fsm_t When frame contains HTC field, the state machine goes to RX_HT_CTRL state
          rxControlNs = RX_HT_CTRL;
      end
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_QOS_CTRL state
        rxControlNs = RX_QOS_CTRL;

    RX_CAR_FRM_CTRL:
      //$fsm_s In RX_CAR_FRM_CTRL state, the state machine waits Carried Frame Control field reception
      if (rxDataValid && stateByteCnt[0])
        //$fsm_t When rxDataValid is received after 2 bytes, the state machine goes to RX_HT_CTRL state
        rxControlNs = RX_HT_CTRL;
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_CAR_FRM_CTRL state
        rxControlNs = RX_CAR_FRM_CTRL;

    RX_HT_CTRL:
      //$fsm_s In RX_HT_CTRL state, the state machine waits HT Control field reception
      if (rxDataValid && (stateByteCnt == 8'h03))
      begin
        if ((rxByteCnt < 16'h0005) || (ctrlWrapFlag && (ackRcved || ctsRcved)))
          //$fsm_t When frame body is null or when ACK or CTS is received from a control wrapper, the state machine goes to RX_FCS state
          rxControlNs = RX_FCS;
        else if ((rxByteCnt <= 16'h000d) && protectedBit)
          //$fsm_t When frame is encrypted and length is less or equal to 13, the state machine goes to RX_FRM_BODY state
          rxControlNs = RX_FRM_BODY;
        else if (ctrlWrapFlag)
          //$fsm_t When frame is a control wrapper, the state machine goes to RX_ADDR2 state
          rxControlNs = RX_ADDR2;
        else if (bcnRcved || probRespRcved)
          //$fsm_t When frame is beacon or probe response, the state machine goes to RX_TIMESTAMP state
          rxControlNs = RX_TIMESTAMP;
`ifdef ENCRYPTION
        else if (protectedBit)
          //$fsm_t When frame is encrypted, the state machine goes to RX_IV_WAPIKEYIDX state
          rxControlNs = RX_IV_WAPIKEYIDX;
`endif
        else
          //$fsm_t When frame is not encrypted, the state machine goes to RX_FRM_BODY state
          rxControlNs = RX_FRM_BODY;
      end
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_HT_CTRL state
        rxControlNs = RX_HT_CTRL;

`ifdef ENCRYPTION
    RX_IV_WAPIKEYIDX:
      //$fsm_s In RX_IV_WAPIKEYIDX state, the state machine waits IV field reception for WEP/CCMP and KEYIDX field reception for WAPI 
`ifdef RW_WAPI_EN
      if(WAPIMode && rxDataValid && (stateByteCnt == 8'h01))
      begin
        rxControlNs = RX_EXTIV_WAPIPN;
      end
      else
      if (!WAPIMode && rxDataValid && (stateByteCnt == 8'h03))
`else
      if (rxDataValid && (stateByteCnt == 8'h03))
`endif //RW_WAPI_EN
      begin
        if (((rxByteCnt <= 16'h000d) && rxData[5]) || !rxData[5])
          //$fsm_t When frame has not extended IV or length is less or equal to 13, the state machine goes to RX_FRM_BODY state
          rxControlNs = RX_FRM_BODY;
        else
          //$fsm_t When frame has extended IV, the state machine goes to RX_EXTIV_WAPIPN state
          rxControlNs = RX_EXTIV_WAPIPN;
      end
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_IV_WAPIKEYIDX state
        rxControlNs = RX_IV_WAPIKEYIDX;

    RX_EXTIV_WAPIPN:
      //$fsm_s In RX_EXTIV_WAPIPN state, the state machine waits Extended IV or WAPI PN field reception
`ifdef RW_WAPI_EN
      if(WAPIMode && rxDataValid && (stateByteCnt == 8'hF))
      begin
        rxControlNs = RX_FRM_BODY;
      end
      else
      if (!WAPIMode && rxDataValid && (stateByteCnt == 8'h03))
`else
      if (rxDataValid && (stateByteCnt == 8'h03))
`endif //RW_WAPI_EN
        //$fsm_t When rxDataValid is received after 4 bytes or 16 bytes for WAPI PN, the state machine goes to RX_FRM_BODY state
        rxControlNs = RX_FRM_BODY;
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_EXTIV_WAPIPN state
        rxControlNs = RX_EXTIV_WAPIPN;
`endif

    RX_FRM_BODY:
      //$fsm_s In RX_FRM_BODY state, the state machine waits end of frame body field reception
      if (rxByteCnt == 16'h0004 && rxDataValid)
        //$fsm_t When rxByteCnt=4, the state machine goes to RX_FCS state
        rxControlNs = RX_FCS; 
`ifdef ENCRYPTION
      else if (!nullKeyFound && rxDataValid && (rxByteCnt == 16'h0008) &&
             ((cTypeKSR == 3'b001) || (cTypeKSR == 3'b010)))
        //$fsm_t When frame is WEP or TKIP, the state machine goes to RX_ICV state
        rxControlNs = RX_ICV; 
`ifdef RW_WAPI_EN
      else if (!nullKeyFound && rxDataValid && 
               (( (cTypeKSR == 3'b011) && (rxByteCnt == 16'h000c) ) ||    // CCMP : MIC(8) +FCS(4)   
                ( (cTypeKSR == 3'b100) && (rxByteCnt == 16'h0014) )    )) // WAPI : MIC(16)+FCS(4)  
`else
      else if (!nullKeyFound && rxDataValid && (rxByteCnt == 16'h000c) &&
              (cTypeKSR == 3'b011))
`endif //RW_WAPI_EN
        //$fsm_t When frame is CCMP or WAPI, the state machine goes to RX_CCMP_WAPI_MIC state
        rxControlNs = RX_CCMP_WAPI_MIC; 
`endif
      else
        //$fsm_t While rxByteCnt>4, the state machine stays in RX_FRM_BODY state
        rxControlNs = RX_FRM_BODY;

`ifdef ENCRYPTION
    RX_ICV:
      //$fsm_s In RX_ICV state, the state machine waits RX_ICV field reception
      if (rxDataValid && (stateByteCnt == 8'h03))
        //$fsm_t When rxDataValid is received after 4 bytes, the state machine goes to RX_FCS state
        rxControlNs = RX_FCS;
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_ICV state
        rxControlNs = RX_ICV;

    RX_CCMP_WAPI_MIC:
      //$fsm_s In RX_CCMP_WAPI_MIC state, the state machine waits RX_CCMP_WAPI_MIC field reception
`ifdef RW_WAPI_EN
      if ( rxDataValid && 
           ((!WAPIMode && (stateByteCnt == 8'h07)) ||    // CCMP MIC = 8 bytes
            ( WAPIMode && (stateByteCnt == 8'h0F))    )) // WAPI MIC = 16 bytes
           
`else
      if (rxDataValid && (stateByteCnt == 8'h07))
`endif
        //$fsm_t When rxDataValid is received after 8 bytes, the state machine goes to RX_FCS state
        rxControlNs = RX_FCS;
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_CCMP_WAPI_MIC state
        rxControlNs = RX_CCMP_WAPI_MIC;
`endif

    RX_FCS:
      //$fsm_s In RX_FCS state, the state machine waits the last 4 FCS bytes of the frame
      if (rxDataValid && (stateByteCnt == 8'h03))
        //$fsm_t When rxDataValid is received after 4 bytes, the state machine goes to CHECK_FCS state
        rxControlNs = CHECK_FCS; 
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_FCS state
        rxControlNs = RX_FCS;

    RX_BA_CTRL:
      //$fsm_s In RX_BA_CTRL state, the state machine waits BA Control field reception
      if (rxDataValid && stateByteCnt[0])
        //$fsm_t When rxDataValid is received after 2 bytes, the state machine goes to RX_BA_SEQ_CTRL state
        rxControlNs = RX_BA_SEQ_CTRL;
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_BA_CTRL state
        rxControlNs = RX_BA_CTRL;

    RX_BA_SEQ_CTRL:
      //$fsm_s In RX_BA_SEQ_CTRL state, the state machine waits BA Starting Sequence Control field reception
      if (rxDataValid && stateByteCnt[0])
      begin
        if (barRcved)
          //$fsm_t When frame is BA Request, the state machine goes to RX_FCS state
          rxControlNs = RX_FCS;
        else
          //$fsm_t When frame is BA, the state machine goes to RX_BA_BITMAP state
          rxControlNs = RX_BA_BITMAP;
      end
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_BA_SEQ_CTRL state
        rxControlNs = RX_BA_SEQ_CTRL;

    RX_BA_BITMAP:
      //$fsm_s In RX_BA_BITMAP state, the state machine waits BA Bitmap field reception
      if (rxDataValid && (((stateByteCnt == 8'h07) && compressedBA) || (stateByteCnt == 8'h7f)))
        //$fsm_t When rxDataValid is received after 8 bytes on compressed BA or after 128 bytes on normal BA, the state machine goes to RX_FCS state
        rxControlNs = RX_FCS;
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_FCS state
        rxControlNs = RX_BA_BITMAP;

    RX_TIMESTAMP:
      //$fsm_s In RX_TIMESTAMP state, the state machine waits Timestamp field reception
      if (rxDataValid && (stateByteCnt == 8'h07))
        //$fsm_t When rxDataValid is received after 8 bytes, the state machine goes to RX_BCN_INTRVL state
        rxControlNs = RX_BCN_INTRVL;
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_TIMESTAMP state
        rxControlNs = RX_TIMESTAMP;

    RX_BCN_INTRVL:
      //$fsm_s In RX_BCN_INTRVL state, the state machine waits Beacon Interval field reception
      if (rxDataValid && stateByteCnt[0])
        //$fsm_t When rxDataValid is received after 2 bytes, the state machine goes to RX_CAPABILITY state
        rxControlNs = RX_CAPABILITY;
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_BCN_INTRVL state
        rxControlNs = RX_BCN_INTRVL;

    RX_CAPABILITY:
      //$fsm_s In RX_CAPABILITY state, the state machine waits Capability info. field reception
      if (rxDataValid && stateByteCnt[0])
        //$fsm_t When rxDataValid is received after 2 bytes, the state machine goes to RX_ELEMENT_ID state
        rxControlNs = RX_ELEMENT_ID;
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_CAPABILITY state
        rxControlNs = RX_CAPABILITY;

    RX_ELEMENT_ID:
      //$fsm_s In RX_ELEMENT_ID state, the state machine waits Element ID field reception
      if (rxDataValid)
      begin
        if (rxByteCnt == 16'h0004)
          //$fsm_t When element body is null, the state machine goes to RX_FCS state
          rxControlNs = RX_FCS;
        else
          //$fsm_t When rxDataValid is true, the state machine goes to RX_ELEMENT_LEN state
          rxControlNs = RX_ELEMENT_LEN;
      end
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_ELEMENT_ID state
        rxControlNs = RX_ELEMENT_ID;

    RX_ELEMENT_LEN:
      //$fsm_s In RX_ELEMENT_LEN state, the state machine waits Element length field reception
      if (rxDataValid)
      begin
        if (rxByteCnt == 16'h0004)
          //$fsm_t When element body is null, the state machine goes to RX_FCS state
          rxControlNs = RX_FCS;
        else if (rxData == 8'h00)
          //$fsm_t When length is null, the state machine goes to RX_ELEMENT_ID state
          rxControlNs = RX_ELEMENT_ID;
        else
          //$fsm_t When length is not null, the state machine goes to RX_ELEMENT_BODY state
         rxControlNs = RX_ELEMENT_BODY;
      end
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_ELEMENT_LEN state
        rxControlNs = RX_ELEMENT_LEN;

    RX_ELEMENT_BODY:
      //$fsm_s In RX_ELEMENT_BODY state, the state machine waits Element body field reception
      if (rxDataValid)
      begin
        if (rxByteCnt == 16'h0004)
          //$fsm_t When last element body is reached, the state machine goes to RX_FCS state
          rxControlNs = RX_FCS;
        else if (stateByteCnt == (infoElemLen - 8'd1))
          //$fsm_t When element length is reached, the state machine goes to RX_ELEMENT_ID state
          rxControlNs = RX_ELEMENT_ID;
        else
          //$fsm_t When length is not reached, the state machine stays in RX_ELEMENT_BODY state
         rxControlNs = RX_ELEMENT_BODY;
      end
      else
        //$fsm_t While rxDataValid is not received, the state machine stays in RX_ELEMENT_BODY state
        rxControlNs = RX_ELEMENT_BODY;

    CHECK_FCS:
      //$fsm_s In CHECK_FCS state, the state machine waits FCS status
`ifdef ENCRYPTION
      if (acceptProtected && !nullKeyFound && protectedPld && !ctrlFrame && !mgmtNoEncryptFrame)
        //$fsm_t When fcsOk is correct and frame is encrypted, the state machine goes to CHECK_ENCR state
        rxControlNs = CHECK_ENCR;
      else if (acceptProtected && (nullKeyFound || !protectedPld || ctrlFrame || mgmtNoEncryptFrame))
        //$fsm_t When fcsOk is correct and frame is encrypted, and no key to decrypt or no payload to decrypt then discard
        rxControlNs = DISCARD_FRAME;
      else
      begin
`endif
        if (rxFIFOOverFlowError)
          //$fsm_t When rxFIFOOverFlowError is active, the state machine goes to IDLE state
          rxControlNs = IDLE;
        else if (acceptRcved && !respError && ((!fcsOk && acceptErrorFrames) || fcsOk))
        begin
          if(rxIndexSearchDone) 
            //$fsm_t When control frame has to be forwarded to SW, the state machine goes to WRITE_STATUS state
            rxControlNs = WRITE_STATUS;
          else
            //$fsm_t When control frame has to be forwarded to SW, but key search is not done the state machine goes to WAIT_KEYSEARCHDONE
            rxControlNs = WAIT_KEYSEARCHDONE;
        end
        else
          //$fsm_t While control frame has not to be forwarded to SW, the state machine goes to DISCARD_FRAME state
          rxControlNs = DISCARD_FRAME;
`ifdef ENCRYPTION
      end

    CHECK_ENCR:
      //$fsm_s In CHECK_ENCR state, the state machine waits status from Encryption engine
      if (rxFIFOOverFlowError)
        //$fsm_t When rxFIFOOverFlowError is active, the state machine goes to IDLE state
        rxControlNs = IDLE;
      else if (decrStatusValid_p || decrStatusValidHold)
      begin
        if (acceptRcved && !respError &&
            !discardDecrypt &&
           (((fcsErrorRcved || invalidProtectPktLen) && acceptErrorFrames) ||
            (fcsOkRcved && !invalidProtectPktLen)))
        begin
          if(rxIndexSearchDone) 
            //$fsm_t When control frame has to be forwarded to SW, the state machine goes to WRITE_STATUS state
            rxControlNs = WRITE_STATUS;
          else
            //$fsm_t When control frame has to be forwarded to SW, but key search is not done the state machine goes to WAIT_KEYSEARCHDONE
            rxControlNs = WAIT_KEYSEARCHDONE;
        end
        else
          //$fsm_t While frame has not to be forwarded to SW, the state machine goes to DISCARD_FRAME state
          rxControlNs = DISCARD_FRAME;
      end
      else
        //$fsm_t While status is not received, the state machine stays in CHECK_ENCR state
        rxControlNs = CHECK_ENCR;
`endif

    WAIT_KEYSEARCHDONE:
      if (rxIndexSearchDone)
        //$fsm_t When control frame has to be forwarded to SW, and key search is done the state machine goes to WRITE_STATUS state
        rxControlNs = WRITE_STATUS;
      else if (rxFIFODone_p || rxFIFOOverFlowError)
        //$fsm_t When rxFIFODone_p is received or rxFIFOOverFlowError is active, the state machine goes to IDLE state
        rxControlNs = IDLE; 
      else
        //$fsm_t When control frame has to be forwarded to SW, but key search is not done the state machine goes to WAIT_KEYSEARCHDONE
        rxControlNs = WAIT_KEYSEARCHDONE;

    WRITE_STATUS:
      if (rxFIFODone_p || rxFIFOOverFlowError) 
        //$fsm_t When rxFIFODone_p is received or rxFIFOOverFlowError is active, the state machine goes to IDLE state
        rxControlNs = IDLE; 
      else
        //$fsm_t While rxFIFODone_p is not received, the state machine stays in WRITE_STATUS state
        rxControlNs = WRITE_STATUS;

    RX_ERROR:
      //$fsm_s In RX_ERROR state, the state machine checks acceptErrorFrames register
      if (acceptErrorFrames && !rxNDP)
        //$fsm_t If acceptErrorFrames is active, the state machine goes to WRITE_STATUS state
        rxControlNs = WRITE_STATUS;
      else
        //$fsm_t While acceptErrorFrames is not active, the state machine goes to DISCARD_FRAME state
        rxControlNs = DISCARD_FRAME;

    DISCARD_FRAME:
      //$fsm_s In DISCARD_FRAME state, the state machine goes to IDLE state
  
      //$fsm_t After one clock cycle, the state machine goes to IDLE state
      rxControlNs = IDLE; 
    
    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
     default:   
        rxControlNs = IDLE; 
    // pragma coverage block = on
    
  endcase

  if ((rxControlCs != IDLE) && (rxControlCs != WRITE_STATUS) && (rxControlCs != WAIT_KEYSEARCHDONE) && 
      (rxControlCs != CHECK_ENCR)  && (rxControlCs != CHECK_FCS) &&
      ((macPhyIfRxErr_p && !macPhyIfRxErrInt_p) || rxDataError_p || 
       macPHYIFOverflow || invalidPkt))
    //$fsm_t When rxDataError_p or macPhyIfRxErr_p are true,
    // or when rxByteCnt=3 and fsm is not in RX_FCS state,
    // or when rxDataEnd_p is true and fsm is not in RX_FCS state, then
    // fsm goes to RX_ERROR state
    rxControlNs = RX_ERROR;

  else if (stopRx_p && (rxControlCs != IDLE) && (rxControlCs != WRITE_STATUS) && (rxControlCs != WAIT_KEYSEARCHDONE)
`ifdef ENCRYPTION
           && (rxControlCs != CHECK_ENCR)
`endif
          )
  begin
    if (rxFIFOOverFlowError)
      //$fsm_t When rxFIFOOverFlowError is active, fsm goes to IDLE state
      rxControlNs = IDLE;
    else
      //$fsm_t When stopRx_p is true and fsm is not idle or write status, fsm goes to DISCARD_FRAME state
      rxControlNs = DISCARD_FRAME;
  end    

  else if (padding4BytesEn_ff1)
    //$fsm_t When padding bytes are written, fsm have to stay in current state
    rxControlNs = rxControlPs;
  
end

// Generation of dataProtectedNoPld which indicates a received frame  
// delayed of one clock cycle
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    protectedPld <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlCs == IDLE) || nullKeyFound)
    protectedPld <= 1'b0;
  else if (rxControlCs == RX_IV_WAPIKEYIDX)
    protectedPld <= 1'b1;
end


// Generation of macPhyIfRxErrInt_p which is macPhyIfRxErr_p
// delayed of one clock cycle
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPhyIfRxErrInt_p <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    macPhyIfRxErrInt_p <= 1'b0;
  else 
    macPhyIfRxErrInt_p <= macPhyIfRxErr_p;
end

// Byte counter by states. This counter maintains the number of
// valid pulses from the A-MPDU deaggregator to be expected in each state.
// Each valid pulse corresponds to a byte received.
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset 
    stateByteCnt <= 8'h00;
  else if(macCoreClkSoftRst_n == 1'b0)
    stateByteCnt <= 8'h00;
  else if ((rxControlCs == IDLE) || (rxControlCs == RX_ERROR) ||
           (!padding4BytesEn && padding4BytesEn_ff1) || 
           ((rxByteCnt == 16'h0004) && rxDataValid))
    stateByteCnt <= 8'h00;
  else if (rxDataValid && !padding4BytesEn)
  begin
    case (rxControlCs)

      // 2 bytes
      RX_FRM_CTRL, RX_DUR_ID, RX_SEQ_CTRL, RX_QOS_CTRL,
      RX_CAR_FRM_CTRL, RX_BA_CTRL, RX_BA_SEQ_CTRL, RX_BCN_INTRVL,
      RX_CAPABILITY:
        if (stateByteCnt == 8'h01)
          stateByteCnt <= 8'h00;
        else
          stateByteCnt <= stateByteCnt + 8'd1;

      // 4 bytes
      RX_HT_CTRL, RX_FCS:
        if (stateByteCnt == 8'h03)
          stateByteCnt <= 8'h00;
        else
          stateByteCnt <= stateByteCnt + 8'd1;

      // 6 bytes
      RX_ADDR1, RX_ADDR2, RX_ADDR3, RX_ADDR4:
        if (stateByteCnt == 8'h05)
          stateByteCnt <= 8'h00;
        else
          stateByteCnt <= stateByteCnt + 8'd1;

      // 8 bytes
      RX_TIMESTAMP:
        if (stateByteCnt == 8'h07)
          stateByteCnt <= 8'h00;
        else
          stateByteCnt <= stateByteCnt + 8'd1;

      // 8 / 128 bytes
      RX_BA_BITMAP:
        if ((compressedBA && (stateByteCnt == 8'h07)) || (stateByteCnt == 8'h7f))
          stateByteCnt <= 8'h00;
        else
          stateByteCnt <= stateByteCnt + 8'd1;

`ifdef ENCRYPTION
      // Encryption states
      RX_IV_WAPIKEYIDX:
`ifdef RW_WAPI_EN
        if ( (!WAPIMode && (stateByteCnt == 8'h03)) || 
             ( WAPIMode && (stateByteCnt == 8'h01))    )
`else
        if (stateByteCnt == 8'h03)
`endif //RW_WAPI_EN
          stateByteCnt <= 8'h00;
        else
          stateByteCnt <= stateByteCnt + 8'd1;
      
      
      RX_EXTIV_WAPIPN:
`ifdef RW_WAPI_EN
        if ( (!WAPIMode && (stateByteCnt == 8'h03)) || 
             ( WAPIMode && (stateByteCnt == 8'h0F))    )
`else
        if (stateByteCnt == 8'h03)
`endif //RW_WAPI_EN
          stateByteCnt <= 8'h00;
        else
          stateByteCnt <= stateByteCnt + 8'd1;
      
      RX_ICV:
        if (stateByteCnt == 8'h03)
          stateByteCnt <= 8'h00;
        else
          stateByteCnt <= stateByteCnt + 8'd1;
          
      RX_CCMP_WAPI_MIC:
`ifdef RW_WAPI_EN
        if ( (!WAPIMode && (stateByteCnt == 8'h07)) || 
             ( WAPIMode && (stateByteCnt == 8'h0F))    )
`else
        if (stateByteCnt == 8'h07)
`endif //RW_WAPI_EN
          stateByteCnt <= 8'h00;
        else
          stateByteCnt <= stateByteCnt + 8'd1;
`endif

      // Element body state
      RX_ELEMENT_BODY:
        if (stateByteCnt == (infoElemLen - 8'd1))
          stateByteCnt <= 8'h00;
        else
          stateByteCnt <= stateByteCnt + 8'd1;
      
      default:
        stateByteCnt <= 8'h00;

    endcase
  end
  else
    stateByteCnt <= stateByteCnt;
end

// generate invalidProtectPktLen indicating that protected bit was set but
// pkt length is wrong (less than 12 -> FCS + IV+ICV) or 
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    invalidProtectPktLen <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlCs == IDLE))
    invalidProtectPktLen <= 1'b0;
  else if (rxDataValid && protectedBit && (rxByteCnt <= 16'h000d) &&
          ((rxControlCs == RX_SEQ_CTRL) || (rxControlCs == RX_ADDR4)  ||
           (rxControlCs == RX_HT_CTRL) || (rxControlCs == RX_QOS_CTRL)))
     invalidProtectPktLen <= 1'b1;
`ifdef ENCRYPTION
  else if ((rxControlCs == RX_IV_WAPIKEYIDX) && rxDataValid && (stateByteCnt == 8'h03) &&
            rxData[5] == 1'b1 && (rxByteCnt <= 16'h000d))
     invalidProtectPktLen <= 1'b1;
  
`endif
end

// generate invalidPkt indicating that pkt is wrong according to RX_FCS state
assign invalidPkt = (rxDataEnd_p || (rxDataValid && (rxByteCnt == 16'h0003))) &&
                    (rxControlCs != RX_FCS);

// Frame decoder command
assign rxFrmCtrlEn         = ((rxControlCs == RX_FRM_CTRL) ||
                              (rxControlCs == RX_CAR_FRM_CTRL)) && !padding4BytesEn_ff1;
assign rxDurationIdEn      = (rxControlCs == RX_DUR_ID);
assign rxAddr1En           = (rxControlCs == RX_ADDR1) && !padding4BytesEn_ff1;
assign rxAddr2En           = (rxControlCs == RX_ADDR2) && !padding4BytesEn_ff1;
assign rxAddr3En           = (rxControlCs == RX_ADDR3);
assign rxQoSCtrlEn         = (rxControlCs == RX_QOS_CTRL) && !padding4BytesEn_ff1;
assign rxHTCtrlEn          = (rxControlCs == RX_HT_CTRL) && !padding4BytesEn_ff1;
assign rxSeqCtrlEn         = (rxControlCs == RX_SEQ_CTRL) && !padding4BytesEn_ff1;
assign rxBACtrlEn          = (rxControlCs == RX_BA_CTRL);
assign rxBASeqCtrlEn       = (rxControlCs == RX_BA_SEQ_CTRL) && !padding4BytesEn_ff1;
`ifdef ENCRYPTION
`ifdef RW_WAPI_EN
assign rxAddr4En           = (rxControlCs == RX_ADDR4);
assign rxWAPIKeyIdxEn      = WAPIMode && (rxControlCs == RX_IV_WAPIKEYIDX) && (stateByteCnt == 8'h00);
assign rxWAPIPNEn          = WAPIMode && (rxControlCs == RX_EXTIV_WAPIPN);
assign rxInitVectorEn      = ~WAPIMode && (rxControlCs == RX_IV_WAPIKEYIDX) && ~padding4BytesEn_ff1;
assign rxExtInitVectorEn   = ~WAPIMode && (rxControlCs == RX_EXTIV_WAPIPN);
`else
assign rxInitVectorEn      = (rxControlCs == RX_IV_WAPIKEYIDX) && !padding4BytesEn_ff1;
assign rxExtInitVectorEn   = (rxControlCs == RX_EXTIV_WAPIPN);
`endif //RW_WAPI_EN
`endif
assign rxTimeStampEn       = (rxControlCs == RX_TIMESTAMP);
assign rxDtimCntEn         = ((rxControlCs == RX_ELEMENT_BODY) &&
                              (elementID == 8'h05) &&
                              (stateByteCnt == 8'h00));
assign rxDtimPeriodEn      = ((rxControlCs == RX_ELEMENT_BODY) &&
                              (elementID == 8'h05) &&
                              (stateByteCnt == 8'h01));
assign rxCfpCntEn          = ((rxControlCs == RX_ELEMENT_BODY) &&
                              (elementID == 8'h04) &&
                              (stateByteCnt == 8'h00));
assign rxCfpPeriodEn       = ((rxControlCs == RX_ELEMENT_BODY) &&
                              (elementID == 8'h04) &&
                              (stateByteCnt == 8'h01));
assign rxCfpDurRemainingEn = ((rxControlCs == RX_ELEMENT_BODY) &&
                              (elementID == 8'h04) &&
                             ((stateByteCnt == 8'h04) ||
                             ((stateByteCnt == 8'h05))));
assign rxQuietCount1En     = ((rxControlCs == RX_ELEMENT_BODY) &&
                              (elementID == 8'h28) &&
                               !quietParameterToggle &&
                              (stateByteCnt == 8'h00));
assign rxQuietPeriod1En    = ((rxControlCs == RX_ELEMENT_BODY) &&
                             (elementID == 8'h28) &&
                             !quietParameterToggle &&
                             (stateByteCnt == 8'h01));
assign rxQuietDuration1En  = ((rxControlCs == RX_ELEMENT_BODY) &&
                             (elementID == 8'h28) &&
                             !quietParameterToggle &&
                             ((stateByteCnt == 8'h02) ||
                             ((stateByteCnt == 8'h03))));
assign rxQuietOffset1En    = ((rxControlCs == RX_ELEMENT_BODY) &&
                              (elementID == 8'h28) &&
                               !quietParameterToggle &&
                             ((stateByteCnt == 8'h04) ||
                             ((stateByteCnt == 8'h05))));
assign rxQuietCount2En     = ((rxControlCs == RX_ELEMENT_BODY) &&
                              (elementID == 8'h28) &&
                               quietParameterToggle &&
                              (stateByteCnt == 8'h00));
assign rxQuietPeriod2En    = ((rxControlCs == RX_ELEMENT_BODY) &&
                             (elementID == 8'h28) &&
                             quietParameterToggle &&
                             (stateByteCnt == 8'h00));
assign rxQuietDuration2En  = ((rxControlCs == RX_ELEMENT_BODY) &&
                              (elementID == 8'h28) &&
                               quietParameterToggle &&
                             ((stateByteCnt == 8'h02) ||
                             ((stateByteCnt == 8'h03))));
assign rxQuietOffset2En    = ((rxControlCs == RX_ELEMENT_BODY) &&
                              (elementID == 8'h28) &&
                               quietParameterToggle &&
                             ((stateByteCnt == 8'h04) ||
                             ((stateByteCnt == 8'h05))));

assign fcsCheck_p          = (rxControlCs == CHECK_FCS);
assign rxDurationIdEnd_p   = (rxControlCs == RX_DUR_ID) &&
                             (stateByteCnt == 8'h01) && rxDataValid;

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxAddr1End_p <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxAddr1End_p <= 1'b0;
  else if ((rxControlCs == RX_ADDR1) && (stateByteCnt == 8'h05) && rxDataValid)
    rxAddr1End_p <= 1'b1;
  else
    rxAddr1End_p <= 1'b0;
end

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxAddr2End_p <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxAddr2End_p <= 1'b0;
  else if ((rxControlCs == RX_ADDR2) && (stateByteCnt == 8'h05) && rxDataValid)
    rxAddr2End_p <= 1'b1;
  else
    rxAddr2End_p <= 1'b0;
end

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    carFrameCtrlEnd_p <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    carFrameCtrlEnd_p <= 1'b0;
  else if ((rxControlCs == RX_CAR_FRM_CTRL) && (stateByteCnt == 8'h01) && rxDataValid)
    carFrameCtrlEnd_p <= 1'b1;
  else
    carFrameCtrlEnd_p <= 1'b0;
end

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxAddr3End_p <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxAddr3End_p <= 1'b0;
  else if ((rxControlCs == RX_ADDR3) && (stateByteCnt == 8'h05) && rxDataValid)
    rxAddr3End_p <= 1'b1;
  else
    rxAddr3End_p <= 1'b0;
end

`ifdef RW_WAPI_EN
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxAddr4End_p <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxAddr4End_p <= 1'b0;
  else if ((rxControlCs == RX_ADDR4) && (stateByteCnt == 8'h05) && rxDataValid)
    rxAddr4End_p <= 1'b1;
  else
    rxAddr4End_p <= 1'b0;
end

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxWAPIKeyIdxEnd_p <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxWAPIKeyIdxEnd_p <= 1'b0;
  else if ((rxControlCs == RX_IV_WAPIKEYIDX) && (stateByteCnt == 8'h01) && rxDataValid)
    rxWAPIKeyIdxEnd_p <= 1'b1;
  else
    rxWAPIKeyIdxEnd_p <= 1'b0;
end

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxWAPIPNEnd_p <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxWAPIPNEnd_p <= 1'b0;
  else if ((rxControlCs == RX_EXTIV_WAPIPN) && (stateByteCnt == 8'h0F) && rxDataValid)
    rxWAPIPNEnd_p <= 1'b1;
  else
    rxWAPIPNEnd_p <= 1'b0;
end
`endif //RW_WAPI_EN

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxSeqCtrlEnd_p <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxSeqCtrlEnd_p <= 1'b0;
  else if ((rxControlCs == RX_SEQ_CTRL) && (stateByteCnt == 8'h01) && rxDataValid)
    rxSeqCtrlEnd_p <= 1'b1;
  else
    rxSeqCtrlEnd_p <= 1'b0;
end

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxQoSEnd_p <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxQoSEnd_p <= 1'b0;
  else if ((rxControlCs == RX_QOS_CTRL) && (stateByteCnt == 8'h01) && rxDataValid)
    rxQoSEnd_p <= 1'b1;
  else
    rxQoSEnd_p <= 1'b0;
end

assign rxBARCtrlEnd_p      = (rxControlCs == RX_BA_CTRL) &&
                             (stateByteCnt == 8'h01) && rxDataValid;
`ifdef ENCRYPTION
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    rxInitVectorEnd_p <= 1'b0;
    rxExtIV_p         <= 1'b0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    rxInitVectorEnd_p <= 1'b0;
    rxExtIV_p         <= 1'b0;
  end
  else if ((rxControlCs == RX_IV_WAPIKEYIDX) && ((rxControlNs == RX_EXTIV_WAPIPN) || (rxControlNs == RX_FRM_BODY)))
  begin
    rxInitVectorEnd_p <= 1'b1;
    if(rxControlNs == RX_EXTIV_WAPIPN)
      rxExtIV_p <= 1'b1;
  end
  else
  begin
    rxExtIV_p         <= 1'b0;
    rxInitVectorEnd_p <= 1'b0;
  end
end
`endif

assign rxControlIdle       = (rxControlCs == IDLE);


// Flag indicating the completion of the MAC Header
assign macHeaderCompleted = (rxControlCs != IDLE) && 
                            (rxControlCs != RX_FRM_CTRL) && 
                            (rxControlCs != RX_DUR_ID) && 
                            (rxControlCs != RX_ADDR1) && 
                            (rxControlCs != RX_ADDR2) && 
                            (rxControlCs != RX_ADDR3) && 
                            (rxControlCs != RX_ADDR4) && 
                            (rxControlCs != RX_SEQ_CTRL) && 
                            (rxControlCs != RX_QOS_CTRL) && 
                            (rxControlCs != RX_CAR_FRM_CTRL) && 
                            (rxControlCs != RX_HT_CTRL) && 
                            (rxControlCs != RX_IV_WAPIKEYIDX) && 
                            (rxControlCs != RX_EXTIV_WAPIPN);

// Beacon element sampling
// information element length is sampled and used in
// RX_ELEMENT_BODY state to determine next state
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    infoElemLen <= 8'h00;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlCs == IDLE))
    infoElemLen <= 8'h00;
  else if ((rxControlCs == RX_ELEMENT_LEN) && rxDataValid)
    infoElemLen <= rxData;
end

// Sample element ID field of beacon
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    elementID  <= 8'h00;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlCs == IDLE))
    elementID  <= 8'h00;
  else if ((rxControlCs == RX_ELEMENT_ID) && rxDataValid)
    elementID <= rxData;
end

// Detect CFP parameters
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    cfpParameterFound <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlCs == IDLE))
    cfpParameterFound <= 1'b0;
  else if (elementID == 8'h04)
    cfpParameterFound <= 1'b1;
end

// Detect DTIM parameters
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    dtimParameterFound <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlCs == IDLE))
    dtimParameterFound <= 1'b0;
  else if (elementID == 8'h05)
    dtimParameterFound <= 1'b1;
end

// Detect Quiet parameters
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    quietParameterFound  <= 1'b0;
    quietParameterToggle <= 1'b0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    quietParameterFound  <= 1'b0;
    quietParameterToggle <= 1'b0;
  end
  else if (rxControlCs == IDLE)
  begin
    if (quietParameterFound)
      quietParameterToggle <= !quietParameterToggle;
    quietParameterFound    <= 1'b0;
  end
  else if (elementID == 8'h28)
    quietParameterFound <= 1'b1;
end


// FCS Control
assign fcsStartRx_p = rxDataStart_p;

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    fcsEnableRx <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    fcsEnableRx <= 1'b0;
  else if (rxDataStart_p)
    fcsEnableRx <= 1'b1;
  else if ((rxControlCs == IDLE) || (rxControlCs == CHECK_FCS) ||
    ((rxControlCs == RX_ERROR) || (rxControlCs == DISCARD_FRAME)))
    fcsEnableRx <= 1'b0;
end


// RX FIFO Interface Controller -> MPDU Status Information
// Frame successful for DMA
assign frmSuccessfulRcved = (fcsOkRcved)           &&
                            (!phyErrorRcved)       &&
                            (!undefErrorRcved)     &&
                            (!rxFIFOOverFlowError) &&
                            (decrStatus != 3'b001) &&
                            (decrStatus != 3'b010)    ;
                            
// End of Encyption Engine procedure
assign decrStatusValid_p = wepTkipPassed_p || wepTkipFailed_p || 
`ifdef RW_WAPI_EN
                           wapiPassed_p    || wapiFailed_p    ||
`endif //RW_WAPI_EN
                           ccmpPassed_p    || ccmpFailed_p;

`ifdef RW_WAPI_EN
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    wapiPassedHold <= 1'b0;
    wapiFailedHold <= 1'b0;
  end
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlCs == IDLE))
  begin
    wapiPassedHold <= 1'b0;
    wapiFailedHold <= 1'b0;
  end
  else if (wapiPassed_p)
    wapiPassedHold <= 1'b1;
  else if (wapiFailed_p)
    wapiFailedHold <= 1'b1;
end

`endif //RW_WAPI_EN
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    decrStatusValidHold <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlCs == IDLE))
    decrStatusValidHold <= 1'b0;
  else if (decrStatusValid_p)
    decrStatusValidHold <= 1'b1;
end

// decrStatus value:
// 3'b000: Frame was not encrypted
// 3'b001: WEP/TKIP ICV failure
// 3'b010: CCMP MIC failure
// 3'b011: A-MSDU Discarded
// 3'b100: Null key found
// 3'b101: WEP decryption successful
// 3'b110: TKIP decryption successful
// 3'b111: CCMP or WAPI decryption successful
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    decrStatus <= 3'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlCs == IDLE))
    decrStatus <= 3'b0;
  else if (!protectedBit)
    // Frame was not encrypted
    decrStatus <= 3'b000;
`ifdef ENCRYPTION
  else if (fcsOkRcved && !undefErrorRcved && (decrStatusValid_p || decrStatusValidHold))
  begin
    if (((sppKSR == 2'b00) || (sppKSR == 2'b11)) && 
        qosDataRcved && rxAMSDUPresent && qosFrame && htcFrame && !qosNullRcved)
      // A-MSDU Discarded
      decrStatus <= 3'b011;
    else if (cTypeKSR == 3'b000)
      // Null key found
      decrStatus <= 3'b100;
    else if (wepTkipFailed_p)
      // WEP/TKIP ICV failure
      decrStatus <= 3'b001;
`ifdef RW_WAPI_EN
    else if (ccmpFailed_p || wapiFailed_p || wapiFailedHold)
`else
    else if (ccmpFailed_p)
`endif //RW_WAPI_EN
      // CCMP or WAPI MIC failure
      decrStatus <= 3'b010;
    else if (wepTkipPassed_p && (cTypeKSR == 3'b001))
      // WEP decryption successful
      decrStatus <= 3'b101;
    else if (wepTkipPassed_p && (cTypeKSR == 3'b010))
      // TKIP decryption successful
      decrStatus <= 3'b110;
`ifdef RW_WAPI_EN
    else if (ccmpPassed_p || wapiPassed_p || wapiPassedHold)
`else
    else if (ccmpPassed_p)
`endif //RW_WAPI_EN
      // CCMP or WAPI decryption successful
      decrStatus <= 3'b111;
  end
`endif
end

// Flag indicating if the frame has to be discarded due to encryption failure.
assign discardDecrypt = (!acceptDecryptErrorFrames && ((decrStatus == 3'b001) || (decrStatus == 3'b010)));


// Status information control
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    fcsOkRcved          <= 1'b0;
    fcsErrorRcved       <= 1'b0;
    phyErrorRcved       <= 1'b0;
    undefErrorRcved     <= 1'b0;
    rxFIFOOverFlowError <= 1'b0;
    statusInfoCheck_p   <= 1'b0;
  end
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlCs == IDLE))
  begin
    fcsOkRcved          <= 1'b0;
    fcsErrorRcved       <= 1'b0;
    phyErrorRcved       <= 1'b0;
    undefErrorRcved     <= 1'b0;
    rxFIFOOverFlowError <= 1'b0;
    statusInfoCheck_p   <= 1'b0;
  end
  else
  begin
    // Status Information pulse
    statusInfoCheck_p <= fcsCheck_p;
    // PHY error status
    if (macPhyIfRxErr_p || rxDataError_p)
      phyErrorRcved <= 1'b1;
    // FIFO overflow status
    if (rxFIFOOverFlow || rxFIFOFull)
      rxFIFOOverFlowError <= 1'b1;
    // FCS status sampling
    if (invalidPkt)
      fcsErrorRcved <= 1'b1;
    else if (fcsCheck_p)
    begin
      fcsOkRcved    <= fcsOk;
      fcsErrorRcved <= !fcsOk;
    end
    // Undefined error status
    if ((statusInfoCheck_p && fcsOkRcved && (protocolError || invalidProtectPktLen)) || 
      macPHYIFOverflow)
      undefErrorRcved <= 1'b1;
  end
end

// RX FIFO Interface Controller -> Payload length in buffers calculation
assign rxByteCntTrig = ((rxControlNs == RX_FRM_BODY)  ||
                        (rxControlNs == RX_BA_CTRL)   ||
                        (rxControlNs == RX_TIMESTAMP) ||
                       ((rxControlNs == RX_ADDR2) && ctrlWrapFlag));

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    payloadLength     <= 16'b0;
    rxByteCntTrig_ff1 <= 1'b0;
  end
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlCs == IDLE))
  begin
    payloadLength     <= 16'b0;
    rxByteCntTrig_ff1 <= 1'b0;
  end
  else 
  begin
    rxByteCntTrig_ff1 <= rxByteCntTrig;
    if (rxByteCntTrig && !rxByteCntTrig_ff1)
      // payloadLength = rxByteCnt
      payloadLength <= rxByteCnt;
  end
end

// payloadBufferLength or rxLengthSub
// Non-encrypted : Payload length - 4 (FCS)
// WEP/TKIP      : Payload length - 4 (ICV) - 4 (FCS)
// CCMP          : Payload length - 8 (MIC) - 4 (FCS)
`ifdef RW_MPDU_AC
assign rxLengthSub         = (invalidProtectPktLen) ? 
                             16'b0 : payloadLengthSub;
`else
assign payloadBufferLength = (invalidProtectPktLen) ? 
                             16'b0 : (payloadLength - payloadLengthSub);
`endif

`ifdef ENCRYPTION
always @*
begin
  if (protectedBit && ((cTypeKSR == 3'b001) || (cTypeKSR == 3'b010)))
    // WEP/TKIP
    payloadLengthSub = 16'h0008;      //ICV 4 + FCS 4 = 8
  else if (protectedBit && (cTypeKSR == 3'b011))
    // CCMP
    payloadLengthSub = 16'h000c;      //MIC 8 + FCS 4 = 12
`ifdef RW_WAPI_EN
  else if (protectedBit && WAPIMode)
    payloadLengthSub = 16'h0014;      //MIC 16 + FCS 4 = 20
`endif // RW_WAPI_EN
  `ifdef RW_MPDU_AC
  else
    // No frame body
    payloadLengthSub = 16'h0004;
  `else
  else if (payloadLength > 16'h0000)
    // Non-encrypted
    payloadLengthSub = 16'h0004;
  else
    // No frame body
    payloadLengthSub = 16'h0000;
  `endif
end
`else
  `ifdef RW_MPDU_AC
  assign payloadLengthSub = 16'h0004;
  `else
  assign payloadLengthSub = (payloadLength > 16'h0000) ? 16'h0004 : 16'h0000;
  `endif
`endif

// RX FIFO Interface Controller -> Quadlet completion
assign frmBody      = (rxControlCs == RX_FRM_BODY) || 
                      (rxControlCs == RX_BA_BITMAP) ||
                      (rxControlCs == RX_ELEMENT_ID) ||
                      (rxControlCs == RX_ELEMENT_LEN) ||
                      (rxControlCs == RX_ELEMENT_BODY);

// RX FIFO Interface Controller -> Tag FIFO
`ifdef RW_MPDU_AC
assign startMacHdr  = (rxControlCs == RX_FRM_CTRL) || (rxControlCs == RX_DUR_ID);
`else
assign startMacHdr  = (rxControlCs == RX_FRM_CTRL);
`endif

assign endPayload   = endHeaderDone &&
                     ((rxControlCs == RX_FCS
`ifdef ENCRYPTION
                      && !rxDataSelect) || (plainOutFCSValid && !encrPadding4BytesFIFOEn
`endif
                       ) || 
                     ((rxControlCs == RX_ERROR) && acceptErrorFrames &&
                      (paddingByteCnt == 4'h3) && macHeaderCntDone));

assign discardFrm   = (rxControlCs == DISCARD_FRAME);

assign acceptError_p = (rxControlCs == RX_ERROR) && (rxControlNs == WRITE_STATUS);

// RX FIFO Interface Controller -> Trailer information
assign writeTrailer = (rxControlCs == WRITE_STATUS) && !rxFIFODone_p;
// The trailer is writen when the FSM is in WRITE_STATUS and when the rxDataEnd has been received.
//assign writeTrailer = (rxControlCs == WRITE_STATUS) && !rxFIFODone_p && rxDataEnd;

// rxDataEnd holded
//always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
//begin
//  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
//    rxDataEnd <= 1'b0;
//  else if ((macCoreClkSoftRst_n == 1'b0) || (rxFIFODone_p == 1'b1))
//    rxDataEnd <= 1'b0;
//  else if (rxDataEnd_p)
//    rxDataEnd <=  1'b1;
//end


// RX FIFO Interface Controller -> Padding control
`ifdef RW_MPDU_AC
always @*
begin
  if ((!acceptRcved && !acceptErrorFrames) || rxFIFOOverFlowError)
  begin
    padding4BytesEn = 1'b0;
    padding2BytesEn = 1'b0;
  end
  `ifdef ENCRYPTION
  else if (rxDataSelect && endHeaderDone)
  begin
    padding4BytesEn = 1'b0;
    padding2BytesEn = 1'b0;
  end
  `endif
  else
  begin
    case(rxControlCs)
    
      IDLE:
      begin
        // Re-initialise signals
        padding4BytesEn = 1'b0;
        padding2BytesEn = 1'b0;
      end

      RX_ADDR1, RX_ADDR2, RX_SEQ_CTRL, RX_ADDR4, RX_QOS_CTRL,RX_HT_CTRL, RX_FRM_BODY, RX_ELEMENT_LEN, RX_ELEMENT_BODY, RX_ELEMENT_ID:
      begin
        // Force 4 bytes padding
        if ( ((rxControlNs == RX_FCS) && !padding4BytesEn_ff1) || ((paddingByteCnt < 4'h3) && padding4BytesEn_ff1) )
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;
      
        // Force 2 bytes padding
        if ((rxControlNs == RX_FCS) && !padding4BytesEn_ff1)
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else
          padding2BytesEn = 1'b0;
      end

      `ifdef ENCRYPTION
      RX_IV_WAPIKEYIDX:
      begin
        padding4BytesEn = 1'b0;
        padding2BytesEn = 1'b0;
      end

      RX_ICV:
      begin
        // Force 4 bytes padding
        if (((stateByteCnt == 8'h03) && rxDataValid) || 
          ((paddingByteCnt == 4'h0) && padding4BytesEn_ff1))
          // Add 2 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        padding2BytesEn = 1'b0;
      end
      `endif

      RX_BA_SEQ_CTRL:
      begin
        // Force 4 bytes padding
        if (barRcved && ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h2) && padding4BytesEn_ff1)))
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        else if (ctrlWrapFlag && ctrlFrame && barRcved &&
          ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h3) && padding4BytesEn_ff1)))
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        if (ctrlWrapFlag && ctrlFrame && barRcved &&
          ((stateByteCnt[0] && rxDataValid)))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else
          padding2BytesEn = 1'b0;
      end

      RX_BA_BITMAP:
      begin
        // Force 4 bytes padding
        if (!ctrlWrapFlag && ctrlFrame && baRcved && 
          ((((stateByteCnt == 8'h7f) || ((stateByteCnt == 8'h07) && compressedBA)) && rxDataValid) ||
          ((paddingByteCnt < 4'h2) && padding4BytesEn_ff1)))
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        else if (ctrlWrapFlag && ctrlFrame && baRcved && 
          ((((stateByteCnt == 8'h7f) || ((stateByteCnt == 8'h07) && compressedBA)) && rxDataValid) ||
          ((paddingByteCnt < 4'h3) && padding4BytesEn_ff1)))
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        if (ctrlWrapFlag && ctrlFrame && baRcved &&
          (((stateByteCnt == 8'h7f) || ((stateByteCnt == 8'h07) &&  compressedBA)) && rxDataValid))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else
          padding2BytesEn = 1'b0;
      end

      RX_ERROR:
      begin
        // Force 4 bytes padding
        if (acceptErrorFrames && !rxNDP)
        begin
          if (!macHeaderCntDone)
            // Add n quadlets according to header counter
            padding4BytesEn = 1'b1;
          else if (!endPayload || ((paddingByteCnt < 4'h3) && padding4BytesEn_ff1))
            // Add 4 quadlets for frame body
            padding4BytesEn = 1'b1;
          else
            padding4BytesEn = 1'b0;
        end
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        padding2BytesEn = 1'b0;
      end

      default:
      begin
        padding4BytesEn = 1'b0;
        padding2BytesEn = 1'b0;
      end
    endcase
  end
end
`else
always @*
begin
  if ((!acceptRcved && !acceptErrorFrames) || rxFIFOOverFlowError)
  begin
    padding4BytesEn = 1'b0;
    padding2BytesEn = 1'b0;
  end
  `ifdef ENCRYPTION
  else if (rxDataSelect && endHeaderDone)
  begin
    padding4BytesEn = 1'b0;
    padding2BytesEn = 1'b0;
  end
  `endif
  else
  begin
    case(rxControlCs)
    
      IDLE:
      begin
        // Re-initialise signals
        padding4BytesEn = 1'b0;
        padding2BytesEn = 1'b0;
      end

      RX_ADDR1:
      begin
        // Force 4 bytes padding
        if (reservedRcved && (rxByteCnt < 5) && (((stateByteCnt == 8'h05) && rxDataValid) ||
           ((paddingByteCnt < 4'hb) && padding4BytesEn_ff1)))
          // Add 12 quadlets
          padding4BytesEn = 1'b1;
        else if (reservedRcved && (((stateByteCnt == 8'h05) && rxDataValid) ||
           ((paddingByteCnt < 4'h8) && padding4BytesEn_ff1)))
          // Add 9 quadlets
          padding4BytesEn = 1'b1;
        else if ((ackRcved || ctsRcved) && (((stateByteCnt == 8'h05) && rxDataValid) ||
          ((paddingByteCnt < 4'hb) && padding4BytesEn_ff1)))
          // Add 12 quadlets
          padding4BytesEn = 1'b1;
        else if (ctrlWrapRcved && (((stateByteCnt == 8'h05) && rxDataValid) || 
          ((paddingByteCnt < 4'h4) && padding4BytesEn_ff1)))
          // Add 5 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        if (ctrlWrapRcved && (paddingByteCnt == 4'h4))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else
          padding2BytesEn = 1'b0;
      end

      RX_ADDR2:
      begin
        // Force 4 bytes padding
        if (ctrlWrapFlag && !(baRcved || barRcved) && 
          (((stateByteCnt == 8'h05) && rxDataValid) ||
          ((paddingByteCnt < 4'h3) && (paddingByteCnt != 4'h0) && padding4BytesEn_ff1)))
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        else if (!ctrlWrapFlag && ctrlFrame && (baRcved || barRcved) &&
          (((stateByteCnt == 8'h05) && rxDataValid) ||
          ((paddingByteCnt < 4'h7) && (paddingByteCnt != 4'h0) && padding4BytesEn_ff1)))
          // Add 7 quadlets
          padding4BytesEn = 1'b1;
        else if (!ctrlWrapFlag && ctrlFrame  && !(baRcved || barRcved) &&
          (((stateByteCnt == 8'h05) && rxDataValid) ||
          ((paddingByteCnt < 4'ha) && (paddingByteCnt != 4'h0) && padding4BytesEn_ff1)))
          // Add 10 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        if (ctrlFrame && (!ctrlWrapFlag || (ctrlWrapFlag && !(baRcved || barRcved))) &&
          (((stateByteCnt == 8'h05) && rxDataValid)))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else
          padding2BytesEn = 1'b0;
      end

      RX_SEQ_CTRL:
      begin
        // Force 4 bytes padding
        if ((rxByteCnt < 16'h0004) && ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h8) && (paddingByteCnt != 4'h0) && padding4BytesEn_ff1)))
          // Add 8 quadlets
          padding4BytesEn = 1'b1;
        else if ((rxByteCnt <= 16'h000c) && protectedBit && !qosFrame && 
          ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h5) && (paddingByteCnt != 4'h0) && padding4BytesEn_ff1)))
          // Add 5 quadlets
          padding4BytesEn = 1'b1;
        else if ((bcnRcved || probRespRcved) && !htcFrame &&
          ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h5) && (paddingByteCnt != 4'h0) && padding4BytesEn_ff1)))

          // Add 5 quadlets
          padding4BytesEn = 1'b1;
        `ifdef ENCRYPTION
        else if (protectedBit && !qosFrame && !(dataFrame && toDS && fromDS) && !htcFrame &&
          ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h3) && (paddingByteCnt != 4'h0) && padding4BytesEn_ff1)))

          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        `endif
        else if (!protectedBit && !qosFrame && !htcFrame && !(dataFrame && toDS && fromDS) && 
          ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h5) && (paddingByteCnt != 4'h0) && padding4BytesEn_ff1)))
          // Add 5 quadlets
          padding4BytesEn = 1'b1;
        else if (!qosFrame && !(dataFrame && toDS && fromDS) && 
          ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h2) && (paddingByteCnt != 4'h0) && padding4BytesEn_ff1)))
          // Add 2 quadlets
          padding4BytesEn = 1'b1;
        else if (qosFrame && !(dataFrame && toDS && fromDS) && ((stateByteCnt[0] && rxDataValid)))
          // Add 1 quadlet
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        if ((rxByteCnt <= 16'h0004) && ((stateByteCnt[0] && rxDataValid)))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else if ((rxByteCnt <= 16'h000c) && protectedBit && !qosFrame && 
          ((stateByteCnt[0] && rxDataValid)))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else if (!(dataFrame && toDS && fromDS) &&
          ((stateByteCnt[0] && rxDataValid)))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else
          padding2BytesEn = 1'b0;
      end

      RX_ADDR4:
      begin
        // Force 4 bytes padding
        if ((rxByteCnt < 16'h0004) && 
          (((stateByteCnt == 8'h05) && rxDataValid) ||
          ((paddingByteCnt < 4'h6) && padding4BytesEn_ff1)))
          // Add 7 quadlets
          padding4BytesEn = 1'b1;
        else if ((rxByteCnt <= 16'h000c) && protectedBit && !qosFrame && 
          (((stateByteCnt == 8'h05) && rxDataValid) ||
          ((paddingByteCnt < 4'h3) && padding4BytesEn_ff1)))
          // Add 4 quadlets
          padding4BytesEn = 1'b1;
        `ifdef ENCRYPTION
        else if (protectedBit && !qosFrame && 
          (((stateByteCnt == 8'h05) && rxDataValid) ||
          ((paddingByteCnt == 4'h0) && padding4BytesEn_ff1)))
          // Add 2 quadlets
          padding4BytesEn = 1'b1;
        `endif
        else if (!protectedBit && !qosFrame && (((stateByteCnt == 8'h05) && rxDataValid) ||
          ((paddingByteCnt < 4'h3) && padding4BytesEn_ff1)))
          // Add 4 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        padding2BytesEn = 1'b0;
      end

      RX_QOS_CTRL:
      begin
        // Force 4 bytes padding
        if ((rxByteCnt < 16'h0004) && ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h6) && (paddingByteCnt != 4'h0) && padding4BytesEn_ff1)))
          // Add 6 quadlets
          padding4BytesEn = 1'b1;
        else if ((rxByteCnt <= 16'h000c) && protectedBit && !htcFrame && 
          ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h3) && (paddingByteCnt != 4'h0) && padding4BytesEn_ff1)))
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        `ifdef ENCRYPTION
        else if (protectedBit && !htcFrame && stateByteCnt[0] && rxDataValid)
          // Add 1 quadlet
          padding4BytesEn = 1'b1;
        `endif
        else if (!protectedBit && !htcFrame && ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h3) && (paddingByteCnt != 4'h0) && padding4BytesEn_ff1)))
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        if ((rxByteCnt <= 16'h0004) && ((stateByteCnt[0] && rxDataValid)))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else if ((rxByteCnt <= 16'h000c) && protectedBit && !htcFrame && 
          ((stateByteCnt[0] && rxDataValid)))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else if (!htcFrame && ((stateByteCnt[0] && rxDataValid)))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else if (htcFrame && ((stateByteCnt[0] && rxDataValid)))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else
          padding2BytesEn = 1'b0;
      end

      RX_HT_CTRL:
      begin
        // Force 4 bytes padding
        if ((((rxByteCnt < 16'h0004)) || (ctrlWrapFlag && (ackRcved || ctsRcved))) && 
          (((stateByteCnt == 8'h03) && rxDataValid) ||
          ((paddingByteCnt < 4'h4) && padding4BytesEn_ff1)))
          // Add 5 quadlets
          padding4BytesEn = 1'b1;
        else if ((rxByteCnt <= 16'h000d) && protectedBit && 
          (((stateByteCnt == 8'h03) && rxDataValid) ||
          ((paddingByteCnt == 4'h0) && padding4BytesEn_ff1)))
          // Add 2 quadlets
          padding4BytesEn = 1'b1;
        else if ((bcnRcved || probRespRcved) && (((stateByteCnt == 8'h03) && rxDataValid) ||
          ((paddingByteCnt == 4'h0) && padding4BytesEn_ff1)))
          // Add 2 quadlets
          padding4BytesEn = 1'b1;
        else if (!protectedBit && (((stateByteCnt == 8'h03) && rxDataValid) ||
          ((paddingByteCnt == 4'h0) && padding4BytesEn_ff1)))
          // Add 2 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        padding2BytesEn = 1'b0;
      end

      `ifdef ENCRYPTION
      RX_IV_WAPIKEYIDX:
      begin
        // Force 4 bytes padding
        if ((((rxByteCnt <= 16'h000c) && rxData[5]) || !rxData[5]) && 
          (stateByteCnt == 8'h03) && rxDataValid)
          // Add 1 quadlet
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        padding2BytesEn = 1'b0;
      end
      `endif

      RX_FRM_BODY, RX_ELEMENT_LEN, RX_ELEMENT_BODY, RX_ELEMENT_ID:
      begin
        // Force 4 bytes padding
        if ((rxByteCnt <= 16'h0004) && (rxDataValid || 
          ((paddingByteCnt < 4'h3) && padding4BytesEn_ff1)))
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;
      
        // Force 2 bytes padding
        if ((rxByteCnt == 16'h0004) && rxDataValid)
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else
          padding2BytesEn = 1'b0;
      end

      `ifdef ENCRYPTION
      RX_ICV:
      begin
        // Force 4 bytes padding
        if (((stateByteCnt == 8'h03) && rxDataValid) || 
          ((paddingByteCnt == 4'h0) && padding4BytesEn_ff1))
          // Add 2 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        padding2BytesEn = 1'b0;
      end
      `endif

      RX_BA_SEQ_CTRL:
      begin
        // Force 4 bytes padding
        if (barRcved && ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h2) && padding4BytesEn_ff1)))
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        else if (ctrlWrapFlag && ctrlFrame && barRcved &&
          ((stateByteCnt[0] && rxDataValid) ||
          ((paddingByteCnt < 4'h3) && padding4BytesEn_ff1)))
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        if (ctrlWrapFlag && ctrlFrame && barRcved &&
          ((stateByteCnt[0] && rxDataValid)))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else
          padding2BytesEn = 1'b0;
      end

      RX_BA_BITMAP:
      begin
        // Force 4 bytes padding
        if (!ctrlWrapFlag && ctrlFrame && baRcved && 
          ((((stateByteCnt == 8'h7f) || ((stateByteCnt == 8'h07) && compressedBA)) && rxDataValid) ||
          ((paddingByteCnt < 4'h2) && padding4BytesEn_ff1)))
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        else if (ctrlWrapFlag && ctrlFrame && baRcved && 
          ((((stateByteCnt == 8'h7f) || ((stateByteCnt == 8'h07) && compressedBA)) && rxDataValid) ||
          ((paddingByteCnt < 4'h3) && padding4BytesEn_ff1)))
          // Add 3 quadlets
          padding4BytesEn = 1'b1;
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        if (ctrlWrapFlag && ctrlFrame && baRcved &&
          (((stateByteCnt == 8'h7f) || ((stateByteCnt == 8'h07) &&  compressedBA)) && rxDataValid))
          // Complete quadlet
          padding2BytesEn = 1'b1;
        else
          padding2BytesEn = 1'b0;
      end

      RX_ERROR:
      begin
        // Force 4 bytes padding
        if (acceptErrorFrames && !rxNDP)
        begin
          if (!macHeaderCntDone)
            // Add n quadlets according to header counter
            padding4BytesEn = 1'b1;
          else if (!endPayload || ((paddingByteCnt < 4'h3) && padding4BytesEn_ff1))
            // Add 4 quadlets for frame body
            padding4BytesEn = 1'b1;
          else
            padding4BytesEn = 1'b0;
        end
        else
          padding4BytesEn = 1'b0;

        // Force 2 bytes padding
        padding2BytesEn = 1'b0;
      end

      default:
      begin
        padding4BytesEn = 1'b0;
        padding2BytesEn = 1'b0;
      end
    endcase
  end
end
`endif


// RX FIFO Interface Controller -> Padding counter control
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    paddingByteCnt <= 4'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    paddingByteCnt <= 4'b0;
  else if ((rxControlCs == IDLE) || (!padding4BytesEn) ||
    ((rxControlCs == RX_ERROR) && !macHeaderCntDone && 
    (((macHeaderCnt == 4'ha) && rxFIFOWrite))))
    paddingByteCnt <= 4'b0;
  else if ((padding4BytesEn_ff1 || padding2BytesEn) && (paddingByteCnt < 4'hf))
    paddingByteCnt <= paddingByteCnt + 4'd1;
end

// RX FIFO Interface Controller -> macHeaderCntDone
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macHeaderCntDone <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlCs == IDLE))
    macHeaderCntDone <= 1'b0;
  else if ((macHeaderCnt == 4'hb) && rxFIFOWrite)
    macHeaderCntDone <= 1'b1;
end

// Padding outputs to RX FIFO Interface Controller
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    padding4BytesEn_ff1 <= 1'b0;
    padding4BytesEn_ff2 <= 1'b0;
  end
  else if ((macCoreClkSoftRst_n == 1'b0) || (discardFrm == 1'b1))
  begin
    padding4BytesEn_ff1 <= 1'b0;
    padding4BytesEn_ff2 <= 1'b0;
  end
  else
  begin
    padding4BytesEn_ff2 <= padding4BytesEn_ff1;
    padding4BytesEn_ff1 <= padding4BytesEn;
  end
end

assign padding4BytesFIFOEn  = padding4BytesEn_ff1 && (acceptRcved || acceptErrorFrames);
assign padding4BytesWriteEn = padding4BytesEn_ff2 && (acceptRcved || acceptErrorFrames);
assign padding2BytesFIFOEn  = padding2BytesEn && (acceptRcved || acceptErrorFrames);

// rxCntrlReady control
assign rxCntrlReady = !(padding4BytesEn || 
                       (rxControlCs == WRITE_STATUS)      ||
                       ((rxControlCs == RX_FCS) && (rxFrmDiscard == 1'b0) && (rxDescAvailable == 1'b0)) ||
`ifdef ENCRYPTION
                       (rxControlCs == CHECK_ENCR) ||
                       // WAPI specific header request to wait to know the ctype before receiving data of IV/KEYIDX field
                       ((rxControlCs == RX_IV_WAPIKEYIDX) && protectedBit && !rxIndexSearchDone) || 
`endif
                       (rxControlCs == RX_ERROR) ||
                       fcsCheck_p || rxDataEnd_p || discardFrm);

// Local frame status based on FCS only
assign localCorrectRcved_p   = fcsCheck_p && fcsOk;
assign localIncorrectRcved_p = fcsCheck_p && !fcsOk;

// MAC pulse control according to local frame status and error cases
assign correctRcved_p        = localCorrectRcved_p && !rxFIFOOverFlowError && !respError;
assign incorrectRcved_p      = (fcsCheck_p && (!fcsOk || rxFIFOOverFlowError || respError || invalidPkt)) ||
                               (rxControlCs == RX_ERROR);

// In case of non-expected response, the flag respError is set. It will generate an incorrectRcved_p
// If a CTS is expected and the frame received if not a CTS or
// If a ACK/BA is expected and the frame received if not a BA or
// If an ACK/BA is expected and the frame received if not an ACK or
// a CTS, BA or ACK is expected and the frame received is part of AMPDU
assign respError = ((rxCts && !ctsRcved) ||
                    (rxAck && !(baRcved || ackRcved)) ||
                    ((rxCts || rxAck) && rxAggregation)) ? 1'b1 : 1'b0;


// NAV pulse control
assign navClear_p            = localCorrectRcved_p && cfEndRcved && !protocolError;
assign navUpdate_p           = localCorrectRcved_p && !addr1Match &&
                               !protocolError && !bcMcRcved &&
                               !cfpParameterFound;
assign navCfpDurRemUpdate_p  = tsfUpdate_p && cfpParameterFound && !bcMcRcved;
assign navLsigUpdate_p       = ((localIncorrectRcved_p && !rxAggregation) || ampduIncorrectRcved_p) && 
                               rxLSIGValid && (rxFormatMod == 3'b010) && lSIGTXOPDetected;


// MAC Timer unit pulse control
assign dtimUpdate_p = tsfUpdate_p && dtimParameterFound && bssType && !ap;
assign cfpUpdate_p  = tsfUpdate_p && cfpParameterFound && bssType && !ap;

// If the TSF Management is disabled, the tsfUpdated_p is not generated.
assign tsfUpdate_p  = !tsfMgtDisable && localCorrectRcved_p && bssIDMatch && !protocolError &&
                     (bcnRcved || (probRespRcved && addr1Match));
            

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    tsfOffsetUpdate_p <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    tsfOffsetUpdate_p <= 1'b0;
  else if ((rxControlCs == RX_TIMESTAMP) && (stateByteCnt == 8'h07) && rxDataValid)
    tsfOffsetUpdate_p <= 1'b1;
  else 
    tsfOffsetUpdate_p <= 1'b0;
end

// Last received packet status for EIFS calculation
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    lastRxWrong <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    lastRxWrong <= 1'b0;
  else if (fcsOkRcved)
    lastRxWrong <= 1'b0;
  else if (mpIfTxEn || backOffDone_p || rxDataStart_p)
    lastRxWrong <= 1'b0;
  else if ((rxControlCs == RX_ERROR) || fcsErrorRcved || macPhyIfRxErr_p)
    lastRxWrong <= 1'b1;
end


// Control and Status Register pulse control
assign quietElement1InValid  = tsfUpdate_p && quietParameterFound && 
                               !quietParameterToggle;
assign quietElement2InValid  = tsfUpdate_p && quietParameterFound && 
                               quietParameterToggle;
assign dtimPeriodInValid     = dtimUpdate_p && (currentState == ACTIVE_STATE);
assign cfpPeriodInValid      = cfpUpdate_p && (currentState == ACTIVE_STATE);


// BA Controller control
assign psBitmapUpdate_p  = correctRcved_p && (barRcved || qosFrame) && (!qosNullRcved) &&
                           addr1Match && !protocolError;
assign psBitmapDiscard_p = incorrectRcved_p ||
                          (!protocolError && correctRcved_p &&
                         ((!(barRcved || qosFrame) || !addr1Match)));
assign baEnable          = fcsEnableRx;


// Interrupt Controller trigger
// assign baRxTrigger = baRcved && addr1Match && correctRcved_p && !protocolError;

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    baRxTrigger <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    baRxTrigger <= 1'b0;
  else
    baRxTrigger <= baRcved && addr1Match && correctRcved_p && !protocolError && acceptRcved;
end


// Decryption FSM control
assign rxControlToFrmBody_p = (rxControlNs == RX_FRM_BODY) && (rxControlCs != RX_FRM_BODY);
assign rxControlToError_p   = ((rxControlNs == RX_ERROR) && (rxControlCs != RX_ERROR)) ||
                              ((rxControlNs == DISCARD_FRAME) && (rxControlCs != DISCARD_FRAME));

assign acceptProtected      = acceptRcved && protectedBit && !dontDecrypt;


// Encryption Engine control
assign rxPayLoadLen         = payloadLength[15:0];


//assign rxCCMPAADwrEn_p      = ((rxControlCs == RX_FRM_CTRL) ||
//                               (rxControlCs == RX_ADDR3)    ||
//                               (rxControlCs == RX_ADDR4)    ||
//                               (rxControlCs == RX_SEQ_CTRL)) && rxDataValid;

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxCCMPAADwrEn_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    rxCCMPAADwrEn_p <= 1'b0;
  else if ((rxControlCs == RX_FRM_CTRL) ||
           (rxControlCs == RX_ADDR3)    ||
           (rxControlCs == RX_ADDR4)    ||
           (rxControlCs == RX_SEQ_CTRL))
    rxCCMPAADwrEn_p <= rxDataValid;
  else  
    rxCCMPAADwrEn_p <= 1'b0;
end

///////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
///////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////
// Display FSM State in string for RTL simulation waveform
//////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
// rxControlCs FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (rxControlCs)
               IDLE  :  rxControlCs_str = {"IDLE"};
        RX_FRM_CTRL  :  rxControlCs_str = {"RX_FRM_CTRL"};
          RX_DUR_ID  :  rxControlCs_str = {"RX_DUR_ID"};
           RX_ADDR1  :  rxControlCs_str = {"RX_ADDR1"};
           RX_ADDR2  :  rxControlCs_str = {"RX_ADDR2"};
           RX_ADDR3  :  rxControlCs_str = {"RX_ADDR3"};
           RX_ADDR4  :  rxControlCs_str = {"RX_ADDR4"};
        RX_SEQ_CTRL  :  rxControlCs_str = {"RX_SEQ_CTRL"};
        RX_QOS_CTRL  :  rxControlCs_str = {"RX_QOS_CTRL"};
    RX_CAR_FRM_CTRL  :  rxControlCs_str = {"RX_CAR_FRM_CTRL"};
         RX_HT_CTRL  :  rxControlCs_str = {"RX_HT_CTRL"};
   RX_IV_WAPIKEYIDX  :  rxControlCs_str = {"RX_IV_WAPIKEYIDX"};
    RX_EXTIV_WAPIPN  :  rxControlCs_str = {"RX_EXTIV_WAPIPN"};
        RX_FRM_BODY  :  rxControlCs_str = {"RX_FRM_BODY"};
             RX_ICV  :  rxControlCs_str = {"RX_ICV"};
   RX_CCMP_WAPI_MIC  :  rxControlCs_str = {"RX_CCMP_WAPI_MIC"};
             RX_FCS  :  rxControlCs_str = {"RX_FCS"};
         RX_BA_CTRL  :  rxControlCs_str = {"RX_BA_CTRL"};
     RX_BA_SEQ_CTRL  :  rxControlCs_str = {"RX_BA_SEQ_CTRL"};
       RX_BA_BITMAP  :  rxControlCs_str = {"RX_BA_BITMAP"};
       RX_TIMESTAMP  :  rxControlCs_str = {"RX_TIMESTAMP"};
      RX_BCN_INTRVL  :  rxControlCs_str = {"RX_BCN_INTRVL"};
      RX_CAPABILITY  :  rxControlCs_str = {"RX_CAPABILITY"};
      RX_ELEMENT_ID  :  rxControlCs_str = {"RX_ELEMENT_ID"};
     RX_ELEMENT_LEN  :  rxControlCs_str = {"RX_ELEMENT_LEN"};
    RX_ELEMENT_BODY  :  rxControlCs_str = {"RX_ELEMENT_BODY"};
          CHECK_FCS  :  rxControlCs_str = {"CHECK_FCS"};
         CHECK_ENCR  :  rxControlCs_str = {"CHECK_ENCR"};
       WRITE_STATUS  :  rxControlCs_str = {"WRITE_STATUS"};
           RX_ERROR  :  rxControlCs_str = {"RX_ERROR"};
      DISCARD_FRAME  :  rxControlCs_str = {"DISCARD_FRAME"};
 WAIT_KEYSEARCHDONE  :  rxControlCs_str = {"WAIT_KEYSEARCHDONE"};
            default  :  rxControlCs_str = {"XXX"};
   endcase
end

// rxControlNs FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (rxControlNs)
               IDLE  :  rxControlNs_str = {"IDLE"};
        RX_FRM_CTRL  :  rxControlNs_str = {"RX_FRM_CTRL"};
          RX_DUR_ID  :  rxControlNs_str = {"RX_DUR_ID"};
           RX_ADDR1  :  rxControlNs_str = {"RX_ADDR1"};
           RX_ADDR2  :  rxControlNs_str = {"RX_ADDR2"};
           RX_ADDR3  :  rxControlNs_str = {"RX_ADDR3"};
           RX_ADDR4  :  rxControlNs_str = {"RX_ADDR4"};
        RX_SEQ_CTRL  :  rxControlNs_str = {"RX_SEQ_CTRL"};
        RX_QOS_CTRL  :  rxControlNs_str = {"RX_QOS_CTRL"};
    RX_CAR_FRM_CTRL  :  rxControlNs_str = {"RX_CAR_FRM_CTRL"};
         RX_HT_CTRL  :  rxControlNs_str = {"RX_HT_CTRL"};
   RX_IV_WAPIKEYIDX  :  rxControlNs_str = {"RX_IV_WAPIKEYIDX"};
    RX_EXTIV_WAPIPN  :  rxControlNs_str = {"RX_EXTIV_WAPIPN"};
        RX_FRM_BODY  :  rxControlNs_str = {"RX_FRM_BODY"};
             RX_ICV  :  rxControlNs_str = {"RX_ICV"};
   RX_CCMP_WAPI_MIC  :  rxControlNs_str = {"RX_CCMP_WAPI_MIC"};
             RX_FCS  :  rxControlNs_str = {"RX_FCS"};
         RX_BA_CTRL  :  rxControlNs_str = {"RX_BA_CTRL"};
     RX_BA_SEQ_CTRL  :  rxControlNs_str = {"RX_BA_SEQ_CTRL"};
       RX_BA_BITMAP  :  rxControlNs_str = {"RX_BA_BITMAP"};
       RX_TIMESTAMP  :  rxControlNs_str = {"RX_TIMESTAMP"};
      RX_BCN_INTRVL  :  rxControlNs_str = {"RX_BCN_INTRVL"};
      RX_CAPABILITY  :  rxControlNs_str = {"RX_CAPABILITY"};
      RX_ELEMENT_ID  :  rxControlNs_str = {"RX_ELEMENT_ID"};
     RX_ELEMENT_LEN  :  rxControlNs_str = {"RX_ELEMENT_LEN"};
    RX_ELEMENT_BODY  :  rxControlNs_str = {"RX_ELEMENT_BODY"};
          CHECK_FCS  :  rxControlNs_str = {"CHECK_FCS"};
         CHECK_ENCR  :  rxControlNs_str = {"CHECK_ENCR"};
       WRITE_STATUS  :  rxControlNs_str = {"WRITE_STATUS"};
           RX_ERROR  :  rxControlNs_str = {"RX_ERROR"};
      DISCARD_FRAME  :  rxControlNs_str = {"DISCARD_FRAME"};
 WAIT_KEYSEARCHDONE  :  rxControlNs_str = {"WAIT_KEYSEARCHDONE"};
            default  :  rxControlNs_str = {"XXX"};
   endcase
end
`endif // RW_SIMU_ON

endmodule