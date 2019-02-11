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
// Description      : Frame decoder of rxController module
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


module frameDecoder( 
            ///////////////////////////////////////////////
            //$port_g Clock and reset
            ///////////////////////////////////////////////
            input wire         macCoreRxClk,            // MAC Core Receive Clock
            input wire         macCoreClkHardRst_n,     // Hard Reset of the MAC Core Clock domain 
                                                        // active low
            input wire         macCoreClkSoftRst_n,     // Soft Reset of the MAC Core Clock domain
                                                        // active low
            ///////////////////////////////////////////////
            //$port_g MAC Controller
            ///////////////////////////////////////////////
            input wire         activeRx,                // Current state Master is active Rx and Rx FSM is not IDLE
            input wire         rxAck,                   // Force receive only ACK after Tx
            input wire         rxCts,                   // Force receive only CTS after RTS Tx
            
            output wire        ackRcved_p,              // ACK received pulse
            output wire        rtsRcved_p,              // RTS received pulse
            output wire        ctsRcved_p,              // CTS received pulse
            output wire        cfEndRcved_p,            // CF-End received pulse
            output wire        baRcved_p,               // BA received pulse
            output wire        barRcved_p,              // BAR received pulse
            output wire        needAckRcved_p,          // Data or management received with ACK needed pulse
            output wire        bcMcRcved_p,             // Broadcast/Multicast received pulse
            output wire        bcnRcved_p,              // Beacon received pulse
            output wire        probRespRcved_p,         // Probe response received pulse
            output wire        notMineRcved_p,          // Frame received but not mine pulse
            output wire        unknownRcved_p,          // Unknown frame received pulse
            output wire        notMinePsPollRcved_p,    // PS-Poll received but not mine pulse
            output wire        notMineRtsRcved_p,       // RTS received but not mine pulse
            
            output reg [47:0]  rxAddr2,                 // Addr2

            output wire        notMineRcved,            // Frame received but not mine

            ///////////////////////////////////////////////
            //$port_g NAV
            ///////////////////////////////////////////////
            output reg [15:0]  rxFrameDuration,         // Frame duration
            output reg [15:0]  cfpDurRemaining,         // CFP duration remaining

            ///////////////////////////////////////////////
            //$port_g MAC Timer unit
            ///////////////////////////////////////////////
            output reg [7:0]   dtimCnt,                 // DTIM counter
            output reg [7:0]   cfpCnt,                  // CFP counter
            output reg [63:0]  timeStamp,               // TSF value
            output wire        olbcUpdate_p,            // Update OLBC counter

            ///////////////////////////////////////////////
            //$port_g Encryption Engine
            ///////////////////////////////////////////////
`ifdef RW_WAPI_EN
            output reg [15:0]  rxFrmCtrl,               // Frame control field
            output reg [47:0]  rxAddr3,                 // Address 3 field
            output reg [47:0]  rxAddr4,                 // Address 4 field
            output reg [15:0]  rxQoSControl,            // QoS control field
            output reg [7:0]   rxWAPIKeyIndex,          // WAPI key index field
            output reg [127:0] rxWAPIPN,                // WAPI packet number(PN) field
`endif //RW_WAPI_EN
            output reg  [47:0] rxAddr1,                 // Addr1
            output wire [23:0] rxInitVector,            // IV
            output reg  [31:0] rxExtInitVector,         // Extended IV

            ///////////////////////////////////////////////
            //$port_g Decryption FSM
            ///////////////////////////////////////////////
            output wire        myFrameRcvedTrig_p,      // my Frame pulse trigger for KSR
            output wire  [1:0] rxDefKeyID,              // Default Key ID

            ///////////////////////////////////////////////
            //$port_g RX Controller FSM
            ///////////////////////////////////////////////
            input wire         rxFrmCtrlEn,             // Frame control field
            input wire         rxDurationIdEn,          // Duration / ID field
            input wire         rxAddr1En,               // ADDR1 field
            input wire         rxAddr2En,               // ADDR2 field
            input wire         rxAddr3En,               // ADDR3 field
`ifdef RW_WAPI_EN
            input wire         rxAddr4En,               // ADDR4 field
            input wire         rxWAPIKeyIdxEn,          // WAPI KeyIdx field
            input wire         rxWAPIPNEn,              // WAPI PN field
`endif //RW_WAPI_EN
            input wire         rxQoSCtrlEn,             // QoS control field
            input wire         rxHTCtrlEn,              // HT control field
            input wire         rxSeqCtrlEn,             // Sequence control field
            input wire         rxBACtrlEn,              // BA control field
            input wire         rxBASeqCtrlEn,           // BA Sequence control field
            input wire         rxInitVectorEn,          // IV field
            input wire         rxExtInitVectorEn,       // Extended IV field
            
            input wire         rxDtimCntEn,             // DTIM counter field
            input wire         rxDtimPeriodEn,          // DTIM period field
            input wire         rxCfpCntEn,              // CFP counter field
            input wire         rxCfpPeriodEn,           // CFP period field
            input wire         rxCfpDurRemainingEn,     // CFP Duration remaining field
            input wire         rxTimeStampEn,           // Timestamp field
            
            input wire         rxQuietCount1En,         // Quiet Count 1 field
            input wire         rxQuietPeriod1En,        // Quiet Period 1 field
            input wire         rxQuietDuration1En,      // Quiet Duration 1 field
            input wire         rxQuietOffset1En,        // Quiet Offset 1 field
            input wire         rxQuietCount2En,         // Quiet Count 2 field
            input wire         rxQuietPeriod2En,        // Quiet Period 2 field
            input wire         rxQuietDuration2En,      // Quiet Duration 2 field
            input wire         rxQuietOffset2En,        // Quiet Offset 2 field

            input wire [7:0]   stateByteCnt,            // Byte counter by states

`ifdef RW_WAPI_EN
            input wire         rxAddr4End_p,            // FSM ADDR4 pulse
            input wire         rxWAPIKeyIdxEnd_p,       // FSM WAPI KeyIdx pulse
            input wire         rxWAPIPNEnd_p,           // FSM WAPI PN pulse
`endif //RW_WAPI_EN
            input wire         fcsCheck_p,              // FSM FCS check
            input wire         rxDurationIdEnd_p,       // FSM Duration / ID end pulse
            input wire         rxAddr1End_p,            // FSM ADDR1 end pulse
            input wire         rxAddr2End_p,            // FSM ADDR2 end pulse
            input wire         carFrameCtrlEnd_p,       // FSM Carried frame control end pulse
            input wire         rxAddr3End_p,            // FSM ADDR3 end pulse
            input wire         rxSeqCtrlEnd_p,          // FSM Sequence Control end pulse
            input wire         rxQoSEnd_p,              // FSM QoS end pulse
            input wire         rxBARCtrlEnd_p,          // FSM BAR control end pulse
            
            input wire         rxControlIdle,           // FSM in idle
            
            output wire        mgmtNoEncryptFrame,      // Flag for management encrypt allowed frame
            output wire        mgmtFrame,               // Management frame
            output wire        ctrlFrame,               // Control frame
            output wire        dataFrame,               // Data frame
            output wire        qosFrame,                // QoS frame
            output wire        htcFrame,                // HT or VHT frame with HTC field

            output wire        bcMcRcved,               // Broadcast/Multicast
            
            output wire        bcnRcved,                // Beacon
            output wire        probRespRcved,           // Probe response
            
            output wire        ctrlWrapRcved,           // Control Wrapper
            output wire        baRcved,                 // BA
            output wire        barRcved,                // BAR
            output wire        psPollRcved,             // PS-Poll
            output wire        rtsRcved,                // RTS
            output wire        ctsRcved,                // CTS
            output wire        ackRcved,                // ACK
            output wire        cfEndRcved,              // CF-End
            
            output reg         ctrlWrapFlag,            // Control Wrapper flag
            
            output wire        dataRcved,               // Data
            output wire        qosDataRcved,            // QoS Data
            output wire        qosNullRcved,            // QoS null

            output wire        reservedRcved,           // Reserved

            output wire        toDS,                    // To DS
            output wire        fromDS,                  // From DS
            output wire        rxMoreFrag,              // More fragment
            output wire        rxRetry,                 // Retry
            output wire        pwrMgt,                  // Power management
            output wire        rxMoreData,              // More data
            output wire        protectedBit,            // Protected bit
            output wire        rxOrder,                 // Order

            output wire        rxAMSDUPresent,          // A-MSDU Present
            output wire [1:0]  rxAckPolicy,             // Ack policy (Ack, No Ack, BA)
            output wire [3:0]  rxTID,                   // TID

            output wire        rxBWSignalingTA,         // Indicate that the received frame has a Bandwidth Signaling TA
            
            output reg [31:0]  rxHTCtrl,                // HT control

            output wire        compressedBA,            // Compressed BA

            output reg         acceptRcved,             // Accept current frame
            
            output reg         addr1Match,              // ADDR1 match
            output reg         bssIDMatch,              // BSSID match
            
            ///////////////////////////////////////////////
            //$port_g BA Controller
            ///////////////////////////////////////////////
            output reg [15:0]  rxSeqCtrl,               // Sequence control
            output reg [11:0]  rxBASSN,                 // BA Starting Sequence Number

            ///////////////////////////////////////////////
            //$port_g A-MPDU Deaggregator
            ///////////////////////////////////////////////
            input wire [ 2:0]  rxFormatMod,             // Format and modulation
            
            input wire [ 7:0]  rxData,                  // Rx data read from MAC-PHY interface FIFO
            input wire         rxDataValid,             // Rx data is valid
            
            ///////////////////////////////////////////////
            //$port_g Control and Status Register
            ///////////////////////////////////////////////
            input wire [47:0]  macAddr,                 // MAC Addr
            input wire [47:0]  macAddrMask,             // MAC Addr mask
            
            input wire [47:0]  bssID,                   // BSSID
            input wire [47:0]  bssIDMask,               // BSSID Mask
            
            input wire         excUnencrypted,          // Exclude unencrypted frames
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
            input wire         acceptOtherMgmtFrames,   // Accept other management frames
            input wire         acceptNotExpectedBA,     // Accept Block Ack Request frames received after SIFS
            input wire         acceptBAR,               // Accept Block Ack Request frames
            input wire         acceptBA,                // Accept Block Ack frames
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
            
            output reg [7:0]   quietCount1In,           // Quiet Count 1
            output reg [7:0]   quietPeriod1In,          // Quiet Period 1
            output reg [15:0]  quietDuration1In,        // Quiet Duration 1
            output reg [15:0]  quietOffset1In,          // Quiet Offset 1
            output reg [7:0]   quietCount2In,           // Quiet Count 2
            output reg [7:0]   quietPeriod2In,          // Quiet Period 2
            output reg [15:0]  quietDuration2In,        // Quiet Duration 2
            output reg [15:0]  quietOffset2In,          // Quiet Offset 2
            
            output reg [7:0]   dtimPeriodIn,            // DTIM period
            output reg [7:0]   cfpPeriodIn,             // CFP period

            input wire         dynBWEn,                 // Enable the Dynamic Bandwidth
            ///////////////////////////////////////////////
            //$port_g RX FIFO Interface Controller
            ///////////////////////////////////////////////
            input  wire        rxBADly,                 // Capture of the rxBA
            output wire [3:0]  subTypeFrame,            // Subtype
            output wire [1:0]  typeFrame,               // Type
            output wire        protocolError            // Protocol version
            );


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
reg         broadCastRcved;   // Broadcast frame
reg         multiCastRcved;   // Multicast frame
reg         ctrlWrapError;    // Control wrapper error
reg         bssIDFrame;       // Frame contains BSSID field
reg  [15:0] rxBACtrl;         // BA control field
wire [47:0] macAddrMasked;    // MAC Addr masked
wire [47:0] bssIDMasked;      // BSSID masked
`ifndef RW_WAPI_EN
reg  [15:0] rxFrmCtrl;        // Frame control field
reg  [15:0] rxQoSControl;          // QoS control field
reg  [47:0] rxAddr3;          // Addr3 for BSSID check
`endif
reg  [31:0] rxInitVectorFull; // IV field

wire probReqRcved;            // Probe request
wire actNoAckRcved;           // Action no Ack
wire otherMgmtRcved;          // Other management frame
wire otherCtrlRcved;          // Other control frame
wire cfRcved;                 // CF frame
wire qosCFRcved;              // QoS CF frame
wire otherDataRcved;          // Other data frame
wire dataNullRcved;           // Null (no data)

wire encryptionFilter;        // Encryption filter
wire errorFilter;             // Error filter
wire addressFilter;           // Address filter
wire bssIDFilter;             // bssID filter
wire frameTypeFilter;         // Frame type filter

wire myFrameRcved_p;          // my Frame correctly received pulse
wire myQoSFrameRcved_p;       // my QoS Frame correctly received pulse
wire barIncorrectRcved_p;     // BAR not supported (Compressed BA only is supported)

`ifdef RW_SIMU_ON
// String definition to display the type of frame
reg [23*8:0] rxFrameType_str;
`endif // RW_SIMU_ON


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// Fields sampling

// Frame control field
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxFrmCtrl <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    // Added reset on rxFrmCtrl[1:0] only for ctrlWrapError generation
    rxFrmCtrl[1:0] <= 2'b0;
  else if (rxDataValid && rxFrmCtrlEn)
  begin
    if (stateByteCnt[0])
      rxFrmCtrl[15:8] <= rxData;
    else
      rxFrmCtrl[7:0]  <= rxData;
  end
end

// MPDU status information
assign subTypeFrame    = rxFrmCtrl[7:4];
assign typeFrame       = rxFrmCtrl[3:2];
assign protocolError   = (rxFrmCtrl[1:0] != 2'h0) || ctrlWrapError;

// Manament Frame type allowed to be decrypted         Disassociation              Authentication               Deauthentication            Action                       Action No Ack
assign mgmtNoEncryptFrame = (typeFrame == 2'h0) && (subTypeFrame != 4'b1010) && (subTypeFrame != 4'b1011) && (subTypeFrame != 4'b1100) && (subTypeFrame != 4'b1101) && (subTypeFrame != 4'b1110);

// Frame type
assign mgmtFrame       = (typeFrame == 2'h0);
assign ctrlFrame       = (typeFrame == 2'h1);
assign dataFrame       = (typeFrame == 2'h2);
assign qosFrame        = (dataFrame && rxFrmCtrl[7]);
assign htcFrame        = ((qosFrame || mgmtFrame) && rxOrder);

// Management frame
assign probReqRcved    = mgmtFrame &&  (subTypeFrame == 4'h4);
assign probRespRcved   = mgmtFrame &&  (subTypeFrame == 4'h5);
assign bcnRcved        = mgmtFrame &&  (subTypeFrame == 4'h8);
assign actNoAckRcved   = mgmtFrame &&  (subTypeFrame == 4'he);
assign otherMgmtRcved  = mgmtFrame && !(bcnRcved || probRespRcved ||
                                        probReqRcved);

// Control frame
assign otherCtrlRcved  = ctrlFrame &&  (subTypeFrame <  4'h7);
assign ctrlWrapRcved   = ctrlFrame &&  (subTypeFrame == 4'h7);
assign barRcved        = ctrlFrame &&  (subTypeFrame == 4'h8);
assign baRcved         = ctrlFrame &&  (subTypeFrame == 4'h9);
assign psPollRcved     = ctrlFrame &&  (subTypeFrame == 4'ha);
assign rtsRcved        = ctrlFrame &&  (subTypeFrame == 4'hb);
assign ctsRcved        = ctrlFrame &&  (subTypeFrame == 4'hc);
assign ackRcved        = ctrlFrame &&  (subTypeFrame == 4'hd);
assign cfEndRcved      = ctrlFrame && ((subTypeFrame == 4'he) ||
                                       (subTypeFrame == 4'hf));

// Control Wrapper flag
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    ctrlWrapFlag <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    ctrlWrapFlag <= 1'b0;
  else if (ctrlWrapRcved)
    ctrlWrapFlag <= 1'b1;
end

// Control Wrapper error
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    ctrlWrapError <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    ctrlWrapError <= 1'b0;
  else if ((ctrlWrapFlag && carFrameCtrlEnd_p && ctrlWrapRcved) ||
    protocolError)
    ctrlWrapError <= 1'b1;
end

// Data frame
assign dataRcved       = dataFrame && ((subTypeFrame == 4'h0) || 
                                       (subTypeFrame == 4'h1) || 
                                       (subTypeFrame == 4'h2) || 
                                       (subTypeFrame == 4'h3));
assign otherDataRcved  = dataFrame && (subTypeFrame == 4'hd);
assign dataNullRcved   = dataFrame && (subTypeFrame == 4'h4);
assign cfRcved         = dataFrame && ((subTypeFrame == 4'h5) || 
                                       (subTypeFrame == 4'h6) || 
                                       (subTypeFrame == 4'h7));
assign qosDataRcved    = dataFrame && ((subTypeFrame == 4'h8) || 
                                       (subTypeFrame == 4'h9) ||
                                       (subTypeFrame == 4'ha) ||
                                       (subTypeFrame == 4'hb));
assign qosNullRcved    = dataFrame &&  (subTypeFrame == 4'hc);
assign qosCFRcved      = dataFrame && ((subTypeFrame == 4'he) || 
                                       (subTypeFrame == 4'hf));

// Reserved frame
assign reservedRcved   = (rxFrmCtrl[3:2] == 2'h3)                ||
                         (dataFrame &&  (subTypeFrame == 4'hd))  ||
                         (mgmtFrame && ((subTypeFrame == 4'h6)   ||
                                        (subTypeFrame == 4'h7)   ||
                                        (subTypeFrame == 4'hf))) ||
                         (dataFrame &&  (subTypeFrame == 4'hd))  ||
                         (ctrlFrame && otherCtrlRcved);

// Frame control fields
assign toDS            = rxFrmCtrl[8];
assign fromDS          = rxFrmCtrl[9];
assign rxMoreFrag      = rxFrmCtrl[10];
assign rxRetry         = rxFrmCtrl[11];
assign pwrMgt          = rxFrmCtrl[12];
assign rxMoreData      = rxFrmCtrl[13];
assign protectedBit    = rxFrmCtrl[14] && (addr1Match || bcMcRcved);
assign rxOrder         = rxFrmCtrl[15];


// Duration / ID field
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxFrameDuration <= 16'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxFrameDuration <= 16'b0;
  else if (rxDataValid && rxDurationIdEn)
  begin
    if (stateByteCnt[0])
      rxFrameDuration[15:8] <= rxData;
    else
      rxFrameDuration[7:0]  <= rxData;
  end
end

// Addr1 matching & sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    addr1Match <= 1'b0;
    rxAddr1    <= 48'b0;
  end
  else if (macCoreClkSoftRst_n == 1'b0)
  begin
    addr1Match <= 1'b0;
    rxAddr1    <= 48'b0;
  end
  else if (rxControlIdle == 1'b1) // Reset only addr1Match and keep rxAddr1
    addr1Match <= 1'b0;
  else if (rxDataValid && rxAddr1En)
  begin
    case (stateByteCnt[2:0])
      3'h0: begin
        rxAddr1[7:0] <= rxData;
        if (macAddrMasked[7:0] == (rxData | macAddrMask[7:0]))
          addr1Match <= 1'b1;
        else
          addr1Match <= 1'b0;
      end

      3'h1: begin
        rxAddr1[15:8] <= rxData;
        if (macAddrMasked[15:8] == (rxData | macAddrMask[15:8]))
          addr1Match <= addr1Match;
        else
          addr1Match <= 1'b0;
      end

      3'h2: begin
        rxAddr1[23:16] <= rxData;
        if (macAddrMasked[23:16] == (rxData | macAddrMask[23:16]))
          addr1Match <= addr1Match;
        else
          addr1Match <= 1'b0;
      end

      3'h3: begin
        rxAddr1[31:24] <= rxData;
        if (macAddrMasked[31:24] == (rxData | macAddrMask[31:24]))
          addr1Match <= addr1Match;
        else
          addr1Match <= 1'b0;
      end

      3'h4: begin
        rxAddr1[39:32] <= rxData;
        if (macAddrMasked[39:32] == (rxData | macAddrMask[39:32]))
          addr1Match <= addr1Match;
        else
          addr1Match <= 1'b0;
      end

      3'h5: begin
        rxAddr1[47:40] <= rxData;
        if (macAddrMasked[47:40] == (rxData | macAddrMask[47:40]))
          addr1Match <= addr1Match;
        else
          addr1Match <= 1'b0;
      end

      // Disable case default state for block coverage
      // pragma coverage block = off
      default: begin
        addr1Match <= addr1Match;
        rxAddr1    <= rxAddr1;
      end
      // pragma coverage block = on
      
    endcase
  end
end

// Addr1 Mask
assign macAddrMasked = (macAddr | macAddrMask);

// Broadcast frame
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    broadCastRcved <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    broadCastRcved <= 1'b0;
  else if (rxDataValid && rxAddr1En)
  begin
    case (stateByteCnt[2:0])
      3'h0:
        if (rxData == 8'hff)
          broadCastRcved <= 1'b1;
        else
          broadCastRcved <= 1'b0;

      3'h1, 3'h2, 3'h3, 3'h4, 3'h5:
        if (rxData == 8'hff)
          broadCastRcved <= broadCastRcved;
        else
          broadCastRcved <= 1'b0;

      // Disable case default state for block coverage
      // pragma coverage block = off
      default:
        broadCastRcved <= broadCastRcved;
      // pragma coverage block = on
        
    endcase
  end
end

// Multicast frame
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    multiCastRcved <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    multiCastRcved <= 1'b0;
  else if (rxDataValid && (stateByteCnt == 8'h00) && rxAddr1En)
    multiCastRcved <= rxData[0];
  else if (rxAddr2En && broadCastRcved)
    multiCastRcved <= 1'b0;
end

// Broadcast/Multicast frame
assign bcMcRcved = (multiCastRcved || broadCastRcved);

// Frame filtering
assign encryptionFilter = (excUnencrypted && !protectedBit) ||
                          !excUnencrypted;

assign errorFilter      = (!acceptErrorFrames && !protocolError) ||
                          acceptErrorFrames;
// If BSSID match
// acceptOtherBSSID is set
// a Probe Request is received
assign bssIDFilter      = bssIDMatch || (!bssIDMatch && acceptOtherBSSID) || (acceptProbeReq && probReqRcved) || (acceptAllBeacon && bcnRcved);

assign addressFilter    = (acceptMulticast && multiCastRcved && bssIDFilter) ||
                          (acceptBroadcast && broadCastRcved && bssIDFilter) ||
                          (acceptUnicast && !addr1Match && !bcMcRcved && (bssIDFilter || (ctrlFrame && !cfEndRcved && !psPollRcved))) ||
                          (acceptMyUnicast && addr1Match && !bcMcRcved);

assign frameTypeFilter  = (acceptProbeReq && probReqRcved) ||
                          (acceptProbeResp && probRespRcved) ||
                          ((acceptBeacon || acceptAllBeacon) && bcnRcved) ||
                          (acceptOtherMgmtFrames && otherMgmtRcved) ||
                          (acceptBAR && (barRcved || ctrlWrapRcved)) ||
                          (((acceptBA && rxBADly) || acceptNotExpectedBA) && (baRcved || ctrlWrapRcved)) ||
                          (acceptPSPoll && (psPollRcved || ctrlWrapRcved)) ||
                          (acceptRTS && (rtsRcved || ctrlWrapRcved)) ||
                          (acceptCTS && (ctsRcved || ctrlWrapRcved)) ||
                          (acceptACK && (ackRcved || ctrlWrapRcved)) ||
                          (acceptCFEnd && (cfEndRcved || ctrlWrapRcved)) ||
                          (acceptOtherCntrlFrames && (otherCtrlRcved || ctrlWrapRcved)) ||
                          (acceptData && dataRcved) ||
                          (acceptCFWOData && cfRcved) ||
                          (acceptQData && qosDataRcved) ||
                          (acceptQCFWOData && qosCFRcved) ||
                          (acceptQoSNull && qosNullRcved) ||
                          (acceptQoSNull && dataNullRcved) ||
                          (acceptOtherDataFrames && otherDataRcved) ||
                          (acceptUnknown && (rxFrmCtrl[3:2] == 2'h3));

// Accept received frame
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    acceptRcved <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    acceptRcved <= 1'b0;
  else if (encryptionFilter && errorFilter &&
           addressFilter && frameTypeFilter)
    acceptRcved <= 1'b1;
  else
    acceptRcved <= 1'b0;
end

// Addr2 sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxAddr2 <= 48'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxDurationIdEnd_p == 1'b1))       // Synchronous Reset
    rxAddr2 <= 48'b0;
  else if (rxDataValid && rxAddr2En)
  begin
    case (stateByteCnt[2:0])
      3'h0:    rxAddr2[7:0]   <= rxData;
      3'h1:    rxAddr2[15:8]  <= rxData;
      3'h2:    rxAddr2[23:16] <= rxData;
      3'h3:    rxAddr2[31:24] <= rxData;
      3'h4:    rxAddr2[39:32] <= rxData;
      3'h5:    rxAddr2[47:40] <= rxData;
      // Disable case default state for block coverage
      // pragma coverage block = off
      default: rxAddr2        <= rxAddr2;
      // pragma coverage block = on
    endcase
  end
end

assign rxBWSignalingTA = dynBWEn && rxAddr2[0];

// Addr3 sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxAddr3 <= 48'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxDurationIdEnd_p == 1'b1))       // Synchronous Reset
    rxAddr3 <= 48'b0;
  else if (rxDataValid && rxAddr3En)
  begin
    case (stateByteCnt[2:0])
      3'h0:    rxAddr3[7:0]   <= rxData;
      3'h1:    rxAddr3[15:8]  <= rxData;
      3'h2:    rxAddr3[23:16] <= rxData;
      3'h3:    rxAddr3[31:24] <= rxData;
      3'h4:    rxAddr3[39:32] <= rxData;
      3'h5:    rxAddr3[47:40] <= rxData;
      // Disable case default state for block coverage
      // pragma coverage block = off
      default: rxAddr3        <= rxAddr3;
      // pragma coverage block = on
    endcase
  end
end

`ifdef RW_WAPI_EN
// Addr4 sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxAddr4 <= 48'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxDurationIdEnd_p == 1'b1))       // Synchronous Reset
    rxAddr4 <= 48'b0;
  else if (rxDataValid && rxAddr4En)
  begin
    case (stateByteCnt[2:0])
      3'h0:    rxAddr4[7:0]   <= rxData;
      3'h1:    rxAddr4[15:8]  <= rxData;
      3'h2:    rxAddr4[23:16] <= rxData;
      3'h3:    rxAddr4[31:24] <= rxData;
      3'h4:    rxAddr4[39:32] <= rxData;
      3'h5:    rxAddr4[47:40] <= rxData;
      // Disable case default state for block coverage
      // pragma coverage block = off
      default: rxAddr4        <= rxAddr4;
      // pragma coverage block = on
    endcase
  end
end

// rxWAPIKeyIndex sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxWAPIKeyIndex <= 8'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxDurationIdEnd_p == 1'b1))       // Synchronous Reset
    rxWAPIKeyIndex <= 8'b0;
  else if (rxDataValid && rxWAPIKeyIdxEn)
    rxWAPIKeyIndex <= rxData;
end


// rxWAPIPN sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxWAPIPN <= 128'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxDurationIdEnd_p == 1'b1))       // Synchronous Reset
    rxWAPIPN <= 128'b0;
  else if (rxDataValid && rxWAPIPNEn)
  begin
    case (stateByteCnt[3:0])
      4'h0:    rxWAPIPN[7:0]     <= rxData;
      4'h1:    rxWAPIPN[15:8]    <= rxData;
      4'h2:    rxWAPIPN[23:16]   <= rxData;
      4'h3:    rxWAPIPN[31:24]   <= rxData;
      4'h4:    rxWAPIPN[39:32]   <= rxData;
      4'h5:    rxWAPIPN[47:40]   <= rxData;
      4'h6:    rxWAPIPN[55:48]   <= rxData;
      4'h7:    rxWAPIPN[63:56]   <= rxData;
      4'h8:    rxWAPIPN[71:64]   <= rxData;
      4'h9:    rxWAPIPN[79:72]   <= rxData;
      4'hA:    rxWAPIPN[87:80]   <= rxData;
      4'hB:    rxWAPIPN[95:88]   <= rxData;
      4'hC:    rxWAPIPN[103:96]  <= rxData;
      4'hD:    rxWAPIPN[111:104] <= rxData;
      4'hE:    rxWAPIPN[119:112] <= rxData;
      4'hF:    rxWAPIPN[127:120] <= rxData;
      // Disable case default state for block coverage
      // pragma coverage block = off
      default: rxWAPIPN          <= rxWAPIPN;
      // pragma coverage block = on
    endcase
  end
end

`endif //RW_WAPI_EN

// BSSID matching
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    bssIDMatch <= 1'b0;
    bssIDFrame <= 1'b0;
  end
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
  begin
    bssIDMatch <= 1'b0;
    bssIDFrame <= 1'b0;
  end
  else if (rxDataValid && 
         ((rxAddr1En && (( toDS && !fromDS &&  dataFrame) || psPollRcved)) ||
          (rxAddr2En && ((!toDS &&  fromDS &&  dataFrame) || cfEndRcved))  ||
          (rxAddr3En &&   !toDS && !fromDS && (dataFrame || mgmtFrame))))
  begin
    // Frame contains bssID field
    bssIDFrame <= 1'b1;
    
    // Check bssID field
    case (stateByteCnt[2:0])
      3'h0:
        if (rxAddr2En && dynBWEn)
        // In case of dynBWEn and TA (Addr2), the Individual/Group bit shall be masked
	      if (bssIDMasked[7:0] == ({rxData[7:1],1'b0} | bssIDMask[7:0]))
	        bssIDMatch <= 1'b1;
	      else
	        bssIDMatch <= 1'b0;
        else
          // otherwise, the check is done on the full rxData
	      if (bssIDMasked[7:0] == (rxData | bssIDMask[7:0]))
	        bssIDMatch <= 1'b1;
	      else
	        bssIDMatch <= 1'b0;

      3'h1:
        if (bssIDMasked[15:8] == (rxData | bssIDMask[15:8]))
          bssIDMatch <= bssIDMatch;
        else
          bssIDMatch <= 1'b0;

      3'h2:
        if (bssIDMasked[23:16] == (rxData | bssIDMask[23:16]))
          bssIDMatch <= bssIDMatch;
        else
          bssIDMatch <= 1'b0;

      3'h3:
        if (bssIDMasked[31:24] == (rxData | bssIDMask[31:24]))
          bssIDMatch <= bssIDMatch;
        else
          bssIDMatch <= 1'b0;

      3'h4:
        if (bssIDMasked[39:32] == (rxData | bssIDMask[39:32]))
          bssIDMatch <= bssIDMatch;
        else
          bssIDMatch <= 1'b0;

      3'h5:
        if (bssIDMasked[47:40] == (rxData | bssIDMask[47:40]))
          bssIDMatch <= bssIDMatch;
        else
          bssIDMatch <= 1'b0;

      // Disable case default state for block coverage
      // pragma coverage block = off
      default:
        bssIDMatch <= bssIDMatch;
      // pragma coverage block = on
      
    endcase
  end
  else if (rxQoSEnd_p && toDS && fromDS && rxAMSDUPresent)
  begin
    // Frame contains bssID field
    bssIDFrame <= 1'b1;
    
    // Check bssID field
    if (bssIDMasked == (rxAddr3 | bssIDMask))
      bssIDMatch <= 1'b1;
    else
      bssIDMatch <= 1'b0;
  end
end

// BSSID Mask
assign bssIDMasked = (bssID | bssIDMask);

// OLBC counter update
assign olbcUpdate_p = bssIDFrame && !bssIDMatch && fcsCheck_p;

// QoS Control sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxQoSControl <= 16'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    rxQoSControl <= 16'b0;
  else if (rxControlIdle && !activeRx)
    rxQoSControl <= 16'b0;
  else if (rxDataValid && rxQoSCtrlEn)
  begin
    if (stateByteCnt[0])
      rxQoSControl[15:8] <= rxData;
    else
      rxQoSControl[7:0] <= rxData;
  end
end

assign rxAMSDUPresent = rxQoSControl[7];
assign rxAckPolicy    = rxQoSControl[6:5];
assign rxTID          = (barRcved || baRcved) ? rxBACtrl[15:12] : rxQoSControl[3:0];

// HT Control sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxHTCtrl <= 32'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    rxHTCtrl <= 32'b0;
  else if (rxDataValid && rxHTCtrlEn)
  begin
    case (stateByteCnt[1:0])
      2'h0:    rxHTCtrl[7:0]   <= rxData;
      2'h1:    rxHTCtrl[15:8]  <= rxData;
      2'h2:    rxHTCtrl[23:16] <= rxData;
      default: rxHTCtrl[31:24] <= rxData;
    endcase
  end
end

// Sequence Control sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxSeqCtrl <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxDurationIdEnd_p == 1'b1))       // Synchronous Reset
    rxSeqCtrl <= 16'b0;
  else if (rxDataValid && rxSeqCtrlEn)
  begin
    if (stateByteCnt[0])
      rxSeqCtrl[15:8] <= rxData;
    else
      rxSeqCtrl[7:0]  <= rxData;
  end
end

// BA Control sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxBACtrl <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxDurationIdEnd_p == 1'b1))       // Synchronous Reset
    rxBACtrl <= 16'b0;
  else if (rxDataValid && rxBACtrlEn)
  begin
    if (stateByteCnt[0])
      rxBACtrl[15:8] <= rxData;
    else
      rxBACtrl[7:0]  <= rxData;
  end
end

assign compressedBA = (rxBACtrl[2:1] == 2'h2);

// BA Starting Sequence Number sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxBASSN <= 12'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxDurationIdEnd_p == 1'b1))       // Synchronous Reset
    rxBASSN <= 12'b0;
  else if (rxDataValid && rxBASeqCtrlEn)
  begin
    if (stateByteCnt[0])
      rxBASSN[11:4] <= rxData;
    else
      rxBASSN[3:0]  <= rxData[7:4];
  end
end

`ifdef ENCRYPTION
// IV sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxInitVectorFull <= 32'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxDurationIdEnd_p == 1'b1))       // Synchronous Reset
    rxInitVectorFull <= 32'b0;
  else if (rxDataValid && rxInitVectorEn)
  begin
    case (stateByteCnt[1:0])
      2'h0:    rxInitVectorFull[7:0]   <= rxData;
      2'h1:    rxInitVectorFull[15:8]  <= rxData;
      2'h2:    rxInitVectorFull[23:16] <= rxData;
      default: rxInitVectorFull[31:24] <= rxData;
    endcase
  end
end

assign rxInitVector = rxInitVectorFull[23:0];

// Extended IV sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxExtInitVector <= 32'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxDurationIdEnd_p == 1'b1))       // Synchronous Reset
    rxExtInitVector <= 32'b0;
  else if (rxDataValid && rxExtInitVectorEn)
  begin
    case (stateByteCnt[1:0])
      2'h0:    rxExtInitVector[7:0]   <= rxData;
      2'h1:    rxExtInitVector[15:8]  <= rxData;
      2'h2:    rxExtInitVector[23:16] <= rxData;
      default: rxExtInitVector[31:24] <= rxData;
    endcase
  end
end
`endif

// DTIM counter sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    dtimCnt <= 8'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    dtimCnt <= 8'b0;
  else if (rxDataValid && rxDtimCntEn)
    dtimCnt <= rxData;
end

// DTIM period sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    dtimPeriodIn <= 8'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    dtimPeriodIn <= 8'b0;
  else if (rxDataValid && rxDtimPeriodEn)
    dtimPeriodIn <= rxData;
end

// CFP counter sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    cfpCnt <= 8'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    cfpCnt <= 8'b0;
  else if (rxDataValid && rxCfpCntEn)
    cfpCnt <= rxData;
end

// CFP period sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    cfpPeriodIn <= 8'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    cfpPeriodIn <= 8'b0;
  else if (rxDataValid && rxCfpPeriodEn)
    cfpPeriodIn <= rxData;
end

// CFP duration remaining sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    cfpDurRemaining <= 16'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    cfpDurRemaining <= 16'b0;
  else if (rxDataValid && rxCfpDurRemainingEn)
  begin
    if (stateByteCnt[0])
      cfpDurRemaining[15:8] <= rxData;
    else
      cfpDurRemaining[7:0]  <= rxData;
  end
end

// Timestamp sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    timeStamp <= 64'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    timeStamp <= 64'b0;
  else if (rxDataValid && rxTimeStampEn)
  begin
    case (stateByteCnt[2:0])
      3'h0:    timeStamp[7:0]   <= rxData;
      3'h1:    timeStamp[15:8]  <= rxData;
      3'h2:    timeStamp[23:16] <= rxData;
      3'h3:    timeStamp[31:24] <= rxData;
      3'h4:    timeStamp[39:32] <= rxData;
      3'h5:    timeStamp[47:40] <= rxData;
      3'h6:    timeStamp[55:48] <= rxData;
      default: timeStamp[63:56] <= rxData;
    endcase
  end
end

// Quiet count 1 sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    quietCount1In <= 8'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    quietCount1In <= 8'b0;
  else if (rxDataValid && rxQuietCount1En)
    quietCount1In <= rxData;
end

// Quiet period 1 sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    quietPeriod1In <= 8'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    quietPeriod1In <= 8'b0;
  else if (rxDataValid && rxQuietPeriod1En)
    quietPeriod1In <= rxData;
end

// Quiet duration 1 sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    quietDuration1In <= 16'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    quietDuration1In <= 16'b0;
  else if (rxDataValid && rxQuietDuration1En)
  begin
    if (stateByteCnt[0])
      quietDuration1In[15:8] <= rxData;
    else
      quietDuration1In[7:0]  <= rxData;
  end
end

// Quiet offset 1 sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    quietOffset1In <= 16'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    quietOffset1In <= 16'b0;
  else if (rxDataValid && rxQuietOffset1En)
  begin
    if (stateByteCnt[0])
      quietOffset1In[15:8] <= rxData;
    else
      quietOffset1In[7:0]  <= rxData;
  end
end

// Quiet count 2 sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    quietCount2In <= 8'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    quietCount2In <= 8'b0;
  else if (rxDataValid && rxQuietCount2En)
    quietCount2In <= rxData;
end

// Quiet period 2 sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    quietPeriod2In <= 8'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    quietPeriod2In <= 8'b0;
  else if (rxDataValid && rxQuietPeriod2En)
    quietPeriod2In <= rxData;
end

// Quiet duration 2 sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    quietDuration2In <= 16'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    quietDuration2In <= 16'b0;
  else if (rxDataValid && rxQuietDuration2En)
  begin
    if (stateByteCnt[0])
      quietDuration2In[15:8] <= rxData;
    else
      quietDuration2In[7:0]  <= rxData;
  end
end

// Quiet offset 2 sampling
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    quietOffset2In <= 16'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    quietOffset2In <= 16'b0;
  else if (rxDataValid && rxQuietOffset2En)
  begin
    if (stateByteCnt[0])
      quietOffset2In[15:8] <= rxData;
    else
      quietOffset2In[7:0]  <= rxData;
  end
end


// my Frame received pulse after the end of ADDR1 field
assign myFrameRcved_p = (rxAddr1End_p || carFrameCtrlEnd_p) &&
                         addr1Match && !protocolError && !qosFrame && !barRcved;

// my QoS Frame received pulse after the end of QoS field
assign myQoSFrameRcved_p = rxQoSEnd_p && addr1Match && 
                           !protocolError && qosFrame;

// Incorrect BAR received pulse after the end of BAR Control field
assign barIncorrectRcved_p = rxBARCtrlEnd_p && addr1Match && 
                             !protocolError && barRcved && !compressedBA;


// Outputs to MAC Controller
assign ackRcved_p           = myFrameRcved_p && ackRcved;
assign rtsRcved_p           = myFrameRcved_p && rtsRcved;
assign ctsRcved_p           = myFrameRcved_p && ctsRcved;
assign cfEndRcved_p         = myFrameRcved_p && cfEndRcved;
assign baRcved_p            = myFrameRcved_p && baRcved;
assign barRcved_p           = rxBARCtrlEnd_p && addr1Match && !protocolError &&
                              barRcved && compressedBA;
assign needAckRcved_p       = barIncorrectRcved_p ||
                              (rxAddr3End_p && probRespRcved && !protocolError) || 
                              (rxDurationIdEnd_p && !protocolError && reservedRcved) ||
                    
                    
                             ((myFrameRcved_p || myQoSFrameRcved_p) && 
                              (!bcMcRcved) && (!bcnRcved) && (!probRespRcved) &&
                              (rxAckPolicy == 2'b00) &&
                             ((dataFrame && (subTypeFrame != 4'h5)) ||
                               psPollRcved                          ||
                              (mgmtFrame && !actNoAckRcved)));
                              
                              
assign bcMcRcved_p          = myFrameRcved_p && bcMcRcved;
assign bcnRcved_p           = rxAddr3End_p && bssIDMatch &&
                              bcnRcved && !protocolError;
assign probRespRcved_p      = rxAddr3End_p && bssIDMatch &&
                              probRespRcved && !protocolError;
assign notMineRcved         = !addr1Match && !bcnRcved && 
                              !bcMcRcved && !protocolError;
assign notMineRcved_p       = rxAddr1End_p && notMineRcved;
assign unknownRcved_p       = rxDurationIdEnd_p && (protocolError || reservedRcved);
assign notMinePsPollRcved_p = (rxAddr1End_p || carFrameCtrlEnd_p) && (psPollRcved) &&
                              (!addr1Match) && (!protocolError) && (!qosFrame);
assign notMineRtsRcved_p    = (rxAddr1End_p || carFrameCtrlEnd_p) && (rtsRcved) &&
                              (!addr1Match) && (!protocolError) && (!qosFrame);

// Outputs Decryption FSM
assign rxDefKeyID         = rxInitVectorFull[31:30];

assign myFrameRcvedTrig_p = rxAddr2End_p && !protocolError;


///////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
///////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////
// Display Frame type in string for RTL simulation waveform
//////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
// Type of received frame displayed in a string to easy simulation and debug
always @*
begin
  casex ({subTypeFrame, typeFrame})
    6'b000000  :  rxFrameType_str = {"ASSOCIATION REQUEST"};
    6'b000100  :  rxFrameType_str = {"ASSOCIATION RESPONSE"};
    6'b001000  :  rxFrameType_str = {"REASSOCIATION REQUEST"};
    6'b001100  :  rxFrameType_str = {"REASSOCIATION RESPONSE"};
    6'b010000  :  rxFrameType_str = {"PROBE RESPONSE"};
    6'b010100  :  rxFrameType_str = {"PROBE RESPONSE"};
    6'b100000  :  rxFrameType_str = {"BEACON"};
    6'b100100  :  rxFrameType_str = {"ATIM"};
    6'b101000  :  rxFrameType_str = {"DISSASSOCIATION"};
    6'b101100  :  rxFrameType_str = {"AUTHENTICATION"};
    6'b110000  :  rxFrameType_str = {"DEAUTHENTICATION"};
    6'b110100  :  rxFrameType_str = {"ACTION"};
    6'b011101  :  rxFrameType_str = {"CONTROL WRAPPER"};
    6'b100001  :  rxFrameType_str = {"BA REQUEST"};
    6'b100101  :  rxFrameType_str = {"BA"};
    6'b101001  :  rxFrameType_str = {"PS-POLL"};
    6'b101101  :  rxFrameType_str = {"RTS"};
    6'b110001  :  rxFrameType_str = {"CTS"};
    6'b110101  :  rxFrameType_str = {"ACK"};
    6'b111001  :  rxFrameType_str = {"CF-END"};
    6'b111101  :  rxFrameType_str = {"CF-END+CF-ACK"};
    6'b000010  :  rxFrameType_str = {"DATA"};
    6'b000110  :  rxFrameType_str = {"DATA+CF-ACK"};
    6'b001010  :  rxFrameType_str = {"DATA+CF-POLL"};
    6'b001110  :  rxFrameType_str = {"DATA+CF-ACK+CF-POLL"};
    6'b010010  :  rxFrameType_str = {"Null"};
    6'b010110  :  rxFrameType_str = {"CF-ACK"};
    6'b011010  :  rxFrameType_str = {"CF-POLL"};
    6'b011110  :  rxFrameType_str = {"CF-ACK+CF-POLL"};
    6'b100010  :  rxFrameType_str = {"QoS DATA"};
    6'b100110  :  rxFrameType_str = {"QoS DATA+CF-ACK"};
    6'b101010  :  rxFrameType_str = {"QoS DATA+CF-POLL"};
    6'b101110  :  rxFrameType_str = {"QoS DATA+CF-ACK+CF-POLL"};
    6'b110010  :  rxFrameType_str = {"QoS Null"};
    6'b111010  :  rxFrameType_str = {"QoS CF-POLL"};
    6'b111110  :  rxFrameType_str = {"QoS CF-ACK+CF-POLL"};
      default  :  rxFrameType_str = {"UNKNOWN"};
  endcase
end
`endif // RW_SIMU_ON

endmodule
