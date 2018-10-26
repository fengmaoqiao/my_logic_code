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
// Description      : 
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
// Application Note :                                                       
// Simulator        :                                                       
// Parameters       :                                                       
// Terms & concepts :                                                       
// Bugs             :                                                       
// Open issues and future enhancements :
//   DualCTS protection and CF-END as an AP not fully supported                                    
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////



module macControllerRx (
          //$port_g Clock and Reset interface
          input  wire        macCoreClk,            // MAC Core Clock
          input  wire        macCoreClkHardRst_n,   // Hard Reset of the MAC Core Clock domain 
                                                    // active low
          input  wire        macCoreClkSoftRst_n,   // Soft Reset of the MAC Core Clock domain 
          output wire        macCoreTxClkEnRxC,     // Enable TX Clocks

          //$port_g MAC Controller Master interface
          input  wire        rxExchangeEnabled,     // Enables the RX frame exchange
          output wire        rxExchangeCompleted_p, // When the completion of a RX frame exchange
          output reg         rxRIFSPossible,        // Enable the RX path of the RF
          output reg         rxRIFSCancelled_p,     // Cancels the potential reception of frame after RIFS 
          output wire        txRxnRxC,              // Indicates the mode between TX and Rx
                                                    //   0 : RX
                                                    //   1 : TX
          input  wire  [1:0] availableBW,           // Bandwidth available before the current reception.

          //$port_g MAC Controller Rate Selection interface
          input  wire  [6:0] mcsRESP,               // MCS Index for response frame
          input  wire  [3:0] legRateRESP,           // Legacy Rate Index for response frame
          output wire        rateUpdateRxC_p,       // Request from the macControllerRx to update the response frame rate
          
          //$port_g Rx Controller interface
          input  wire        reservedRcved,         // RSVD received
          input  wire        ackRcved_p,            // ACK received
          input  wire        rtsRcved_p,            // RTS received
          input  wire        ctsRcved_p,            // CTS received
          input  wire        cfEndRcved_p,          // CF-End received
          input  wire        baRcved_p,             // BA received 
          input  wire        barRcved_p,            // BAR received
          input  wire        needAckRcved_p,        // Data or management received with ACK needed
          input  wire        bcMcRcved_p,           // Broadcast/Multicast
          input  wire        bcnRcved_p,            // Beacon received
          input  wire        probRespRcved_p,       // Prob Response received
          input  wire        notMineRtsRcved_p,     // Not mine RTS received
          input  wire        notMinePsPollRcved_p,  // Not mine PS-Poll received
          input  wire        notMineRcved_p,        // Frame received but not mine
          input  wire        unknownRcved_p,        // Unknown frame received
          input  wire        macHeaderCompleted,    // End of MAC Header reception
          input  wire [47:0] rxAddr1,               // Received addr1
          input  wire [47:0] rxAddr2,               // Received addr2
          input  wire        rxMoreFrag,            // More Frag bit of the received frame
          input  wire  [1:0] rxAckPolicy,           // Ack policy (Ack, No Ack, BA)
          input  wire [31:0] rxHTCtrl,              // HT control field of the received frame
          input  wire [15:0] rxFrameDuration,       // Frame duration

          input  wire        incorrectRcved_p,      // Frame not received correctly
          input  wire        correctRcved_p,        // Frame received correctly

          input  wire        rxBWSignalingTA,       // Indicate that the received frame has a Bandwidth Signaling TA

          input  wire  [3:0] rxLegRateConv,         // Legacy rate of received frame
          input  wire  [6:0] rxMCS,                 // MCS Index of received frame
          input  wire [15:0] rxHTLength,            // HT length of received frame
          input  wire [11:0] rxLegLength,           // Legacy length of received frame
          input  wire  [1:0] rxSTBC,                // STBC field of received frame

          input  wire        rxDynBW,               // Dynamique Bandwidth
          input  wire  [1:0] rxChBW,                // Bandwidth  of received frame       
          input  wire  [1:0] rxChBWInNonHT,         // Channel bandwidth in Non-HT extracted from the scrambler initialization sequence
          input  wire  [1:0] rxChOffset,            // Channel Offset of received frame
          input  wire        rxLSIGValid,           // L-SIG Valid of received frame
          input  wire  [7:0] rxAntennaSet,          // Antenna Set of received frame
          input  wire  [7:0] rxSMMIndex,            // Spatial Map Matrix Index of received frame
          input  wire        rxPreType,             // Preamble Type of received frame
                                                    //   1'b0: SHORT
                                                    //   1'b1: LONG
          input  wire  [2:0] rxFormatMod,           // Format and Modulation of received frame
                                                    //   3'b000: NON-HT
                                                    //   3'b001: NON-HT-DUP-OFDM
                                                    //   3'b010: HT-MF
                                                    //   3'b011: HT-GF
                                                    //   3'b100: VHT
          input  wire  [1:0] rxNumExtnSS,           // Number of Extension Spatial Streams of received frame
          input  wire        rxFecCoding,           // Low Density Partity Check  of received frame      
          input  wire  [2:0] rxNTx,                 // Number of Transmit Chains for PPDU   of received frame     
          input  wire        rxShortGI,             // Short Guard Interval of received frame
          output reg         lSIGTXOPDetected,      // Flag indicating RX packet protected with LSIG TXOP

          //$port_g Deaggregator interface
          input  wire        ampduCorrectRcved_p,   // A-MPDU received correctly
          input  wire        ampduIncorrectRcved_p, // A-MPDU not received correctly
          input  wire        rxSingleVHTMPDU,       // Detect EOF bit in delimiter in VHT Single MPDU
          input  wire        rxVector1Valid_p,      // Rx vector 1 is available
          input  wire        rxEndOfFrame_p,        // Rx vector 2 is available
          input  wire        rxAggregation,         // Indicates that the receving frame is an AMPDU

          output wire        startRxRxC_p,          // Start Rx
          output wire        stopRxRxC_p,           // Stop Rx

          //$port_g TX Controller interface
          input  wire        txDone_p,              // Indicates the completion of the transmission
          output reg         sendCTSRxC_p,          // Indicates that a CTS packet has to be sent
          output reg         sendACK_p,             // Indicates that an ACK packet has to be sent
          output reg         sendBA_p,              // Indicates that an Block ACK packet has to be sent
          output reg         sendCFENDRxC_p,        // Indicates that an CF-END packet has to be sent
          output wire        sendOnSIFSRxC,         // If set, data is sent on tickSIFS else on tickSlot
          output wire        sendOnPIFSRxC,         // If set, data is sent on tickPIFS

          output reg  [47:0] destAddrRxC,           // Receiver address
          output reg  [47:0] srcAddrRxC,            // Source address
          output reg  [15:0] durationRxC,           // Duration

          output wire  [6:0] txMCSRxC,              // MCS (Only used for HT frame)
          output wire [11:0] txLegLengthRxC,        // Legacy Length of the PPDU         
          output wire  [3:0] txLegRateRxC,          // Legacy Rate of the PPDU.         
          output wire [15:0] txHTLengthRxC,         // Length of the HT PPDU         
          output wire  [1:0] txSTBCRxC,             // Transmit a Frame with Space Time Block Coding
          output wire        txResp,                // Transmit a Response Frame

          output wire  [1:0] txChBWRxC,             // Response Transmission with Bandwidth        
          output wire        txBWSignalingRxC,      // Response Transmission with BW Signaling
          output wire        txDynBWRxC,             // Transmission with Dynamic BW
          output wire  [7:0] respTxAntennaSet,      // Response Transmission with Antenna Set
          output wire  [7:0] respTxSMMIndex,        // Response Transmission with Spatial Map Matrix Index
          output wire        respTxPreType,         // Response Transmission with Preamble Type
                                                    //   1'b0: SHORT
                                                    //   1'b1: LONG
          output wire  [2:0] respTxFormatMod,       // Response Transmission with Format and Modulation
                                                    //   3'd0: NON-HT
                                                    //   3'd1: NON-HT-DUP-OFDM
                                                    //   3'd2: HT-MF
                                                    //   3'd3: HT-GF
                                                    //   3'd4: VHT
          output wire  [1:0] respTxNumExtnSS,       // Response Transmission with Number of Extension Spatial Streams
          output wire        respTxFECCoding,       // Response Transmission with Low Density Partity Check       
          output wire  [2:0] respTxNTx,             // Response Transmission with Number of Transmit Chains for PPDU        
          output wire        respTxShortGI,         // Response Transmission with Short Guard Interval


          //$port_g TX Time interface
          input  wire [15:0] timeOnAirMC,            // Time On Air result to MAC Controller
                                                     // This field gives the time taken for frame transmission in microseconds (us)
                                                     // computed from parameters given by the MAC Controller.
          input  wire        timeOnAirValidMC,       // Time On Air Valid to MAC Controller
                                                     // This field is set when the air time computation is completed.

          output reg  [15:0] ppduLengthMCRx,         // PPDU Length from MAC Controller
                                                     // This field gives the length of the PPDU for computing time on air.
          output reg   [1:0] ppduBWMCRx,             // PPDU 40 MHz from MAC Controller
                                                     // This field indicates that that the PPDU should be transmitted at 40 MHz.
          output reg   [2:0] ppduPreTypeMCRx,        // PPDU Preamble Type from MAC Controller
	                                                   // This field indicates what type of preamble is transmitted for the frame.
                                                     // The encoding is as follows:
                                                     //   3'b000: Non-HT-Short
                                                     //   3'b001: Non-HT-Long
                                                     //   3'b010: HT-MF
                                                     //   3'b011: HT-GF
                                                     //   3'b100: VHT
          output reg   [1:0] ppduNumExtnSSMCRx,      // Number of Extension Spatial Streams      
          output reg   [1:0] ppduSTBCMCRx,           // Enable Space Time Block Coding          
          output reg         ppduShortGIMCRx,        // PPDU Short Guard Interval from MAC Controller
                                                     // Indicates that the frame should be transmitted with Short GI.
          output reg   [7:0] ppduMCSIndexMCRx,       // PPDU LegRate or MCS Index from MAC Controller
                                                     // This field indicates the rate at which this PPDU is transmitted. 
          output wire        woPreambleMCRx,         // Indicates that total duration should not include the preamble duration 
          output reg         startComputationMCRx_p, // Start Time on Air computation from MAC Controller

          //$port_g NAV Module interface
          input  wire        channelBusy,           // Channel busy indicator
          output wire [15:0] ctsDuration,           // Indicates the duration of a CTS frame response of the received RTS
          output wire        ctsDurationValid_p,    // Indicates that the ctsDuration is valid
          output wire [15:0] ackDuration,           // Indicates the duration of a ACK frame response of the received PS-POLL
          output wire        ackDurationValid_p,    // Indicates that the ackDuration is valid
          output reg   [7:0] phyRxStartDelay,       // Receive Start Delay of the PHY
          output reg  [15:0] navLsigDuration,       // Indicates the duration computed based on L_LENGTH and L_RATE in HT_MM
          
          //$port_g MAC Timer Unit interface
          input  wire        tickPIFS_p,            // A pulse to indicate the end of PIFS period
          output reg  [15:0] frmDurWithoutMH,       // Indicates the duration if the Beacon or Probe Response from the end of the MAC header

          //$port_g MAC PHY interface
          input  wire        macPhyIfRxCca,         // CCA trigger                   
          input  wire        mpIfTxErr_p,           // Tx error from MAC-PHY if. resynchronized
          input  wire        macPhyIfRxEnd_p,       // Rx error from MAC-PHY if. resynchronized
          input  wire        macPhyIfRxErr_p,       // Rx error from MAC-PHY if. resynchronized
          input  wire        macPhyIfRxFlush_p,     // Rx flush pulse
          input  wire        macPHYIFUnderRun,      // Underrun from MAC-PHY if.

          //$port_g HW Error detected
          input  wire        hwErr,                 // HW error detected

          //$port_g Debug Port
          output wire [15:0] debugPortMACControllerRx,// DebugPort of the MAC Controller Rx
          
          //$port_g CSReg interface
          output reg   [3:0] macControllerRxFSMCs,  // State of the MAC Controller RX FSM      
          input  wire  [7:0] sifsA,                 // Provide SIFS A duration in us
          input  wire  [7:0] sifsB,                 // Provide SIFS B duration in us
          input  wire  [7:0] slotTime,              // Provide Slot duration in us
          input  wire        ap,                    // Indicates the type of device (0: STA, 1: AP)
          input  wire  [7:0] rxStartDelayMIMO,      // Receive Start Delay for MIMO
          input  wire  [7:0] rxStartDelayShort,     // Receive Start Delay for DSSS/CCK Short preamble
          input  wire  [7:0] rxStartDelayLong,      // Receive Start Delay for DSSS/CCK Long preamble
          input  wire  [7:0] rxStartDelayOFDM,      // Receive Start Delay for OFDM
          input  wire        disableACKResp,        // Disable ACK Response This bit is set by SW to disable 
                                                    // the automatic ACK generation logic in HW.
          input  wire        disableCTSResp,        // Disable CTS Response This bit is set by SW to disable 
                                                    // the automatic CTS generation logic in HW.
          input  wire        disableBAResp,         // Disable BA Response This bit is set by SW to disable 
                                                    // the automatic BA generation logic in HW.
          input  wire        dynBWEn,               // Enable dynamic Bandwidth support
          input  wire        supportLSTP,           // Indicates that the HW supports L-SIG TXOP
          input  wire  [7:0] ctsSTBCDur,            // CTS STBC Duration
          input  wire        dualCTSProt,           // Dual-CTS Protection
          input  wire  [6:0] basicSTBCMCS           // Basic STBC MCS
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
localparam
     NON_HT           = 3'd0,
     NON_HT_DUP_OFDM  = 3'd1,
     HT_MM            = 3'd2,
     HT_GF            = 3'd3,
     VHT              = 3'd4;

// macControllerRxFSM FSM states definition
//$fsm_sd macControllerRxFSM
localparam
                 IDLE  =  4'd0,
             RX_FRAME  =  4'd1,
 COMP_DURATION_RX_LEG  =  4'd2,
  COMP_DURATION_RX_MM  =  4'd3,
   COMP_DURATION_RESP  =  4'd4,
    COMP_DURATION_TFS  =  4'd5,
          RX_WAIT_END  =  4'd6,
              TX_RESP  =  4'd7,
         CHECK_MEDIUM  =  4'd8,
         TX_STBC_RESP  =  4'd9;

localparam 
       RESP_TYPE_NONE  =  3'd0,
        RESP_TYPE_ACK  =  3'd1,
        RESP_TYPE_CTS  =  3'd2,
         RESP_TYPE_BA  =  3'd3,
      RESP_TYPE_CFEND  =  3'd4;
      
//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// macControllerRxFSM FSM signals definition
reg [3:0]  macControllerRxFSMNs;  // macControllerRxFSM FSM Next State
reg [3:0]  macControllerRxFSMPs;  // macControllerRxFSM FSM Previous State

reg        incorrectRcved;        // Frame not received correctly
reg        correctRcved;          // Frame received correctly
reg        durationCompEndFlag;   // duration computation end
wire       durationCompEnd;       // duration computation end
reg [2:0]  expectedResp;
reg        rxEndOfFrame;
reg [15:0] txRespLength;          // Length of the response      
reg [15:0] legLengthComputed;     // Legacy Length computed for HT_MM
reg [15:0] rxFrameLegDuration;
reg [15:0] rxFrameHTDuration;
reg        lsigCheckDone;         // Indicates that the lSIG check has been done
reg        notMinePsPollRcved;    // Indicates that a not mine PS-POLL has been received.
reg        notMineRtsRcved;       // Indicates that a not mine RTS has been received.
reg        tsfRcved;              // Indicates that a frame carrying a TSF (Beacon or Prob Response) has been received.
reg        probRespRcved;         // Prob Response received
reg        bcnRcved;              // Beacon received
reg        macPhyIfRxFlush;
reg        macHeaderCompleted_ff1;// End of MAC Header reception
wire       rxFrameIsHT;			  // Indicate that the received frame is HT of VHT


`ifdef RW_SIMU_ON
// String definition to display macControllerRxFSM current state
reg [21*8-1:0] macControllerRxFSMCs_str;
reg [15*8-1:0] expectedResp_str;
reg [15*8-1:0] respTxFormatMod_str;
`endif // RW_SIMU_ON


reg         frameExpectingResp;
reg         frameDontExpectingResp;
reg  [15:0] estDuration;         // Estimated duration of the response frame and SIFS.
wire [15:0] lSIGDuration;        // L-SIG Duration
wire [15:0] txTimeInt;           // Equal to TXTIME-(signalExtension - 20)
wire [15:0] lSIGDurationInt;     // Equal to lSIGDuration-signalExtension
wire  [2:0] signalExtension;

reg         rxNDPAn;             // NDP Announcement bit from the HT Control Field of the received frame
reg         rxTRQ;               // TRQ bit from the HT Control Field of the received frame
reg         respIsHT;            // Indicates if the response frame should be HT or NON-HT PPDU
reg         dualRespNeeded;      // Indicates if the response needs STBC.

wire        txErr;               // Indicates that a error occured during transmission

reg         respBWFail;          // Indicates that the requested bandwidth is not available.
                                 // this flag is generated only in case of BW signaling mode with dynBW = static           
wire        timeOnAirDone_p;     // Indicates the end of the time on air computation
reg         timeOnAirValidMC_ff1;// timeOnAirValidMC delayed of one clock cycle

reg   [1:0] txChBWInt;           // Response Transmission with Bandwidth        


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

assign macCoreTxClkEnRxC = (macControllerRxFSMCs == TX_RESP || macControllerRxFSMCs == TX_STBC_RESP || macControllerRxFSMCs == CHECK_MEDIUM) ? 1'b1 : 1'b0; //$todo clock gating

// macControllerRxFSM FSM Current State Logic 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macControllerRxFSMCs <= IDLE; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macControllerRxFSMCs <= IDLE; 
  else
    macControllerRxFSMCs <= macControllerRxFSMNs; 
end
// macControllerRxFSM FSM Previous State Logic 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macControllerRxFSMPs <= IDLE; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macControllerRxFSMPs <= IDLE; 
  else
    macControllerRxFSMPs <= macControllerRxFSMCs; 
end


// macControllerRxFSM FSM Next State Logic.
always @* 
begin
  case(macControllerRxFSMCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits for a trigger from the macControllerMaster state machine
      if (rxExchangeEnabled && !rxExchangeCompleted_p) 
        //$fsm_t When rxExchangeEnabled is received indicating the beginning of a reception, the state machine goes to RX_FRAME state.
        macControllerRxFSMNs = RX_FRAME; 
      else
        //$fsm_t While rxExchangeEnabled is not received, the state machine stays in IDLE state.
        macControllerRxFSMNs = IDLE;

    RX_FRAME:
      //$fsm_s In RX_FRAME state, the rxController is receiving the first bytes of the frame. The state machine waits for an indication
      // from the RX Controller indicating the type of frame which is being received.
      if (macPhyIfRxErr_p || rxEndOfFrame)
        //$fsm_t When macPhyIfRxErr_p is received indicating that an phy error has been detected, 
        // the state machine goes to IDLE state.
        macControllerRxFSMNs = IDLE;
      else if (rxVector1Valid_p && ((rxFormatMod == HT_MM) || (rxFormatMod == VHT)))
        //$fsm_t When rxVector1Valid_p is received with rxFormatMod = 2 or 4 indicating that we are receiving a HT_MM or a VHT frame, 
        // the state machine goes to COMP_DURATION_RX_LEG state to compute the rx frame duration.
        macControllerRxFSMNs = COMP_DURATION_RX_LEG;
      else if (bcnRcved || probRespRcved) 
        //$fsm_t When a Beacon or a Prob Response has been received, the state machine goes to COMP_DURATION_TFS state.
        macControllerRxFSMNs = COMP_DURATION_TFS;
      else if ((notMinePsPollRcved || notMineRtsRcved || frameExpectingResp) && macHeaderCompleted && correctRcved_p)
        //$fsm_t When frameExpectingResp is received indicating that a frame is being received and expects a 
        //response or a PS-POLL or a RTS, the state machine goes to COMP_DURATION_RESP state.
        macControllerRxFSMNs = COMP_DURATION_RESP;
//       else if (frameDontExpectingResp || (!rxAggregation && correctRcved) || (rxAggregation && ampduCorrectRcved)) 
      else if ((!notMinePsPollRcved && !notMineRtsRcved && frameDontExpectingResp && macHeaderCompleted) || correctRcved) 
        //$fsm_t When frameDontExpectingResp is received indicating that a frame is being received and does 
        //not expect a response, the state machine goes to RX_WAIT_END state.
        macControllerRxFSMNs = RX_WAIT_END;
      else        
        //$fsm_t While nothing is received, the state machine stays in RX_FRAME state.
        macControllerRxFSMNs = RX_FRAME;

    COMP_DURATION_RX_LEG :
      //$fsm_s In COMP_DURATION_RX_LEG state, the state machine waits for the completion of the duration computation of the received frame
      if (macPhyIfRxErr_p)      
        //$fsm_t When macPhyIfRxErr_p is received set meaning that a PHY error has been detected, 
        //the state machine goes to IDLE state.
        macControllerRxFSMNs = IDLE; 
      else if (durationCompEnd)
        //$fsm_t When durationCompEnd is received, the state machine moves to COMP_DURATION_RX_MM.
        macControllerRxFSMNs = COMP_DURATION_RX_MM;
      else        
        //$fsm_t While durationCompEnd is not received, the state machine stays in COMP_DURATION_RX_LEG state.
        macControllerRxFSMNs = COMP_DURATION_RX_LEG;
    
    COMP_DURATION_RX_MM :
      //$fsm_s In COMP_DURATION_RX_MM state, the state machine waits for the completion of the duration computation of the received frame
      if (macPhyIfRxErr_p)      
        //$fsm_t When macPhyIfRxErr_p is received set meaning that a PHY error has been detected, 
        //the state machine goes to IDLE state.
        macControllerRxFSMNs = IDLE; 
      else if (durationCompEnd)
        //$fsm_t When durationCompEnd is received, the state machine moves back to RX_FRAME.
        macControllerRxFSMNs = RX_FRAME;
      else        
        //$fsm_t While durationCompEnd is not received, the state machine stays in COMP_DURATION_RX_MM state.
        macControllerRxFSMNs = COMP_DURATION_RX_MM;
    

    COMP_DURATION_RESP:
      //$fsm_s In COMP_DURATION_RESP state, the state machine waits for the completion of the duration computation
      if (macPhyIfRxErr_p)      
        //$fsm_t When macPhyIfRxErr_p is received set meaning that a PHY error has been detected, 
        //the state machine goes to IDLE state.
        macControllerRxFSMNs = IDLE; 
      else if (durationCompEnd && correctRcved && rxEndOfFrame && (expectedResp != RESP_TYPE_NONE))
      begin
        if ((channelBusy || respBWFail) && (expectedResp == RESP_TYPE_CTS))
          //$fsm_t When channelBusy is set after reception of rxEndOfFrame_p meaning that the NAV is set,
          // Or if the requested bandwidth is not available (in case of BW signaling),
          // the CTS response is not transmitted.
          macControllerRxFSMNs = IDLE; 
        else if ((rxSTBC != 2'b0) && dualCTSProt)
          //$fsm_t When correctRcved, rxEndOfFrame and durationCompEnd are set meaning that the frame has been completly received with the FCS OK 
          //the duration computation is finished and the frame received is a STBC frame and dualCTS Protection is enabled, 
          //the state machine goes to TX_STBC_RESP state.
          macControllerRxFSMNs = TX_STBC_RESP; 
        else           
          //$fsm_t When correctRcved, rxEndOfFrame and durationCompEnd are set meaning that the frame has been completly received with the FCS OK 
          //the duration computation is finished and the frame received requires a response, 
          //the state machine goes to TX_RESP state.
          macControllerRxFSMNs = TX_RESP; 
      end
      else if (incorrectRcved && rxEndOfFrame)      
        //$fsm_t When rxEndOfFrame_p is received with incorrectRcved set meaning that the frame has been 
        // completly received with an FCS error, the state machine goes to RX_WAIT_END state.
        macControllerRxFSMNs = RX_WAIT_END; 
      else if (correctRcved && rxEndOfFrame && (expectedResp == RESP_TYPE_NONE))      
        //$fsm_t When rxEndOfFrame_p is received with correctRcved set meaning that the frame which does not expect reponse has been 
        // completly received without FCS error, the state machine goes to IDLE state.
        macControllerRxFSMNs = IDLE; 
      else
        //$fsm_t While durationCompEnd is not received, the state machine stays in COMP_DURATION_RESP state.
        macControllerRxFSMNs = COMP_DURATION_RESP;


    COMP_DURATION_TFS:
      //$fsm_s In COMP_DURATION_TFS state, the state machine waits for the completion of the duration computation
      if (macPhyIfRxErr_p)      
        //$fsm_t When macPhyIfRxErr_p is received set meaning that a PHY error has been detected, 
        //the state machine goes to IDLE state.
        macControllerRxFSMNs = IDLE;
      else if (durationCompEnd && probRespRcved && (expectedResp != RESP_TYPE_NONE) && macHeaderCompleted)
        //$fsm_t When a probe Response which expected a response was received and its frame duration computing is completed, 
        //the state machine moves to COMP_DURATION_RESP.
        macControllerRxFSMNs = COMP_DURATION_RESP;  
      else if (durationCompEnd && rxEndOfFrame)      
        //$fsm_t When rxEndOfFrame_p is received with incorrectRcved set meaning that the frame has been 
        // completly received with an FCS error, the state machine goes to RX_WAIT_END state.
        macControllerRxFSMNs = RX_WAIT_END; 
      else
        //$fsm_t While durationCompEnd is not received, the state machine stays in COMP_DURATION_TFS state.
        macControllerRxFSMNs = COMP_DURATION_TFS;

    TX_RESP:
      //$fsm_s In TX_RESP state, the state machine launches the response frame transmission and waits until its completion
      if (txErr) 
        //$fsm_t When txErr is received meaning that a PHY error has been detected, 
        //the state machine goes to IDLE state.
        macControllerRxFSMNs = IDLE; 
      else if (txDone_p) 
        if (ap && dualRespNeeded && (rxSTBC == 2'b0))
          //$fsm_t When txDone_p is received meaning that the response frame has been completely transmitted, 
          // and a STBC CTS or CFEND has to be transmitted (ap = 1 and dualRespNeeded = 1) and the RTS/CFEND received was not STBC (rxSTBC = 0),
          // the state machine moves to TX_STBC_RESP state.
          // Note that the dual CTS/CFEND response only applies to the AP; a non-AP STA shall respond to a RTS request with a single CTS and 
          // shall not respond to a CFEND.
          macControllerRxFSMNs = TX_STBC_RESP; 
        else  
          //$fsm_t When txDone_p is received meaning that the response frame has been completely transmitted, 
          // and a STBC CTS/CFEND transmission is not required, the state machine moves to IDLE state.
          macControllerRxFSMNs = IDLE; 
      else
        //$fsm_t While txDone_p is not received, the state machine stays in TX_RESP state.
        macControllerRxFSMNs = TX_RESP;

    CHECK_MEDIUM:
      //$fsm_s In CHECK_MEDIUM state, the state machine turns the PHY in RX to check if the medium is free for PIFS
      if (tickPIFS_p) 
        //$fsm_t When tickPIFS_p is received meaning that the medium was free for PIFS, the second CTS has to be transmitted.
        // So, the state machine moves to TX_RESP state.
        macControllerRxFSMNs = TX_RESP; 
      else if (macPhyIfRxCca) 
          //$fsm_t When macPhyIfRxCca is received meaning that the the PHY has detected a frame, 
          // the state machine moves to IDLE state.
          macControllerRxFSMNs = IDLE; 
      else
        //$fsm_t While tickPIFS_p or macPhyIfRxCca are not received, the state machine stays in CHECK_MEDIUM state.
        macControllerRxFSMNs = CHECK_MEDIUM;

    TX_STBC_RESP:
      //$fsm_s In TX_STBC_RESP state, the state machine launches the STBC response frame transmission and waits until its completion
      if (txErr) 
        //$fsm_t When txErr is received meaning that a PHY error has been detected, 
        //the state machine goes to IDLE state.
        macControllerRxFSMNs = IDLE; 
      else if (txDone_p) 
        if (ap && dualRespNeeded && (rxSTBC != 2'b00) && (expectedResp == RESP_TYPE_CTS))
          //$fsm_t When txDone_p is received meaning that the STBC response frame has been completely transmitted, 
          // and a non-STBC CTS has to be transmitted (ap = 1 and dualRespNeeded = 1 and rxSTBC != 0 and expectedResp == RESP_TYPE_CTS),
          // the state machine moves to TX_RESP state. 
          // Note that the dual CTS response only applies to the AP; a non-AP STA shall respond to a RTS request with a single CTS.
          macControllerRxFSMNs = CHECK_MEDIUM; 
        else if (ap && dualRespNeeded && (rxSTBC != 2'b00))
          //$fsm_t When txDone_p is received meaning that the STBC response frame has been completely transmitted, 
          // and a non-STBC CFEND has to be transmitted (ap = 1 and dualRespNeeded = 1 and rxSTBC != 0),
          // the state machine moves to TX_RESP state. 
          // Note that the dual CFEND response only applies to the AP; a non-AP STA shall not respond to a CFEND.
          macControllerRxFSMNs = TX_RESP; 
        else  
          //$fsm_t When txDone_p is received meaning that the STBC response frame has been completely transmitted, 
          // and a non-STBC CTS/CFEND transmission is not required, the state machine moves to IDLE state.
          macControllerRxFSMNs = IDLE; 
      else
        //$fsm_t While txDone_p is not received, the state machine stays in TX_STBC_RESP state.
        macControllerRxFSMNs = TX_STBC_RESP;

    RX_WAIT_END:
      //$fsm_s In RX_WAIT_END state, the state machine waits for the completion of the reception 
      // This state is reached only when the frame which is receiving does not expect response.
      // In case of correctRcved (FCS OK), the FSM waits for rxEndOfFrame_p
      // In case of incorrectRcved (FCS ERROR), the FSM waits for the completion of the MACPHY RX FIFO flush (macPhyIfRxFlush_p)
      // In case of macPhyIfRxErr_p, the FSM moves to IDLE.
      if ((correctRcved && rxEndOfFrame) || (incorrectRcved && macPhyIfRxFlush) || macPhyIfRxErr_p)
        //$fsm_t When incorrectRcved_p or correctRcved_p is received meaning that the frame a been completely receive., 
        //the state machine moves to IDLE state.
        macControllerRxFSMNs = IDLE; 
      else
        //$fsm_t While incorrectRcved_p or correctRcved_p are not received, the state machine stays in RX_WAIT_END state.
        macControllerRxFSMNs = RX_WAIT_END;

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
     default:   
        macControllerRxFSMNs = IDLE; 
    // pragma coverage block = on 
  endcase
end


// Generates a flag when the receiving a frame expecting a response is received.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    frameExpectingResp <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    frameExpectingResp <= 1'b0; 
  else
  begin
    if (rxAggregation && ((needAckRcved_p || barRcved_p) && !disableBAResp))
        frameExpectingResp <= 1'b1;
    else if (!rxAggregation && 
        ((rtsRcved_p && !disableCTSResp) || 
         (barRcved_p && !disableBAResp) || 
         (needAckRcved_p && !disableACKResp) || 
         (ap && cfEndRcved_p)))
        frameExpectingResp <= 1'b1;
  end
end  

// Generates a flag when a frame is received and does not expect a response.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    frameDontExpectingResp <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    frameDontExpectingResp <= 1'b0; 
  else
  begin
    if (rxAggregation && ampduIncorrectRcved_p)
        frameDontExpectingResp <= 1'b1;
    if (!rxAggregation && 
        (ackRcved_p || 
         ctsRcved_p || 
         (!ap && cfEndRcved_p) || 
         baRcved_p || 
         bcnRcved_p || 
         bcMcRcved_p || 
         notMineRcved_p || 
        (unknownRcved_p && !reservedRcved) || 
         (needAckRcved_p && disableACKResp) || 
         (rtsRcved_p && disableCTSResp)|| 
         (barRcved_p && disableBAResp) || 
         incorrectRcved_p))
        frameDontExpectingResp <= 1'b1;
  end
end  

// Generate a pulse to the MAC Controller Master when the RX Exchange is completed.
assign rxExchangeCompleted_p = ((macControllerRxFSMCs == IDLE) && (macControllerRxFSMPs != IDLE));

// Generates a pulse to start the reception. This pulse is generated when the FSM moves in RX_FRAME or in CHECK_MEDIUM
// assign startRxRxC_p = (((macControllerRxFSMCs == IDLE) && (macControllerRxFSMNs == RX_FRAME)) ||
//                        ((macControllerRxFSMCs == TX_STBC_RESP) && (macControllerRxFSMNs == CHECK_MEDIUM))) ? 1'b1 : 1'b0;

// Generates a pulse to start the reception. This pulse is generated when the FSM moves in CHECK_MEDIUM
assign startRxRxC_p = ((macControllerRxFSMPs == TX_STBC_RESP) && (macControllerRxFSMCs == CHECK_MEDIUM)) ? 1'b1 : 1'b0;

// Generates a pulse to stop the reception. This pulse is generated when the FSM moves in TX_RESP or if a frame is not correctly received. 
// Note that in case of phyErr, the stopRx_p is not generated because already handled by the macPhyIf.
assign stopRxRxC_p  = (((macControllerRxFSMCs == TX_RESP) && (macControllerRxFSMPs != TX_RESP)) || 
                       ((macControllerRxFSMCs == TX_STBC_RESP) && (macControllerRxFSMPs != TX_STBC_RESP)) || 
                       ((macControllerRxFSMPs != IDLE) && !correctRcved && rxEndOfFrame_p)) ? 1'b1 : 1'b0;

// Generates a pulse to launch the response frame rate selection. This pulse is generated when the FSM moves in COMP_DURATION_RESP state.
assign rateUpdateRxC_p = ((macControllerRxFSMPs != COMP_DURATION_RESP) && (macControllerRxFSMCs == COMP_DURATION_RESP)) ? 1'b1 : 1'b0;

//
// RIFS Detection
// These following processes check if another reception after SIFS could be prossible.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxRIFSPossible <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    rxRIFSPossible <= 1'b0; 
  else if (rxVector1Valid_p)  
    rxRIFSPossible <= 1'b1;
  else
    rxRIFSPossible <= 1'b0;
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxRIFSCancelled_p <= 1'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    rxRIFSCancelled_p <= 1'b0; 
  else if (incorrectRcved_p || ampduIncorrectRcved_p || needAckRcved_p)
    rxRIFSCancelled_p <= 1'b1;  
  else if (frameExpectingResp && macHeaderCompleted)
    rxRIFSCancelled_p <= 1'b1;  
end


// RA/TA capture
////////////////////////////

// Destination address assignation
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    destAddrRxC <= 48'b0;
  else if (correctRcved_p)
    destAddrRxC <= rxAddr2;  
  else if (sendCTSRxC_p)
    destAddrRxC[0] <= 1'b0;  
end

// Source address assignation
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    srcAddrRxC <= 48'b0;
  else if (correctRcved_p)
    srcAddrRxC <= rxAddr1;  
end

// Indicates that a error occured during transmission
assign txErr = mpIfTxErr_p || macPHYIFUnderRun;

 
// Duration field update
// In ACK frames, the duration value is the value obtained from the Duration/ID field of the immediately previous data,
// management, PS-Poll, BlockAckReq, or BlockAck frame minus the time, in microseconds, required to
// transmit the ACK frame and its SIFS interval.
// For all CTS frames sent in response to RTS frames, the duration value is the value obtained from the
// Duration field of the immediately previous RTS frame, minus the time, in microseconds, required to
// transmit the CTS frame and its SIFS interval. 
// If the BlockAck frame is sent in response to the BlockAckReq frame, the Duration/ID field value is the
// value obtained from the Duration/ID field of the immediate BlockAckReq frame, minus the time, in
// microseconds, required to transmit the BlockAck frame and its SIFS interval. 
// If the calculated duration includes a fractional microsecond, that value is rounded to the next higher integer.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    durationRxC <= 16'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    durationRxC <= 16'b0; 
  else
  begin
    if (sendACK_p || sendBA_p || sendCTSRxC_p)
    begin
      if (rxFrameDuration > estDuration)
        durationRxC <= rxFrameDuration - estDuration;
      else 
        durationRxC <= 16'b0;
    end    
  end
end  

// Compute the estimated duration of the response frame + SIFS
// If the FSM is in TX_RESP with dualRespNeeded and (rxSTBC != 0) meaning that the second CTS transmission in non-STBC is requested,
//  the estimated duration from the end of the reception to the end of this transmission is
//  SIFS + CTS in STBC duration + PIFS + CTS duration in non-STBC
//
// If the FSM is in TX_STBC_RESP with dualRespNeeded and (rxSTBC != 0) meaning that the first CTS transmission in STBC is requested,
//  the estimated duration from the end of the reception to the end of this transmission is
//  SIFS + CTS in STBC duration
//
// If the FSM is in TX_STBC_RESP with dualRespNeeded and (rxSTBC == 0) meaning that the second CTS transmission in STBC is requested,
//  the estimated duration from the end of the reception to the end of this transmission is
//  SIFS + CTS in non-STBC duration + SIFS + CTS duration in STBC
//
// If the received frame is a legacy rate smaller or equal to 3 (DSSS/CCK modulation), the estimated duration is SIFSB + response
//
// For all the other cases, the estimated duration is timeOnAir of the response + SIFSA
always @*
begin
  if (dualRespNeeded && (rxSTBC != 2'b0) && (macControllerRxFSMCs == TX_RESP))
    estDuration = {8'b0,ctsSTBCDur} + {7'b0,sifsA,1'b0} + timeOnAirMC + {8'b0,slotTime};
  else if (dualRespNeeded && (rxSTBC != 2'b0) && (macControllerRxFSMCs == TX_STBC_RESP))
    estDuration = {8'b0,ctsSTBCDur} + {8'b0,sifsA};
  else if (dualRespNeeded && (rxSTBC == 2'b0) && (macControllerRxFSMCs == TX_STBC_RESP))
    estDuration = timeOnAirMC + {7'b0,sifsA,1'b0} + {8'b0,ctsSTBCDur};
  else if (rxLegRateConv <= 4'd3)
    estDuration = timeOnAirMC + {8'b0,sifsB};
  else  
    estDuration = timeOnAirMC + {8'b0,sifsA};
end


// When the FSM moves to TX_RESP or TX_STBC_RESP and the expected response is CTS,
// the sendCTSRxC_p pulse to trig the TX Controller for CTS transmission is generated
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    sendCTSRxC_p <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    sendCTSRxC_p <= 1'b0; 
  else
    if ((((macControllerRxFSMCs == TX_RESP) && (macControllerRxFSMPs != TX_RESP)) ||
         ((macControllerRxFSMCs == TX_STBC_RESP) && (macControllerRxFSMPs != TX_STBC_RESP))) &&
        (expectedResp == RESP_TYPE_CTS))
      sendCTSRxC_p <= 1'b1; 
    else  
      sendCTSRxC_p <= 1'b0; 
end

// When the FSM moves to TX_RESP or TX_STBC_RESP and the expected response is CFEND,
// the sendCFENDRxC_p pulse to trig the TX Controller for CFEND transmission is generated
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    sendCFENDRxC_p <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    sendCFENDRxC_p <= 1'b0; 
  else
    if ((((macControllerRxFSMCs == TX_RESP) && (macControllerRxFSMPs != TX_RESP)) ||
         ((macControllerRxFSMCs == TX_STBC_RESP) && (macControllerRxFSMPs != TX_STBC_RESP))) &&
        (expectedResp == RESP_TYPE_CFEND))
      sendCFENDRxC_p <= 1'b1; 
    else  
      sendCFENDRxC_p <= 1'b0; 
end

// If the current state is COMP_DURATION_RESP and the next state is TX_RESP or TX_STBC_RESP and the expected response is ACK,
// the sendACK_p pulse is generated
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    sendACK_p <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    sendACK_p <= 1'b0; 
  else
    if (((macControllerRxFSMCs == TX_RESP) || (macControllerRxFSMCs == TX_STBC_RESP)) && 
        (macControllerRxFSMPs == COMP_DURATION_RESP) && 
        (expectedResp == RESP_TYPE_ACK))
      sendACK_p <= 1'b1; 
    else  
      sendACK_p <= 1'b0; 
end

// If the current state is COMP_DURATION_RESP and the next state is TX_RESP or TX_STBC_RESP and the expected response is BLOCK ACK,
// the sendBA_p pulse is generated
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    sendBA_p <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    sendBA_p <= 1'b0; 
  else
    if (((macControllerRxFSMCs == TX_RESP) || (macControllerRxFSMCs == TX_STBC_RESP)) && 
        (macControllerRxFSMPs == COMP_DURATION_RESP) && 
        (expectedResp == RESP_TYPE_BA))
      sendBA_p <= 1'b1; 
    else  
      sendBA_p <= 1'b0; 
end

// All the response are transmitted after SIFS except for the second CTS in dualCTS protection if it is STBC
assign sendOnSIFSRxC = ~sendOnPIFSRxC;

// When the dual Protection is enabled, the second CTS is transmitted after PIFS only if it is STBC
assign sendOnPIFSRxC = ((expectedResp == RESP_TYPE_CTS) && (macControllerRxFSMCs == TX_STBC_RESP) && (rxSTBC == 2'b0)) ? 1'b1 : 1'b0;

assign txResp = ((macControllerRxFSMCs == TX_RESP) || (macControllerRxFSMCs == TX_STBC_RESP)) ? 1'b1 : 1'b0;

assign txRxnRxC = (macControllerRxFSMCs == TX_RESP) || (macControllerRxFSMCs == TX_STBC_RESP);

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    expectedResp <= RESP_TYPE_NONE; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    expectedResp <= RESP_TYPE_NONE; 
  else
  begin
    if (frameDontExpectingResp)
      expectedResp <= RESP_TYPE_NONE; 
    if (!rxAggregation && needAckRcved_p && !disableACKResp)
      expectedResp <= RESP_TYPE_ACK; 
    if (rtsRcved_p && !disableCTSResp && !respBWFail)
      expectedResp <= RESP_TYPE_CTS; 
    if (barRcved_p && !disableBAResp)
      expectedResp <= RESP_TYPE_BA;
    if (rxAggregation && needAckRcved_p && !disableBAResp)
    begin
      if (rxSingleVHTMPDU)
        expectedResp <= RESP_TYPE_ACK;
      else
        expectedResp <= RESP_TYPE_BA;
    end
    if (ap && cfEndRcved_p)
      expectedResp <= RESP_TYPE_CFEND; 
   end
end



// Capture the incorrectRcved_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    incorrectRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    incorrectRcved <= 1'b0; 
  else
  begin
    if (!rxAggregation && incorrectRcved_p)
      incorrectRcved <= 1'b1; 
    if (rxAggregation && ampduIncorrectRcved_p)
      incorrectRcved <= 1'b1; 
  end    
end

// Capture the correctRcved_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    correctRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    correctRcved <= 1'b0; 
  else
  begin
    if (!rxAggregation && correctRcved_p)
      correctRcved <= 1'b1; 
    if (rxAggregation && ampduCorrectRcved_p)
      correctRcved <= 1'b1; 
  end
end

// Capture the probRespRcved_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    probRespRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    probRespRcved <= 1'b0; 
  else
    if (probRespRcved_p)
      probRespRcved <= 1'b1; 
end

// Capture the probRespRcved_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    bcnRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    bcnRcved <= 1'b0; 
  else
    if (bcnRcved_p)
      bcnRcved <= 1'b1; 
end

// Capture the timeOnAirValidMC pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    durationCompEndFlag <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE) || startComputationMCRx_p)  // Synchronous Reset
    durationCompEndFlag <= 1'b0; 
  else
    if (timeOnAirDone_p)
      durationCompEndFlag <= 1'b1; 
end

assign durationCompEnd = durationCompEndFlag && !startComputationMCRx_p && (macControllerRxFSMCs == macControllerRxFSMPs);


// Capture the rxEndOfFrame_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxEndOfFrame <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    rxEndOfFrame <= 1'b0;
  else
    if (rxEndOfFrame_p)
      rxEndOfFrame <= 1'b1;
end

// Capture the macPhyIfRxFlush_p pulse
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPhyIfRxFlush <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    macPhyIfRxFlush <= 1'b0;
  else
    if (macPhyIfRxFlush_p)
      macPhyIfRxFlush <= 1'b1;
end



// This process assignes the response frame length to txRespLength.
always @*
begin
  case (expectedResp)
    RESP_TYPE_ACK    : txRespLength = 16'd14;
    RESP_TYPE_CTS    : txRespLength = 16'd14;
    RESP_TYPE_BA     : txRespLength = 16'd32; // Only Compressed BA is supported
    RESP_TYPE_CFEND  : txRespLength = 16'd14;
    default          : txRespLength = 16'd00;
  endcase
end

// decided if the dual response with STBC is needed
// If as an AP the Frame received is a RTS in HT PPDU and the dualCTS protection is enabled.
// the DUAL CTS transmission is enabled (dualRespNeeded = 1).
// If as an AP the Frame received is a CFEND in HT PPDU and the dualCTS protection is enabled.
// the DUAL CFEND transmission is enabled (dualRespNeeded = 1).
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    dualRespNeeded <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    dualRespNeeded <= 1'b0;
  else
  begin
    if (ap && dualCTSProt && rtsRcved_p && rxFrameIsHT)
      dualRespNeeded <= 1'b1;
    if (ap && dualCTSProt && cfEndRcved_p && rxFrameIsHT)
      dualRespNeeded <= 1'b1;
  end    
end


// Assign rate coming from the Rate Selection module
assign txMCSRxC        = mcsRESP;
assign txLegRateRxC    = (respIsHT) ? 4'b0100 : legRateRESP;  

// Assign HT length
// If the reponse frame is an HT frame (respIsHT == 1'b1), the HT Length takes the txRespLength else it takes the value 0
assign txHTLengthRxC   = (respIsHT) ? txRespLength : 16'b0;  

// If the reponse frame is an non-HT frame (respIsHT == 1'b0), the Legacy Length takes the txRespLength else it takes the 
// legLengthComputed value
assign txLegLengthRxC  = (respIsHT == 1'b0) ? txRespLength[11:0] : {legLengthComputed[11:0]};

assign txSTBCRxC  = (macControllerRxFSMCs == TX_STBC_RESP) ? 2'b1 : 2'b0; //$todo Is STBC = 1 ok?

// Extract and capture the TRQ and NDP Announcement bit from the HT Control Field of the received frame
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    rxTRQ <= 1'b0;
    rxNDPAn <= 1'b0;
  end
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
  begin
    rxTRQ <= 1'b0;
    rxNDPAn <= 1'b0;
  end
  else
    if (macHeaderCompleted && !macHeaderCompleted_ff1)
    begin
      rxTRQ   <= rxHTCtrl[1];
      rxNDPAn <= rxHTCtrl[24];
    end    
end


assign rxFrameIsHT = ((rxFormatMod == HT_MM) || (rxFormatMod == HT_GF) || (rxFormatMod == VHT)) ? 1'b1 : 1'b0; 

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macHeaderCompleted_ff1 <= 1'b0;
  else
    macHeaderCompleted_ff1 <= macHeaderCompleted;
end

// determind if the response should be HT or NON-HT PPDU.
// A control response frame must be carried in an HT PPDU if it responds to a frame that:
//  1.	Contained TRQ = 1 and NDP announcement = 0
//  2.	Was an RTS carried in an HT-PPDU
//  3.	Used STBC, and Dual CTS Protection is enabled
//  4.  Contains an L-SIG Duration value (lSIGTXOPDetected = 1)
// Else, it must be carried in a non-HT PPDU.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    respIsHT <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
     respIsHT <= 1'b0;
  else
    if ((rxTRQ && !rxNDPAn) ||                                          
        ((expectedResp == RESP_TYPE_CTS) &&  rxFrameIsHT == 1'b1) || 
        ((rxSTBC != 2'b0) && dualCTSProt) ||
        lSIGTXOPDetected)
      respIsHT <= 1'b1;
    else
      respIsHT <= 1'b0;
end

// If the response Legacy Rate is 0, the ppduPreTypeMCRx is forced to 1 (NON-HT Long preamble)
assign respTxPreType    = (legRateRESP == 4'b0) ? 1'b1 : rxPreType;    
assign respTxShortGI    = (respIsHT) ? rxShortGI : 1'b0;    
assign respTxNumExtnSS  = 2'b00;
assign respTxAntennaSet = rxAntennaSet;

assign respTxSMMIndex   = 8'h00;
assign respTxFECCoding  = (respIsHT) ? rxFecCoding : 1'b0;
assign respTxNTx        = 3'b0;    //$todo Forced to 0 because always equal to 1 Tx Chain.

// If the response frame is HT-PPDU (respIsHT set), the response Format Modulation is HT-MF (the HT-GF is not supported in transmit)
// else, if the received frame was a NON-HT-DUP-OFDM (rxFormatMod = 1), the response Format Modulation is NON-HT-DUP-OFDM else it is NON-HT
assign respTxFormatMod  = (respIsHT) ? 2'd2 : ((rxFormatMod == NON_HT_DUP_OFDM) || (rxChBW != 2'd0)) ? 2'd1 : 2'd0;

////////////////////////////////////////////////////////////////////////////////
// TX Time Calculation signals assignment
////////////////////////////////////////////////////////////////////////////////

// Delay the timeOnAirValidMC signal of one clock cycle
// This signal is used to detect the rising edge and create /home/blauret/bt_eclipse_workspacethe timeOnAirDone_p pulse.
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



// If a frame is received in HT_MM and the current duration computing is for TXTIME (macControllerRxFSMCs == COMP_DURATION_RX_MM), 
//   the duration is computed on rxHTLength,
// If a frame is received in HT_MM and the current duration computing is for Legacy duration (macControllerRxFSMCs == COMP_DURATION_RX_LEG), 
//   the duration is computed on rxLegLength,
// If a frame containing a TSF (Beacon or ProbResponse) is received (macControllerRxFSMCs == COMP_DURATION_TFS set), 
//   the duration is computed payload length without MAC Header (24 bytes),
// else
//   if the received frame does not expect response (expectedResp == RESP_TYPE_NONE), 
//     the length is set to 14 to enable CTS or ACK duration computing if required
//     (to update the nav in case of not Mine RTS or not Mine PSPOLL)
//   else it is computed on the entire frame length
always @ *
begin
  if (macControllerRxFSMCs == COMP_DURATION_RX_MM)
    ppduLengthMCRx = rxHTLength;
  else if (macControllerRxFSMCs == COMP_DURATION_RX_LEG)
    ppduLengthMCRx = {4'b0,rxLegLength}; 
  else if (macControllerRxFSMCs == COMP_DURATION_TFS)
  begin
    if (rxFrameIsHT)
      ppduLengthMCRx = rxHTLength - 16'd24;
    else
      ppduLengthMCRx = {4'b0,rxLegLength} - 16'd24;
  end      
  else
    ppduLengthMCRx = (expectedResp == RESP_TYPE_NONE) ? 16'd14 : txRespLength;
end

// If the current duration computing is for the TXTIME of the response, ppduBWMCRx takes the bandwidth of the response frame.
// Else it takes the bandwidth of the received frame
always @ *
begin
  if (macControllerRxFSMCs == COMP_DURATION_RESP)
    ppduBWMCRx = txChBWRxC;
  else
    ppduBWMCRx = rxChBW;
end


// If a frame is received in HT_MM and the current duration computing is for TXTIME (macControllerRxFSMCs == COMP_DURATION_RX_MM), 
//   the duration is computed with a HT_MM preamble,
// If a frame is received in HT_MM and the current duration computing is for Legacy duration (macControllerRxFSMCs == COMP_DURATION_RX_LEG), 
//   the duration is computed with a OFDM preamble
// If a frame containing a TSF (Beacon or ProbResponse) is received (macControllerRxFSMCs == COMP_DURATION_TFS), 
//   the ppduPreTypeMCRx takes the preamble Type 0 but this computqation is done without preamble. So it is not used.
// If the frame received was an HT frame (rxFormatMod >=2), ppduPreTypeMCRx takes the rxFormatMod value (MM or GF). Else it takes the 
//   rxPreType value (Long or Short).
// else
//   If the response frame is a NON-HT frame (respTxFormatMod<2), ppduPreTypeMC takes the value of respTxPreType (short or long preamble)
//   else it takes HT-MF value (the HT-GF is not supported in transmit).
always @ *
begin
  if (macControllerRxFSMCs == COMP_DURATION_RX_MM)
    ppduPreTypeMCRx = 3'b010;
  else if (macControllerRxFSMCs == COMP_DURATION_RX_LEG)
    ppduPreTypeMCRx = 3'b000; 
  else if (macControllerRxFSMCs == COMP_DURATION_TFS)
    ppduPreTypeMCRx = (rxFormatMod <= 1) ? {2'b0,rxPreType} : rxFormatMod; 
  else
    ppduPreTypeMCRx = ((respTxFormatMod == NON_HT) || (respTxFormatMod == NON_HT_DUP_OFDM)) ? {2'b0,respTxPreType} : (respTxFormatMod == VHT) ? 3'b100 : 3'b010;
end

// If the current duration computing is for the TXTIME of the response, 
//   ppduNumExtnSSMCRx takes the Number of Extended Spacial Stream of the response frame.
// Else it takes the Number if Extended Spacial Stream of the received frame
always @ *
begin
  if (macControllerRxFSMCs == COMP_DURATION_RESP)
    ppduNumExtnSSMCRx = respTxNumExtnSS;
  else 
    ppduNumExtnSSMCRx = rxNumExtnSS;
end

// If the current duration computing is for the TXTIME of the response, 
//   ppduSTBCMCRx takes 0. (the duration of the STBC response is given by the register ctsSTBCDur
// Else it takes the STBC information of the received frame
always @ *
begin
  if (ap && dualCTSProt && (expectedResp == RESP_TYPE_CTS) && (macControllerRxFSMCs == COMP_DURATION_RESP))
    ppduSTBCMCRx = 2'b0;
  else 
    ppduSTBCMCRx = rxSTBC;
end

// If a frame is received in HT_MM and the current duration computing is for TXTIME (macControllerRxFSMCs == COMP_DURATION_RX_MM), 
//   the duration is computed with the ShortGI of the received frame,
// If a frame is received in HT_MM and the current duration computing is for Legacy duration (macControllerRxFSMCs == COMP_DURATION_RX_LEG), 
//   the duration is computed without ShortGI
// If a frame containing a TSF (Beacon or ProbResponse) is received (macControllerRxFSMCs == COMP_DURATION_TFS), 
//   the duration is computed with the ShortGI of the received frame,
// else
//   If the response frame is an HT Frame, ppduShortGIMCRx takes the value of respTxShortGI (short or normal Guard interval)
//   else the Guard Interval is forced to 0 (Normal GI)
always @ *
begin
  if (macControllerRxFSMCs == COMP_DURATION_RX_MM)
    ppduShortGIMCRx = rxShortGI;
  else if (macControllerRxFSMCs == COMP_DURATION_RX_LEG)
    ppduShortGIMCRx = 1'b0; 
  else if (macControllerRxFSMCs == COMP_DURATION_TFS)
    ppduShortGIMCRx = rxShortGI;
  else 
    ppduShortGIMCRx = (respTxFormatMod >= 3'd2) ? respTxShortGI : 1'b0;
end

// If a frame is received in HT_MM and the current duration computing is for TXTIME (macControllerRxFSMCs == COMP_DURATION_RX_MM), 
//   the duration is computed with the received MCS
// If a frame is received in HT_MM and the current duration computing is for Legacy duration (macControllerRxFSMCs == COMP_DURATION_RX_LEG), 
//   the duration is computed with the received LegRate
// If a frame containing a TSF (Beacon or ProbResponse) is received (macControllerRxFSMCs == COMP_DURATION_TFS), 
//   If the frame received was an HT frame (rxFrameIsHT >=2), ppduMCSIndexMC takes the rxMCS value (HT Rate).
//   else it takes the rxLegRateConv value (non-HT rate).
// else
//   If the response is an HT frame (respTxFormatMod >=2), ppduMCSIndexMC takes the mcsRESP value (HT Rate). 
//   else it takes the legRateRESP value (non-HT rate).
always @ *
begin
  if (macControllerRxFSMCs == COMP_DURATION_RX_MM)
    ppduMCSIndexMCRx = {1'b1,rxMCS};
  else if (macControllerRxFSMCs == COMP_DURATION_RX_LEG)
    ppduMCSIndexMCRx = {4'b0, rxLegRateConv}; 
  else if (macControllerRxFSMCs == COMP_DURATION_TFS)
    ppduMCSIndexMCRx = (rxFrameIsHT) ? {1'b1, rxMCS} : {4'b0, rxLegRateConv};
  else
    ppduMCSIndexMCRx = (respTxFormatMod >= 3'd2) ? {1'b1,mcsRESP} : {4'b0,legRateRESP};
end

// Indicates to the TX Time Computing that the duration has to be computed without preamble duration.
// This is the case for the MAC Header duration and for Legacy Duration.
assign woPreambleMCRx = ((macControllerRxFSMCs == COMP_DURATION_TFS) || (macControllerRxFSMCs == COMP_DURATION_RX_LEG)) ? 1'b1 : 1'b0;


// When the FSM moves to COMP_DURATION_RESP or COMP_DURATION_TFS, the macControllerRx launches a time on air computation to the TX TIME Module.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    startComputationMCRx_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    startComputationMCRx_p <= 1'b0; 
  else if (((macControllerRxFSMCs != macControllerRxFSMPs) && 
           ((macControllerRxFSMCs == COMP_DURATION_RESP) || 
            (macControllerRxFSMCs == COMP_DURATION_RX_MM) || 
            (macControllerRxFSMCs == COMP_DURATION_RX_LEG) || 
            (macControllerRxFSMCs == COMP_DURATION_TFS))))
    startComputationMCRx_p <= 1'b1;
  else   
    startComputationMCRx_p <= 1'b0;
end

////////////////////////////////////////////////////////////////////////////////
// L-SIG Length and Duration 
////////////////////////////////////////////////////////////////////////////////

// L_LENGTH (legLengthComputed) and L_DATARATE determine the duration that non-HT STAs will not transmit, equal to the
// remaining duration of the HT PPDU or the L-SIG Duration when L-SIG TXOP protection is used as defined
// in 9.13.5, following the non-HT portion of the preamble of the HT-mixed format PPDU.
//
// The L_DATARATE parameter of the TXVECTOR shall be set to the value 6 Mb/s.
//
// A STA that is transmitting a PPDU with the FORMAT parameter of the TXVECTOR set to HT_MF, and that
// is n
// parameter to the value (in units of octets) given by Equation (9-1) :
//
// L_LENGTH = ((TXTIME - Signal Extension) - (aPreambleLength + aPLCPHeaderLength))*NOPS/aSymbolLength - (aPLCPServiceLength + aPLCPConvolutionalTailLength)/8
// 
//
// A STA that is transmitting a PPDU with the FORMAT parameter of the TXVECTOR set to HT_MF, and that
// is not operating by the L-SIG TXOP protection rules described in 9.13.5 (lSIGTXOPDetected = 1) shall set the value of the L_LENGTH
// parameter to the value (in units of octets) given by Equation (9-1) :
//
// L_LENGTH (legLengthComputed) = (lSIGDuration - signalExtension) * NOPS/aSymbolLength - (aPLCPServiceLength + aPLCPConvolutionalTailLength)/8 
//
// where :
//   NOPS is the number of octets transmitted during a period of aSymbolLength at
//        the rate specified by L_DATARATE
// 
//   aPLCPServiceLength is the number of bits in the PLCP SERVICE field (16 bits)
//                     
//   aPLCPConvolutionalTailLength is the number of bits in the convolutional code tail bit sequence (6 bits)
//   
//   aSymbolLength is the duration of symbol, 4us
//
// if  (lSIGTXOPDetected = 0)
// legLengthComputed = (TXTIME - signalExtension - 20)*3/4 - 3
// 
// if  (lSIGTXOPDetected = 1)
// legLengthComputed = (lSIGDuration - signalExtension)*3/4 - 3
//
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    legLengthComputed <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    legLengthComputed <= 16'b0;
  else
    if ((respTxFormatMod == HT_MM) || (respTxFormatMod == VHT))
    begin
      if (lSIGTXOPDetected)
      begin
        if (lSIGDurationInt[1:0] != 2'b0)
          // if lSIGDurationInt[1:0] !=0, the rounding is done by adding 3. So, the -3 disappears
          legLengthComputed <= {1'b0,lSIGDurationInt[15:2],1'b0} + {2'b0,lSIGDurationInt[15:2]}; 
        else  
          legLengthComputed <= {1'b0,lSIGDurationInt[15:2],1'b0} + {2'b0,lSIGDurationInt[15:2]} - 16'd3;
      end
      else if ((macControllerRxFSMCs == TX_STBC_RESP) || (macControllerRxFSMCs == TX_RESP))
      begin
        if (txTimeInt[1:0] != 2'b0)
          // if txTimeInt[1:0] !=0, the rounding is done by adding 3. So, the -3 disappears
          legLengthComputed <= {1'b0,txTimeInt[15:2],1'b0} + {2'b0,txTimeInt[15:2]};
        else  
          legLengthComputed <= {1'b0,txTimeInt[15:2],1'b0} + {2'b0,txTimeInt[15:2]} - 16'd3;
      end    
    end
    else    
      legLengthComputed <= 16'b0;
end

// txTimeInt is the result of (TXTIME - signalExtension - 20)
// It is used in the previous process to compute the L_LENGTH for the response
// In case of STBC Response, timeOnAir is replaced by ctsSTBCDur from register.
assign txTimeInt       = ((macControllerRxFSMCs == TX_STBC_RESP) && (ap && dualCTSProt && (expectedResp == RESP_TYPE_CTS))) ? 
                          ({8'd0,ctsSTBCDur} - 16'd20) : 
                          (timeOnAirMC - {13'd0,signalExtension} - 16'd20);

// lSIGDurationInt is the result of (lSIGDuration - signalExtension)
// It is used in the previous process to compute the L_LENGTH for the response
assign lSIGDurationInt = lSIGDuration - {13'd0,signalExtension};

// 9.13.5.3 L-SIG TXOP protection rules at the TXOP responder
// On receiving a PPDU containing an L-SIG Duration addressed to itself, a TXOP responder that set the L-SIG
// TXOP Protection Support field to 1 on association shall generate an L-SIG TXOP Protection response frame
// with the L-SIG Duration equivalent to:
//  L-SIG Duration = (TMACDur - SIFS - (aPreambleLength + aPLCPHeaderLength))
//
// where :
//   TMACDur is the Duration/ID value carried in the MAC Header of frame(s) received in the PPDU that
//   generated the response
//   aPreambleLength +  aPLCPHeaderLength = 20 us
//
// If the rxFrameDuration is smaller or equal to SIFS + (aPreambleLength + aPLCPHeaderLength), the lSIGDuration is forced to 0
assign lSIGDuration = (rxFrameDuration > {8'b0,sifsA} + 16'd20) ? (rxFrameDuration - {8'b0,sifsA} - 16'd20) : 16'b0; //$todo DualCTS case to be handled

// Set lSIGTXOPDetected when a L_SIG TXOP is detected on the received frame.
// A LSIG TXOP is detected when the  duration value determined from the L_DATARATE 
// and L_LENGTH parameters rounded up to a multiple of aSymbolLength that is not equal to the 
// remaining duration of the frame
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    lSIGTXOPDetected <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    lSIGTXOPDetected <= 1'b0;
  else
  begin
    if ((macControllerRxFSMCs == RX_FRAME) && lsigCheckDone)
    begin
//       if (rxLSIGValid && (rxFrameHTDuration < (rxFrameLegDuration+16'd15)))
      if (supportLSTP && rxLSIGValid && (rxFrameHTDuration < rxFrameLegDuration))
      begin
        lSIGTXOPDetected <= 1'b1;
      end
      else
        lSIGTXOPDetected <= 1'b0;
    end    
  end    
end

// Captured the computed Duration based on received L_DATARATE 
// and L_LENGTH parameters.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxFrameLegDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    rxFrameLegDuration <= 16'b0;
  else
  begin
    if ((macControllerRxFSMCs == COMP_DURATION_RX_LEG) && timeOnAirDone_p)
        rxFrameLegDuration <= timeOnAirMC;
  end    
end

// Captured the computed Duration based on received HT_DATARATE 
// and HT_LENGTH parameters.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxFrameHTDuration <= 16'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    rxFrameHTDuration <= 16'b0;
  else
  begin
    if ((macControllerRxFSMCs == COMP_DURATION_RX_MM) && timeOnAirDone_p)
        rxFrameHTDuration <= timeOnAirMC;
  end    
end

// Captured the computed Duration based on received HT_DATARATE 
// and HT_LENGTH parameters.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    lsigCheckDone <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    lsigCheckDone <= 1'b0;
  else
  begin
    if ((macControllerRxFSMCs == COMP_DURATION_RX_MM) && timeOnAirValidMC)
        lsigCheckDone <= 1'b1;
  end    
end


assign signalExtension   = 3'd0; //$todo 0 in a mode. 6 in bg mode if SIFS is 10us else 0

////////////////////////////////////////////////////////////////////////////////
// NAV Interface control
////////////////////////////////////////////////////////////////////////////////

// PSPoll Reception capture
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    notMinePsPollRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    notMinePsPollRcved <= 1'b0; 
  else
  begin
    if (notMinePsPollRcved_p)
      notMinePsPollRcved<= 1'b1; 
  end
end  

// RTS Reception capture
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    notMineRtsRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    notMineRtsRcved <= 1'b0; 
  else
  begin
    if (notMineRtsRcved_p)
      notMineRtsRcved<= 1'b1; 
  end
end  

// Beacon/Prob Response Reception capture
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    tsfRcved <= 1'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    tsfRcved <= 1'b0; 
  else
  begin
    if (bcnRcved_p || probRespRcved_p)
      tsfRcved<= 1'b1; 
    else if (macControllerRxFSMCs == COMP_DURATION_RESP)  
      tsfRcved<= 1'b0; 
  end
end  

// Provide duration information to the NAV block in case of incorrect reception.
assign ctsDuration         = timeOnAirMC;
assign ctsDurationValid_p  = (notMineRtsRcved && timeOnAirValidMC) ? 1'b1 : 1'b0; 
assign ackDuration         = timeOnAirMC;        
assign ackDurationValid_p  = (notMinePsPollRcved && timeOnAirValidMC) ? 1'b1 : 1'b0;

// Compute LSIG Duration for NAV in case of HT_MM with FCS error.
// navLsigDuration  = Legacy frame duration - HT frame duration + Legacy preamble duration
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    navLsigDuration <= 16'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    navLsigDuration <= 16'b0; 
  else
    if ((macControllerRxFSMNs == RX_FRAME) && (macControllerRxFSMCs == COMP_DURATION_RX_MM))
      navLsigDuration <= rxFrameLegDuration - timeOnAirMC + 16'd20;
end


// Provide duration from the end of the MAC Header until the end of the received Beacon or Prob Response frame.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    frmDurWithoutMH <= 16'b0; 
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    frmDurWithoutMH <= 16'b0; 
  else
  begin
    if ((macControllerRxFSMCs == COMP_DURATION_TFS) && timeOnAirDone_p)
      frmDurWithoutMH <= timeOnAirMC; 
  end
end  



// Assign phyRxStartDelay duration based on the preamble type of the received frame.
// This signal is valid on ctsDurationValid_p pulse and indicates the PHY Start delay of the expected CTS
always @ *
begin
  if (rxFrameIsHT)
    phyRxStartDelay = rxStartDelayMIMO;
  else if (rxLegRateConv > 4'd3)
    phyRxStartDelay = rxStartDelayOFDM;
  else if (rxPreType)
    phyRxStartDelay = rxStartDelayLong;
  else  
    phyRxStartDelay = rxStartDelayShort;
end


////////////////////////////////////////////////////////////////////////////////
// Dynamic Bandwidth Support
////////////////////////////////////////////////////////////////////////////////

//  A VHT STA that is addressed by an RTS frame in a non-HT or non-HT duplicate PPDU that has a bandwidth
//  signaling TA and that has the RXVECTOR parameter DYN_BANDWIDTH_IN_NON_HT equal to Static,
//  behaves as follows:
//  - If the NAV indicates idle and CCA has been idle for all secondary channels (secondary 20 MHz
//  channel, secondary 40 MHz channel and secondary 80 MHz channel) in the channel width indicated
//  by the RTS frame's RXVECTOR parameter CH_BANDWIDTH_IN_NON_HT for a PIFS period
//  prior to the start of the RTS frame, then the STA shall respond with a CTS frame carried in a non-HT
//  or non-HT duplicate PPDU after a SIFS period. The CTS frame's TXVECTOR parameters
//  CH_BANDWIDTH and CH_BANDWIDTH_IN_NON_HT shall be set to the same value as the
//  RTS frame's RXVECTOR parameter CH_BANDWIDTH_IN_NON_HT.
//  - Otherwise the STA shall not respond with a CTS frame.
//
//  A VHT STA that is addressed by an RTS frame in a non-HT or non-HT duplicate PPDU that has a bandwidth
//  signaling TA and that has the RXVECTOR parameter DYN_BANDWIDTH_IN_NON_HT equal to Dynamic,
//  behaves as follows:
//   - If the NAV indicates idle, then the STA shall respond with a CTS frame in a non-HT or non-HT
//  duplicate PPDU after a SIFS period. The CTS frame's TXVECTOR parameters CH_BANDWIDTH
//  and CH_BANDWIDTH_IN_NON_HT may be set to any channel width for which CCA on all secondary
//  channels has been idle for a PIFS prior to the start of the RTS frame and that is equal to or
//  less than the channel width indicated in the RTS frame's RXVECTOR parameter
//  CH_BANDWIDTH_IN_NON_HT.
//    - Otherwise the STA shall not respond with a CTS frame.
//
//  A non-VHT STA that is addressed by an RTS frame or a VHT STA that is addressed by an RTS frame carried
//  in a non-HT or non-HT duplicate PPDU that has a non-bandwidth signaling TA or a VHT STA that is addressed
//  by an RTS frame in a format other than non-HT or non-HT duplicate behaves as follows:
//    - If the NAV indicates idle, the STA shall respond with a CTS frame after a SIFS period.
//    - Otherwise, the STA shall not respond with a CTS frame

// This process computes the bandwith of the response in case of DYN_BANDWIDTH_IN_NON_HT equal to Dynamic
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txChBWInt <= 2'd0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    txChBWInt <= 2'd0;
  else if (dynBWEn)
  begin  
    if (rxBWSignalingTA && correctRcved_p)
    begin
      if (rxDynBW)
      begin
        if (availableBW < rxChBWInNonHT) 
          txChBWInt <= availableBW;
        else
          txChBWInt <= rxChBWInNonHT;
      end
      else
        txChBWInt  <= rxChBWInNonHT;   
    end
    else if (correctRcved_p)
      txChBWInt  <= rxChBW;   
  end
  else if (correctRcved_p)
    txChBWInt  <= rxChBW;   
end

// It may occur that the received frame was VHT 80MHz but the response fram eis HT.
// In this case, the BW of the response frame shall be limited to 40MHz.
assign txChBWRxC = (respTxFormatMod >= 2'd2 && txChBWInt >= 2'd2) ? 2'b1 : txChBWInt;

// Check if the dynamic bandwidth selection fails in case of DYN_BANDWIDTH_IN_NON_HT equal to Static
// It fails if the bandwidth available is lower than the requested (availableBW < rxChBW)
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    respBWFail <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (macControllerRxFSMCs == IDLE))  // Synchronous Reset
    respBWFail <= 1'b0;
  else if (dynBWEn)
  begin  
    if (correctRcved_p)
    begin
      if (rxBWSignalingTA && !rxDynBW && (availableBW < rxChBWInNonHT)) 
        respBWFail <= 1'b1;
      else
        respBWFail <= 1'b0;
    end
  end
end


assign txBWSignalingRxC = (!respBWFail) ? rxBWSignalingTA : 1'b0;

// If the BW Signaling is used for the current reception (in this case, RTS reception), the flag rxDynBW coming from the rxVector is 
// provided to the Tx Controller 
assign txDynBWRxC = (txBWSignalingRxC) ? rxDynBW : 1'b0;

////////////////////////////////////////////////////////////////////////////////
// debug Port
////////////////////////////////////////////////////////////////////////////////
assign debugPortMACControllerRx = {rxFormatMod[2] || rxFormatMod[1],
                                   respIsHT,
                                   lSIGTXOPDetected,
                                   tsfRcved,
                                   (rxTRQ && !rxNDPAn),
                                   rxSTBC,
                                   rxShortGI,
                                   correctRcved,
                                   incorrectRcved,
                                   expectedResp[1:0],
                                   sendBA_p,
                                   sendACK_p,
                                   sendCFENDRxC_p,
                                   rxAggregation};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
// Disable coverage.
// pragma coverage block = off 
// macControllerRxFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (macControllerRxFSMCs)
                 IDLE  :  macControllerRxFSMCs_str = {"IDLE"};
             RX_FRAME  :  macControllerRxFSMCs_str = {"RX_FRAME"};
 COMP_DURATION_RX_LEG  :  macControllerRxFSMCs_str = {"COMP_DURATION_RX_LEG"};
  COMP_DURATION_RX_MM  :  macControllerRxFSMCs_str = {"COMP_DURATION_RX_MM"};
   COMP_DURATION_RESP  :  macControllerRxFSMCs_str = {"COMP_DURATION_RESP"};
    COMP_DURATION_TFS  :  macControllerRxFSMCs_str = {"COMP_DURATION_TFS"};
          RX_WAIT_END  :  macControllerRxFSMCs_str = {"RX_WAIT_END"};
              TX_RESP  :  macControllerRxFSMCs_str = {"TX_RESP"};
         CHECK_MEDIUM  :  macControllerRxFSMCs_str = {"CHECK_MEDIUM"};
         TX_STBC_RESP  :  macControllerRxFSMCs_str = {"TX_STBC_RESP"};
              default  :  macControllerRxFSMCs_str = {"XXX"};
   endcase
end

//  expected Response displayed in a string to easy simulation and debug
always @*
begin
  case (expectedResp)
      RESP_TYPE_ACK : expectedResp_str = {"RESP_TYPE_ACK  "};
      RESP_TYPE_CTS : expectedResp_str = {"RESP_TYPE_CTS  "};
       RESP_TYPE_BA : expectedResp_str = {"RESP_TYPE_BA   "};
    RESP_TYPE_CFEND : expectedResp_str = {"RESP_TYPE_CFEND"};
            default : expectedResp_str = {"RESP_TYPE_NONE "};
  endcase
end

//  respTxFormatMod displayed in a string to easy simulation and debug
always @*
begin
  case (respTxFormatMod)
               NON_HT : respTxFormatMod_str = {"NON-HT"};
      NON_HT_DUP_OFDM : respTxFormatMod_str = {"NON-HT-DUP-OFDM"};
                HT_MM : respTxFormatMod_str = {"HT-MM"};
                HT_GF : respTxFormatMod_str = {"HT-GF"};
                  VHT : respTxFormatMod_str = {"VHT"};
              default : respTxFormatMod_str = {"XXX"};
  endcase
end

// pragma coverage block = on 
`endif // RW_SIMU_ON


`ifdef RW_ASSERT_ON

// System Verilog Assertions
////////////////////////////

// $rw_sva Checks if a STA does not transmit a PPDU with the FORMAT parameter set to HT_MF in TXVECTOR if the corresponding
// L_LENGTH value calculated exceeds 4095 octets.(LSIG Duration > 5468 us)
property maxLLenghtCheck_prop;
@(posedge macCoreClk)
    (((rxFormatMod == HT_MM) || (rxFormatMod == VHT)) && (sendACK_p || sendBA_p || sendCTSRxC_p)) |-> lSIGDuration <= 5468;
endproperty
maxLLenghtCheck: assert property (maxLLenghtCheck_prop); 


// Cover Points Definitions
///////////////////////////

//$rw_sva This cover point checks if we have received a RTS Frame
countRTSReceivedFrame: cover property (@(posedge macCoreClk) (rtsRcved_p));

//$rw_sva This cover point checks if we have received a Block Ack Request
countBAReqReceivedFrame: cover property (@(posedge macCoreClk) (barRcved_p));

//$rw_sva This cover point checks if we have received a frame which requires a acknowledgement
countneedAckReceivedFrame: cover property (@(posedge macCoreClk) (needAckRcved_p));

//$rw_sva This cover point checks if we have received a ACK
countACKReceivedFrame: cover property (@(posedge macCoreClk) (ackRcved_p));

//$rw_sva This cover point checks if we have received a CTS
countCTSReceivedFrame: cover property (@(posedge macCoreClk) (ctsRcved_p));

//$rw_sva This cover point checks if we have received a CF-END
countCFENDReceivedFrame: cover property (@(posedge macCoreClk) (cfEndRcved_p));

//$rw_sva This cover point checks if we have received a Block ACK
countBAReceivedFrame: cover property (@(posedge macCoreClk) (baRcved_p));

//$rw_sva This cover point checks if we have received a Beacon
countBCNReceivedFrame: cover property (@(posedge macCoreClk) (bcnRcved_p));

//$rw_sva This cover point checks if we have received a Prob Response
countProbRespReceivedFrame: cover property (@(posedge macCoreClk) (probRespRcved_p));

//$rw_sva This cover point checks if we have received a Broadcast/Multicast frame
countBcMcReceivedFrame: cover property (@(posedge macCoreClk) (bcMcRcved_p));

//$rw_sva This cover point checks if we have received a notMine frame
countnotMineReceivedFrame: cover property (@(posedge macCoreClk) (notMineRcved_p));

//$rw_sva This cover point checks if we have received a notMine PsPoll frame
countnotMinePsPollReceivedFrame: cover property (@(posedge macCoreClk) (notMinePsPollRcved_p));

//$rw_sva This cover point checks if we have received a notMine RTS frame
countnotMineRTSReceivedFrame: cover property (@(posedge macCoreClk) (notMineRtsRcved_p));

//$rw_sva This cover point checks if we have received an unknown frame
countunknownReceivedFrame: cover property (@(posedge macCoreClk) (unknownRcved_p));

//$rw_sva This cover point checks if we have received an A-MPDU 
countAMPDUReceivedFrame: cover property (@(posedge macCoreClk) (ampduCorrectRcved_p || ampduIncorrectRcved_p));

//$rw_sva This cover point checks if we have received an A-MPDU and a BA has been transmitted 
countBAResponseToAMPDU: cover property (@(posedge sendBA_p) (rxAggregation));

//$rw_sva This cover point checks if a response frame has been transmitted in HT-MM formatMod
countHTMMRespFrame: cover property (@(posedge macCoreClk) ((sendCTSRxC_p || sendACK_p || sendBA_p || sendCFENDRxC_p) && (respTxFormatMod == HT_MM)));

//$rw_sva This cover point checks if a response frame has been transmitted in HT-GF formatMod
countHTGFRespFrame: cover property (@(posedge macCoreClk) ((sendCTSRxC_p || sendACK_p || sendBA_p || sendCFENDRxC_p) && (respTxFormatMod == HT_GF)));

//$rw_sva This cover point checks if a response frame has been transmitted in VHT formatMod
countVHTRespFrame: cover property (@(posedge macCoreClk) ((sendCTSRxC_p || sendACK_p || sendBA_p || sendCFENDRxC_p) && (respTxFormatMod == VHT)));

//$rw_sva This cover point checks if a CFEND response frame has been transmitted in STBC mode as an AP
countCFENDSTBCRespFrameAsAP: cover property (@(posedge sendCFENDRxC_p) (txSTBCRxC != 0));

//$rw_sva This cover point checks if a CTS response frame has been transmitted in STBC mode as an AP
countCTSSTBCRespFrameAsAP: cover property (@(posedge macCoreClk) (ap && sendCTSRxC_p && (rxSTBC != 0)));

//$rw_sva This cover point checks if a CTS response frame has been transmitted in STBC mode as a STA
countCTSSTBCRespFrameAsSTA: cover property (@(posedge macCoreClk) (!ap && sendCTSRxC_p && (rxSTBC != 0)));

//$rw_sva This cover point checks if a BA frame has been transmitted in STBC mode
countBASTBCRespFrame: cover property (@(posedge sendBA_p) (rxSTBC != 0));

//$rw_sva This cover point checks if an ACK frame has been transmitted in STBC mode
countACKSTBCRespFrame: cover property (@(posedge sendACK_p) (rxSTBC != 0));

//$rw_sva This cover point checks if an CTS frame has been transmitted in STBC mode after PIFS
countCTSSTBCSendOnPIFS: cover property (@(posedge sendCTSRxC_p) (sendOnPIFSRxC));

//$rw_sva This cover point checks if the CCA was raised during PIFS in case of dual CTS protection
countDualCTSResponseAbortedDuringPIFS: cover property (@(posedge macCoreClk) ((macControllerRxFSMCs == CHECK_MEDIUM) && macPhyIfRxCca));

//$rw_sva This cover point checks if an LSIG TXOP has been detected and a response transmitted
countLSIGTXOPWithResponse: cover property (@(posedge txDone_p) (lSIGTXOPDetected));


`endif // RW_ASSERT_ON


endmodule