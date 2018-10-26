//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author: $
// Company: RivieraWaves
//----------------------------------------------------------------------------
// $Revision: $
// $Date: $
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : Module which creates and formats the MPDU frames. 
//                    
// Simulation Notes : 
//                    
//    For simulation, one define is available
//
//    RW_SIMU_ON   : which creates string signals to display the FSM states on  
//                the waveform viewers
//
// Some pragmas for code coverage have been defined.
//  - The implicite default state has been excluded
//  - The some default states have been excluded because not reachable by design
// pragma coverage implicit_default=off 
//
// Synthesis Notes  :
// Application Note :                                                       
// Simulator        :                                                       
// Parameters       :                                                       
// Terms & concepts :                                                       
// Bugs             :                                                       
// Open issues and future enhancements : 
//   This version does not include yet the optimization found if the two first 
//   byte of the MAC Header Descriptor which are marked as "Reserved" are not 
//   provided by the txFIFO. This modification requires a change in the DMA 
//   Engine
//   
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//module txController (
module formatMPDU (
          //$port_g Clock and Reset interface
          input  wire        macCoreTxClk,          // MAC Core Transmit Clock
          input  wire        macCoreClkHardRst_n,   // Hard Reset of the MAC Core Clock domain 
                                                    // active low
          input  wire        macCoreTxClkSoftRst_n, // Soft Reset of the MAC Core Clock domain 
                                                    // active low
          //$port_g MAC Controller interface
          input  wire        skipMPDU_p,            // Indication that MPDU in TX FIFO has to be discarded
          input  wire [15:0] duration,              // Duration
          input  wire        retry,                 // Retry Bit
          input  wire [15:0] tsfDuration,           // Duration from the preamble until the first bit of TSF
          input  wire        sendOnSIFS,            // If set, data is sent on tickSIFS else on tickSlot
          output reg   [3:0] txTID,                 // TID of the transmitted frame
          output reg   [1:0] typeTx,                // TYPE of the transmitted frame
          output reg         typeTxValid,           // Indicates the typeTx signal is valid
          output reg         txAMSDUPresent,        // Indicates than the transmitted frame is an A-MSDU
          output reg         txBcMc,                // Indicates than the transmitted frame has a group address.
          output reg         sentCFEND,             // Indicates that the transmitted frame is a CF-END
          output reg         sentRTS,               // Indicates that the transmitted frame is a RTS
          output reg         sentBAReq,             // Indicates that the transmitted frame is a BA-Request
          output reg         skipMPDUDone_p,        // Indicates that MPDU contained in the TXFIFO has been discarded.

          //$port_g MAC-PHY-IF Block interface
          input  wire        mpIfTxEn,              // Transmit on-going indication 

          //$port_g Tx Controller Main FSM interface
          input  wire        sendMPDU_p,            // Indicates that a DATA packet has to be sent
          output reg         mpduDone_p,            // Indicates that the DATA packet has been sent
          output wire        mpduTxStart_p,         // Indicates to the MAC PHY IF that the TX start
          
          //$port_g Tx Parameters Cache interface
          input  wire [15:0] MPDUFrameLengthTx,     // Gives the length of the MPDU.
          input  wire        useRIFSTx,             // Use RIFS for Transmission
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

          //$port_g Tx FIFO interface
          input  wire        txFIFOEmpty,           // Indicates that a TX FIFO is empty
          input  wire  [7:0] txFIFORdData,          // Read data from TX FIFO
          input  wire  [1:0] txFIFOMPDUDelimiters,  // MPDU delimiter coming from the TX Tag FIFO
          input  wire        txFIFODataValid,       // Indicates when the txFIFORdData is Valid

          output wire        txFIFORead,            // Read data request from TX FIFO
          output wire        txFIFOReadByFour,      // Read data by four bytes
          output wire        txFIFOReadByTwo,       // Read data by two bytes

          //$port_g Key Search Engine interface
          input  wire  [2:0] cTypeRAM,              // Indicates the type of encryption
                                                    // 0 : No Key
                                                    // 1 : WEP
                                                    // 2 : TKIP
                                                    // 3 : CCMP

          //$port_g TxVector Interface
          input  wire  [2:0] formatMod,             // 3'b000: NON-HT
                                                    // 3'b001: NON-HT-DUP-OFDM
                                                    // 3'b010: HT-MF
                                                    // 3'b011: HT-GF
                                                    // 3'b100: VHT

          //$port_g Encryption Engine interface
          // Shared by all encrypt mode
          output wire        txCsIsIdle,            // Indicates the FSM is out of IDLE
          output reg  [15:0] txDataLength,          // Indicate the Tx Data to encrypted Length
          output reg         txCryptoKeyValid,      // Indicate that the key is valid
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
          output reg         txWEP,                 // WEP Mode
          output reg [23:0]  txWEPIV,               // WEP IV
          output reg         txWEPIVValid,          // Validating WEP IV 

          // TKIP Only
          output reg         txTKIP,                // TKIP Mode

          // CCMP Only
          input  wire        txCCMPBusy,            // High when aes is processing on Data
          input  wire        txCCMPMicDone,         // Get Mic Calculation Done
          output reg         txCCMP,                // CCMP Mode
          output wire        txCCMPStart,           // Start Data CCMP encrypt
          output wire        txCCMPHeaderValid,     // Plain Data is MAC Header
          output wire        txCCMPDataValid,       // Plain Data is Valid for CCMP ADD + Nonce + Data
          output wire        txCCMPAdd4Pres,        // Address 4 is present
          output wire        txCCMPQoSPres,         // Frame is QoS
          output reg  [47:0] txCCMPAddr1,           // Address 1 Value
          output reg  [47:0] txCCMPAddr2,           // Address 2 Value
          output reg         txCCMPHT,              // Indicate HT mode for CCMP
          
`ifdef RW_WAPI_EN
          // WAPI Only
          output reg         txWAPI,                // WAPI Mode
          output wire        txWAPIStart,           // Start Data WAPI encrypt
          input wire         txWAPIMicDone,         // Get WAPI Mic Calculation Done
          input  wire        txWAPIBusy,            // High when wpi is processing data
          
          output reg [15:0]  txWAPIFrameControl,    // MAC Header Frame Control Field
          output reg [47:0]  txWAPIAddr3,           // MAC Header Address 3 Field
          output reg [47:0]  txWAPIAddr4,           // MAC Header Address 4 Field
          output reg [15:0]  txWAPIQoSCF,           // MAC Header QoS Control Field
          output reg [15:0]  txWAPISeqControl,      // MAC Header Seauence Control Field
          output reg [7:0]   txWAPIKeyIdx,          // WAPI Header Key Index
          output reg [127:0] txWAPIPN,              // WAPI Header Packet Number (PN) Field
`endif //RW_WAPI_EN
          

          //$port_g FCS Block interface
          input  wire        fcsEnd_p,              // Indicates the end of the transmission
          input  wire        fcsBusy,               // Indicates that the FCS block is busy cannot accept new data.

          output wire        mpduFCSEnable,         // Enable the FCS Block
          output wire        mpduFCSStart_p,        // Indicates the begining of the transmission and enable the FCS block
          output wire        mpduFCSShiftTx,        // Indicates FCS engine to append FCS calculated on data
          output wire  [7:0] mpduFCSDInTx,          // Data to the FCS block
          output wire        mpduFCSDInValidTx,     // Indicates that the data on fcsDInTx is valid and can be processed.

          //$port_g Timers Block interface
          input  wire        tickSIFS,              // A pulse to indicate the end of SIFS period
          input  wire        tickSlot,              // A pulse to indicate the end of Slot period
          input  wire  [7:0] dtimCnt,               // Current DTIM count
          input  wire [63:0] tsf,                   // TSF current value

          //$port_g CSReg Block interface
          input  wire  [7:0] timOffset,             // Indicates to the HW the offset, from the first byte of the Beacon frame, 
                                                    // at which the first byte of the TIM field is located
          input  wire        pwrMgt,                // Power Management is enabled for the current
 
          //$port_g Backoff Block interface
          input  wire  [2:0] activeAC,              // Indicates the current AC which has won contention

          //$port_g Debug interface
          output reg   [4:0] formatMPDUFSMCs,       // formatMPDUFSM FSM Current State
          output wire        mpduSeqCtrlDone_p,     // Indicates that the sequence number has been transmitted
          output wire [14:0] formatMPDUFrameDebug1, // frame Debug 1 from formatMPDU module
          output wire [14:0] formatMPDUFrameDebug2  // frame Debug 2 from formatMPDU module
                 );

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

// formatMPDUFSM FSM states definition
//$fsm_sd formatMPDUFSM
localparam 
             FD_IDLE  =  5'd0,  
       FD_INITCRYPTO  =  5'd1,  
          FD_STARTTX  =  5'd2,  
   FD_FRMCNTRL_BYTE1  =  5'd3,  
   FD_FRMCNTRL_BYTE2  =  5'd4,  
       FD_DURID_DATA  =  5'd5,  
            FD_ADDR1  =  5'd6,  
            FD_ADDR2  =  5'd7,  
            FD_ADDR3  =  5'd8, 
         FD_SQNCNTRL  =  5'd9, 
            FD_ADDR4  =  5'd10, 
         FD_QOSCNTRL  =  5'd11, 
          FD_CFCNTRL  =  5'd12, 
          FD_HTCNTRL  =  5'd13, 
              FD_TSF  =  5'd14, 
               FD_IV  =  5'd15, 
            FD_EXTIV  =  5'd16, 
      FD_WAPI_KEYIDX  =  5'd17, 
          FD_WAPI_PN  =  5'd18, 
        FD_MPDUSTART  =  5'd19, 
         FD_FRM_BODY  =  5'd20, 
              FD_ICV  =  5'd21, 
  FD_WAITCCMPMICDONE  =  5'd22, 
          FD_CCMPMIC  =  5'd23, 
          FD_WAPIMIC  =  5'd24, 
              FD_FCS  =  5'd25,  
      FD_FLUSHTXFIFO  =  5'd26;  

localparam
FRMCNTRL_BYTE1_OFFSET = 16'd0,   // Offset of the first byte of the frame control 
FRMCNTRL_BYTE2_OFFSET = 16'd1,   // Offset of the second byte of the frame control

        DURID_BYTECNT = 16'd2,   // Number of bytes of Duration ID field
        DURID_OFFSET  = 16'd2,   // Offset of the Duration ID field

         ADDR_BYTECNT = 16'd6,   // Number of bytes of ADDR field
         ADDR1_OFFSET = 16'd4,   // Offset of the ADDR1 field
         ADDR2_OFFSET = 16'd10,  // Offset of the ADDR2 field
         ADDR3_OFFSET = 16'd16,  // Offset of the ADDR3 field
         ADDR4_OFFSET = 16'd24,  // Offset of the ADDR4 field

     SQNCNTRL_BYTECNT = 16'd2,   // Number of bytes of Sequence Control field
      SQNCNTRL_OFFSET = 16'd22,  // Offset of the Sequence Control field

     QOSCNTRL_BYTECNT = 16'd2,   // Number of bytes of QoS Control field
      QOSCNTRL_OFFSET = 16'd30,  // Offset of the QoS Control field

      CFCNTRL_BYTECNT = 16'd2,   // Number of bytes of Carried Frame Control field
       CFCNTRL_OFFSET = 16'd32,  // Offset of the Carried Frame Control field

      HTCNTRL_BYTECNT = 16'd4,   // Number of bytes of HT Control field
       HTCNTRL_OFFSET = 16'd34,  // Offset of the HT Control field

    `ifdef ENCRYPTION
           IV_BYTECNT = 16'd4,   // Number of bytes of IV field
           IV_OFFSET  = 16'd38,  // Offset of the IV field

        EXTIV_BYTECNT = 16'd4,   // Number of bytes of Extended IV field
         EXTIV_OFFSET = 16'd42,  // Offset of the Extended IV field


          ICV_BYTECNT = 16'd4,   // Number of bytes of ICV field

      CCMPMIC_BYTECNT = 16'd8,   // Number of bytes of CCMPMIC field
    `endif // ENCRYPTION
    
    `ifdef RW_WAPI_EN
   WAPI_KEYIDX_BYTECNT = 16'd2,   // Number of bytes of KeyIdx field 
   WAPI_KEYIDX_OFFSET  = 16'd38,  // Offset of the KeyIdx field
       
       WAPI_PN_BYTECNT = 16'd16,  // Number of bytes of PN field 
       WAPI_PN_OFFSET  = 16'd40,  // Offset of the PN field
       
      WAPIMIC_BYTECNT  = 16'd16,  // Number of bytes of WAPIMIC field
    `endif //RW_WAPI_EN

      FRM_BODY_OFFSET = 16'd46,  // Offset of the Extended IV field

          FCS_BYTECNT = 16'd4,   // Number of bytes of FCS field
           FCS_OFFSET = 16'd46,  // Offset from the end of the frame of the FCS field        

          TSF_BYTECNT = 16'd8,   // Number of bytes of TSF field
           TSF_OFFSET = 16'd46;  // Offset from the end of the frame of the TSF field        

localparam 
`ifdef RW_SIMU_ON
   ENCRYPTION_TYPE_NONE = 3'd0,   // None encryption is selected
`endif // RW_SIMU_ON
   ENCRYPTION_TYPE_WEP  = 3'd1,   // WEP encryption is selected
   ENCRYPTION_TYPE_TKIP = 3'd2,   // TKIP encryption is selected
`ifdef RW_WAPI_EN
   ENCRYPTION_TYPE_WAPI = 3'd4,   // WAPI encryption is selected
`endif // RW_WAPI_EN
   ENCRYPTION_TYPE_CCMP = 3'd3;   // CCMP encryption is selected

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// formatMPDUFSM FSM signals definition
reg [4:0] formatMPDUFSMNs;  // formatMPDUFSM FSM Next State

`ifdef RW_SIMU_ON
// String definition to display formatMPDUFSM current state
reg [17*8-1:0] formatMPDUFSMCs_str;
// String definition to display the type of frame
reg [23*8-1:0] txFrameType_str;
// String definition to display the type of encryption
reg [4*8-1:0] encryptionType_str;
`endif // RW_SIMU_ON


wire        countDone_p;          // Pulse to indicate the end of a multiple bytes field
reg  [15:0] txByteCnt;            // Counts the number of transmitted bytes
reg  [15:0] readByteCnt;          // Counts the number of bytes read from the TxFIFO
reg  [15:0] readByteCnt_ff1;      // Counts the number of bytes read from the TxFIFO
reg  [15:0] readGoodByteCnt;      // Counts the number of bytes read from the TxFIFO
reg  [15:0] readFieldByteCnt;     // Counts the number of bytes read in the current field
reg  [15:0] fieldBytes;           // Number of bytes of the current field
reg  [15:0] fieldOffset;          // Offset in byte of the current field in the Transmit Header Descriptor
reg  [15:0] frameBodyLength;      // Length of the frame body computed based on the frame length and 
                                  // the length of the mac header fields transmitted
reg         txFIFOReadEn;         // Enable the read accesses from the Tx FIFO 
reg         toDS;                 // Indicates that the toDs bit extracted from the MAC Header is set 
reg         fromDS;               // Indicates that the fromDs bit extracted from the MAC Header is set 
reg         protectedFrame;       // Indicates that the Protected bit extracted from the MAC Header is set
reg         order;                // Indicates that the order bit extracted from the MAC Header is set 
reg   [3:0] subtypeTx;            // Frame SubType extracted from the MAC Header.
reg         extIV;                // Indicates that the extIV bit extracted from the MAC Header is set

reg   [7:0] Addr1MSB;             // Stores MSB of the Transmitted ADDR1
reg   [5:0] seqNumber;            // Stores Transmitted Sequence Number
reg   [3:0] fragNumber;           // Stores Transmitted Fragment Number
reg         txPwrMgt;             // Stores Transmitted PwrMgt bit
reg         moreFrag;             // Stores Transmitted more Frag bit
reg         moreData;             // Stores Transmitted more Data bit
reg         txRetry;              // Stores Transmitted Retry bit

wire        firstByteOfFrameBody; // Indicates when the first byte of the frame bady is being processed.
wire        endOfMPDUinTxFifo;    // Indicates when the last byte of the MPDU has been popped from the TX FIFO
reg         endOfMPDUinTxFifo_fcs;// Save the pulse when it is detected outside of FLUSH fifo
reg   [7:0] txData;               // Bytes which are transmitted.    
reg         writePointer;         // Write Pointer of the ping-pong buffer
reg         readPointer;          // Read Pointer of the ping-pong buffer
reg   [7:0] readDataBank0;        // Bank 0 of the ping-pong buffer
reg   [7:0] readDataBank1;        // Bank 1 of the ping-pong buffer

reg   [1:0] carriedFrameType;     // Type of carried frame
reg   [3:0] carriedFrameSubType;  // Subtype of carried frame

reg         txFIFOReadByFour_ff1; // txFIFOReadByFour indication delayed of one clock period
reg         txFIFOReadByTwo_ff1;  // txFIFOReadByTwo indication delayed of one clock period

wire        controlWrapperFrame;  // Indicates that the frame is a Control Warapper Frame
wire        qosFrame;             // Indicates that the frame is a QoS Frame
wire        htcFrame;             // Indicates that the frame is a +HTC Frame
wire        isBeacon;             // Indicates that the frame is a Beacon
wire        isProbeResponse;      // Indicates that the frame is a Probe Response
wire        endOfFrame;           // Indicates the end of the frame.
reg  [63:0] tsfAntenna;           // TSF value at the antenna taken into account the PHY and RF TX delays
wire [15:0] dtimOffset;           // Indicates the offset, from the first byte of the Beacon frame, 
                                  // at which the DTIM field is located

wire        txWEPTKIPDataValid;   // Valid for WEP TKIP payload
reg         txCryptoKeyValidSaved;
//reg         aMPDU_keyUseDefaultDone; // Flag to skip FD Search for each MPDU after teh first MPDU

reg [47:0]  txCCMPSeqCnt;         // Capture CCMP pkt number
reg [47:0]  txTKIPSeqCnt;         // Capture TKIP pkt number

reg         CSIsIdle;             // Pulse to indicate that the CS is idle
wire        enable;               // Signal to indicate the block is no idle

reg         wait4Slot;            // Flag indicating that the formatMPDU is waiting for the slot boundary
//reg         mpduStarted;          // Flag indicating that the pulse mpduStart has raised

reg         skipMPDU;             // Flag indicating a skip MPDU request from txcontroller

`ifdef RW_WAPI_EN
wire        txWAPIDataValid;
`endif 

`ifdef RW_MPDU_AC
reg  [15:0]   readByteOffset;       // used for RW_MPDU_AC
reg   [5:0]   readByteOffset_ff1;   // used for RW_MPDU_AC
wire          nextcountdone_p;      // used for RW_MPDU_AC
`endif


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// signal to enable most of registers blocks
assign enable       = (((formatMPDUFSMCs == FD_IDLE) && (formatMPDUFSMNs != FD_IDLE)) || (formatMPDUFSMCs != FD_IDLE));

// formatMPDUFSM FSM Current State Logic 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    formatMPDUFSMCs <= FD_IDLE; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    formatMPDUFSMCs <= FD_IDLE; 
  else if(enable)
    formatMPDUFSMCs <= formatMPDUFSMNs; 
end


// formatMPDUFSM FSM Next State Logic.
always @* 
begin
  case(formatMPDUFSMCs)

    FD_IDLE:
      //$fsm_s In FD_IDLE state, the state machine waits until it is triggered by 
      //the MAC Controller. 
      if (sendMPDU_p)
      begin 
        //$fsm_t When sendMPDU_p is received, the state machine goes to FD_STARTTX state.
        formatMPDUFSMNs = FD_STARTTX;
      end
      else if (skipMPDU_p)
        //$fsm_t When skipMPDU_p is received, the state machine moves to FD_FLUSHTXFIFO state to discard the current MPDU.
        formatMPDUFSMNs = FD_FLUSHTXFIFO;
      else
        //$fsm_t While sendMPDU_p or skipMPDU_p is not received, the state machine stays in FD_IDLE state.
        formatMPDUFSMNs = FD_IDLE;

    FD_STARTTX:
      //$fsm_s In FD_STARTTX state, the state machine start the FCS engine and the MAC-PHY Interface.
      if (MPDUFrameLengthTx == 16'd0)
        //$fsm_t When MPDUFrameLengthTx is null, the state machine moves to FD_MPDUSTART.
        formatMPDUFSMNs = FD_MPDUSTART;
      else 
      if (dontGenerateMH)
        //$fsm_t One clock cycle after and if the SW has requested to do not generate the MAC Header (dontGenerateMH set), 
        //the state machine moves to FD_MPDUSTART state.
        formatMPDUFSMNs = FD_MPDUSTART; 
      else
        //$fsm_t One clock cycle after and if the SW has requested to generate the MAC Header (dontGenerateMH reset), 
        //the state machine moves to FD_FRMCNTRL_BYTE1 state.
        formatMPDUFSMNs = FD_FRMCNTRL_BYTE1; 

    FD_FRMCNTRL_BYTE1:
      //$fsm_s In FD_FRMCNTRL_BYTE1 state, the Tx Controller sends the first byte of the DATA frame Control.
      if (countDone_p)
        //$fsm_t When countDone_p is low meaning that the TX Controller can continus the processing, 
        //the state machine goes to FD_FRMCNTRL_BYTE2 state.
        formatMPDUFSMNs = FD_FRMCNTRL_BYTE2;
      else
        //$fsm_t While countDone_p is high meaning that the TX Controller has to wait, 
        //the state machine stays in FD_FRMCNTRL_BYTE1 state.
        formatMPDUFSMNs = FD_FRMCNTRL_BYTE1;

    FD_FRMCNTRL_BYTE2:
      //$fsm_s In FD_FRMCNTRL_BYTE2 state, the Tx Controller sends the second byte of the DATA frame Control.
      if (countDone_p) 
        //$fsm_t When countDone_p is low meaning that the TX Controller can continus the processing, 
        //the state machine goes to FD_DURID_DATA state.
        formatMPDUFSMNs = FD_DURID_DATA; 
      else
        //$fsm_t While countDone_p is high meaning that the TX Controller has to wait, 
        //the state machine stays in FD_FRMCNTRL_BYTE2 state.
        formatMPDUFSMNs = FD_FRMCNTRL_BYTE2;

    FD_DURID_DATA:
      //$fsm_s In FD_DURID_DATA state, the Tx Controller sends the durationID of the DATA frame.
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the Duration ID has been completely sent, 
        //the state machine goes to FD_ADDR1 state.
        formatMPDUFSMNs = FD_ADDR1; 
      else
        //$fsm_t While countDone_p is low meaning that the DurationID has not been yet completely sent, 
        //the state machine stays in FD_DURID_DATA state.
        formatMPDUFSMNs = FD_DURID_DATA;

    FD_ADDR1:
      //$fsm_s In FD_ADDR1 state, the Tx Controller sends the ADDR1 field of the DATA frame.
      if (countDone_p) 
      begin
        // If countDone_p is received, the state machine moves to another state. However, this next state
        // depends on the type of frame.
        // 
        //  1- If the frame is a Control Wrapper frame, the next state is FD_CFCNTRL to process the 
        //     Carried Frame Control field.
        //
        //  2- If the frame is an ACK or CTS, the next state is FD_MPDUSTART.
        //
        //  3- If the frame is neither an ACK, CTS nor Control wrapper, the next state is FD_ADDR2 
        //     to process the ADDR2 field.
        //
        if (controlWrapperFrame)
          //$fsm_t When countDone_p is received meaning that the ADDR1 field has been completely sent,
          // and the frame is a Control Wrapper, the state machine goes to FD_CFCNTRL state.
          formatMPDUFSMNs = FD_CFCNTRL; 

        else if ((typeTx == 2'b01) && ((subtypeTx == 4'b1100) || (subtypeTx == 4'b1101)))
          //$fsm_t When countDone_p is received meaning that the ADDR1 field has been completely sent,
          // and the frame is a ACK or a CTS, the state machine goes to FD_MPDUSTART state.
          formatMPDUFSMNs = FD_MPDUSTART;
        else  
          //$fsm_t When countDone_p is received meaning that the ADDR1 field has been completely sent,
          //and the frame is neither a ACK, a CTS nor a Control Wrapper, 
          //the state machine goes to FD_ADDR2 state.
          formatMPDUFSMNs = FD_ADDR2; 
      end
      else
        //$fsm_t While countDone_p is low meaning that the ADDR1 has not been yet completely sent, 
        //the state machine stays in FD_ADDR1 state.
        formatMPDUFSMNs = FD_ADDR1;

    FD_ADDR2:
      //$fsm_s In FD_ADDR2 state, the Tx Controller sends the ADDR2 field of the DATA frame.
      if (countDone_p) 
      begin
        // If countDone_p is received, the state machine moves to another state. However, this next state depends on
        // the type of frame.
        // 
        //  1- If the frame is a BlockAck or BlockAckReq frame, the next state is FD_MPDUSTART 
        //     to process the ADDR2 field.
        //
        //  2- If the frame is a RTS, CF-END, CF-END+CF-ACK or a PS-POLL, the next state is FD_MPDUSTART.
        //
        //  3- If the frame is a Management or Data frame, the next state is FD_ADDR3 
        //     to process the ADDR3 field.
        //
        if ((typeTx == 2'b01) && ((subtypeTx == 4'b1000) || (subtypeTx == 4'b1001)))
          //$fsm_t When countDone_p is received meaning that the ADDR2 field has been completely sent,
          //and the frame is a BlockAck or BlockAckReq, the state machine goes to FD_MPDUSTART state.
          formatMPDUFSMNs = FD_MPDUSTART; 
        else if (typeTx == 2'b01)
          //$fsm_t When countDone_p is received meaning that the ADDR2 field has been completely sent,
          //and the frame is a RTS, CF-END, CF-END+CF-ACK or a PS-POLL, the state machine goes to FD_MPDUSTART state.
          formatMPDUFSMNs = FD_MPDUSTART;
        else
          //$fsm_t When countDone_p is received meaning that the ADDR2 field has been completely sent,
          //and the frame is a Management of Data frame, the state machine goes to FD_ADDR3 state.
          formatMPDUFSMNs = FD_ADDR3; 
      end
      else
        //$fsm_t While countDone_p is low meaning that the ADDR2 has not been yet completely sent, 
        //the state machine stays in FD_ADDR2 state.
        formatMPDUFSMNs = FD_ADDR2;

    FD_ADDR3:
      //$fsm_s In FD_ADDR3 state, the Tx Controller sends the ADDR3 field of the DATA frame.
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the ADDR3 field has been completely sent, 
        //the state machine goes to FD_SQNCNTRL state.
        formatMPDUFSMNs = FD_SQNCNTRL; 
      else
        //$fsm_t While countDone_p is low meaning that the ADDR3 has not been yet completely sent, 
        //the state machine stays in FD_ADDR3 state.
        formatMPDUFSMNs = FD_ADDR3;

    FD_SQNCNTRL:
      //$fsm_s In FD_SQNCNTRL state, the Tx Controller sends the Sequence Number field of the DATA frame.
      if (countDone_p) 
      begin
        // If countDone_p is received, the state machine moves to another state. However, this next state depends on
        // the type of frame.
        // 
        //  1- If the frame has both fromDS and toDS bit sets, the next state is FD_ADDR4 
        //     to process the ADDR4 field.
        //
        //  2- If the frame does not have fromDS and toDS bit sets but is a QoS Dataframe (qosFrame = 1),  
        //     the next state is FD_QOSCNTRL to process the QoS Control field. 
        //
        //  3- If the frame does not have fromDS or toDS bit sets, is not a QoS Dataframe (qosFrame = 0),
        //     but is a HTC frame (htcFrame set), the next state is FD_HTC to process the HT Control field. 
        //
        //  4- If the frame does not have fromDS or toDS bit sets, is neither a QoS Dataframe (qosFrame = 0) nor an 
        //     HTC frame but is protected (protectedFrame bit set), the next state is FD_IV to process the IV field.
        //     If WAPI encryption is supported and active the next state is FD_WAPI_KEYIDX.
        //
        //  5- If the frame does not have fromDS or toDS bit sets, is neither a QoS Dataframe (qosFrame = 0) nor an 
        //     HTC frame and is not protected (protectedFrame bit reset), the next state is FD_MPDUSTART.
        //
        if (fromDS && toDS)
          // Case 1
          //$fsm_t When countDone_p is received meaning that the Sequence Control field has been completely sent,
          //and the frame has both fromDS and toDS bit sets, the state machine goes to FD_ADDR4 state.
          formatMPDUFSMNs = FD_ADDR4; 

        else
        begin
          if (qosFrame)
            // Case 2
            //$fsm_t When countDone_p is received meaning that the Sequence Control field has been completely sent,
            //and the Data frame does not have fromDS and toDS bit sets but is a QoS Dataframe (qosFrame = 1), 
            //the state machine goes to FD_QOSCNTRL state.
            formatMPDUFSMNs = FD_QOSCNTRL; 

          else 
          begin
            if (htcFrame)
              // Case 3
              //$fsm_t When countDone_p is received meaning that the Sequence Control field has been completely sent,
              //and the Data frame does not have fromDS and toDS bit sets and is not a QoS Dataframe but is a HTC Frame (htcFrame = 1),
              //the state machine goes to FD_HTCNTRL state.
              formatMPDUFSMNs = FD_HTCNTRL; 

            else
            begin 
            `ifdef ENCRYPTION
              `ifdef RW_WAPI_EN
              if ( protectedFrame && (txWEP || txTKIP || txCCMP) )
                // Case 4
                //$fsm_t When countDone_p is received meaning that the Sequence Control field has been completely sent,
                //and the frame does not have fromDS and toDS bit sets, is not a QoS nor an HT frame but is encrypted 
                //(protectedFrame = 1), the state machine goes to FD_IV state.
                //If WAPI mode is active the next state is FD_WAPI_KEYIDX
                formatMPDUFSMNs = FD_IV; 
              else if ( protectedFrame && txWAPI )
                formatMPDUFSMNs = FD_WAPI_KEYIDX;
              else
              `else // RW_WAPI_EN
              if ( protectedFrame )
                // Case 4
                //$fsm_t When countDone_p is received meaning that the Sequence Control field has been completely sent,
                //and the frame does not have fromDS and toDS bit sets, is not a QoS nor an HT frame but is encrypted 
                //(protectedFrame = 1), the state machine goes to FD_IV state.
                formatMPDUFSMNs = FD_IV; 
              else
              `endif // RW_WAPI_EN
            `endif // ENCRYPTION

                // Case 5        
                //$fsm_t If the frame does not have fromDS or toDS bit sets, is neither a QoS Dataframe (qosFrame = 0) nor an 
                //HTC frame and is not protected (protectedFrame bit reset), the next state is FD_MPDUSTART.
                formatMPDUFSMNs = FD_MPDUSTART;
            end  
          end  
        end  
      end  
      else
        //$fsm_t While countDone_p is low meaning that the Sequence Number field has not been yet completely sent, 
        //the state machine stays in FD_SQNCNTRL state.
        formatMPDUFSMNs = FD_SQNCNTRL;

    FD_ADDR4:
      //$fsm_s In FD_ADDR4 state, the Tx Controller sends the ADDR4 field of the DATA frame
      // Note that a Management frame is not supposed to reach this state!
      if (countDone_p) 
      begin
        // If countDone_p is received, the state machine moves to another state. However, this next state depends on
        // the type of frame.
        // 
        //  1- If the frame is a QoS Dataframe (qosFrame = 1),  
        //     the next state is FD_QOSCNTRL to process the QoS Control field. 
        //
        //  2- If the frame is not a QoS Dataframe (qosFrame = 0),
        //     but is an HTC frame (htcFrame set), the next state is FD_HTC to process the HT Control field. 
        //
        //  3- If the frame is neither a QoS Dataframe (qosFrame = 0) nor an 
        //     HTC frame but is protected (protectedFrame bit set), the next state is FD_IV to process the IV field.
        //
        //  4- If the frame is neither a QoS Dataframe (qosFrame = 0) nor an 
        //     HTC frame and is not protected (protectedFrame bit reset), the next state is FD_MPDUSTART to process 
        //     the Frame body field.
        //
        //
        if (qosFrame)
          // Case 1
          //$fsm_t When countDone_p is received meaning that the ADDR4 field has been completely sent,
          //and the Data frame is a QoS Dataframe (qosFrame = 1), the state machine 
          //goes to FD_QOSCNTRL state.
          formatMPDUFSMNs = FD_QOSCNTRL; 

        else 
        begin
          if (htcFrame)
            // Case 2
            //$fsm_t When countDone_p is received meaning that the ADDR4 field has been completely sent,
            //and the Data frame is not a QoS Dataframe but is an HT Frame (htcFrame = 1), the state machine 
            //goes to FD_HTCNTRL state.
            formatMPDUFSMNs = FD_HTCNTRL; 

          else
          begin 
          `ifdef ENCRYPTION
            `ifdef RW_WAPI_EN
            if ( protectedFrame && (txWEP || txTKIP || txCCMP) )
              // Case 3
              //$fsm_t When countDone_p is received meaning that the ADDR4 field has been completely sent,
              //and the frame is neither a QoS nor an HT frame but is encrypted (protectedFrame = 1), the 
              //state machine goes to FD_IV state.
              //If WAPI mode is active the next state is FD_WAPI_KEYIDX
              formatMPDUFSMNs = FD_IV; 
            else if ( protectedFrame && txWAPI )
              formatMPDUFSMNs = FD_WAPI_KEYIDX;
            else
            `else // RW_WAPI_EN
            if ( protectedFrame )
              // Case 3
              //$fsm_t When countDone_p is received meaning that the ADDR4 field has been completely sent,
              //and the frame is neither a QoS nor an HT frame but is encrypted (protectedFrame = 1), the 
              //state machine goes to FD_IV state.
              formatMPDUFSMNs = FD_IV; 
            else
            `endif // RW_WAPI_EN
          `endif // ENCRYPTION
              // Case 4        
              //$fsm_t When countDone_p is received meaning that the ADDR4 field has been completely sent,
              //and the frame is neither a QoS nor an HT frame and is not encrypted, the state machine goes to FD_MPDUSTART state.
              formatMPDUFSMNs = FD_MPDUSTART;
          end  
        end  
      end  

      else
        //$fsm_t While countDone_p is low meaning that the ADDR4 field has not been yet completely sent, 
        //the state machine stays in FD_ADDR4 state.
        formatMPDUFSMNs = FD_ADDR4;

    FD_QOSCNTRL:
      //$fsm_s FD_QOSCNTRL state, the Tx Controller sends the QoS Control field of the DATA frame
      if (countDone_p) 
      begin
        // If countDone_p is received, the state machine moves to another state. However, this next state depends on
        // the type of frame.
        // 
        //  1- If the frame is an HTC frame (htcFrame set), the next state is FD_HTC to process the HT Control field. 
        //
        //  2- If the frame is not an HTC frame (htcFrame reset) but is protected (protectedFrame bit set), 
        //     the next state is FD_IV to process the IV field.
        //
        //  3- If the frame does not an HTC frame and is not protected (protectedFrame bit reset) , the next state is FD_MPDUSTART 
        //     to process the Frame body field.
        //
        if (htcFrame)
          // Case 1
          //$fsm_t When countDone_p is received meaning that the QoS Control field has been completely sent,
          //and the Data frame is an HT Frame (htcFrame = 1), the state machine goes to FD_HTCNTRL state.
          formatMPDUFSMNs = FD_HTCNTRL; 

        else
        begin 
          `ifdef ENCRYPTION
            if(protectedFrame)
            begin
              `ifdef RW_WAPI_EN
              if(txWAPI)
                formatMPDUFSMNs = FD_WAPI_KEYIDX;
              else
                formatMPDUFSMNs = FD_IV;
              `else
                formatMPDUFSMNs = FD_IV;
              `endif //RW_WAPI_EN
            end
            else
//            `ifdef RW_WAPI_EN
//            if ( protectedFrame && (txWEP || txTKIP || txCCMP) )
//              // Case 2
//              //$fsm_t When countDone_p is received meaning that the QoS Control field has been completely sent,
//              //and the frame is not an HT frame but is encrypted (protectedFrame = 1), the state machine goes to FD_IV state.
//              //If WAPI mode is active the next state is FD_WAPI_KEYIDX
//              formatMPDUFSMNs = FD_IV; 
//            else if ( protectedFrame && txWAPI )
//              formatMPDUFSMNs = FD_WAPI_KEYIDX;
//            else
//            `else // RW_WAPI_EN
//            if ( protectedFrame )
//              // Case 2
//              //$fsm_t When countDone_p is received meaning that the QoS Control field has been completely sent,
//              //and the frame is not an HT frame but is encrypted (protectedFrame = 1), the state machine goes to FD_IV state.
//              formatMPDUFSMNs = FD_IV; 
//            else
//            `endif // RW_WAPI_EN
          `endif // ENCRYPTION
            // Case 3       
            //$fsm_t When countDone_p is received meaning that the QoS Control field has been completely sent,
            //and the frame is not an HT frame and is not encrypted, the state machine goes to FD_MPDUSTART state.
            formatMPDUFSMNs = FD_MPDUSTART;

        end  
      end  
      else
        //$fsm_t While countDone_p is low meaning that the QoS Control field has not been yet completely sent, 
        //the state machine stays in FD_QOSCNTRL state.
        formatMPDUFSMNs = FD_QOSCNTRL;

    FD_CFCNTRL:
      //$fsm_s FD_CFCNTRL state, the Tx Controller sends the CF Control field of the DATA frame.
      if (countDone_p) 
        //$fsm_t If countDone_p is received  meaning that the CF Control field has been completely sent, 
        //the state machine goes to FD_HTCNTRL state.
        formatMPDUFSMNs = FD_HTCNTRL; 
      else
        //$fsm_t While countDone_p is low meaning that the CF Control field has not been yet completely sent, 
        //the state machine stays in FD_CFCNTRL state.
        formatMPDUFSMNs = FD_CFCNTRL;

    FD_HTCNTRL:
      //$fsm_s FD_HTCNTRL state, the Tx Controller sends the HT Control field of the DATA frame
      if (countDone_p) 
      begin
        // If countDone_p is received, the state machine moves to another state. However, this next state depends on
        // the type of frame.
        // 
        //  1- If the frame is protected (protectedFrame bit set), the next state is FD_IV to process the IV field.
        //
        //  2- If the frame is not protected (protectedFrame bit reset), the next state is FD_MPDUSTART.
        //
        
        //TODO : Check if WAPI Frame include MAC header with HT Control Field
        `ifdef ENCRYPTION
        if (protectedFrame)
          // Case 1
          //$fsm_t When countDone_p is received meaning that the HT Control field has been completely sent,
          //and the frame is encrypted (protectedFrame = 1), the state machine goes to FD_IV state.
          formatMPDUFSMNs = FD_IV;

        else
        `endif // ENCRYPTION
        begin
          // Case 2        
          //$fsm_t If the frame is not protected (protectedFrame bit reset), the next state is FD_MPDUSTART.
          formatMPDUFSMNs = FD_MPDUSTART;
        end
      end
      else
        //$fsm_t While countDone_p is low meaning that the HT Control field has not been yet completely sent, 
        //the state machine stays in FD_HTCNTRL state.
        formatMPDUFSMNs = FD_HTCNTRL;

    FD_TSF:
      //$fsm_s FD_TSF state, the Tx Controller sends the TSF field of the Beacon or Probe Response frame.
      if (countDone_p) 
      begin
        //$fsm_t If countDone_p is received meaning that the TSF field has been completely sent, 
        //the state machine goes to FD_FRM_BODY state.
        //Note that only a Beacon or a Probe Response frame can reach this state.
          formatMPDUFSMNs = FD_FRM_BODY;
      end
      else
        //$fsm_t While countDone_p is low meaning that the TSF field has not been yet completely sent, 
        //the state machine stays in FD_TSF state.
        formatMPDUFSMNs = FD_TSF;

    `ifdef ENCRYPTION
    FD_IV:
      // If countDone_p is received, the state machine moves to another state. However, this next state depends on
      // the encryption type.
      // 
      //  1- If the frame has an Extended IV field (TKIP and CCMP encryption), the next state is FD_EXTIV 
      //     to process the Extended IV field.
      //
      //  2- If the frame does not have Extended IV field (WEP encryption), the next state is FD_MPDUSTART
      //     to process the Frame body field.
      //
      //$fsm_s FD_IV state, the Tx Controller sends the IV field of the DATA frame.
      if (countDone_p) 
      begin
        if(protectedFrame && txWEP && !txSBOXInitDone)
          //$fsm_t When countDone_p and cipher type is WEP but SBOX Init is not done then the FSM has to wait, 
          //the state machine goes to FD_INITCRYPTO state
          formatMPDUFSMNs = FD_INITCRYPTO;
        else if (extIV)
          //$fsm_t If countDone_p is received  meaning that the IV field has been completely sent, 
          //and the frame has an Extended IV field (TKIP or CCMP) (extIV bit = 1), the state machine goes to FD_EXTIV state.
          formatMPDUFSMNs = FD_EXTIV;
        else
          //$fsm_t If countDone_p is received  meaning that the IV field has been completely sent, 
          //and the frame does not an Extended IV field (WEP) (extIV bit = 0), the state machine goes to FD_MPDUSTART state.
          formatMPDUFSMNs = FD_MPDUSTART; 
      end
      else
        //$fsm_t While countDone_p is low meaning that the IV field has not been yet completely sent, 
        //the state machine stays in FD_IV state.
        formatMPDUFSMNs = FD_IV;

    FD_EXTIV:
      //$fsm_s FD_EXTIV state, the Tx Controller sends the Extended IV field of the DATA frame.
      if (countDone_p)
      begin
        if(protectedFrame && txTKIP && !txSBOXInitDone)
          //$fsm_t When countDone_p and cipher type is WEP but SBOX Init is not done then the FSM has to wait,
          //the state machine goes to FD_INITCRYPTO state
          formatMPDUFSMNs = FD_INITCRYPTO;
        else if(protectedFrame && txCCMP && txCCMPStart)
          //$fsm_t If countDone_p is received and cipher type is CCMP then the FSM has to wait CCMP init,
          //the state machine goes to FD_INITCRYPTO state
          formatMPDUFSMNs = FD_INITCRYPTO;
        else
          //$fsm_t If countDone_p is received meaning that the Extended IV field has been completely sent, and it is txTKIP and txSBOXInitDone,
          //the state machine goes to FD_MPDUSTART state.
          formatMPDUFSMNs = FD_MPDUSTART;
      end
      else
        //$fsm_t While countDone_p is low meaning that the Extended IV field has not been yet completely sent, 
        //the state machine stays in FD_EXTIV state.
        formatMPDUFSMNs = FD_EXTIV;

    FD_INITCRYPTO:
      //$fsm_s In FD_INITCRYPTO state, the state machine waits for either txSBOXInitDone or not txCCMPBusy
      if (txSBOXInitDone && !fcsBusy && (txWEP || txTKIP)) 
        //$fsm_t When txSBOXInitDone is high and not fcsBusy and cipher type is either WEP or TKIP,
        //the state machine goes to FD_MPDUSTART state.
        formatMPDUFSMNs = FD_MPDUSTART;
      else if(!txCCMPBusy && !fcsBusy && txCCMP && (txByteCnt >= readGoodByteCnt))
        //$fsm_t When txCCMPBusy is low and not fcsBusy and cipher type is CCMP,
        //the state machine goes to FD_MPDUSTART state.
        formatMPDUFSMNs = FD_MPDUSTART;
      `ifdef RW_WAPI_EN
      else if(!txWAPIBusy && !fcsBusy && txWAPI && (txByteCnt >= readGoodByteCnt))
        //$fsm_t When txWAPIBusy is low and not fcsBusy and cipher type is WAPI,
        //the state machine goes to FD_MPDUSTART state.
        formatMPDUFSMNs = FD_MPDUSTART;
      `endif
      
      else
        //$fsm_t While cipher init is not done, the state machine stays in FD_INITCRYPTO state.
        formatMPDUFSMNs = FD_INITCRYPTO;
        
        
    `ifdef RW_WAPI_EN
    FD_WAPI_KEYIDX:
    //$fsm_s In FD_WAPI_KEYIDX state, the Tx Controller sends the Key Index of the WAPI encrypted DATA Frame 
      if (countDone_p) 
        //$fsm_t When countDone_p is received, the state machine moves to FW_WAPI_PN state 
        formatMPDUFSMNs = FD_WAPI_PN;
      else
        //$fsm_t While countDone_p is not received, the state machine stays in FD_WAPI_KEYIDX state
        formatMPDUFSMNs = FD_WAPI_KEYIDX;
        
    FD_WAPI_PN:
      //TODO check against other encryption protocol for going into MPDUSTART state
      //$fsm_s FD_WAPI_PN state, the Tx Controller sends the Packet Number of the WAPI encrypted DATA frame.
      if (countDone_p)
          formatMPDUFSMNs = FD_INITCRYPTO;
      else
        //$fsm_t While countDone_p is low the state machine stays in FD_WAPI_PN state.
        formatMPDUFSMNs = FD_WAPI_PN;
        
    `endif //RW_WAPI_EN
    
    `endif // ENCRYPTION

    FD_MPDUSTART:
      //$fsm_s In FD_MPDUSTART state, the FSM waits for mpduTxStart_p,
      //thus avoid the tx end pulse before the rising of tx req,
      //ampdu and rifs can ignored the pulse.

      if (aMPDU || useRIFSTx || dontGenerateMH)
        //$fsm_t If ampdu or RIFS or dontGenerateMH then goes to FD_FRM_BODY state.
        formatMPDUFSMNs = FD_FRM_BODY;
      else
      begin
        if (mpIfTxEn)
        begin
          if (isBeacon || isProbeResponse)
            //$fsm_t If mpIfTxEn and is a Beacon or a ProbeResponse then goes to TSF state.
            formatMPDUFSMNs = FD_TSF;
          else if ((typeTx == 2'b01) && ((subtypeTx == 4'b1100) || (subtypeTx == 4'b1101)))
            //$fsm_t If mpIfTxEn and is a CTS or a ACK then goes to FCS state.
            formatMPDUFSMNs = FD_FCS;
          else if((typeTx == 2'b01) && ((subtypeTx != 4'b1000) && (subtypeTx != 4'b1001) && (subtypeTx != 4'b0111) && (subtypeTx != 4'b0101) && (subtypeTx != 4'b0100)))
            //$fsm_t If mpIfTxEn and it is a Control Frame and it is neither a BA nor a BAR nor CWRAPPER nor a VHT NDP Announcement nor a Beaforming Report Poll
            // then goes to FCS
            formatMPDUFSMNs = FD_FCS;
          else
            //$fsm_t If mpIfTxEn and others cases then goes to FD_FRM_BODY
            formatMPDUFSMNs = FD_FRM_BODY;
        end
        else
          //$fsm_t If not mpIfTxEn, then wait in  FD_MPDUSTART State
          formatMPDUFSMNs = FD_MPDUSTART;
      end

    FD_FRM_BODY:
      //$fsm_s FD_FRM_BODY state, the Tx Controller sends the Frame Body field of the DATA frame.
      if (countDone_p) 
      begin
        // If countDone_p is received, the state machine moves to another state. However, this next state depends on
        // the encryption type.
        // 
        //  1- If encryption type is TKIP or WEP, the next state is FD_ICV to process the ICV field.
        //
        //  2- If encryption type is CCMP, the next state is FD_CCMPMIC to process the CCMP MIC field.
        //
        //  3- Else the next state is FD_FCS to process the FCS field.
        //
        if(protectedFrame && (fieldBytes >= 16'd0) && !dontEncrypt)
        begin
          `ifdef ENCRYPTION
          case (cTypeRAM)
            ENCRYPTION_TYPE_WEP : 
              //$fsm_t If countDone_p is received  meaning that the Frame Body field has been completely sent, 
              //and the frame is encrypted in WEP (cTypeRAM = 1), the state machine goes to FD_ICV state.
              formatMPDUFSMNs = FD_ICV; 

            ENCRYPTION_TYPE_TKIP :
              //$fsm_t If countDone_p is received  meaning that the Frame Body field has been completely sent, 
              //and the frame is encrypted in TKIP (cTypeRAM = 2), the state machine goes to FD_ICV state.
              formatMPDUFSMNs = FD_ICV; 

            ENCRYPTION_TYPE_CCMP :
              //$fsm_t If countDone_p is received  meaning that the Frame Body field has been completely sent, 
              //and the frame is encrypted in CCMP (cTypeRAM = 3), the state machine goes to FD_WAITCCMPMICDONE state.
              formatMPDUFSMNs = FD_WAITCCMPMICDONE; 
`ifdef RW_WAPI_EN

            ENCRYPTION_TYPE_WAPI :
              //$fsm_t If countDone_p is received  meaning that the Frame Body field has been completely sent, 
              //and the frame is encrypted in WAPI (cTypeRAM = 4), the state machine goes to FD_WAPIMIC state.
              formatMPDUFSMNs = FD_WAPIMIC; 

`endif //RW_WAPI_EN
            default :  
          `endif // ENCRYPTION
              //$fsm_t If countDone_p is received  meaning that the Frame Body field has been completely sent,  
              //and the cipher type is neither WE Pnor TKIP nor CCMP,then the state machine goes to FD_FCS state.
              formatMPDUFSMNs = FD_FCS; 
          `ifdef ENCRYPTION
          endcase
          `endif // ENCRYPTION
        end
        else
          //$fsm_t If countDone_p is received  meaning that the Frame Body field has been completely sent,  
          //and the frame is not ecnrypted,then the state machine goes to FD_FCS state.
          formatMPDUFSMNs = FD_FCS;
      end
      else
        //$fsm_t While countDone_p is low meaning that the Frame Body field has not been yet completely sent, 
        //the state machine stays in FD_FRM_BODY state.
        formatMPDUFSMNs = FD_FRM_BODY;

    `ifdef ENCRYPTION
    FD_ICV:
      //$fsm_s FD_FD_ICV state, the Tx Controller sends the ICV field of the DATA frame.
      if (countDone_p) 
        //$fsm_t If countDone_p is received  meaning that the ICV field has been completely sent, 
        //the state machine goes to FD_FCS state.
        formatMPDUFSMNs = FD_FCS; 
      else
        //$fsm_t While countDone_p is low meaning that the ICV field has not been yet completely sent, 
        //the state machine stays in FD_ICV state.
        formatMPDUFSMNs = FD_ICV;

    FD_WAITCCMPMICDONE:
      //$fsm_s In FD_WAITCCMPMICDONE state, the Tx Controller wait for Encryption Enginge to finish computing the MIC.
      if (txCCMPMicDone)
        //$fsm_t If txCCMPMicDone is received  meaning that the MIC has been computed, then the state goes to FD_CCMPMIC state.
        formatMPDUFSMNs = FD_CCMPMIC;
      else
        //$fsm_t If not txCCMPMicDone, then the state waits in FD_WAITCCMPMICDONE state.
        formatMPDUFSMNs = FD_WAITCCMPMICDONE;

    FD_CCMPMIC:
      //$fsm_s FD_CCMPMIC state, the Tx Controller sends the CCMP MIC field of the DATA frame.
      if (countDone_p) 
        //$fsm_t If countDone_p is received  meaning that the CCMP MIC field has been completely sent, 
        //the state machine goes to FD_FCS state.
        formatMPDUFSMNs = FD_FCS; 
      else
        //$fsm_t While countDone_p is low meaning that the CCMP MIC field has not been yet completely sent, 
        //the state machine stays in FD_CCMPMIC state.
        formatMPDUFSMNs = FD_CCMPMIC;
    `endif // ENCRYPTION
    
    `ifdef RW_WAPI_EN
    FD_WAPIMIC:
      //$fsm_s FD_WAPIMIC state, the Tx Controller sends the WAPI MIC field of the DATA frame.
      if (txWAPIMicDone) 
        //$fsm_t If countDone_p is received  meaning that the WAPI MIC field has been completely sent, 
        //the state machine goes to FD_FCS state.
        formatMPDUFSMNs = FD_FCS; 
      else
        //$fsm_t While countDone_p is low meaning that the WAPI MIC field has not been yet completely sent, 
        //the state machine stays in FD_WAPIMIC state.
        formatMPDUFSMNs = FD_WAPIMIC;
    `endif //RW_WAPI_EN

    FD_FCS:
      //$fsm_s In FD_FCS state, the state machine trigs the FCS block to shift out the FCS value and wait until its completion.
      if (countDone_p) 
        if (endOfMPDUinTxFifo || endOfMPDUinTxFifo_fcs)
          //$fsm_t When countDone_p is received meaning that the FCS has been completely sent and the complete MPDU has been read from the TX FIFO
          //, the state machine goes back to FD_IDLE state
          formatMPDUFSMNs = FD_IDLE; 
        else  
          //$fsm_t When countDone_p is received but the last byte of MPDU indication has not been received,the state machine goes to FD_FLUSHTXFIFO state
          // to flush the TX FIFO.
          formatMPDUFSMNs = FD_FLUSHTXFIFO; 
      else
        //$fsm_t While countDone_p is not received, the state machine stays in FD_FCS state
        formatMPDUFSMNs = FD_FCS;

    FD_FLUSHTXFIFO:
      //$fsm_s In FD_FLUSHTXFIFO state, the state machine reads the TX Fifo until it gets the last byte of MPDU indication. This state is 
      // reached  in two cases
      //   1- Request from MAC Controller to skip the MPDU stored in TX FIFO. 
      //   2- length mistmatch between the number of bytes in the TX FIFO and the MPDU Length defined.
      if (endOfMPDUinTxFifo) 
        //$fsm_t When endOfMPDUinTxFifo is received meaning that the TX FIFO has been completely flushed, the state machine goes back to FD_IDLE state
        formatMPDUFSMNs = FD_IDLE; 
      else
        //$fsm_t While endOfMPDUinTxFifo is not received, the state machine stays in FD_FLUSHTXFIFO state
        formatMPDUFSMNs = FD_FLUSHTXFIFO;

     // Disable coverage on the default state because it cannot be reached.
     // pragma coverage block = off 
     default:   
        formatMPDUFSMNs = FD_IDLE; 
     // pragma coverage block = on 

  endcase
end


// Pulse indication CS is IDLE
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    CSIsIdle <= 1'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
    CSIsIdle <= 1'b0; 
  else if(enable) 
    if((formatMPDUFSMCs != FD_IDLE) && (formatMPDUFSMNs == FD_IDLE))
      CSIsIdle <= 1'b1; 
end

// Transmitted frame Type and SubType parsing.
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    typeTx      <= 2'b0;
    subtypeTx   <= 4'b0;
    typeTxValid <= 1'b0;
  end
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
  begin
    typeTx      <= 2'b0;
    subtypeTx   <= 4'b0;
    typeTxValid <= 1'b0;
  end
  else if(enable)
  begin
    if (formatMPDUFSMCs == FD_FRMCNTRL_BYTE1)
      if (txFIFODataValid)
      begin
        typeTx      <= txFIFORdData[3:2];
        subtypeTx   <= txFIFORdData[7:4];
        typeTxValid <= 1'b1;
      end  
  end
end  

// Indicates that the transmitted frame is a CF-END or a CF-END+CF-ACK
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    sentCFEND <= 1'b0;
  else
  begin
    if ({typeTx,subtypeTx[3:1]} == 5'b01111)
      sentCFEND <= 1'b1;
    else  
      sentCFEND <= 1'b0;
  end
end  

// Indicates that the transmitted frame is a RTS
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    sentRTS <= 1'b0;
  else
  begin
    if ({typeTx,subtypeTx} == 6'b011011)
      sentRTS <= 1'b1;
    else if (({typeTx,subtypeTx} == 6'b010111) && ({carriedFrameType,carriedFrameSubType} == 6'b011011))
      sentRTS <= 1'b1;
    else  
      sentRTS <= 1'b0;
  end
end  

// Indicates that the transmitted frame is a BA request
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    sentBAReq <= 1'b0;
  else
  begin
    if ({typeTx,subtypeTx} == 6'b011000)
      sentBAReq <= 1'b1;
    else if (({typeTx,subtypeTx} == 6'b010111) && ({carriedFrameType,carriedFrameSubType} == 6'b011000))
      sentBAReq <= 1'b1;
    else  
      sentBAReq <= 1'b0;
  end
end  

// Transmitted frame toDS, fromDS, protectedFrame and order parsing.
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    toDS            <= 1'b0;
    fromDS          <= 1'b0;
    moreFrag        <= 1'b0;
    txRetry         <= 1'b0;
    txPwrMgt        <= 1'b0;
    moreData        <= 1'b0;
    order           <= 1'b0;
    protectedFrame  <= 1'b0;
  end
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
  begin
    toDS            <= 1'b0;
    fromDS          <= 1'b0;
    order           <= 1'b0;
    moreFrag        <= 1'b0;
    txRetry         <= 1'b0;
    txPwrMgt        <= 1'b0;
    moreData        <= 1'b0;
    protectedFrame  <= 1'b0;
  end
  else if(enable)
  begin
    if (formatMPDUFSMCs == FD_FRMCNTRL_BYTE2)
      if (txFIFODataValid)
      begin
        toDS            <= txFIFORdData[0];
        fromDS          <= txFIFORdData[1];
        moreFrag        <= txFIFORdData[2];
        moreData        <= txFIFORdData[5];
        order           <= txFIFORdData[7];

        case({typeTx,subtypeTx})
           6'b100000  :  protectedFrame  <= txFIFORdData[6];//DATA
           6'b100001  :  protectedFrame  <= txFIFORdData[6];//DATA+CF-ACK
           6'b100010  :  protectedFrame  <= txFIFORdData[6];//DATA+CF-POLL
           6'b100011  :  protectedFrame  <= txFIFORdData[6];//DATA+CF-ACK+CF-POLL
//           6'b100100  :  protectedFrame  <= txFIFORdData[6];//Null
           6'b101000  :  protectedFrame  <= txFIFORdData[6];//QoS DATA
           6'b101001  :  protectedFrame  <= txFIFORdData[6];//QoS DATA+CF-ACK
           6'b101010  :  protectedFrame  <= txFIFORdData[6];//QoS DATA+CF-POLL
           6'b101011  :  protectedFrame  <= txFIFORdData[6];//QoS DATA+CF-ACK+CF-POLL
//           6'b101100  :  protectedFrame  <= txFIFORdData[6];//QoS Null
                
           6'b001010  :  protectedFrame  <= txFIFORdData[6];//Disassociation only CCMP
           6'b001011  :  protectedFrame  <= txFIFORdData[6];//Authentification only WEP
           6'b001100  :  protectedFrame  <= txFIFORdData[6];//Deauthentification only CCMP
           6'b001101  :  protectedFrame  <= txFIFORdData[6];//Action only CCMP
           default    :  protectedFrame  <= 1'b0;
        endcase

        if (dontGenerateMH)
        begin
          txRetry   <= txFIFORdData[3];
          txPwrMgt  <= txFIFORdData[4];
        end  
        else  
        begin
          txRetry   <= retry;
          // The pwrMgt bit of the Frame Control is set 
          // the pwrMgt register is set or 
          // the MAC Header formatted by the SW has the pwrMgt bit set
          txPwrMgt  <= pwrMgt || txFIFORdData[4];
        end  
      end  
  end
end  

// Transmitted frame toDS, fromDS, protectedFrame and order parsing.
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    carriedFrameType    <= 2'd0;
    carriedFrameSubType <= 4'd0;
  end
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
  begin
    carriedFrameType    <= 2'd0;
    carriedFrameSubType <= 4'd0;
  end
  else if(enable)
  begin
    if (formatMPDUFSMCs == FD_CFCNTRL)
      if (txFIFODataValid && (readByteCnt_ff1 == fieldOffset))
      begin
        carriedFrameType    <= txFIFORdData[3:2];
        carriedFrameSubType <= txFIFORdData[7:4];
      end  
  end
end  


`ifdef ENCRYPTION
// Pulse to indicate the next state machine should goes to extIV or not
always @(*)
begin
  // Ext IV only valid for TKIP when the bit is set high, and always valid for CCMP
  if((formatMPDUFSMCs == FD_IV) && (txFIFODataValid && (readByteCnt_ff1 == fieldOffset + fieldBytes)) && (cTypeRAM[1] == 1'b1))
    extIV = txFIFORdData[5] | cTypeRAM[0];
  else
    extIV = 1'b0;
end
`endif // ENCRYPTION

// Transmitted frame TID parsing.
// This process extract the TID information from the last byte of the QoS field.
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    txTID            <= 4'b0;
    txAMSDUPresent   <= 1'b0;
  end
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    txTID            <= 4'b0;
    txAMSDUPresent   <= 1'b0;
  end  
  else if(enable)
  begin
    if (formatMPDUFSMCs == FD_STARTTX)
    begin
      case(activeAC)
        3'b011: txTID    <= 4'd1;
        3'b010: txTID    <= 4'd0;
        3'b001: txTID    <= 4'd4;
        3'b000: txTID    <= 4'd6;
       default: txTID    <= 4'd0;
      endcase
      txAMSDUPresent    <= 1'b0;
    end    
    else if (formatMPDUFSMCs == FD_QOSCNTRL)
    begin
      if (txFIFODataValid && (readByteCnt_ff1 == fieldOffset))
      begin
          txTID           <= txFIFORdData[3:0];
          txAMSDUPresent  <= txFIFORdData[7];
      end
    end
  end
end  

always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txBcMc           <= 1'b0;
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    txBcMc           <= 1'b0;
  else if(enable)
  begin
    if (formatMPDUFSMCs == FD_STARTTX)
      txBcMc           <= 1'b0;
    else if (formatMPDUFSMCs == FD_ADDR1)
    begin
      if (txFIFODataValid && (readByteCnt_ff1 == fieldOffset))
        txBcMc  <= txFIFORdData[0];
    end
  end
end  

// Type of transmitted frames
// The frame is a Control Wrapper Frame when typeTx is 1 (Control) and sybtypeTx is 7
assign controlWrapperFrame = ((typeTx == 2'b01) && (subtypeTx == 4'b0111)) ? 1'b1 : 1'b0;

// The frame is a QoS Frame when typeTx is 2 (Data) and sybtypeTx bigger or equal to 8
assign qosFrame = ((typeTx == 2'b10) && subtypeTx[3]) ? 1'b1 : 1'b0;

// The frame is an HTC Frame is this is a ControlWrapperFrame or a QoS or management frame with the order bit set.
assign htcFrame = (((qosFrame || (typeTx == 2'b00)) && order) || (controlWrapperFrame)) ? 1'b1 : 1'b0;

// The frame is a Beacon Frame when typeTx is 0 (Management) and sybtypeTx is 8
assign isBeacon = ((typeTx == 2'b00) && (subtypeTx == 4'b1000)) ? 1'b1 : 1'b0;

// The frame is a Probe Response Frame when typeTx is 0 (Management) and sybtypeTx is 5
assign isProbeResponse = ((typeTx == 2'b00) && (subtypeTx == 4'b0101)) ? 1'b1 : 1'b0;



// This combinational process assigns the number of bytes contained into the current field as well as the 
// offset of the current field in the TX Header Descriptor.
// Note that fieldBytes is 1 byte less than the number of byte of the field because
// it is used as reference for the txByteCnt counter which starts at 0.
always @ *
begin
  case (formatMPDUFSMCs)
  
    FD_FRMCNTRL_BYTE1 :
      begin 
        fieldBytes      = 16'd0;
        fieldOffset     = FRMCNTRL_BYTE1_OFFSET;
      end
  
    FD_FRMCNTRL_BYTE2 :
      begin 
        fieldBytes      = 16'd0;
        fieldOffset     = FRMCNTRL_BYTE2_OFFSET;
      end
  
    FD_DURID_DATA :
      begin 
        fieldBytes      = DURID_BYTECNT - 16'd1;
        fieldOffset     = DURID_OFFSET;
      end
      
    FD_ADDR1 : 
      begin 
        fieldBytes      = ADDR_BYTECNT - 16'd1;
        fieldOffset     = ADDR1_OFFSET;
      end
    
    FD_ADDR2 : 
      begin 
        fieldBytes      = ADDR_BYTECNT - 16'd1;
        fieldOffset     = ADDR2_OFFSET;
      end

    FD_ADDR3 : 
      begin 
        fieldBytes      = ADDR_BYTECNT - 16'd1;
        fieldOffset     = ADDR3_OFFSET;
      end

    FD_ADDR4 : 
      begin 
        fieldBytes      = ADDR_BYTECNT - 16'd1;
        fieldOffset     = ADDR4_OFFSET;
      end

    FD_SQNCNTRL : 
      begin 
        fieldBytes      = SQNCNTRL_BYTECNT - 16'd1;
        fieldOffset     = SQNCNTRL_OFFSET;
      end

    FD_QOSCNTRL : 
      begin 
        fieldBytes      = QOSCNTRL_BYTECNT - 16'd1;
        fieldOffset     = QOSCNTRL_OFFSET;
      end

    FD_CFCNTRL : 
      begin 
        fieldBytes      = CFCNTRL_BYTECNT - 16'd1;
        fieldOffset     = CFCNTRL_OFFSET;
      end

    FD_HTCNTRL : 
      begin 
        fieldBytes      = HTCNTRL_BYTECNT - 16'd1;
        fieldOffset     = HTCNTRL_OFFSET;
      end

    FD_TSF : 
      begin 
        fieldBytes      = TSF_BYTECNT - 16'd1;
        fieldOffset     = TSF_OFFSET;
      end

    `ifdef ENCRYPTION
    FD_IV : 
      begin 
        fieldBytes      = IV_BYTECNT - 16'd1;
        fieldOffset     = IV_OFFSET;
      end

    FD_EXTIV : 
      begin 
        fieldBytes      = EXTIV_BYTECNT - 16'd1;
        fieldOffset     = EXTIV_OFFSET;
      end
    `endif // ENCRYPTION

     `ifdef RW_WAPI_EN
     FD_WAPI_KEYIDX :
       begin
         fieldBytes      = WAPI_KEYIDX_BYTECNT - 16'd1;
         fieldOffset     = WAPI_KEYIDX_OFFSET;
       end 
     FD_WAPI_PN :
      begin
         fieldBytes      = WAPI_PN_BYTECNT - 16'd1;
         fieldOffset     = WAPI_PN_OFFSET;
      end 
    `endif //RW_WAPI_EN       
   
    FD_FRM_BODY :
      begin 
        fieldBytes = (frameBodyLength > 16'd0) ? frameBodyLength - 16'd1 : 16'd0;
        if (dontGenerateMH)
          fieldOffset   = 16'b0;
        else
        begin
          if (isBeacon || isProbeResponse)
            fieldOffset = FRM_BODY_OFFSET + 16'd8;
          else  
`ifdef RW_WAPI_EN
            fieldOffset = txWAPI ? FRM_BODY_OFFSET + 16'd10 : FRM_BODY_OFFSET;
`else
            fieldOffset = FRM_BODY_OFFSET;
`endif
        end  
      end
  
    `ifdef ENCRYPTION
    FD_ICV : 
      begin 
        fieldBytes    = ICV_BYTECNT - 16'd1;
        fieldOffset   = frameBodyLength + FRM_BODY_OFFSET;
      end

    FD_CCMPMIC : 
      begin 
        fieldBytes    = CCMPMIC_BYTECNT - 16'd1;
        fieldOffset   = frameBodyLength + FRM_BODY_OFFSET;
      end
    `endif // ENCRYPTION
    
    `ifdef RW_WAPI_EN
    FD_WAPIMIC :
      begin
        fieldBytes    = WAPIMIC_BYTECNT - 16'd1;
        fieldOffset   = frameBodyLength + FRM_BODY_OFFSET;
      end
    `endif //RW_WAPI_EN
    
    FD_FCS : 
      begin 
        fieldBytes    = FCS_BYTECNT - 16'd1;    
        if (dontGenerateMH)
          fieldOffset = frameBodyLength;
        else
        begin
          `ifdef ENCRYPTION
          if(dontEncrypt || !protectedFrame)
            fieldOffset = frameBodyLength + FCS_OFFSET;
          else
          begin
            if(txWEP || txTKIP)
              fieldOffset = frameBodyLength + ICV_BYTECNT + FCS_OFFSET;
            else if(txCCMP)
              fieldOffset = frameBodyLength + CCMPMIC_BYTECNT + FCS_OFFSET;
            `ifdef RW_WAPI_EN
            else if(txWAPI)
              fieldOffset = frameBodyLength + WAPIMIC_BYTECNT + FCS_OFFSET;
            `endif
            else
              fieldOffset = frameBodyLength + FCS_OFFSET;
          end
          `else
           `ifdef RW_WAPI_EN
            if(txWAPI)
              fieldOffset = frameBodyLength + WAPIMIC_BYTECNT + FCS_OFFSET;
            else
            `endif
            fieldOffset = frameBodyLength + FCS_OFFSET;
          `endif // ENCRYPTION
        end
      end

    default :
      begin
        fieldBytes  = 16'd0;
        fieldOffset = 16'd0;
      end  

  endcase   
end


// This process computes the the frame body field length.
// When the first byte of the frame Body is popped from the TX FIFO, the Frame Body length is:
// MPDU Frame Length - number of byte already transmitted - the FCS byte count(4).
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    frameBodyLength      <= 16'b0; 
  end
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
  begin
    frameBodyLength      <= 16'b0; 
  end
  else if(enable)
  begin
    if((formatMPDUFSMCs != FD_FRM_BODY) && (formatMPDUFSMNs == FD_FRM_BODY))
    begin
      if((txWEP || txTKIP) && protectedFrame)
        frameBodyLength <= MPDUFrameLengthTx - readGoodByteCnt - 16'd8; // WEP : ICV (4 bytes) + FCS (4 bytes)
      else if(txCCMP && protectedFrame && (txDataLength > 16'h0))
        frameBodyLength <= MPDUFrameLengthTx - readGoodByteCnt - 16'd12; // CCMP: MIC (8 bytes) + FCS (4 bytes)
      `ifdef RW_WAPI_EN
      else if(txWAPI && protectedFrame && (txDataLength > 16'h0))
        frameBodyLength <= MPDUFrameLengthTx - readGoodByteCnt - 16'd20; // WAPI: MIC (16 bytes) + FCS (4 bytes)
      `endif
      else
        frameBodyLength <= MPDUFrameLengthTx - readGoodByteCnt - 16'd4; // FCS (4 bytes)
    end
  end
end

`ifdef RW_MPDU_AC
assign firstByteOfFrameBody = ((formatMPDUFSMCs == FD_MPDUSTART) && (formatMPDUFSMNs == FD_FRM_BODY));
`else
assign firstByteOfFrameBody = ((formatMPDUFSMCs == FD_FRM_BODY) && (readByteCnt == fieldOffset));
`endif
// Enable the Read process
// When the state machine reaches the FD_STARTTX state, the TX FIFO Read accesses are enabled.
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
   txFIFOReadEn       <= 1'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
    txFIFOReadEn      <= 1'b0; 
  else if(enable)
  begin
    if ((formatMPDUFSMNs == FD_STARTTX) || (formatMPDUFSMNs == FD_FLUSHTXFIFO)) 
      txFIFOReadEn    <= 1'b1;
  end  
end

// Assign TX FIFO Read Enable
// The TX FIFO is read when :
// - The TX FIFO Read is enabled
// - and the end of MPDU is not yet reach in the TX FIFO (MPDU Delimiter != 2)
// - and the TX FIFO is not empty (!txFIFOEmpty)
// - and the FCS Engine is not busy or we are in Flush mode or we are shifting out the FCS signature.
// assign txFIFORead = txFIFOReadEn && !endOfMPDUinTxFifo && !txFIFOEmpty && 
//                           (!fcsBusy || (formatMPDUFSMCs == FD_FLUSHTXFIFO) || (!dontTouchFCS && (formatMPDUFSMCs == FD_FCS))); 
assign txFIFORead = (txFIFOReadEn && !endOfMPDUinTxFifo && !endOfMPDUinTxFifo_fcs && !txFIFOEmpty && !mpduDone_p) &&
                    (!fcsBusy || (formatMPDUFSMCs == FD_FLUSHTXFIFO))                 &&
                    (formatMPDUFSMCs != FD_WAITCCMPMICDONE)                           &&
                    (formatMPDUFSMCs != FD_INITCRYPTO)                                &&
                    (formatMPDUFSMNs != FD_INITCRYPTO)                                &&
                    (formatMPDUFSMNs != FD_MPDUSTART)                                 &&
                    (formatMPDUFSMNs != FD_FCS)                                       &&
                    `ifdef RW_WAPI_EN
                    (!txWAPIBusy || ((formatMPDUFSMCs == FD_WAPI_PN) && (formatMPDUFSMNs != FD_FRM_BODY))) &&
                    `endif //RW_WAPI_EN
                    (!txCCMPBusy || (((formatMPDUFSMCs == FD_IV) || (formatMPDUFSMCs == FD_EXTIV)) && (formatMPDUFSMNs != FD_FRM_BODY))); 


// txFIFOReadByFour and txFIFOReadByTwo indication generation in order to speed up the fecthing of 
// non-transmitted bytes from the TX FIFO.
// When the number of byte until the next valid field is bigger or equal to four, the formatMPDU requests a 
// read by four to the TX FIFO. This flag is set only when the current read byte is the byte 0 of the word.
assign txFIFOReadByFour = ((formatMPDUFSMNs != FD_FRM_BODY) && (readByteCnt + 16'd4 <= fieldOffset) && (fieldOffset > 16'd0) && (readByteCnt[1:0] == 2'b0)) ? 1'b1 : 1'b0;

// When the number of byte until the next valid field is bigger or equal to two, the formatMPDU requests a 
// read by two to the TX FIFO. This flag is set only when the current read byte is the byte 0 or 2 of the word.
//assign txFIFOReadByTwo = ((readByteCnt + 2 <= fieldOffset) && (fieldOffset>0) && readByteCnt[0] == 1'b0) ? 1'b1 : 1'b0;
assign txFIFOReadByTwo = 1'b0; //$todo could be re-enabled once the non-aligned DMA access will be implemented

always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    readDataBank1     <= 8'b0; 
    readDataBank0     <= 8'b0; 
  end
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
  begin
    readDataBank1     <= 8'b0; 
    readDataBank0     <= 8'b0; 
  end
  else if(enable)
  begin
    if (txFIFODataValid)
    begin
      if (writePointer)
        readDataBank1      <= txData;
      else
        readDataBank0      <= txData;
    end    
  end    
end

// Add the TX Delay in PHY and RF to transmit the TSF 
// The timestamp in the beacon should be the TSF contents at the point
// of transmission of the first bit of TSF in the air.
//assign tsfAntenna = tsf + tsfDuration
// tsfDuration is the duration between the beginning of the transmission until the first bit of the TSF field
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    tsfAntenna     <= 64'b0; 
  end
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (formatMPDUFSMCs == FD_IDLE))  // Synchronous Reset
  begin
    tsfAntenna     <= 64'b0; 
  end
  else
  begin
    if (mpduTxStart_p)
      tsfAntenna <= tsf + {48'b0,tsfDuration};
  end    
end

// Compute the offset, from the first byte of the Beacon frame, 
// at which the DTIM field is located.
assign dtimOffset = {8'h0,timOffset} + 16'd2;

// This combinational process patches the MAC Header fields, the TSF and DTIM fields is required.
always @ *
begin
  case (formatMPDUFSMCs)

    FD_FRMCNTRL_BYTE2 :
      begin 

        if (dontTouchFC || dontGenerateMH)
          txData      = txFIFORdData;
        else if (pwrMgt)
          txData      = {txFIFORdData[7:5],1'b1,retry,txFIFORdData[2:0]};
        else   
          txData      = {txFIFORdData[7:4],retry,txFIFORdData[2:0]};

      end
  
    FD_DURID_DATA :
      begin 
        if (dontTouchDur)
          txData      = txFIFORdData;
        else if (sentCFEND)
          txData      = 8'b0;
        else
        begin
          case (readFieldByteCnt[0])
            1'b0 : txData = duration[7:0];
            1'b1 : txData = duration[15:8]; 
          endcase
        end
      end

    FD_TSF :
      begin 
        if (dontTouchTSF)
          txData      = txFIFORdData;
        else
        begin
          case (readFieldByteCnt)
            16'h00     : txData = tsfAntenna[7:0];
            16'h01     : txData = tsfAntenna[15:8]; 
            16'h02     : txData = tsfAntenna[23:16]; 
            16'h03     : txData = tsfAntenna[31:24]; 
            16'h04     : txData = tsfAntenna[39:32];
            16'h05     : txData = tsfAntenna[47:40]; 
            16'h06     : txData = tsfAntenna[55:48]; 
            16'h07     : txData = tsfAntenna[63:56]; 
            // Disable coverage on the default state because it cannot be reached.
            // pragma coverage block = off 
            default    : txData = txFIFORdData;
            // pragma coverage block = on
          endcase
        end
      end

    FD_FRM_BODY :
      begin 
        // If the dontTouchDTIM bit is not see and the frame is a Beacon, the DTIM field has to be updated
        if (!dontTouchDTIM && isBeacon)
        begin
          // When the number of read good bytes reaches the dtimOffset (i.e. timOffset from register plus 2) 
          // the txData is updated by the dtimCnt comming from the Timers module.
          if (readGoodByteCnt == dtimOffset)
            txData = dtimCnt;
          else  
            txData = txFIFORdData;
        end
        else
          txData = txFIFORdData;
            
      end

    default:
      txData  = txFIFORdData;

  endcase
end  



// Detects the end of the MPDU in the TX FIFO based on the MPDU Delimiters.
// When the last byte of the MPDU has been read from the TX FIFO, the flag endOfMPDUinTxFifo is set
// and the read accesses from the TX FIFO are stopped.
assign endOfMPDUinTxFifo = (txFIFODataValid && (txFIFOMPDUDelimiters == 2'b10));

always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    endOfMPDUinTxFifo_fcs <= 1'b0;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))
    endOfMPDUinTxFifo_fcs <= 1'b0;
  else if(enable)
  begin
    if((formatMPDUFSMCs != FD_FLUSHTXFIFO) && endOfMPDUinTxFifo)
      endOfMPDUinTxFifo_fcs <= 1'b1;
  end
end

always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    writePointer     <= 1'b0; 
    readPointer      <= 1'b0; 
  end
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
  begin
    writePointer     <= 1'b0; 
    readPointer      <= 1'b0; 
  end
  else if(enable)
  begin
    if (txFIFODataValid)
    begin
      if (readByteCnt_ff1 >= fieldOffset)     
       writePointer      <= ~writePointer; 
    end   
    if (mpduFCSDInValidTx)
      readPointer      <= ~readPointer; 
  end
end
// Increment the number of bytes read from the TX FIFO.
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    txFIFOReadByFour_ff1      <= 1'b0; 
    txFIFOReadByTwo_ff1       <= 1'b0; 
  end  
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
  begin
    txFIFOReadByFour_ff1      <= 1'b0; 
    txFIFOReadByTwo_ff1       <= 1'b0; 
  end  
  else if(enable)
  begin
    txFIFOReadByFour_ff1      <= txFIFOReadByFour; 
    txFIFOReadByTwo_ff1       <= txFIFOReadByTwo; 
  end  
end

`ifdef RW_MPDU_AC

assign nextcountdone_p = ((readByteCnt_ff1 == fieldBytes + fieldOffset - 16'd1) && (txFIFODataValid)  && (!fcsBusy)) ||
                         ((readByteCnt_ff1 == fieldBytes + fieldOffset)         && (!txFIFODataValid) && (!fcsBusy))    ;
always @(*)
begin
  case(formatMPDUFSMCs)
    FD_ADDR1:
    begin
      if(nextcountdone_p)
      begin
        if(controlWrapperFrame)
          // jump to CFCNTRL
          readByteOffset = CFCNTRL_OFFSET - ADDR1_OFFSET - ADDR_BYTECNT; // 32 - 10 = 12
        else if((typeTx == 2'b01) && ((subtypeTx == 4'b1100) || (subtypeTx == 4'b1101)))
          // jump to MPDU START
          readByteOffset = 16'd46 - ADDR1_OFFSET + ADDR_BYTECNT;
        else
          // jump to ADDR2
          readByteOffset = 16'd0;
      end
      else
        readByteOffset = 16'd0;
    end

    FD_ADDR2:
    begin
      if(nextcountdone_p && (typeTx == 2'b01))
        // jump to MPDU START
        readByteOffset = 16'd46 - ADDR2_OFFSET - ADDR_BYTECNT;
      else
        // jump to ADDR3
        readByteOffset = 16'd0;
    end

    FD_SQNCNTRL:
    begin
      if(nextcountdone_p)
      begin
        if(toDS && fromDS)
          // jump to ADDR4
          readByteOffset = 16'd0;
        else if(qosFrame)
           // jump to QoS
          readByteOffset = QOSCNTRL_OFFSET - SQNCNTRL_OFFSET - SQNCNTRL_BYTECNT; // 30 - 24 = 4
        else if (htcFrame)
          // jump to HTC
          readByteOffset = HTCNTRL_OFFSET  - SQNCNTRL_OFFSET - SQNCNTRL_BYTECNT; // 34 - 24 = 6
        else if (protectedFrame)
          // jump to IV
          readByteOffset = IV_OFFSET       - SQNCNTRL_OFFSET - SQNCNTRL_BYTECNT; // 38 - 24 = 10
        else
          // jump to MPDU START
          readByteOffset = 16'd46          - SQNCNTRL_OFFSET - SQNCNTRL_BYTECNT;
      end
      else
        readByteOffset = 16'd0;
    end

    FD_ADDR4:
    begin
      if(nextcountdone_p)
      begin
        if (qosFrame)
          // jump to QoS
          readByteOffset = 16'd0;
        else if (htcFrame)
          // jump to HTC
          readByteOffset = HTCNTRL_OFFSET  - ADDR4_OFFSET - ADDR_BYTECNT; // 34 - 30 = 4
        else if (protectedFrame)
          // jump to IV
          readByteOffset = IV_OFFSET       - ADDR4_OFFSET - ADDR_BYTECNT; // 38 - 30 = 8
        else
          // jump to MPDU START
          readByteOffset = 16'd46          - ADDR4_OFFSET - ADDR_BYTECNT;
      end
      else
        readByteOffset = 16'd0;
    end

    FD_QOSCNTRL:
    begin
      if (nextcountdone_p)
      begin
        if(htcFrame)
          // jump to HTC
          readByteOffset = HTCNTRL_OFFSET  - QOSCNTRL_OFFSET - QOSCNTRL_BYTECNT;
        else if(protectedFrame)
          // jump to IV
          readByteOffset = IV_OFFSET       - QOSCNTRL_OFFSET - QOSCNTRL_BYTECNT; // 38 - 34 = 4
        else
          // jump to MPDU START
          readByteOffset = 16'd46          - QOSCNTRL_OFFSET - QOSCNTRL_BYTECNT;
      end
      else
        readByteOffset = 16'd0;
    end

    FD_HTCNTRL:
    begin
      if (nextcountdone_p)
      begin
        if(protectedFrame)
          // jump to IV
          readByteOffset = 16'd0;
        else
          // jump to MPDU START
          readByteOffset = 16'd46          - HTCNTRL_OFFSET - HTCNTRL_BYTECNT;
      end
      else
        readByteOffset = 16'd0;
    end

    FD_IV:
    begin
      if (nextcountdone_p)
      begin
        if(txCCMP || txTKIP)
          // jump to Ext IV or Search Key
          readByteOffset = 16'd0;
        else
          // jump to INITCRYPTO or MPDUSTART
          readByteOffset = 16'd46          - IV_OFFSET - IV_BYTECNT;
      end
      else
        readByteOffset = 16'd0;
    end

    default
    begin
      readByteOffset = 16'd0;
    end
  endcase
end

always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    readByteOffset_ff1       <= 6'd0;
  end
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
  begin
    readByteOffset_ff1       <= 6'd0;
  end
  else if(enable)
  begin
    if(nextcountdone_p)
      readByteOffset_ff1     <= readByteOffset[5:0];
    else
      readByteOffset_ff1     <= 6'd0;
  end
end
`endif

// delayed the readByteCnt of one clock cycle
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    readByteCnt_ff1       <= 16'd0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
    readByteCnt_ff1       <= 16'd0; 
  else if(enable)
  begin
    if (txFIFODataValid)
    begin
      if (txFIFOReadByFour_ff1)
        readByteCnt_ff1       <= readByteCnt_ff1 + 16'd4;
      else if (txFIFOReadByTwo_ff1)
        readByteCnt_ff1       <= readByteCnt_ff1 + 16'd2;
      else
        `ifdef RW_MPDU_AC
        readByteCnt_ff1       <= readByteCnt_ff1 + 16'd1 + {10'd0,readByteOffset_ff1[5:0]};
        `else
        readByteCnt_ff1       <= readByteCnt_ff1 + 16'd1;
        `endif
    end
    `ifdef RW_MPDU_AC
    else if((formatMPDUFSMNs==FD_INITCRYPTO) && (formatMPDUFSMCs!=FD_INITCRYPTO))
    begin
      readByteCnt_ff1 <= 16'd46;
    end
    `endif
  end
end

// Increment the number of bytes read from the TX FIFO.
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    readByteCnt       <= 16'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
    readByteCnt       <= 16'b0; 
  else if(enable)
  begin
    if (txFIFORead)
    begin
      if (txFIFOReadByFour)
        readByteCnt       <= readByteCnt + 16'd4;
      else if (txFIFOReadByTwo)
        readByteCnt       <= readByteCnt + 16'd2;
      else
        `ifdef RW_MPDU_AC
        readByteCnt       <= readByteCnt + 16'd1 + readByteOffset[15:0];
        `else
        readByteCnt       <= readByteCnt + 16'd1;
        `endif
    end
    `ifdef RW_MPDU_AC
    else if((formatMPDUFSMNs==FD_INITCRYPTO) && (formatMPDUFSMCs!=FD_INITCRYPTO))
    begin
      readByteCnt <= 16'd46;
    end
    `endif
  end
end

// Increment the number of good bytes read from the TX FIFO.
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    readGoodByteCnt     <= 16'b0; 
  end
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
  begin
    readGoodByteCnt     <= 16'b0; 
  end
  else if(enable)
  begin
    if (txFIFODataValid)
      if ((readByteCnt_ff1 >= fieldOffset) && (readGoodByteCnt < MPDUFrameLengthTx))
        readGoodByteCnt  <= readGoodByteCnt + 16'd1;

  end
end

// This counter allows to count the number of transmitted bytes
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txByteCnt       <= 16'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
    txByteCnt       <= 16'b0; 
  else if(enable)
  begin
    if (fcsEnd_p) 
      txByteCnt       <= txByteCnt + 16'd4;  
    else if (mpduFCSDInValidTx) 
      txByteCnt       <= txByteCnt + 16'd1;  
  end
end

// This counter allows to count the number of bytes read per field
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    readFieldByteCnt       <= 16'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
    readFieldByteCnt       <= 16'b0; 
  else if(enable)
  begin
    if (txFIFODataValid) 
      if (readByteCnt_ff1 >= fieldOffset)
        readFieldByteCnt   <= readFieldByteCnt + 16'd1;  
    if (countDone_p) 
      readFieldByteCnt     <= 16'b0;  
  end
end


// The countDone_p indication used to change the state is generated when the readByteCnt_ff1 counter reaches 
// the end of the corresponding field position in the Transmit Header Descriptor. This position is given by 
// the following formula :
//  fieldBytes  : Number of bytes of the current field.
//  fieldOffset : Number of bytes between the begining of the THD and the current field
// Due to the handshaking, this pulse is generated only when the txFIFODataValid is valid.
// At the end of the transmission (FCS field), the countDone_p pulse is not generated when the last byte of the FCS 
// has been read from the Tx FIFO but when this last bytes has been processed by the FCS Engine.
assign countDone_p = (((formatMPDUFSMCs != FD_FCS) && (txFIFODataValid && (readByteCnt_ff1 == fieldOffset + fieldBytes))) || 
                     endOfFrame || fcsEnd_p) ? 1'b1 : 1'b0;

//assign endOfFrame = ((formatMPDUFSMCs == FD_FCS) && (txByteCnt == MPDUFrameLengthTx)) ? 1'b1 : 1'b0;
assign endOfFrame = (txByteCnt == MPDUFrameLengthTx) ? 1'b1 : 1'b0;


// mpduDone_p pulses generation indicating the end of the DATA frame transmission
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    mpduDone_p       <= 1'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    mpduDone_p       <= 1'b0; 
  else if(enable)
  begin
    // The mpduDone_p pulse is generated when the fcsEnd_p is received
    if ((formatMPDUFSMCs == FD_FCS || formatMPDUFSMCs == FD_FLUSHTXFIFO) && (formatMPDUFSMNs == FD_IDLE))
      mpduDone_p    <= 1'b1; 
  end
end

// SkipMPU request from tx controler logic
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    skipMPDU <= 1'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    skipMPDU <= 1'b0; 
  else
  begin
     if(skipMPDU_p)
       skipMPDU <= 1'b1;
     else if(skipMPDUDone_p)
       skipMPDU <= 1'b0;
  end 
end

// When the FSM moves from FD_FLUSHTXFIFO to FD_IDLE, the skipMPDUDone_p pulse indicating the completion fo the MPDU Skip fro the TX FIFO
// is generated.
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    skipMPDUDone_p   <= 1'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    skipMPDUDone_p   <= 1'b0; 
  else if(enable)
  begin
    if ((formatMPDUFSMCs == FD_FLUSHTXFIFO) && (formatMPDUFSMNs == FD_IDLE) && skipMPDU)
      skipMPDUDone_p <= 1'b1; 
  end
end


// FCS Block Control
////////////////////

// When the state machine is in FD_STARTTX, the FCS Engine is started
assign mpduFCSStart_p   = (formatMPDUFSMCs == FD_STARTTX) ? 1'b1 : 1'b0;


// If dontTouchFCS is not set, the FCS field comes from the FCS engine and not from the TX FIFO. In this case,
// when the number of transmitted bytes reaches the MPDU Frame Length minus 4 (which is the the full frame except the FCS), 
// the FCS engine is requested to shift out the computed signature.
// Note that when mpduFCSShiftTx is set, the Tx Controller does not stop fetching the TX FIFO but stop to send the data 
// to the FCS engine
assign mpduFCSShiftTx   = ((formatMPDUFSMCs != FD_IDLE) && !dontTouchFCS && (txByteCnt >= MPDUFrameLengthTx - 16'd5) && !fcsEnd_p) ? 1'b1 : 1'b0;

// The mpduFCSInValid indicates when the mpduFCSDInTx can be captured by the FCS Engine.
// The mpduFCSDInTx are valid if the number of Good byte read from the TxFifo is bigger than the number of transmitted bytes, 
// the FCS Engine is not busy (fcsBusy low) and we are not shifting the FCS from the FCS Engine.
//assign mpduFCSDInValidTx = ((txByteCnt < readGoodByteCnt) && (formatMPDUFSMCs != FD_FLUSHTXFIFO) && !fcsBusy && !mpduFCSShiftTx) ? 1'b1 : 1'b0; 
`ifdef RW_WAPI_EN
assign mpduFCSDInValidTx = (!firstByteOfFrameBody && protectedFrame && (txWEP || txTKIP || txCCMP || txWAPI) &&              
`else
assign mpduFCSDInValidTx = (!firstByteOfFrameBody && protectedFrame && (txWEP || txTKIP || txCCMP ) &&              
`endif
                                                                       ((formatMPDUFSMCs == FD_FRM_BODY)        || 
                                                                        (formatMPDUFSMCs == FD_WAITCCMPMICDONE) || 
                                                                        (formatMPDUFSMCs == FD_CCMPMIC)         || 
`ifdef RW_WAPI_EN
                                                                        (formatMPDUFSMCs == FD_WAPIMIC)         || 
`endif //RW_WAPI_EN
                                                                        (formatMPDUFSMCs == FD_ICV)             || 
                                                                        (formatMPDUFSMCs == FD_FCS))
                                                                       )                                        ? 
                                                                       txEncrDataValid :
                           ((txByteCnt < readGoodByteCnt) && (formatMPDUFSMCs != FD_FLUSHTXFIFO) && !fcsBusy) ? 1'b1 : 1'b0; 

// The mpduFCSDInTx data provided to the FCS Engine comes fom one of the two banks depending on the readPointer.
`ifdef RW_WAPI_EN
assign mpduFCSDInTx    = (!firstByteOfFrameBody && protectedFrame && (txWEP || txTKIP || txCCMP || txWAPI) && ( (formatMPDUFSMCs == FD_FRM_BODY)        || 
`else 
assign mpduFCSDInTx    = (!firstByteOfFrameBody && protectedFrame && (txWEP || txTKIP || txCCMP) && ( (formatMPDUFSMCs == FD_FRM_BODY)        || 
`endif
                                                                                                      (formatMPDUFSMCs == FD_WAITCCMPMICDONE) || 
                                                                                                      (formatMPDUFSMCs == FD_CCMPMIC)         ||
`ifdef RW_WAPI_EN
                                                                                                      (formatMPDUFSMCs == FD_WAPIMIC)         || 
`endif //RW_WAPI_EN         || 
                                                                                                      (formatMPDUFSMCs == FD_ICV)             || 
                                                                                                      (formatMPDUFSMCs == FD_FCS)
                                                                                                      )) ? txEncrData :
                         (readPointer) ? readDataBank1 : readDataBank0;

assign mpduFCSEnable = (formatMPDUFSMCs != FD_IDLE);


// MAC-PHY Interface management
// ////////////////////////////

always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    wait4Slot       <= 1'b0; 
  end  
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
  begin
    wait4Slot       <= 1'b0; 
  end  
  else
    if (sendMPDU_p && !aMPDU && !useRIFSTx)
      wait4Slot      <= 1'b1; 
    else if (mpduTxStart_p)
      wait4Slot      <= 1'b0; 
end

// When the state machine is in FD_WAIT state and the SIFS or SLOT tick indication is received,
// the Transmission is requested. That guaranty to request the transmission on the sifs boundary
assign mpduTxStart_p    = (wait4Slot && (tickSlot || (tickSIFS && sendOnSIFS))) ? 1'b1 : 1'b0;


//// Flag to memorize the pulse mpduTxStart_p when it is not ampdu
//// It is used to get out of FD_MPDUSTART state
//always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
//begin
//  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
//  begin
//    mpduStarted  <= 1'b0; 
//  end  
//  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
//  begin
//    mpduStarted  <= 1'b0; 
//  end  
//  else 
//  begin
//    if(mpduTxStart_p)
//      mpduStarted  <= 1'b1;
//    else if(mpduDone_p)
//      mpduStarted  <= 1'b0;
//  end
//end

// Debug Interface management
// ////////////////////////////


// mpduDone_p pulses generation indicating the end of the DATA frame transmission
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    fragNumber       <= 4'b0; 
    seqNumber        <= 6'b0; 
  end  
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
  begin
    fragNumber       <= 4'b0; 
    seqNumber        <= 6'b0; 
  end  
  else if(enable)
  begin
    if (formatMPDUFSMCs == FD_SQNCNTRL)
    begin
      case (readFieldByteCnt[0])
        1'b0 : 
          begin
            fragNumber      <= txFIFORdData[3:0];
            seqNumber[3:0]  <= txFIFORdData[7:4]; 
          end  
        1'b1 : 
          seqNumber[5:4]    <= txFIFORdData[1:0]; 
      endcase
    end
  end
end

// mpduDone_p pulses generation indicating the end of the DATA frame transmission
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    Addr1MSB        <= 8'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    Addr1MSB        <= 8'b0; 
  else if(enable)
    if ((formatMPDUFSMCs == FD_SQNCNTRL) && (readFieldByteCnt == 16'h05))
        Addr1MSB <= txFIFORdData;
end

assign formatMPDUFrameDebug1 = { fragNumber, protectedFrame, txPwrMgt, moreFrag, moreData, txRetry, subtypeTx, typeTx};
assign formatMPDUFrameDebug2 = { seqNumber, 1'b0, Addr1MSB};

assign mpduSeqCtrlDone_p = (formatMPDUFSMCs == FD_FRM_BODY) || (formatMPDUFSMCs == FD_FCS);


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// CryptoEngine Control

// SBOX init for TKIP and WEP (reset crypto engine SBOX value from 0 to 255)
assign txSBOXInit  = (txWEP || txTKIP) && (formatMPDUFSMCs != FD_IDLE) && (formatMPDUFSMNs == FD_IDLE) && !aMPDU;

// CCMP Nonce and ADD init for AES MIC (only if the length is > 0)
assign txCCMPStart = (txCCMP && protectedFrame && countDone_p && (formatMPDUFSMCs == FD_EXTIV) && (txDataLength > 16'h0));

`ifdef RW_WAPI_EN
assign txWAPIStart = (txWAPI && protectedFrame && countDone_p && (formatMPDUFSMCs == FD_WAPI_PN) && (txDataLength > 16'h0));
`endif

// ICV enable pulse
assign txICVEnable = ((txWEP || txTKIP) && (formatMPDUFSMCs == FD_FRM_BODY) && (formatMPDUFSMNs == FD_ICV));

// CCMP Header valid signal 
assign txCCMPHeaderValid = (txCCMP && txFIFODataValid && ( (formatMPDUFSMCs == FD_FRMCNTRL_BYTE1) ||
                                                           (formatMPDUFSMCs == FD_FRMCNTRL_BYTE2) ||
                                                           (protectedFrame  && (
                                                                                (formatMPDUFSMCs == FD_DURID_DATA)     ||
                                                                                (formatMPDUFSMCs == FD_ADDR1)          ||
                                                                                (formatMPDUFSMCs == FD_ADDR2)          ||
                                                                                (formatMPDUFSMCs == FD_ADDR3)          ||
                                                                                (formatMPDUFSMCs == FD_SQNCNTRL)       ||
                                                                                (formatMPDUFSMCs == FD_ADDR4)          ||
                                                                                (formatMPDUFSMCs == FD_QOSCNTRL)       ||
                                                                                (formatMPDUFSMCs == FD_HTCNTRL)        ||
                                                                                (formatMPDUFSMCs == FD_EXTIV)          ||
                                                                                `ifdef RW_MPDU_AC
                                                                                (formatMPDUFSMCs == FD_IV)
                                                                                `else
                                                                                ((formatMPDUFSMCs == FD_IV) && (readByteCnt_ff1 >= fieldOffset))
                                                                                `endif
                                                                               )
                                                          )
                                                        )
                           );

// CCMP Data valid signal
assign txCCMPDataValid = (txCCMP && txFIFODataValid && ((formatMPDUFSMCs == FD_FRMCNTRL_BYTE1) ||
                                                        (formatMPDUFSMCs == FD_FRMCNTRL_BYTE2) ||
                                                        (protectedFrame && (
                                                                            (formatMPDUFSMCs == FD_ADDR3)          ||
                                                                            (formatMPDUFSMCs == FD_SQNCNTRL)       ||
                                                                            (formatMPDUFSMCs == FD_ADDR4)          ||
                                                                            (formatMPDUFSMCs == FD_QOSCNTRL)
                                                                           )                   ||
                                                         (txCCMP         && (formatMPDUFSMCs == FD_FRM_BODY))
                                                        )
                                                       )
                         );

`ifdef RW_WAPI_EN
assign txWAPIDataValid = (txWAPI && txFIFODataValid && (formatMPDUFSMCs == FD_FRM_BODY));
`endif //RW_WAPI_EN

// WEP TKIP Data valid signal
assign txWEPTKIPDataValid = ((txWEP || txTKIP) && 
                             protectedFrame    && 
                             txFIFODataValid   && 
                             (((formatMPDUFSMCs == FD_FRM_BODY) && (readByteCnt_ff1 >= fieldOffset)) ||  (formatMPDUFSMCs == FD_ICV)));

// CCMP ADD4 Flag
assign txCCMPAdd4Pres  = (toDS && fromDS);

// CCMP QoS Flag
assign txCCMPQoSPres   = qosFrame;

// Tx IDLE Flag
assign txCsIsIdle      = (formatMPDUFSMCs == FD_IDLE);

// Plain Data to Encrypt Engine
assign txPlainData     = txData;

`ifdef RW_WAPI_EN
// Plain Data Valid
assign txPlainDataValid= (txWAPIDataValid || txCCMPHeaderValid || txCCMPDataValid || txWEPTKIPDataValid);

`else
// Plain Data Valid
assign txPlainDataValid= (txCCMPHeaderValid || txCCMPDataValid || txWEPTKIPDataValid);
`endif //RW_WAPI_EN

// Plain Data end pulse
assign txPlainDataEnd  = (txPlainDataValid && countDone_p && (formatMPDUFSMCs == FD_FRM_BODY));

// CCMP Tx Data length calculation before teh CCMP start pulse
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txDataLength  <= 16'h0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1))  // Synchronous Reset
    txDataLength  <= 16'h0;
  else if(enable)
//    if((formatMPDUFSMCs == FD_EXTIV) && (readByteCnt_ff1 == fieldOffset) && typeTx[1] && (subtypeTx != 4'b0100) && (subtypeTx != 4'b1100))
    if((formatMPDUFSMCs == FD_EXTIV) && (readByteCnt_ff1 == fieldOffset) && protectedFrame)
      txDataLength <= (MPDUFrameLengthTx[15:0] - readGoodByteCnt[15:0] - 16'd8 - 16'd4 - 16'd4);
`ifdef RW_WAPI_EN
    else if((formatMPDUFSMCs == FD_WAPI_KEYIDX) && (readByteCnt_ff1 == fieldOffset) && protectedFrame)
    // encrDataLength     MPDU Length                  Header            KeyIdx   FCS     PN
      txDataLength <= (MPDUFrameLengthTx[15:0] - readGoodByteCnt[15:0] - 16'd18 - 16'd4 - 16'd16);
`endif //RW_WAPI_EN

end

// RSR to store the Packet number for CCMP
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txCCMPSeqCnt   <= 48'h0;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    txCCMPSeqCnt   <= 48'h0;
  else if(enable)
  begin
    if(protectedFrame && txFIFODataValid && ((formatMPDUFSMCs == FD_EXTIV) || ((formatMPDUFSMCs == FD_IV) && ((readByteCnt_ff1 == fieldOffset) || (readByteCnt_ff1 == fieldOffset+16'h1)))))
        txCCMPSeqCnt   <= {txCCMPSeqCnt[39:0],txFIFORdData};
  end
end

// RSR to store the Packet number for TKIP
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txTKIPSeqCnt   <= 48'h0;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    txTKIPSeqCnt   <= 48'h0;
  else if(enable)
  begin
    if(protectedFrame && txFIFODataValid && ((formatMPDUFSMCs == FD_EXTIV) || ((formatMPDUFSMCs == FD_IV) && ((readByteCnt_ff1 == fieldOffset) || (readByteCnt_ff1 == fieldOffset+16'h2)))))
    begin
      if((formatMPDUFSMCs == FD_IV) && (readByteCnt_ff1 == fieldOffset))
        txTKIPSeqCnt[7:0] <= txFIFORdData;
      else if((formatMPDUFSMCs == FD_IV) && (readByteCnt_ff1 == (fieldOffset + 16'h2)))
        txTKIPSeqCnt[15:8] <= txFIFORdData;
      else
        txTKIPSeqCnt   <= {txTKIPSeqCnt[39:0],txFIFORdData};
    end
  end
end

assign txCCMPTKIPSeqCnt = (txTKIP) ? txTKIPSeqCnt :
                          (txCCMP) ? txCCMPSeqCnt :
                                     48'h0;

// CCMP ADD1 LSR
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txCCMPAddr1   <= 48'h0;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    txCCMPAddr1   <= 48'h0;
  else if(enable)
    if((formatMPDUFSMCs == FD_ADDR1) && (txFIFODataValid == 1'b1))
      txCCMPAddr1   <= {txFIFORdData,txCCMPAddr1[47:8]};
end

// CCMP ADD2 LSR
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txCCMPAddr2   <= 48'h0;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    txCCMPAddr2   <= 48'h0;
  else if(enable)
    if((formatMPDUFSMCs == FD_ADDR2) && (txFIFODataValid == 1'b1))
      txCCMPAddr2   <= {txFIFORdData,txCCMPAddr2[47:8]};
end

`ifdef RW_WAPI_EN
// WAPI Frame Control Field 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txWAPIFrameControl <= 16'h0;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    txWAPIFrameControl <= 16'h0;
  else if(enable)
  begin
    if((formatMPDUFSMCs == FD_FRMCNTRL_BYTE1) && (txFIFODataValid == 1'b1))
      txWAPIFrameControl[7:0]  <= txFIFORdData;
    else if((formatMPDUFSMCs == FD_FRMCNTRL_BYTE2) && (txFIFODataValid == 1'b1))
      txWAPIFrameControl[15:8]  <= txFIFORdData;    
  end
end

// WAPI ADDR3 LSR
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txWAPIAddr3   <= 48'h0;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    txWAPIAddr3   <= 48'h0;
  else if(enable)
    if((formatMPDUFSMCs == FD_ADDR3) && (txFIFODataValid == 1'b1))
      txWAPIAddr3   <= {txFIFORdData,txWAPIAddr3[47:8]};
end

// WAPI ADDR4 LSR
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txWAPIAddr4   <= 48'h0;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    txWAPIAddr4   <= 48'h0;
  else if(enable)
    if((formatMPDUFSMCs == FD_ADDR4) && (txFIFODataValid == 1'b1))
      txWAPIAddr4   <= {txFIFORdData,txWAPIAddr4[47:8]};
end

// WAPI QoS Control Field 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txWAPIQoSCF <= 16'h0;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    txWAPIQoSCF <= 16'h0;
  else if(enable)
  begin
    if((formatMPDUFSMCs == FD_QOSCNTRL) && (txFIFODataValid == 1'b1))
      txWAPIQoSCF <= {txFIFORdData,txWAPIQoSCF[15:8]};
  end
end

// WAPI Sequence Control Field 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txWAPISeqControl <= 16'h0;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    txWAPISeqControl <= 16'h0;
  else if(enable)
  begin
    if((formatMPDUFSMCs == FD_SQNCNTRL) && (txFIFODataValid == 1'b1))
      txWAPISeqControl <= {txFIFORdData,txWAPISeqControl[15:8]};
  end
end

// WAPI Key index Field 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txWAPIKeyIdx <= 8'h0;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    txWAPIKeyIdx <= 8'h0;
  else if(enable)
  begin
    // register only the first byte since second byte is the reserved field
    if((formatMPDUFSMCs == FD_WAPI_KEYIDX) && (txFIFODataValid == 1'b1) && ~countDone_p)
      txWAPIKeyIdx <= txFIFORdData;
  end
end

// WAPI Packet Number (PN) Field 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txWAPIPN <= 8'h0;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
    txWAPIPN <= 8'h0;
  else if(enable)
  begin
    if((formatMPDUFSMCs == FD_WAPI_PN) && (txFIFODataValid == 1'b1))
      txWAPIPN <= {txFIFORdData,txWAPIPN[127:8]};
  end
end

`endif //RW_WAPI_EN

// WEP IV Capture and WEP/TKIP IV Valid
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    txWEPIV      <= 24'h0;
    txWEPIVValid <= 1'b0;
  end
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
  begin
    txWEPIV      <= 24'h0;
    txWEPIVValid <= 1'b0;
  end
  else if(enable)
  begin

    if((formatMPDUFSMCs == FD_IV) && txFIFODataValid && protectedFrame && (readByteCnt_ff1 < fieldBytes + fieldOffset))
      txWEPIV <= {txFIFORdData,txWEPIV[23:8]};

    if((formatMPDUFSMCs != FD_INITCRYPTO) && (formatMPDUFSMNs == FD_INITCRYPTO) && (txWEP || txTKIP) && protectedFrame) 
      txWEPIVValid <= 1'b1;
  end
end


// WEP    Flag
// TKIP   Flag
// CCMP   Flag
// CCMPHT Flag
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    txWEP                   <= 1'b0;
    txTKIP                  <= 1'b0;
    txCCMP                  <= 1'b0;
`ifdef RW_WAPI_EN
    txWAPI                  <= 1'b0;
`endif 
    txCCMPHT                <= 1'b0;
    txCryptoKeyValidSaved   <= 1'b0;
    txCryptoKeyValid        <= 1'b0;
  end
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (CSIsIdle == 1'b1)) // Synchronous Reset
  begin
    txWEP                   <= 1'b0;
    txTKIP                  <= 1'b0;
    txCCMP                  <= 1'b0;
`ifdef RW_WAPI_EN
    txWAPI                  <= 1'b0;
`endif 
    txCCMPHT                <= 1'b0;
    txCryptoKeyValidSaved   <= 1'b0;
    txCryptoKeyValid        <= 1'b0;
  end
  else if(enable)
  begin
    if(!dontEncrypt)
    begin
      // by default txCCMP is on for capturing the mac header
      if(formatMPDUFSMCs == FD_STARTTX)
      begin
        if(cTypeRAM == ENCRYPTION_TYPE_WEP)
        begin
          txWEP                 <= 1'b1;
          txTKIP                <= 1'b0;
          txCCMP                <= 1'b0;
`ifdef RW_WAPI_EN
          txWAPI                <= 1'b0;
`endif 
          txCCMPHT              <= 1'b0;
          txCryptoKeyValidSaved <= 1'b1;
        end
        else if(cTypeRAM == ENCRYPTION_TYPE_TKIP)
        begin
          txWEP                 <= 1'b0;
          txTKIP                <= 1'b1;
          txCCMP                <= 1'b0;
`ifdef RW_WAPI_EN
          txWAPI                <= 1'b0;
`endif 
          txCCMPHT              <= 1'b0;
          txCryptoKeyValidSaved <= 1'b1;
        end
        else if(cTypeRAM == ENCRYPTION_TYPE_CCMP)
        begin
          txWEP                   <= 1'b0;
          txTKIP                  <= 1'b0;
          txCCMP                  <= 1'b1;
`ifdef RW_WAPI_EN
          txWAPI                  <= 1'b0;
`endif 
          txCCMPHT                <= ((formatMod == 3'b010) || (formatMod == 3'b011) || (formatMod == 3'b100));
          txCryptoKeyValidSaved   <= 1'b1;
        end
`ifdef RW_WAPI_EN
        else if(cTypeRAM == ENCRYPTION_TYPE_WAPI)
        begin
          txWEP                   <= 1'b0;
          txTKIP                  <= 1'b0;
          txCCMP                  <= 1'b0;
          txWAPI                  <= 1'b1/*((formatMod == 3'b010) || (formatMod == 3'b011) || (formatMod == 3'b100))*/;
          txCCMPHT                <= 1'b0;
          txCryptoKeyValidSaved   <= 1'b1;
        end
`endif //RW_WAPI_EN
        else
        begin
          txWEP                   <= 1'b0;
          txTKIP                  <= 1'b0;
          txCCMP                  <= 1'b0;
`ifdef RW_WAPI_EN
          txWAPI                  <= 1'b0;
`endif 
          txCCMPHT                <= 1'b0;
          txCryptoKeyValidSaved   <= 1'b0;
        end
      end
    
    
      if(((cTypeRAM == ENCRYPTION_TYPE_WEP) && (formatMPDUFSMCs == FD_IV)) ||
`ifdef RW_WAPI_EN
         (formatMPDUFSMCs == FD_EXTIV) || (formatMPDUFSMCs == FD_WAPI_KEYIDX) )
`else
         (formatMPDUFSMCs == FD_EXTIV))
`endif //RW_WAPI_EN
      begin
        txCryptoKeyValid <= txCryptoKeyValidSaved;
      end
    end
  end
end

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// Display FSM State in string for RTL simulation waveform
//////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
// Disable coverage the RW_SIMU_ON part because this code is not functional but 
// here to ease the simulation
// pragma coverage block = off 

// formatMPDUFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (formatMPDUFSMCs)
              FD_IDLE  :  formatMPDUFSMCs_str = {"FD_IDLE"};
        FD_INITCRYPTO  :  formatMPDUFSMCs_str = {"FD_INITCRYPTO"};
           FD_STARTTX  :  formatMPDUFSMCs_str = {"FD_STARTTX"};
    FD_FRMCNTRL_BYTE1  :  formatMPDUFSMCs_str = {"FD_FRMCNTRL_BYTE1"};
    FD_FRMCNTRL_BYTE2  :  formatMPDUFSMCs_str = {"FD_FRMCNTRL_BYTE2"};
        FD_DURID_DATA  :  formatMPDUFSMCs_str = {"FD_DURID_DATA"};
             FD_ADDR1  :  formatMPDUFSMCs_str = {"FD_ADDR1"};
             FD_ADDR2  :  formatMPDUFSMCs_str = {"FD_ADDR2"};
             FD_ADDR3  :  formatMPDUFSMCs_str = {"FD_ADDR3"};
          FD_SQNCNTRL  :  formatMPDUFSMCs_str = {"FD_SQNCNTRL"};
             FD_ADDR4  :  formatMPDUFSMCs_str = {"FD_ADDR4"};
          FD_QOSCNTRL  :  formatMPDUFSMCs_str = {"FD_QOSCNTRL"};
           FD_CFCNTRL  :  formatMPDUFSMCs_str = {"FD_CFCNTRL"};
           FD_HTCNTRL  :  formatMPDUFSMCs_str = {"FD_HTCNTRL"};
               FD_TSF  :  formatMPDUFSMCs_str = {"FD_TSF"};
                FD_IV  :  formatMPDUFSMCs_str = {"FD_IV"};
             FD_EXTIV  :  formatMPDUFSMCs_str = {"FD_EXTIV"};
       FD_WAPI_KEYIDX  :  formatMPDUFSMCs_str = {"FD_WAPI_KEYIDX"};
           FD_WAPI_PN  :  formatMPDUFSMCs_str = {"FD_WAPI_PN"};
         FD_MPDUSTART  :  formatMPDUFSMCs_str = {"FD_MPDUSTART"};
          FD_FRM_BODY  :  formatMPDUFSMCs_str = {"FD_FRM_BODY"};
               FD_ICV  :  formatMPDUFSMCs_str = {"FD_ICV"};
   FD_WAITCCMPMICDONE  :  formatMPDUFSMCs_str = {"FD_WAITCCMPMICDONE"};
           FD_CCMPMIC  :  formatMPDUFSMCs_str = {"FD_CCMPMIC"};
           FD_WAPIMIC  :  formatMPDUFSMCs_str = {"FD_WAPIMIC"};
               FD_FCS  :  formatMPDUFSMCs_str = {"FD_FCS"};
       FD_FLUSHTXFIFO  :  formatMPDUFSMCs_str = {"FD_FLUSHTXFIFO"};
              default  :  formatMPDUFSMCs_str = {"XXX"};
   endcase
end

// Type of transmitted frame displayed in a string to easy simulation and debug
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if ((macCoreClkHardRst_n == 1'b0))  // Asynchronous Reset
    txFrameType_str = {"XXX"};
  else
    if ((MPDUFrameLengthTx == 16'd0) && (formatMPDUFSMCs == FD_STARTTX))
      txFrameType_str = {"NDP"};
    else if (formatMPDUFSMCs == FD_FRMCNTRL_BYTE2)
      casex ({subtypeTx,typeTx})
           6'b000000  :  txFrameType_str = {"ASSOCIATION REQUEST"};
           6'b000100  :  txFrameType_str = {"ASSOCIATION RESPONSE"};
           6'b001000  :  txFrameType_str = {"REASSOCIATION REQUEST"};
           6'b001100  :  txFrameType_str = {"REASSOCIATION RESPONSE"};
           6'b010000  :  txFrameType_str = {"PROBE RESPONSE"};
           6'b010100  :  txFrameType_str = {"PROBE RESPONSE"};
           6'b100000  :  txFrameType_str = {"BEACON"};
           6'b100100  :  txFrameType_str = {"ATIM"};
           6'b101000  :  txFrameType_str = {"DISSASSOCIATION"};
           6'b101100  :  txFrameType_str = {"AUTHENTICATION"};
           6'b110000  :  txFrameType_str = {"DEAUTHENTICATION"};
           6'b110100  :  txFrameType_str = {"ACTION"};
           6'b010001  :  txFrameType_str = {"BEAMFORMING REPORT POLL"};
           6'b010101  :  txFrameType_str = {"VHT NDP ANNOUNCEMENT"};
           6'b011101  :  txFrameType_str = {"CONTROL WRAPPER"};
           6'b100001  :  txFrameType_str = {"BA REQUEST"};
           6'b100101  :  txFrameType_str = {"BA"};
           6'b101001  :  txFrameType_str = {"PS-POLL"};
           6'b101101  :  txFrameType_str = {"RTS"};
           6'b110001  :  txFrameType_str = {"CTS"};
           6'b110101  :  txFrameType_str = {"ACK"};
           6'b111001  :  txFrameType_str = {"CF-END"};
           6'b111101  :  txFrameType_str = {"CF-END+CF-ACK"};
           6'b000010  :  txFrameType_str = {"DATA"};
           6'b000110  :  txFrameType_str = {"DATA+CF-ACK"};
           6'b001010  :  txFrameType_str = {"DATA+CF-POLL"};
           6'b001110  :  txFrameType_str = {"DATA+CF-ACK+CF-POLL"};
           6'b010010  :  txFrameType_str = {"Null"};
           6'b010110  :  txFrameType_str = {"CF-ACK"};
           6'b011010  :  txFrameType_str = {"CF-POLL"};
           6'b011110  :  txFrameType_str = {"CF-ACK+CF-POLL"};
           6'b100010  :  txFrameType_str = {"QoS DATA"};
           6'b100110  :  txFrameType_str = {"QoS DATA+CF-ACK"};
           6'b101010  :  txFrameType_str = {"QoS DATA+CF-POLL"};
           6'b101110  :  txFrameType_str = {"QoS DATA+CF-ACK+CF-POLL"};
           6'b110010  :  txFrameType_str = {"QoS Null"};
           6'b111010  :  txFrameType_str = {"QoS CF-POLL"};
           6'b111110  :  txFrameType_str = {"QoS CF-ACK+CF-POLL"};
             default  :  txFrameType_str = {"UNKNOWN"};
       endcase
end

// Type of encryption displayed in a string to easy simulation and debug
always @*
begin
  case (cTypeRAM)
    ENCRYPTION_TYPE_NONE : encryptionType_str = {"NONE"};
     ENCRYPTION_TYPE_WEP : encryptionType_str = {"WEP"};
    ENCRYPTION_TYPE_TKIP : encryptionType_str = {"TKIP"};
    ENCRYPTION_TYPE_CCMP : encryptionType_str = {"CCMP"};
`ifdef RW_WAPI_EN
    ENCRYPTION_TYPE_WAPI : encryptionType_str = {"WAPI"};
`endif // RW_WAPI_EN
  endcase
end


// pragma coverage block = on 
`endif // RW_SIMU_ON

`ifdef RW_ASSERT_ON

// System Verilog Assertions
////////////////////////////


// Cover Points Definitions
///////////////////////////

//$rw_sva This cover point checks if we are transmitting a CTS Frame
countCTSFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx} == 6'b011100)));

//$rw_sva This cover point checks if we are transmitting a RTS Frame
countRTSFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx} == 6'b011011)));

//$rw_sva This cover point checks if we are transmitting a ACK Frame
countACKFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx} == 6'b011101)));

//$rw_sva This cover point checks if we are transmitting a BA Frame
countBAFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx} == 6'b011001)));

//$rw_sva This cover point checks if we are transmitting a BA_REQ Frame
countBAREQFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx} == 6'b011000)));

//$rw_sva This cover point checks if we are transmitting a CONTROL WRAPPER Frame
countCONTROLWRAPPERFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx} == 6'b010111)));

//$rw_sva This cover point checks if we are transmitting a CF-END Frame
countCFENDFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx} == 6'b011110)));

//$rw_sva This cover point checks if we are transmitting a CF-END+CF-ACK Frame
countCFENDPCFACKFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx} == 6'b011111)));

//$rw_sva This cover point checks if we are transmitting a PS-POLL Frame
countPSPOLLFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx} == 6'b011010)));

//$rw_sva This cover point checks if we are transmitting a Beacon Frame
countBeaconFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx} == 6'b001000)));

//$rw_sva This cover point checks if we are transmitting a Probe Response Frame
countProbeResponseFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx} == 6'b000101)));

//$rw_sva This cover point checks if we are transmitting a QoS Data Frame
countQoSDataFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx[3]} == 3'b101)));

//$rw_sva This cover point checks if we are transmitting a Data Frame
countDataFromFifo: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx[3]} == 3'b100)));

//$rw_sva This cover point checks if we are transmitting a QoS +HTC Frame
countHTCFrame: cover property (@(posedge macCoreTxClk) (mpduDone_p && ({typeTx,subtypeTx[3]} == 3'b101) && htcFrame));

//$rw_sva This cover point checks if we are transmitting a Management Frame
countManagementFrame: cover property (@(posedge macCoreTxClk) (mpduDone_p && (typeTx == 3'b00)));

//$rw_sva This cover point checks if we are transmitting an encrypted Frame
countEncryptedFrame: cover property (@(posedge macCoreTxClk) (mpduDone_p && protectedFrame && dontEncrypt));

//$rw_sva This cover point checks if we are transmitting a WDS Frame
countWDSFrame: cover property (@(posedge macCoreTxClk) (mpduDone_p && toDS && fromDS));

`endif // RW_ASSERT_ON


endmodule