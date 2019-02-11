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
// Description      : Module which creates and formats the RTS frames. 
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
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

module formatRTS (
          //$port_g Clock and Reset interface
          input  wire        macCoreTxClk,          // MAC Core Transmit Clock
          input  wire        macCoreClkHardRst_n, // Hard Reset of the MAC Core Clock domain 
                                                    // active low
          input  wire        macCoreTxClkSoftRst_n, // Soft Reset of the MAC Core Clock domain 
                                                    // active low
          //$port_g MAC Controller interface
          input  wire [47:0] destAddr,              // Receiver address
          input  wire [47:0] srcAddr,               // Source address
          input  wire [15:0] duration,              // Duration
          input  wire        txBWSignaling,         // Transmission with BW Signaling

          //$port_g Tx Controller Main FSM interface
          input  wire        sendRTS_p,             // Indicates that a RTS packet has to be sent
          input  wire        sendOnPIFS,            // If set, data is sent on tickPIFS else on SIFS
          input  wire        sendOnSIFS,            // If set, data is sent on tickPIFS else on SIFS
          output reg         rtsDone_p,             // indicates that the RTS packet has been sent
          output wire        rtsTxStart_p,          // indicates to the MAC PHY IF that the TX start
          
          //$port_g FCS Block interface
          input  wire        fcsEnd_p,              // indicates the end of the transmission
          input  wire        fcsBusy,               // indicates that the FCS block is busy cannot accept new data.
          
          output wire        rtsFCSEnable,          // Enable the FCS Block
          output wire        rtsFCSStart_p,         // indicates the begining of the transmission and enable the FCS block
          output wire        rtsFCSShiftTx,         // indicates FCS engine to append FCS calculated on data
          output reg   [7:0] rtsFCSDInTx,           // Data to the FCS block
          output wire        rtsFCSDInValidTx,      // indicates that the data on fcsDInTx is valid and can be processed.

          //$port_g Timers Block interface
          input  wire        tickSIFS,            // A pulse to indicate the end of SIFS period
          input  wire        tickPIFS_p,            // A pulse to indicate the end of PIFS period
          input  wire        tickSlot_p,            // A pulse to indicate the end of Slot period

          //$port_g CSReg Block interface
          input  wire        pwrMgt,                // Power Management is enabled for the current

          //$port_g Debug interface
          output reg   [3:0] formatRTSFSMCs         // formatRTSFSM FSM Current State
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// formatRTSFSM FSM states definition
//$fsm_sd formatRTSFSM
localparam 
             RTS_IDLE  =  4'd0, 
             RTS_WAIT  =  4'd1, 
          RTS_STARTTX  =  4'd2, 
   RTS_FRMCNTRL_BYTE1  =  4'd3, 
   RTS_FRMCNTRL_BYTE2  =  4'd4, 
       RTS_DURATIONID  =  4'd5, 
               RTS_RA  =  4'd6, 
               RTS_TA  =  4'd7, 
              RTS_FCS  =  4'd8; 
               


localparam
            RA_BYTECNT = 3'd6,     // Number of bytes of RA field
            TA_BYTECNT = 3'd6,     // Number of bytes of TA field
    DURATIONID_BYTECNT = 3'd2,     // Number of bytes of Duration ID field
         CNTRLFRM_TYPE = 2'b01,    // Control Frame Type
           RTS_SUBTYPE = 4'b1011,  // RTS Frame Sub-Type
      PROTOCOL_VERSION = 2'b00;    // Protocol version
          

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// formatRTSFSM FSM signals definition
reg [3:0] formatRTSFSMNs;  // formatRTSFSM FSM Next State


`ifdef RW_SIMU_ON
// String definition to display formatRTSFSM current state
reg [22*8:0] formatRTSFSMCs_str;
`endif // RW_SIMU_ON


wire       countDone_p;     // Pulse to indicate the end of a multiple bytes field
reg  [2:0] byteCnt;         // Counts the number of bytes
wire       byteCntEn;       // Enable the byteCnt counter
reg  [2:0] nBytes;          // Number of bytes of the current field

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// formatRTSFSM FSM Current State Logic 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    formatRTSFSMCs <= RTS_IDLE; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    formatRTSFSMCs <= RTS_IDLE; 
  else
    formatRTSFSMCs <= formatRTSFSMNs; 
end


// formatRTSFSM FSM Next State Logic.
always @* 
begin
  case(formatRTSFSMCs)

    RTS_IDLE:
      //$fsm_s In RTS_IDLE state, the state machine waits until it is triggered by 
      //the MAC Controller
      if (sendRTS_p) 
        //$fsm_t When sendRTS_p is received, the state machine goes to RTS_WAIT state
        formatRTSFSMNs = RTS_WAIT; 
      else
        //$fsm_t While sendRTS_p is not received, the state machine stays in RTS_IDLE state
        formatRTSFSMNs = RTS_IDLE;

    RTS_WAIT:
      //$fsm_s In RTS_WAIT state, the state machine waits for a PIFS tick (if sendOnPIFS is set. Only used in dual CTS protection mode)
      // Else it waits for a SIFS tick or a Slot tick (depending on sendOnSIFS). Once received, the MAC-PHY IF is triggered 
      if ((sendOnPIFS && tickPIFS_p) || (!sendOnPIFS && sendOnSIFS && tickSIFS) || (!sendOnPIFS && !sendOnSIFS && tickSlot_p))
        //$fsm_t When tickSIFS is true, the state machine goes to RTS_STARTTX state
        formatRTSFSMNs = RTS_STARTTX; 
      else
        //$fsm_t While tickSIFS is not received, the state machine stays in RTS_WAIT state
        formatRTSFSMNs = RTS_WAIT;

    RTS_STARTTX:
      //$fsm_s In RTS_STARTTX state, the state machine start the FCS engine and the MAC-PHY Interface

      //$fsm_t One clock cycle after, the state machine moves to RTS_FRMCNTRL_BYTE1 state
        formatRTSFSMNs = RTS_FRMCNTRL_BYTE1; 

    RTS_FRMCNTRL_BYTE1:
      //$fsm_s In RTS_FRMCNTRL_BYTE1 state, the state machine sends the first byte of the RTS frame Control
      if (!fcsBusy) 
        //$fsm_t When fcsBusy is low meaning that the FCS is free, the state machine goes to RTS_FRMCNTRL_BYTE2 state
        formatRTSFSMNs = RTS_FRMCNTRL_BYTE2; 
      else
        //$fsm_t When fcsBusy is high meaning that the FCS block is busy, the state machine stays in RTS_FRMCNTRL_BYTE1 state
        formatRTSFSMNs = RTS_FRMCNTRL_BYTE1;

    RTS_FRMCNTRL_BYTE2:
      //$fsm_s In RTS_FRMCNTRL_BYTE1 state, the state machine sends the second byte of the RTS frame Control
      if (!fcsBusy)  
        //$fsm_t When fcsBusy is low meaning that the FCS is free, the state machine goes to RTS_DURATIONID state
        formatRTSFSMNs = RTS_DURATIONID; 
      else
        //$fsm_t When fcsBusy is high meaning that the FCS block is busy, the state machine stays in RTS_FRMCNTRL_BYTE2 state
        formatRTSFSMNs = RTS_FRMCNTRL_BYTE2;

    RTS_DURATIONID:
      //$fsm_s In RTS_FRMCNTRL_BYTE1 state, the state machine sends the Duration ID to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the Duration ID has been completely sent through the FCS, 
        //the state machine goes to RTS_RA state
        formatRTSFSMNs = RTS_RA; 
      else
        //$fsm_t When countDone_p is low meaning that the Duration ID has not been yet completely sent through the FCS block, 
        //the state machine stays in RTS_DURATIONID state
        formatRTSFSMNs = RTS_DURATIONID;

    RTS_RA:
      //$fsm_s In RTS_RA state, the state machine sends the RA to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the RA has been completely sent through the FCS, 
        //the state machine goes to RTS_TA state
        formatRTSFSMNs = RTS_TA; 
      else
        //$fsm_t When countDone_p is low meaning that the RA has not been yet completely sent through the FCS block, 
        //the state machine stays in RTS_RA state
        formatRTSFSMNs = RTS_RA;

    RTS_TA:
      //$fsm_s In RTS_RA state, the state machine sends the TA to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the TA has been completely sent through the FCS, 
        //the state machine goes to RTS_FCS state
        formatRTSFSMNs = RTS_FCS; 
      else
        //$fsm_t When countDone_p is low meaning that the TA has not been yet completely sent through the FCS block, 
        //the state machine stays in RTS_TA state
        formatRTSFSMNs = RTS_TA;

    RTS_FCS:
      //$fsm_s In RTS_FCS state, the state machine trigs the FCS block to shift out the FCS value and wait until its completion.
      if (fcsEnd_p) 
        //$fsm_t When fcsEnd_p is received meaning that the FCS has been completely sent, the state machine goes back to RTS_IDLE state
        formatRTSFSMNs = RTS_IDLE; 
      else
        //$fsm_t While fcsEnd_p is not received, the state machine stays in RTS_FCS state
        formatRTSFSMNs = RTS_FCS;

     // Disable coverage on the default state because it cannot be reached.
     // pragma coverage block = off 
     default:   
        formatRTSFSMNs = RTS_IDLE; 
     // pragma coverage block = on 
  endcase
end


// byteCnt counter generation
// This counter allows to count the number of bytes per field
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    byteCnt     <= 3'b0; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    byteCnt     <= 3'b0; 
  else
  begin
    // The counter is incremented only if it is started and when the FCS block is not busy
    if (!fcsBusy && byteCntEn)
    begin
      // While the value of the counter is not equal to nBytes, the byteCnt counter is incremented
//      if ((nBytes != 3'd0) && (byteCnt < nBytes))
      if (byteCnt < nBytes)
        byteCnt <= byteCnt + 3'd1; 
      else
      begin
        byteCnt  <= 3'b0;
      end  
    end
  end      
end

// This combinational process assigns the number of the current field.
// Note that nBytes is 1 byte less than the number of byte of the field because
// it is used as reference for the byteCnt counter which starts at 0.
always @*
begin
  case (formatRTSFSMCs)
    RTS_DURATIONID : 
      nBytes = DURATIONID_BYTECNT - 3'd1;

    RTS_RA : 
      nBytes = RA_BYTECNT - 3'd1;
    
    RTS_TA : 
      nBytes = TA_BYTECNT - 3'd1;
    
    default 
      nBytes = 3'd0;
  endcase   
end

// Start the counter in the start which have more that 1 byte length as for DURATIONID and RA. 
assign byteCntEn = ((formatRTSFSMCs == RTS_DURATIONID) || 
                    (formatRTSFSMCs == RTS_RA)         ||
                    (formatRTSFSMCs == RTS_TA)) 
                    ? 1'b1 : 1'b0;

// The countDone_p indication used to change the state is generated when the byteCnt counter reach the nBytes value.
// Due to the handshaking, this pulse is generated only when the fcs is not busy.
// Note also that this pulse is generated only when the counter is started.
assign countDone_p = (byteCntEn && (byteCnt == nBytes) && !fcsBusy) ? 1'b1 : 1'b0;


// rtsDone_p pulses generation indicating the end of the RTS transmission
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rtsDone_p       <= 1'b0; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    rtsDone_p       <= 1'b0; 
  else
  begin
    rtsDone_p       <= 1'b0; 
    if ((formatRTSFSMCs == RTS_FCS) && fcsEnd_p)
    // The rtsDone_p pulse is generated when the fcsEnd_p is received
      rtsDone_p    <= 1'b1; 
  end
end



// FCS Block Control
////////////////////


// FCS data assignment
always @* 
begin
  case(formatRTSFSMCs)

    RTS_FRMCNTRL_BYTE1 :
      rtsFCSDInTx = {RTS_SUBTYPE, CNTRLFRM_TYPE, PROTOCOL_VERSION};

    RTS_FRMCNTRL_BYTE2 :
      // frame control for RTS will be {order = 1'b0, wep = 1'b0, moreData = 1'b0,
      // pwrMgt = pwrMgt, retry = 1'b0, morefrg = 1'b0,  frmDs = 1'b0, toDs = 1'b0
      rtsFCSDInTx = {3'b0, pwrMgt, 4'b0};

    RTS_DURATIONID :
      begin
        case(byteCnt[0])
          1'b0      : rtsFCSDInTx = duration[7:0];
          1'b1      : rtsFCSDInTx = duration[15:8];
        endcase
      end

    RTS_RA  :
      begin
        case(byteCnt)
          3'b000     : rtsFCSDInTx = destAddr[7:0];
          3'b001     : rtsFCSDInTx = destAddr[15:8];
          3'b010     : rtsFCSDInTx = destAddr[23:16];
          3'b011     : rtsFCSDInTx = destAddr[31:24];
          3'b100     : rtsFCSDInTx = destAddr[39:32];
          3'b101     : rtsFCSDInTx = destAddr[47:40];
          // Disable coverage because in CTS_RA state, byteCnt cannot be bigger than 5
          // pragma coverage block = off 
          default    : rtsFCSDInTx = 8'b0;
          // pragma coverage block = on 
        endcase
      end  

    RTS_TA  :
      begin
        case(byteCnt)
          3'b000     : begin
                         if (txBWSignaling)
                           rtsFCSDInTx = {srcAddr[7:1],txBWSignaling};
                         else
                           rtsFCSDInTx = srcAddr[7:0];
                       end    
          3'b001     : rtsFCSDInTx = srcAddr[15:8];
          3'b010     : rtsFCSDInTx = srcAddr[23:16];
          3'b011     : rtsFCSDInTx = srcAddr[31:24];
          3'b100     : rtsFCSDInTx = srcAddr[39:32];
          3'b101     : rtsFCSDInTx = srcAddr[47:40];
          // Disable coverage because in CTS_TA state, byteCnt cannot be bigger than 5
          // pragma coverage block = off 
          default    : rtsFCSDInTx = 8'b0;
          // pragma coverage block = on 
        endcase
      end  

    default : 
      rtsFCSDInTx = 8'b0;

  endcase
end

// When the state machine is in RTS_STARTTX, the FCS Engine is started
assign rtsFCSStart_p   = (formatRTSFSMCs == RTS_STARTTX) ? 1'b1 : 1'b0;
// When the state machine  is in RTS_FCS state, the FCS engine is requested to shift out the computed signature
//assign rtsFCSShiftTx   = ((formatRTSFSMNs == RTS_FCS) && !fcsEnd_p) ? 1'b1 : 1'b0;
assign rtsFCSShiftTx   = (formatRTSFSMNs == RTS_FCS) ? 1'b1 : 1'b0;

// Data Valid generation
// The data valid is high when the consumer (here the FCS engine) is not busy.
// In this specific case, the data are valid only when the FSM is in an active state with data
// The RTS_STARTTX, RTS_WAIT states does not provide data and the RTS_FCS neither.
assign rtsFCSDInValidTx = ((formatRTSFSMCs != RTS_IDLE) &&
                           (formatRTSFSMCs != RTS_WAIT) && 
                           (formatRTSFSMCs != RTS_STARTTX) &&
                           (formatRTSFSMCs != RTS_FCS) && 
                           !fcsBusy) ? 1'b1 : 1'b0;

assign rtsFCSEnable = (formatRTSFSMCs != RTS_IDLE);

// MAC-PHY Interface management
// ////////////////////////////

// When the state machine is in RTS_WAIT state and the SIFS tick indication is received,
// the Transmission is requested. That guaranty to request the transmission on the sifs boundary
assign rtsTxStart_p    = ((formatRTSFSMCs == RTS_WAIT) && (formatRTSFSMNs == RTS_STARTTX)) ? 1'b1 : 1'b0;


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

// formatRTSFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (formatRTSFSMCs)
             RTS_IDLE  :  formatRTSFSMCs_str = {"RTS_IDLE"};
             RTS_WAIT  :  formatRTSFSMCs_str = {"RTS_WAIT"};
          RTS_STARTTX  :  formatRTSFSMCs_str = {"RTS_STARTTX"};
   RTS_FRMCNTRL_BYTE1  :  formatRTSFSMCs_str = {"RTS_FRMCNTRL_BYTE1"};
   RTS_FRMCNTRL_BYTE2  :  formatRTSFSMCs_str = {"RTS_FRMCNTRL_BYTE2"};
       RTS_DURATIONID  :  formatRTSFSMCs_str = {"RTS_DURATIONID"};
               RTS_RA  :  formatRTSFSMCs_str = {"RTS_RA"};
               RTS_TA  :  formatRTSFSMCs_str = {"RTS_TA"};
              RTS_FCS  :  formatRTSFSMCs_str = {"RTS_FCS"};
              default  :  formatRTSFSMCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

endmodule
                 
