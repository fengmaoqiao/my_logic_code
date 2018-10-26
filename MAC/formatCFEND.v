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
// Description      : Module which creates and formats the CFEND frames. 
//                    
// Simulation Notes : 
//                    
//    For simulation, one define is available
//
//    RW_SIMU_ON   : which creates string signals to display the FSM states on  
//                the waveform viewers
//
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

module formatCFEND (
          //$port_g Clock and Reset interface
          input  wire        macCoreTxClk,          // MAC Core Transmit Clock
          input  wire        macCoreClkHardRst_n, // Hard Reset of the MAC Core Clock domain 
                                                    // active low
          input  wire        macCoreTxClkSoftRst_n, // Soft Reset of the MAC Core Clock domain 
                                                    // active low
          //$port_g Tx Controller Main FSM interface
          input  wire        sendCFEND_p,           // indicates that a CFEND pcfendet has to be sent
          output reg         cfendDone_p,           // indicates that the CFEND pcfendet has been sent
          output wire        cfendTxStart_p,        // indicates to the MAC PHY IF that the TX start
          
          //$port_g FCS Block interface
          input  wire        fcsEnd_p,              // indicates the end of the transmission
          input  wire        fcsBusy,               // indicates that the FCS block is busy cannot accept new data.
          
          output wire        cfendFCSEnable,        // Enable the FCS Block
          output wire        cfendFCSStart_p,       // indicates the begining of the transmission and enable the FCS block
          output wire        cfendFCSShiftTx,       // indicates FCS engine to append FCS calculated on data
          output reg   [7:0] cfendFCSDInTx,         // Data to the FCS block
          output wire        cfendFCSDInValidTx,    // indicates that the data on fcsDInTx is valid and can be processed.

          //$port_g Timers Block interface
          input  wire        tickSIFS,              // A flag to indicate the end of SIFS period

          //$port_g CSReg Block interface
          input  wire [47:0] bssID,                 // BSS ID
          input  wire        pwrMgt,                // Power Management is enabled for the current

          //$port_g Debug interface
          output reg   [3:0] formatCFENDFSMCs       // formatCFENDFSM FSM Current State
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// formatCFENDFSM FSM states definition
//$fsm_sd formatCFENDFSM
localparam 
             CFEND_IDLE  =  4'd0, 
             CFEND_WAIT  =  4'd1, 
          CFEND_STARTTX  =  4'd2, 
   CFEND_FRMCNTRL_BYTE1  =  4'd3, 
   CFEND_FRMCNTRL_BYTE2  =  4'd4, 
       CFEND_DURATIONID  =  4'd5, 
               CFEND_RA  =  4'd6, 
            CFEND_BSSID  =  4'd7, 
              CFEND_FCS  =  4'd8; 
               


localparam
           RA_BYTECNT = 3'd6,     // Number of bytes of RA field
        BSSID_BYTECNT = 3'd6,     // Number of bytes of BSSID field
   DURATIONID_BYTECNT = 3'd2,     // Number of bytes of Duration ID field
        CNTRLFRM_TYPE = 2'b01,    // Control Frame Type
        CFEND_SUBTYPE = 4'b1110,  // CFEND Frame Sub-Type
     PROTOCOL_VERSION = 2'b00;    // Protocol version
          

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// formatCFENDFSM FSM signals definition
reg [3:0] formatCFENDFSMNs;  // formatCFENDFSM FSM Next State


`ifdef RW_SIMU_ON
// String definition to display formatCFENDFSM current state
reg [22*8:0] formatCFENDFSMCs_str;
`endif // RW_SIMU_ON


wire       countDone_p;     // Pulse to indicate the end of a multiple bytes field
reg  [2:0] byteCnt;         // Counts the number of bytes
wire       byteCntEn;       // Enable the byteCnt counter
reg  [2:0] nBytes;          // Number of bytes of the current field

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// formatCFENDFSM FSM Current State Logic 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    formatCFENDFSMCs <= CFEND_IDLE; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    formatCFENDFSMCs <= CFEND_IDLE; 
  else
    formatCFENDFSMCs <= formatCFENDFSMNs; 
end


// formatCFENDFSM FSM Next State Logic.
always @* 
begin
  case(formatCFENDFSMCs)

    CFEND_IDLE:
      //$fsm_s In CFEND_IDLE state, the state machine waits until it is triggered by 
      //the MAC Controller
      if (sendCFEND_p) 
        //$fsm_t When sendCFEND_p is received, the state machine goes to CFEND_WAIT state
        formatCFENDFSMNs = CFEND_WAIT; 
      else
        //$fsm_t While sendCFEND_p is not received, the state machine stays in CFEND_IDLE state
        formatCFENDFSMNs = CFEND_IDLE;

    CFEND_WAIT:
      //$fsm_s In CFEND_WAIT state, the state machine waits for a SIFS tick. Once received, the 
      // MAC-PHY IF is triggered 
      if (tickSIFS) 
        //$fsm_t When tickSIFS is true, the state machine goes to CFEND_STARTTX state
        formatCFENDFSMNs = CFEND_STARTTX; 
      else
        //$fsm_t While tickSIFS is not received, the state machine stays in CFEND_WAIT state
        formatCFENDFSMNs = CFEND_WAIT;

    CFEND_STARTTX:
      //$fsm_s In CFEND_STARTTX state, the state machine start the FCS engine and the MAC-PHY Interface

      //$fsm_t One clock cycle after, the state machine moves to CFEND_FRMCNTRL_BYTE1 state
        formatCFENDFSMNs = CFEND_FRMCNTRL_BYTE1; 

    CFEND_FRMCNTRL_BYTE1:
      //$fsm_s In CFEND_FRMCNTRL_BYTE1 state, the state machine sends the first byte of the CFEND frame Control
      if (!fcsBusy) 
        //$fsm_t When fcsBusy is low meaning that the FCS is free, the state machine goes to CFEND_FRMCNTRL_BYTE2 state
        formatCFENDFSMNs = CFEND_FRMCNTRL_BYTE2; 
      else
        //$fsm_t When fcsBusy is high meaning that the FCS block is busy, the state machine stays in CFEND_FRMCNTRL_BYTE1 state
        formatCFENDFSMNs = CFEND_FRMCNTRL_BYTE1;

    CFEND_FRMCNTRL_BYTE2:
      //$fsm_s In CFEND_FRMCNTRL_BYTE1 state, the state machine sends the second byte of the CFEND frame Control
      if (!fcsBusy)  
        //$fsm_t When fcsBusy is low meaning that the FCS is free, the state machine goes to CFEND_DURATIONID state
        formatCFENDFSMNs = CFEND_DURATIONID; 
      else
        //$fsm_t When fcsBusy is high meaning that the FCS block is busy, the state machine stays in CFEND_FRMCNTRL_BYTE2 state
        formatCFENDFSMNs = CFEND_FRMCNTRL_BYTE2;

    CFEND_DURATIONID:
      //$fsm_s In CFEND_FRMCNTRL_BYTE1 state, the state machine sends the Duration ID to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the Duration ID has been completely sent through the FCS, 
        //the state machine goes to CFEND_RA state
        formatCFENDFSMNs = CFEND_RA; 
      else
        //$fsm_t When countDone_p is low meaning that the Duration ID has not been yet completely sent through the FCS block, 
        //the state machine stays in CFEND_DURATIONID state
        formatCFENDFSMNs = CFEND_DURATIONID;

    CFEND_RA:
      //$fsm_s In CFEND_RA state, the state machine sends the RA to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the RA has been completely sent through the FCS, 
        //the state machine goes to CFEND_BSSID state
        formatCFENDFSMNs = CFEND_BSSID; 
      else
        //$fsm_t When countDone_p is low meaning that the RA has not been yet completely sent through the FCS block, 
        //the state machine stays in CFEND_RA state
        formatCFENDFSMNs = CFEND_RA;

    CFEND_BSSID:
      //$fsm_s In CFEND_BSSID state, the state machine sends the BSSID to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the BSSID has been completely sent through the FCS, 
        //the state machine goes to CFEND_FCS state
        formatCFENDFSMNs = CFEND_FCS; 
      else
        //$fsm_t When countDone_p is low meaning that the BSSID has not been yet completely sent through the FCS block, 
        //the state machine stays in CFEND_BSSID state
        formatCFENDFSMNs = CFEND_BSSID;

    CFEND_FCS:
      //$fsm_s In CFEND_FCS state, the state machine trigs the FCS block to shift out the FCS value and wait until its completion.
      if (fcsEnd_p) 
        //$fsm_t When fcsEnd_p is received meaning that the FCS has been completely sent, the state machine goes bcfend to CFEND_IDLE state
        formatCFENDFSMNs = CFEND_IDLE; 
      else
        //$fsm_t While fcsEnd_p is not received, the state machine stays in CFEND_FCS state
        formatCFENDFSMNs = CFEND_FCS;

     // Disable coverage on the default state because it cannot be reached.
     // pragma coverage block = off 
     default:   
        formatCFENDFSMNs = CFEND_IDLE; 
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
  case (formatCFENDFSMCs)
    CFEND_DURATIONID : 
      nBytes = DURATIONID_BYTECNT - 3'd1;

    CFEND_RA : 
      nBytes = RA_BYTECNT - 3'd1;
    
 CFEND_BSSID : 
      nBytes = BSSID_BYTECNT - 3'd1;
    
    default 
      nBytes = 3'd0;
  endcase   
end

// Start the counter in the start which have more that 1 byte length as for DURATIONID and RA. 
assign byteCntEn = ((formatCFENDFSMCs == CFEND_DURATIONID) || 
                    (formatCFENDFSMCs == CFEND_RA) ||
                    (formatCFENDFSMCs == CFEND_BSSID)) 
                    ? 1'b1 : 1'b0;

// The countDone_p indication used to change the state is generated when the byteCnt counter reach the nBytes value.
// Due to the handshaking, this pulse is generated only when the fcs is not busy.
// Note also that this pulse is generated only when the counter is started.
assign countDone_p = (byteCntEn && (byteCnt == nBytes) && !fcsBusy) ? 1'b1 : 1'b0;


// cfendDone_p pulses generation indicating the end of the CFEND transmission
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    cfendDone_p       <= 1'b0; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    cfendDone_p       <= 1'b0; 
  else
  begin
    cfendDone_p       <= 1'b0; 
    if ((formatCFENDFSMCs == CFEND_FCS) && fcsEnd_p)
    // The cfendDone_p pulse is generated when the fcsEnd_p is received
      cfendDone_p    <= 1'b1; 
  end
end



// FCS Block Control
////////////////////


// FCS data assignment
always @* 
begin
  case(formatCFENDFSMCs)

    CFEND_FRMCNTRL_BYTE1 :
      cfendFCSDInTx = {CFEND_SUBTYPE, CNTRLFRM_TYPE, PROTOCOL_VERSION};

    CFEND_FRMCNTRL_BYTE2 :
      // frame control for CF-END will be {order = 1'b0, wep = 1'b0, moreData = 1'b0,
      // pwrMgt = pwrMgt, retry = 1'b0, morefrg = 1'b0,  frmDs = 1'b0, toDs = 1'b0
      cfendFCSDInTx = {3'b0, pwrMgt, 4'b0};

    CFEND_DURATIONID :
      cfendFCSDInTx = 8'b0;

    CFEND_RA  :
      cfendFCSDInTx = 8'hff;

    CFEND_BSSID  :
      begin
        case(byteCnt)
          3'b000     : cfendFCSDInTx = bssID[7:0];
          3'b001     : cfendFCSDInTx = bssID[15:8];
          3'b010     : cfendFCSDInTx = bssID[23:16];
          3'b011     : cfendFCSDInTx = bssID[31:24];
          3'b100     : cfendFCSDInTx = bssID[39:32];
          3'b101     : cfendFCSDInTx = bssID[47:40];
          // Disable coverage because in CFEND_BSSID state, byteCnt cannot be bigger than 5
          // pragma coverage block = off 
          default    : cfendFCSDInTx = 8'b0;
          // pragma coverage block = on 
        endcase
      end  

    default : 
      cfendFCSDInTx = 8'b0;

  endcase
end

// When the state machine is in CFEND_STARTTX, the FCS Engine is started
assign cfendFCSStart_p   = (formatCFENDFSMCs == CFEND_STARTTX) ? 1'b1 : 1'b0;
// When the state machine  is in CFEND_FCS state, the FCS engine is requested to shift out the computed signature
assign cfendFCSShiftTx   = ((formatCFENDFSMNs == CFEND_FCS) && !fcsEnd_p) ? 1'b1 : 1'b0;

// Data Valid generation
// The data valid is high when the consumer (here the FCS engine) is not busy.
// In this specific case, the data are valid only when the FSM is in an active state with data
// The CFEND_STARTTX, CFEND_WAIT states does not provide data and the CFEND_FCS neither.
assign cfendFCSDInValidTx = ((formatCFENDFSMCs != CFEND_IDLE) &&
                             (formatCFENDFSMCs != CFEND_WAIT) && 
                             (formatCFENDFSMCs != CFEND_STARTTX) && 
                             (formatCFENDFSMCs != CFEND_FCS) && 
                                                   !fcsBusy) ? 1'b1 : 1'b0;


assign cfendFCSEnable = (formatCFENDFSMCs != CFEND_IDLE);

// MAC-PHY Interface management
// ////////////////////////////

// When the state machine is in CFEND_WAIT state and the SIFS tick indication is received,
// the Transmission is requested. That guaranty to request the transmission on the sifs boundary
assign cfendTxStart_p    = ((formatCFENDFSMCs == CFEND_WAIT) && tickSIFS) ? 1'b1 : 1'b0;


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

// formatCFENDFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (formatCFENDFSMCs)
             CFEND_IDLE  :  formatCFENDFSMCs_str = {"CFEND_IDLE"};
             CFEND_WAIT  :  formatCFENDFSMCs_str = {"CFEND_WAIT"};
          CFEND_STARTTX  :  formatCFENDFSMCs_str = {"CFEND_STARTTX"};
   CFEND_FRMCNTRL_BYTE1  :  formatCFENDFSMCs_str = {"CFEND_FRMCNTRL_BYTE1"};
   CFEND_FRMCNTRL_BYTE2  :  formatCFENDFSMCs_str = {"CFEND_FRMCNTRL_BYTE2"};
       CFEND_DURATIONID  :  formatCFENDFSMCs_str = {"CFEND_DURATIONID"};
               CFEND_RA  :  formatCFENDFSMCs_str = {"CFEND_RA"};
            CFEND_BSSID  :  formatCFENDFSMCs_str = {"CFEND_BSSID"};
              CFEND_FCS  :  formatCFENDFSMCs_str = {"CFEND_FCS"};
              default    :  formatCFENDFSMCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

endmodule
                 
