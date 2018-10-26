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
// Description      : Module which creates and formats the ACK frames. 
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

module formatACK (
          //$port_g Clock and Reset interface
          input  wire        macCoreTxClk,          // MAC Core Transmit Clock
          input  wire        macCoreClkHardRst_n,   // Hard Reset of the MAC Core Clock domain 
                                                    // active low
          input  wire        macCoreTxClkSoftRst_n, // Soft Reset of the MAC Core Clock domain 
                                                    // active low
          //$port_g MAC Controller interface
          input  wire [47:0] destAddr,              // Receiver address
          input  wire [15:0] duration,              // Duration

          //$port_g Tx Controller Main FSM interface
          input  wire        sendACK_p,             // indicates that a ACK packet has to be sent
          output reg         ackDone_p,             // indicates that the ACK packet has been sent
          output wire        ackTxStart_p,          // indicates to the MAC PHY IF that the TX start
          
          //$port_g FCS Block interface
          input  wire        fcsEnd_p,              // indicates the end of the transmission
          input  wire        fcsBusy,               // indicates that the FCS block is busy cannot accept new data.
          
          output wire        ackFCSEnable,          // Enable the FCS Block
          output wire        ackFCSStart_p,         // indicates the begining of the transmission and enable the FCS block
          output wire        ackFCSShiftTx,         // indicates FCS engine to append FCS calculated on data
          output reg   [7:0] ackFCSDInTx,           // Data to the FCS block
          output wire        ackFCSDInValidTx,      // indicates that the data on fcsDInTx is valid and can be processed.

          //$port_g Timers Block interface
          input  wire        tickSIFS,              // A pulse to indicate the end of SIFS period

          //$port_g CSReg Block interface
          input  wire        pwrMgt,                // Power Management is enabled for the current

          //$port_g Debug interface
          output reg   [2:0] formatACKFSMCs         // formatACKFSM FSM Current State
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// formatACKFSM FSM states definition
//$fsm_sd formatACKFSM
localparam 
             ACK_IDLE  =  3'd0, 
             ACK_WAIT  =  3'd1, 
          ACK_STARTTX  =  3'd2, 
   ACK_FRMCNTRL_BYTE1  =  3'd3, 
   ACK_FRMCNTRL_BYTE2  =  3'd4, 
       ACK_DURATIONID  =  3'd5, 
               ACK_RA  =  3'd6, 
              ACK_FCS  =  3'd7; 
               


localparam
           RA_BYTECNT = 3'd6,     // Number of bytes of RA field
   DURATIONID_BYTECNT = 3'd2,     // Number of bytes of Duration ID field
        CNTRLFRM_TYPE = 2'b01,    // Control Frame Type
          ACK_SUBTYPE = 4'b1101,  // ACK Frame Sub-Type
     PROTOCOL_VERSION = 2'b00;    // Protocol version
          

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// formatACKFSM FSM signals definition
reg [2:0] formatACKFSMNs;  // formatACKFSM FSM Next State


`ifdef RW_SIMU_ON
// String definition to display formatACKFSM current state
reg [22*8:0] formatACKFSMCs_str;
`endif // RW_SIMU_ON


wire       countDone_p;     // Pulse to indicate the end of a multiple bytes field
reg  [2:0] byteCnt;         // Counts the number of bytes
wire       byteCntEn;       // Enable the byteCnt counter
reg  [2:0] nBytes;          // Number of bytes of the current field

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// formatACKFSM FSM Current State Logic 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    formatACKFSMCs <= ACK_IDLE; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    formatACKFSMCs <= ACK_IDLE; 
  else
    formatACKFSMCs <= formatACKFSMNs; 
end


// formatACKFSM FSM Next State Logic.
always @* 
begin
  case(formatACKFSMCs)

    ACK_IDLE:
      //$fsm_s In ACK_IDLE state, the state machine waits until it is triggered by 
      //the MAC Controller
      if (sendACK_p) 
        //$fsm_t When sendACK_p is received, the state machine goes to ACK_WAIT state
        formatACKFSMNs = ACK_WAIT; 
      else
        //$fsm_t While sendACK_p is not received, the state machine stays in ACK_IDLE state
        formatACKFSMNs = ACK_IDLE;

    ACK_WAIT:
      //$fsm_s In ACK_WAIT state, the state machine waits for a SIFS tick. Once received, the 
      // MAC-PHY IF is triggered 
      if (tickSIFS) 
        //$fsm_t When tickSIFS is true, the state machine goes to ACK_STARTTX state
        formatACKFSMNs = ACK_STARTTX; 
      else
        //$fsm_t While tickSIFS is not received, the state machine stays in ACK_WAIT state
        formatACKFSMNs = ACK_WAIT;

    ACK_STARTTX:
      //$fsm_s In ACK_STARTTX state, the state machine start the FCS engine and the MAC-PHY Interface

      //$fsm_t One clock cycle after, the state machine moves to ACK_FRMCNTRL_BYTE1 state
        formatACKFSMNs = ACK_FRMCNTRL_BYTE1; 

    ACK_FRMCNTRL_BYTE1:
      //$fsm_s In ACK_FRMCNTRL_BYTE1 state, the state machine sends the first byte of the ACK frame Control
      if (!fcsBusy) 
        //$fsm_t When fcsBusy is low meaning that the FCS is free, the state machine goes to ACK_FRMCNTRL_BYTE2 state
        formatACKFSMNs = ACK_FRMCNTRL_BYTE2; 
      else
        //$fsm_t When fcsBusy is high meaning that the FCS block is busy, the state machine stays in ACK_FRMCNTRL_BYTE1 state
        formatACKFSMNs = ACK_FRMCNTRL_BYTE1;

    ACK_FRMCNTRL_BYTE2:
      //$fsm_s In ACK_FRMCNTRL_BYTE1 state, the state machine sends the second byte of the ACK frame Control
      if (!fcsBusy)  
        //$fsm_t When fcsBusy is low meaning that the FCS is free, the state machine goes to ACK_DURATIONID state
        formatACKFSMNs = ACK_DURATIONID; 
      else
        //$fsm_t When fcsBusy is high meaning that the FCS block is busy, the state machine stays in ACK_FRMCNTRL_BYTE2 state
        formatACKFSMNs = ACK_FRMCNTRL_BYTE2;

    ACK_DURATIONID:
      //$fsm_s In ACK_FRMCNTRL_BYTE1 state, the state machine sends the Duration ID to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the Duration ID has been completely sent through the FCS, 
        //the state machine goes to ACK_RA state
        formatACKFSMNs = ACK_RA; 
      else
        //$fsm_t When countDone_p is low meaning that the Duration ID has not been yet completely sent through the FCS block, 
        //the state machine stays in ACK_DURATIONID state
        formatACKFSMNs = ACK_DURATIONID;

    ACK_RA:
      //$fsm_s In ACK_RA state, the state machine sends the RA to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the RA has been completely sent through the FCS, 
        //the state machine goes to ACK_FCS state
        formatACKFSMNs = ACK_FCS; 
      else
        //$fsm_t When countDone_p is low meaning that the RA has not been yet completely sent through the FCS block, 
        //the state machine stays in ACK_RA state
        formatACKFSMNs = ACK_RA;

    ACK_FCS:
      //$fsm_s In ACK_FCS state, the state machine trigs the FCS block to shift out the FCS value and wait until its completion.
      if (fcsEnd_p) 
        //$fsm_t When fcsEnd_p is received meaning that the FCS has been completely sent, the state machine goes back to ACK_IDLE state
        formatACKFSMNs = ACK_IDLE; 
      else
        //$fsm_t While fcsEnd_p is not received, the state machine stays in ACK_FCS state
        formatACKFSMNs = ACK_FCS;

     // Disable coverage on the default state because it cannot be reached.
     // pragma coverage block = off 
     default:   
        formatACKFSMNs = ACK_IDLE; 
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
  case (formatACKFSMCs)
    ACK_DURATIONID : 
      nBytes = DURATIONID_BYTECNT - 3'd1;

    ACK_RA : 
      nBytes = RA_BYTECNT - 3'd1;
    
    default 
      nBytes = 3'd0;
  endcase   
end

// Start the counter in the start which have more that 1 byte length as for DURATIONID and RA. 
assign byteCntEn = ((formatACKFSMCs == ACK_DURATIONID) || 
                    (formatACKFSMCs == ACK_RA)) 
                    ? 1'b1 : 1'b0;

// The countDone_p indication used to change the state is generated when the byteCnt counter reach the nBytes value.
// Due to the handshaking, this pulse is generated only when the fcs is not busy.
// Note also that this pulse is generated only when the counter is started.
assign countDone_p = (byteCntEn && (byteCnt == nBytes) && !fcsBusy) ? 1'b1 : 1'b0;


// ackDone_p pulses generation indicating the end of the ACK transmission
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    ackDone_p       <= 1'b0; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    ackDone_p       <= 1'b0; 
  else
  begin
    ackDone_p       <= 1'b0; 
    if ((formatACKFSMCs == ACK_FCS) && fcsEnd_p)
    // The ackDone_p pulse is generated when the fcsEnd_p is received
      ackDone_p    <= 1'b1; 
  end
end



// FCS Block Control
////////////////////


// FCS data assignment
always @* 
begin
  case(formatACKFSMCs)

    ACK_FRMCNTRL_BYTE1 :
      ackFCSDInTx = {ACK_SUBTYPE, CNTRLFRM_TYPE, PROTOCOL_VERSION};

    ACK_FRMCNTRL_BYTE2 :
      // frame control for ACK will be {order = 1'b0, wep = 1'b0, moreData = 1'b0,
      // pwrMgt = pwrMgt, retry = 1'b0, morefrg = 1'b0,  frmDs = 1'b0, toDs = 1'b0
      ackFCSDInTx = {3'b0, pwrMgt, 4'b0};

    ACK_DURATIONID :
      begin
        case(byteCnt[0])
          1'b0       : ackFCSDInTx = duration[7:0];
          1'b1       : ackFCSDInTx = duration[15:8];
        endcase
      end

    ACK_RA  :
      begin
        case(byteCnt)
          3'b000     : ackFCSDInTx = destAddr[7:0];
          3'b001     : ackFCSDInTx = destAddr[15:8];
          3'b010     : ackFCSDInTx = destAddr[23:16];
          3'b011     : ackFCSDInTx = destAddr[31:24];
          3'b100     : ackFCSDInTx = destAddr[39:32];
          3'b101     : ackFCSDInTx = destAddr[47:40];
          // Disable coverage because in CTS_RA state, byteCnt cannot be bigger than 5
          // pragma coverage block = off 
          default    : ackFCSDInTx = 8'b0;
          // pragma coverage block = on 
        endcase
      end  

    default : 
      ackFCSDInTx = 8'b0;

  endcase
end

// When the state machine is in ACK_STARTTX, the FCS Engine is started
assign ackFCSStart_p   = (formatACKFSMCs == ACK_STARTTX) ? 1'b1 : 1'b0;
// When the state machine  is in ACK_FCS state, the FCS engine is requested to shift out the computed signature
assign ackFCSShiftTx   = ((formatACKFSMNs == ACK_FCS) && !fcsEnd_p) ? 1'b1 : 1'b0;

// Data Valid generation
// The data valid is high when the consumer (here the FCS engine) is not busy.
// In this specific case, the data are valid only when the FSM is in an active state with data
// The ACK_STARTTX, ACK_WAIT states does not provide data and the ACK_FCS neither.
assign ackFCSDInValidTx = ((formatACKFSMCs != ACK_IDLE) &&
                         (formatACKFSMCs != ACK_WAIT) && 
                         (formatACKFSMCs != ACK_STARTTX) && 
                         (formatACKFSMCs != ACK_FCS) && 
                         !fcsBusy) ? 1'b1 : 1'b0;

assign ackFCSEnable = (formatACKFSMCs != ACK_IDLE);


// MAC-PHY Interface management
// ////////////////////////////

// When the state machine is in ACK_WAIT state and the SIFS tick indication is received,
// the Transmission is requested. That guaranty to request the transmission on the sifs boundary
assign ackTxStart_p    = ((formatACKFSMCs == ACK_WAIT) && tickSIFS) ? 1'b1 : 1'b0;


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

// formatACKFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (formatACKFSMCs)
             ACK_IDLE  :  formatACKFSMCs_str = {"ACK_IDLE"};
             ACK_WAIT  :  formatACKFSMCs_str = {"ACK_WAIT"};
          ACK_STARTTX  :  formatACKFSMCs_str = {"ACK_STARTTX"};
   ACK_FRMCNTRL_BYTE1  :  formatACKFSMCs_str = {"ACK_FRMCNTRL_BYTE1"};
   ACK_FRMCNTRL_BYTE2  :  formatACKFSMCs_str = {"ACK_FRMCNTRL_BYTE2"};
       ACK_DURATIONID  :  formatACKFSMCs_str = {"ACK_DURATIONID"};
               ACK_RA  :  formatACKFSMCs_str = {"ACK_RA"};
              ACK_FCS  :  formatACKFSMCs_str = {"ACK_FCS"};
              default  :  formatACKFSMCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

endmodule
                 
