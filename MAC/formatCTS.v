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
// Description      : Module which creates and formats the CTS frames. 
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


module formatCTS (
          //$port_g Clock and Reset interface
          input  wire        macCoreTxClk,          // MAC Core Transmit Clock
          input  wire        macCoreClkHardRst_n, // Hard Reset of the MAC Core Clock domain 
                                                    // active low
          input  wire        macCoreTxClkSoftRst_n, // Soft Reset of the MAC Core Clock domain 
                                                    // active low
          //$port_g MAC Controller interface
          input  wire [47:0] destAddr,              // Receiver address
          input  wire [15:0] duration,              // Duration

          //$port_g Tx Controller Main FSM interface
          input  wire        sendCTS_p,             // indicates that a CTS packet has to be sent
          input  wire        sendOnPIFS,            // If set, data is sent on tickPIFS else on SIFS
          input  wire        sendOnSIFS,            // If set, data is sent on tickPIFS else on SIFS
          output reg         ctsDone_p,             // indicates that the CTS packet has been sent
          output wire        ctsTxStart_p,          // indicates to the MAC PHY IF that the TX start
          
          //$port_g FCS Block interface
          input  wire        fcsEnd_p,              // indicates the end of the transmission
          input  wire        fcsBusy,               // indicates that the FCS block is busy cannot accept new data.
          
          output wire        ctsFCSEnable,          // Enable the FCS Block
          output wire        ctsFCSStart_p,         // indicates the begining of the transmission and enable the FCS block
          output wire        ctsFCSShiftTx,         // indicates FCS engine to append FCS calculated on data
          output reg   [7:0] ctsFCSDInTx,           // Data to the FCS block
          output wire        ctsFCSDInValidTx,      // indicates that the data on fcsDInTx is valid and can be processed.

          //$port_g Timers Block interface
          input  wire        tickSIFS,              // A pulse to indicate the end of SIFS period
          input  wire        tickSlot_p,            // A pulse to indicate the end of Slot period
          input  wire        tickPIFS,              // A pulse to indicate the end of PIFS period

          //$port_g CSReg Block interface
          input  wire        pwrMgt,                // Power Management is enabled for the current

          //$port_g Debug interface
          output reg   [2:0] formatCTSFSMCs         // formatCTSFSM FSM Current State
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// formatCTSFSM FSM states definition
//$fsm_sd formatCTSFSM
localparam 
             CTS_IDLE  =  3'd0, 
             CTS_WAIT  =  3'd1, 
          CTS_STARTTX  =  3'd2, 
   CTS_FRMCNTRL_BYTE1  =  3'd3, 
   CTS_FRMCNTRL_BYTE2  =  3'd4, 
       CTS_DURATIONID  =  3'd5, 
               CTS_RA  =  3'd6, 
              CTS_FCS  =  3'd7; 
               


localparam
           RA_BYTECNT = 3'd6,     // Number of bytes of RA field
   DURATIONID_BYTECNT = 3'd2,     // Number of bytes of Duration ID field
        CNTRLFRM_TYPE = 2'b01,    // Control Frame Type
          CTS_SUBTYPE = 4'b1100,  // CTS Frame Sub-Type
    PROTOCOL_VERSION = 2'b00;    // Protocol version
          

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// formatCTSFSM FSM signals definition
reg [2:0] formatCTSFSMNs;  // formatCTSFSM FSM Next State


`ifdef RW_SIMU_ON
// String definition to display formatCTSFSM current state
reg [22*8:0] formatCTSFSMCs_str;
`endif // RW_SIMU_ON

wire       countDone_p;     // Pulse to indicate the end of a multiple bytes field
reg  [2:0] byteCnt;         // Counts the number of bytes
wire       byteCntEn;       // Enable the byteCnt counter
reg  [2:0] nBytes;          // Number of bytes of the current field

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// formatCTSFSM FSM Current State Logic 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    formatCTSFSMCs <= CTS_IDLE; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    formatCTSFSMCs <= CTS_IDLE; 
  else
    formatCTSFSMCs <= formatCTSFSMNs; 
end


// formatCTSFSM FSM Next State Logic.
always @* 
begin
  case(formatCTSFSMCs)

    CTS_IDLE:
      //$fsm_s In CTS_IDLE state, the state machine waits until it is triggered by 
      //the MAC Controller
      if (sendCTS_p) 
        //$fsm_t When sendCTS_p is received, the state machine goes to CTS_WAIT state
        formatCTSFSMNs = CTS_WAIT; 
      else
        //$fsm_t While sendCTS_p is not received, the state machine stays in CTS_IDLE state
        formatCTSFSMNs = CTS_IDLE;

    CTS_WAIT:
      //$fsm_s In CTS_WAIT state, the state machine waits for a PIFS tick (if sendOnPIFS is set. Only used in dual CTS protection mode)
      // Else it waits for a SIFS tick or a Slot tick (depending on sendOnSIFS). Once received, the MAC-PHY IF is triggered 
      if ((sendOnPIFS && tickPIFS) || (!sendOnPIFS && sendOnSIFS && tickSIFS) || (!sendOnPIFS && !sendOnSIFS && tickSlot_p))
        //$fsm_t When tickSIFS is true, the state machine goes to CTS_STARTTX state
        formatCTSFSMNs = CTS_STARTTX; 
      else
        //$fsm_t While tickSIFS is not received, the state machine stays in CTS_WAIT state
        formatCTSFSMNs = CTS_WAIT;

    CTS_STARTTX:
      //$fsm_s In CTS_STARTTX state, the state machine start the FCS engine and the MAC-PHY Interface

      //$fsm_t One clock cycle after, the state machine moves to CTS_FRMCNTRL_BYTE1 state
        formatCTSFSMNs = CTS_FRMCNTRL_BYTE1; 

    CTS_FRMCNTRL_BYTE1:
      //$fsm_s In CTS_FRMCNTRL_BYTE1 state, the state machine sends the first byte of the CTS frame Control
      if (!fcsBusy) 
        //$fsm_t When fcsBusy is low meaning that the FCS is free, the state machine goes to CTS_FRMCNTRL_BYTE2 state
        formatCTSFSMNs = CTS_FRMCNTRL_BYTE2; 
      else
        //$fsm_t When fcsBusy is high meaning that the FCS block is busy, the state machine stays in CTS_FRMCNTRL_BYTE1 state
        formatCTSFSMNs = CTS_FRMCNTRL_BYTE1;

    CTS_FRMCNTRL_BYTE2:
      //$fsm_s In CTS_FRMCNTRL_BYTE1 state, the state machine sends the second byte of the CTS frame Control
      if (!fcsBusy)  
        //$fsm_t When fcsBusy is low meaning that the FCS is free, the state machine goes to CTS_DURATIONID state
        formatCTSFSMNs = CTS_DURATIONID; 
      else
        //$fsm_t When fcsBusy is high meaning that the FCS block is busy, the state machine stays in CTS_FRMCNTRL_BYTE2 state
        formatCTSFSMNs = CTS_FRMCNTRL_BYTE2;

    CTS_DURATIONID:
      //$fsm_s In CTS_FRMCNTRL_BYTE1 state, the state machine sends the Duration ID to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the Duration ID has been completely sent through the FCS, 
        //the state machine goes to CTS_RA state
        formatCTSFSMNs = CTS_RA; 
      else
        //$fsm_t When countDone_p is low meaning that the Duration ID has not been yet completely sent through the FCS block, 
        //the state machine stays in CTS_DURATIONID state
        formatCTSFSMNs = CTS_DURATIONID;

    CTS_RA:
      //$fsm_s In CTS_RA state, the state machine sends the RA to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the RA has been completely sent through the FCS, 
        //the state machine goes to CTS_FCS state
        formatCTSFSMNs = CTS_FCS; 
      else
        //$fsm_t When countDone_p is low meaning that the RA has not been yet completely sent through the FCS block, 
        //the state machine stays in CTS_RA state
        formatCTSFSMNs = CTS_RA;

    CTS_FCS:
      //$fsm_s In CTS_FCS state, the state machine trigs the FCS block to shift out the FCS value and wait until its completion.
      if (fcsEnd_p) 
        //$fsm_t When fcsEnd_p is received meaning that the FCS has been completely sent, the state machine goes back to CTS_IDLE state
        formatCTSFSMNs = CTS_IDLE; 
      else
        //$fsm_t While fcsEnd_p is not received, the state machine stays in CTS_FCS state
        formatCTSFSMNs = CTS_FCS;

     // Disable coverage on the default state because it cannot be reached.
     // pragma coverage block = off 
     default:   
        formatCTSFSMNs = CTS_IDLE; 
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
  case (formatCTSFSMCs)
    CTS_DURATIONID : 
      nBytes = DURATIONID_BYTECNT - 3'd1;

    CTS_RA : 
      nBytes = RA_BYTECNT - 3'd1;
    
    default 
      nBytes = 3'd0;
  endcase   
end

// Start the counter in the start which have more that 1 byte length as for DURATIONID and RA. 
assign byteCntEn = ((formatCTSFSMCs == CTS_DURATIONID) || 
                    (formatCTSFSMCs == CTS_RA)) 
                    ? 1'b1 : 1'b0;

// The countDone_p indication used to change the state is generated when the byteCnt counter reach the nBytes value.
// Due to the handshaking, this pulse is generated only when the fcs is not busy.
// Note also that this pulse is generated only when the counter is started.
assign countDone_p = (byteCntEn && (byteCnt == nBytes) && !fcsBusy) ? 1'b1 : 1'b0;


// ctsDone_p pulses generation indicating the end of the CTS transmission
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    ctsDone_p       <= 1'b0; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    ctsDone_p       <= 1'b0; 
  else
  begin
    ctsDone_p       <= 1'b0; 
    if ((formatCTSFSMCs == CTS_FCS) && fcsEnd_p)
    // The ctsDone_p pulse is generated when the fcsEnd_p is received
      ctsDone_p    <= 1'b1; 
  end    
end



// FCS Block Control
////////////////////


// FCS data assignment
always @* 
begin
  case(formatCTSFSMCs)

    CTS_FRMCNTRL_BYTE1 :
      ctsFCSDInTx = {CTS_SUBTYPE, CNTRLFRM_TYPE, PROTOCOL_VERSION};

    CTS_FRMCNTRL_BYTE2 :
      // frame control for CTS will be {order = 1'b0, wep = 1'b0, moreData = 1'b0,
      // pwrMgt = pwrMgt, retry = 1'b0, morefrg = 1'b0,  frmDs = 1'b0, toDs = 1'b0
      ctsFCSDInTx = {3'b0, pwrMgt, 4'b0};

    CTS_DURATIONID :
      begin
        case(byteCnt[0])
          1'b0       : ctsFCSDInTx = duration[7:0];
          1'b1       : ctsFCSDInTx = duration[15:8];
        endcase 
      end

    CTS_RA  :
      begin
        case(byteCnt)
          3'b000     : ctsFCSDInTx = destAddr[7:0];
          3'b001     : ctsFCSDInTx = destAddr[15:8];
          3'b010     : ctsFCSDInTx = destAddr[23:16];
          3'b011     : ctsFCSDInTx = destAddr[31:24];
          3'b100     : ctsFCSDInTx = destAddr[39:32];
          3'b101     : ctsFCSDInTx = destAddr[47:40];
          // Disable coverage because in CTS_RA state, byteCnt cannot be bigger than 5
          // pragma coverage block = off 
          default    : ctsFCSDInTx = 8'b0;
          // pragma coverage block = on 
        endcase
      end  

    default : 
      ctsFCSDInTx = 8'b0;

  endcase
end

// When the state machine is in CTS_STARTTX, the FCS Engine is started
assign ctsFCSStart_p   = (formatCTSFSMCs == CTS_STARTTX) ? 1'b1 : 1'b0;
// When the state machine  is in CTS_FCS state, the FCS engine is requested to shift out the computed signature
assign ctsFCSShiftTx   = ((formatCTSFSMNs == CTS_FCS) && !fcsEnd_p) ? 1'b1 : 1'b0;

// Data Valid generation
// The data valid is high when the consumer (here the FCS engine) is not busy.
// In this specific case, the data are valid only when the FSM is in an active state with data
// The CTS_STARTTX, CTS_WAIT states does not provide data and the CTS_FCS neither.
assign ctsFCSDInValidTx = ((formatCTSFSMCs != CTS_IDLE) &&
                           (formatCTSFSMCs != CTS_WAIT) && 
                           (formatCTSFSMCs != CTS_STARTTX) && 
                           (formatCTSFSMCs != CTS_FCS) && 
                           !fcsBusy) ? 1'b1 : 1'b0;

assign ctsFCSEnable = (formatCTSFSMCs != CTS_IDLE);


// MAC-PHY Interface management
// ////////////////////////////

// When the state machine is in CTS_WAIT state and the SIFS tick indication is received,
// the Transmission is requested. That guaranty to request the transmission on the sifs boundary
assign ctsTxStart_p    = ((formatCTSFSMCs == CTS_WAIT) && (formatCTSFSMNs == CTS_STARTTX)) ? 1'b1 : 1'b0;


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

// formatCTSFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (formatCTSFSMCs)
             CTS_IDLE  :  formatCTSFSMCs_str = {"CTS_IDLE"};
             CTS_WAIT  :  formatCTSFSMCs_str = {"CTS_WAIT"};
          CTS_STARTTX  :  formatCTSFSMCs_str = {"CTS_STARTTX"};
   CTS_FRMCNTRL_BYTE1  :  formatCTSFSMCs_str = {"CTS_FRMCNTRL_BYTE1"};
   CTS_FRMCNTRL_BYTE2  :  formatCTSFSMCs_str = {"CTS_FRMCNTRL_BYTE2"};
       CTS_DURATIONID  :  formatCTSFSMCs_str = {"CTS_DURATIONID"};
               CTS_RA  :  formatCTSFSMCs_str = {"CTS_RA"};
              CTS_FCS  :  formatCTSFSMCs_str = {"CTS_FCS"};
              default  :  formatCTSFSMCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

endmodule
                 
