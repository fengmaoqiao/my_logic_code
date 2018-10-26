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
// Description      : Module which creates and formats the BLOCK ba frames. 
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

module formatBA (
          //$port_g Clock and Reset interface
          input  wire        macCoreTxClk,          // MAC Core Transmit Clock
          input  wire        macCoreClkHardRst_n,   // Hard Reset of the MAC Core Clock domain 
                                                    // active low
          input  wire        macCoreTxClkSoftRst_n, // Soft Reset of the MAC Core Clock domain 
                                                    // active low
          //$port_g MAC Controller interface
          input  wire [47:0] destAddr,              // Receiver address
          input  wire [47:0] srcAddr,               // Source address
          input  wire [15:0] duration,              // Duration

          //$port_g Tx Controller Main FSM interface
          input  wire        sendBA_p,              // indicates that a ba pBAet has to be sent
          output reg         baDone_p,              // indicates that the ba pBAet has been sent
          output wire        baTxStart_p,           // indicates to the MAC PHY IF that the TX start
          
          //$port_g Rx Controller interface
          input  wire   [3:0] rxTID,                // TID of the received frame

          //$port_g FCS Block interface
          input  wire        fcsEnd_p,              // indicates the end of the transmission
          input  wire        fcsBusy,               // indicates that the FCS block is busy cannot accept new data.
          
          output wire        baFCSEnable,           // Enable the FCS Block
          output wire        baFCSStart_p,          // indicates the begining of the transmission and enable the FCS block
          output wire        baFCSShiftTx,          // indicates FCS engine to append FCS calculated on data
          output reg   [7:0] baFCSDInTx,            // Data to the FCS block
          output wire        baFCSDInValidTx,       // indicates that the data on fcsDInTx is valid and can be processed.

          //$port_g BA Controller
          input  wire  [7:0] psBitmap,              // PS Bitmap field
          input  wire        psBitmapValid,         // PS Bitmap field valid          
          
          output wire        psBitmapReady,         // PS Bitmap field request

          //$port_g Timers Block interface
          input  wire        tickSIFS,              // A pulse to indicate the end of SIFS period

          //$port_g CSReg Block interface
          input  wire        pwrMgt,                // Power Management is enabled for the current

          //$port_g Debug interface
          output reg   [3:0] formatBAFSMCs          // formatBAFSM FSM Current State
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// formatBAFSM FSM states definition
//$fsm_sd formatBAFSM
localparam 
             BA_IDLE  =  4'd0, 
             BA_WAIT  =  4'd1, 
          BA_STARTTX  =  4'd2, 
   BA_FRMCNTRL_BYTE1  =  4'd3, 
   BA_FRMCNTRL_BYTE2  =  4'd4, 
       BA_DURATIONID  =  4'd5, 
               BA_RA  =  4'd6, 
               BA_TA  =  4'd7, 
          BA_CONTROL  =  4'd8, 
             BA_INFO  =  4'd9, 
              BA_FCS  =  4'd10; 
               


localparam
           RA_BYTECNT = 4'd6,     // Number of bytes of RA field
           TA_BYTECNT = 4'd6,     // Number of bytes of RA field
   DURATIONID_BYTECNT = 4'd2,     // Number of bytes of Duration ID field
      CONTROL_BYTECNT = 4'd2,     // Number of bytes of ba Control field
         INFO_BYTECNT = 4'd10,     // Number of bytes of ba Information field
        CNTRLFRM_TYPE = 2'b01,    // Control Frame Type
           BA_SUBTYPE = 4'b1001,  // ba Frame Sub-Type
     PROTOCOL_VERSION = 2'b00;    // Protocol version
          

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// formatBAFSM FSM signals definition
reg [3:0] formatBAFSMNs;  // formatBAFSM FSM Next State


`ifdef RW_SIMU_ON
// String definition to display formatBAFSM current state
reg [22*8:0] formatBAFSMCs_str;
`endif // RW_SIMU_ON


wire       countDone_p;     // Pulse to indicate the end of a multiple bytes field
reg  [3:0] byteCnt;         // Counts the number of bytes
wire       byteCntEn;       // Enable the byteCnt counter
reg  [3:0] nBytes;          // Number of bytes of the current field

wire       baActive;        // Indicate that formatBA is active

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// formatBAFSM FSM Current State Logic 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    formatBAFSMCs <= BA_IDLE; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    formatBAFSMCs <= BA_IDLE; 
  else
    formatBAFSMCs <= formatBAFSMNs; 
end


// formatBAFSM FSM Next State Logic.
always @* 
begin
  case(formatBAFSMCs)

    BA_IDLE:
      //$fsm_s In BA_IDLE state, the state machine waits until it is triggered by 
      //the MAC Controller
      if (sendBA_p) 
        //$fsm_t When sendBA_p is received, the state machine goes to BA_WAIT state
        formatBAFSMNs = BA_WAIT; 
      else
        //$fsm_t While sendBA_p is not received, the state machine stays in BA_IDLE state
        formatBAFSMNs = BA_IDLE;

    BA_WAIT:
      //$fsm_s In BA_WAIT state, the state machine waits for a SIFS tick. Once received, the 
      // MAC-PHY IF is triggered 
      if (tickSIFS) 
        //$fsm_t When tickSIFS is true, the state machine goes to BA_STARTTX state
        formatBAFSMNs = BA_STARTTX; 
      else
        //$fsm_t While tickSIFS is not received, the state machine stays in BA_WAIT state
        formatBAFSMNs = BA_WAIT;

    BA_STARTTX:
      //$fsm_s In BA_STARTTX state, the state machine start the FCS engine and the MAC-PHY Interface

      //$fsm_t One clock cycle after, the state machine moves to BA_FRMCNTRL_BYTE1 state
        formatBAFSMNs = BA_FRMCNTRL_BYTE1; 

    BA_FRMCNTRL_BYTE1:
      //$fsm_s In BA_FRMCNTRL_BYTE1 state, the state machine sends the first byte of the ba frame Control
      if (!fcsBusy) 
        //$fsm_t When fcsBusy is low meaning that the FCS is free, the state machine goes to BA_FRMCNTRL_BYTE2 state
        formatBAFSMNs = BA_FRMCNTRL_BYTE2; 
      else
        //$fsm_t When fcsBusy is high meaning that the FCS block is busy, the state machine stays in BA_FRMCNTRL_BYTE1 state
        formatBAFSMNs = BA_FRMCNTRL_BYTE1;

    BA_FRMCNTRL_BYTE2:
      //$fsm_s In BA_FRMCNTRL_BYTE1 state, the state machine sends the second byte of the ba frame Control
      if (!fcsBusy)  
        //$fsm_t When fcsBusy is low meaning that the FCS is free, the state machine goes to BA_DURATIONID state
        formatBAFSMNs = BA_DURATIONID; 
      else
        //$fsm_t When fcsBusy is high meaning that the FCS block is busy, the state machine stays in BA_FRMCNTRL_BYTE2 state
        formatBAFSMNs = BA_FRMCNTRL_BYTE2;

    BA_DURATIONID:
      //$fsm_s In BA_FRMCNTRL_BYTE1 state, the state machine sends the Duration ID to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the Duration ID has been completely sent through the FCS, 
        //the state machine goes to BA_RA state
        formatBAFSMNs = BA_RA; 
      else
        //$fsm_t When countDone_p is low meaning that the Duration ID has not been yet completely sent through the FCS block, 
        //the state machine stays in BA_DURATIONID state
        formatBAFSMNs = BA_DURATIONID;

    BA_RA:
      //$fsm_s In BA_RA state, the state machine sends the RA to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the RA has been completely sent through the FCS, 
        //the state machine goes to BA_TA state
        formatBAFSMNs = BA_TA; 
      else
        //$fsm_t When countDone_p is low meaning that the RA has not been yet completely sent through the FCS block, 
        //the state machine stays in BA_RA state
        formatBAFSMNs = BA_RA;

    BA_TA:
      //$fsm_s In BA_TA state, the state machine sends the TA to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the TA has been completely sent through the FCS, 
        //the state machine goes to BA_CONTROL state
        formatBAFSMNs = BA_CONTROL; 
      else
        //$fsm_t When countDone_p is low meaning that the TA has not been yet completely sent through the FCS block, 
        //the state machine stays in BA_TA state
        formatBAFSMNs = BA_TA;

    BA_CONTROL:
      //$fsm_s In BA_TA state, the state machine sends the ba Control field to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the ba Control field has been completely sent through the FCS, 
        //the state machine goes to BA_INFO state
        formatBAFSMNs = BA_INFO; 
      else
        //$fsm_t When countDone_p is low meaning that the ba Control field has not been yet completely sent through the FCS block, 
        //the state machine stays in BA_CONTROL state
        formatBAFSMNs = BA_CONTROL;

    BA_INFO:
      //$fsm_s In BA_TA state, the state machine sends the ba Information field to FCS block
      if (countDone_p) 
        //$fsm_t When countDone_p is received meaning that the ba Information field has been completely sent through the FCS, 
        //the state machine goes to BA_FCS state
        formatBAFSMNs = BA_FCS; 
      else
        //$fsm_t When countDone_p is low meaning that the ba Information field has not been yet completely sent through the FCS block, 
        //the state machine stays in BA_INFO state
        formatBAFSMNs = BA_INFO;

    BA_FCS:
      //$fsm_s In BA_FCS state, the state machine trigs the FCS block to shift out the FCS value and wait until its completion.
      if (fcsEnd_p) 
        //$fsm_t When fcsEnd_p is received meaning that the FCS has been completely sent, the state machine goes bBA to BA_IDLE state
        formatBAFSMNs = BA_IDLE; 
      else
        //$fsm_t While fcsEnd_p is not received, the state machine stays in BA_FCS state
        formatBAFSMNs = BA_FCS;

     // Disable coverage on the default state because it cannot be reached.
     // pragma coverage block = off 
     default:   
        formatBAFSMNs = BA_IDLE; 
     // pragma coverage block = on 
  endcase
end


// byteCnt counter generation
// This counter allows to count the number of bytes per field
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    byteCnt     <= 4'b0; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    byteCnt     <= 4'b0; 
  else
  begin
    // The counter is incremented only if it is started and when the FCS block is not busy
    if (!fcsBusy && byteCntEn)
    begin
      // While the value of the counter is not equal to nBytes, the byteCnt counter is incremented
      if (byteCnt < nBytes)
        byteCnt <= byteCnt + 4'd1; 
      else
      begin
        byteCnt  <= 4'b0;
      end  
    end
  end      
end

// This combinational process assigns the number of the current field.
// Note that nBytes is 1 byte less than the number of byte of the field because
// it is used as reference for the byteCnt counter which starts at 0.
always @*
begin
  case (formatBAFSMCs)
    BA_DURATIONID : 
      nBytes = DURATIONID_BYTECNT - 4'd1;

    BA_RA : 
      nBytes = RA_BYTECNT - 4'd1;
    
    BA_TA : 
      nBytes = TA_BYTECNT - 4'd1;
    
    BA_CONTROL : 
      nBytes = CONTROL_BYTECNT - 4'd1; // to take into account the clock cycle delay from the BA Controller

    BA_INFO : 
      nBytes = INFO_BYTECNT - 4'd1;
    
    
    default 
      nBytes = 4'd0;
  endcase   
end

// Start the counter in the start which have more that 1 byte length as for DURATIONID and RA. 
assign byteCntEn = ((formatBAFSMCs == BA_DURATIONID) || 
                    (formatBAFSMCs == BA_RA) || 
                    (formatBAFSMCs == BA_TA) || 
                    (formatBAFSMCs == BA_CONTROL) || 
                    ((formatBAFSMCs == BA_INFO) && psBitmapValid)) 
                    ? 1'b1 : 1'b0;

// The countDone_p indication used to change the state is generated when the byteCnt counter reach the nBytes value.
// Due to the handshaking, this pulse is generated only when the fcs is not busy.
// Note also that this pulse is generated only when the counter is started.
assign countDone_p = (byteCntEn && (byteCnt == nBytes) && !fcsBusy) ? 1'b1 : 1'b0;


// baDone_p pulses generation indicating the end of the ba transmission
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    baDone_p       <= 1'b0; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    baDone_p       <= 1'b0; 
  else
  begin
    baDone_p       <= 1'b0; 
    if ((formatBAFSMCs == BA_FCS) && fcsEnd_p)
    // The baDone_p pulse is generated when the fcsEnd_p is received
      baDone_p    <= 1'b1; 
  end
end



// FCS Block Control
////////////////////


// FCS data assignment
always @* 
begin
  case(formatBAFSMCs)

    BA_FRMCNTRL_BYTE1 :
      baFCSDInTx = {BA_SUBTYPE, CNTRLFRM_TYPE, PROTOCOL_VERSION};

    BA_FRMCNTRL_BYTE2 :
      // frame control for ba will be {order = 1'b0, wep = 1'b0, moreData = 1'b0,
      // pwrMgt = pwrMgt, retry = 1'b0, morefrg = 1'b0,  frmDs = 1'b0, toDs = 1'b0
      baFCSDInTx = {3'b0, pwrMgt, 4'b0};

    BA_DURATIONID :
      begin
        case(byteCnt[0])
          1'b0       : baFCSDInTx = duration[7:0];
          1'b1       : baFCSDInTx = duration[15:8];
        endcase
      end

    BA_RA  :
      begin
        case(byteCnt)
          4'd0       : baFCSDInTx = destAddr[7:0];
          4'd1       : baFCSDInTx = destAddr[15:8];
          4'd2       : baFCSDInTx = destAddr[23:16];
          4'd3       : baFCSDInTx = destAddr[31:24];
          4'd4       : baFCSDInTx = destAddr[39:32];
          4'd5       : baFCSDInTx = destAddr[47:40];
          // Disable coverage because in BA_RA state, byteCnt cannot be bigger than 5
          // pragma coverage block = off 
          default    : baFCSDInTx = 8'b0;
          // pragma coverage block = on 
        endcase
      end  

    BA_TA  :
      begin
        case(byteCnt)
          4'd0       : baFCSDInTx = srcAddr[7:0];
          4'd1       : baFCSDInTx = srcAddr[15:8];
          4'd2       : baFCSDInTx = srcAddr[23:16];
          4'd3       : baFCSDInTx = srcAddr[31:24];
          4'd4       : baFCSDInTx = srcAddr[39:32];
          4'd5       : baFCSDInTx = srcAddr[47:40];
          // Disable coverage because in BA_TA state, byteCnt cannot be bigger than 5
          // pragma coverage block = off 
          default    : baFCSDInTx = 8'b0;
          // pragma coverage block = on 
        endcase
      end  

    BA_CONTROL  :
      begin
        case(byteCnt)
          4'd0       : baFCSDInTx = {8'h04};
          4'd1       : baFCSDInTx = {rxTID,4'b0};
          // Disable coverage because in BA_CONTROL state, byteCnt cannot be bigger than 2
          // pragma coverage block = off 
          default    : baFCSDInTx = 8'b0;
          // pragma coverage block = on 
        endcase
      end  

    BA_INFO  :
      baFCSDInTx = psBitmap;

    default : 
      baFCSDInTx = 8'b0;

  endcase
end

// When the state machine is in BA_STARTTX, the FCS Engine is started
assign baFCSStart_p   = (formatBAFSMCs == BA_STARTTX) ? 1'b1 : 1'b0;
// When the state machine  is in BA_FCS state, the FCS engine is requested to shift out the computed signature
assign baFCSShiftTx   = ((formatBAFSMNs == BA_FCS) && !fcsEnd_p) ? 1'b1 : 1'b0;

// Data Valid generation
// The data valid is high when the consumer (here the FCS engine) is not busy.
// In this specific case, the data are valid only when the FSM is in an active state with data
assign baFCSDInValidTx = (formatBAFSMCs == BA_INFO) ? (psBitmapValid && !fcsBusy) : (baActive && !fcsBusy) ? 1'b1 : 1'b0;


// Indicate when the formatBA module is active and shift data to the FCS 
// The BA_STARTTX, BA_WAIT states does not provide data and the BA_FCS neither.
assign baActive = ((formatBAFSMCs != BA_IDLE) &&
                   (formatBAFSMCs != BA_WAIT) && 
                   (formatBAFSMCs != BA_STARTTX) && 
                   (formatBAFSMCs != BA_FCS)) ? 1'b1 : 1'b0; 

// Enable the FCS module.
assign baFCSEnable = (formatBAFSMCs != BA_IDLE);


// ba Interface management
//////////////////////////
assign psBitmapReady = ((formatBAFSMCs == BA_INFO) && !fcsBusy) ? 1'b1 : 1'b0;


// MAC-PHY Interface management
///////////////////////////////

// When the state machine is in BA_WAIT state and the SIFS tick indication is received,
// the Transmission is requested. That guaranty to request the transmission on the sifs boundary
assign baTxStart_p    = ((formatBAFSMCs == BA_WAIT) && tickSIFS) ? 1'b1 : 1'b0;


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

// formatBAFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (formatBAFSMCs)
             BA_IDLE  :  formatBAFSMCs_str = {"BA_IDLE"};
             BA_WAIT  :  formatBAFSMCs_str = {"BA_WAIT"};
          BA_STARTTX  :  formatBAFSMCs_str = {"BA_STARTTX"};
   BA_FRMCNTRL_BYTE1  :  formatBAFSMCs_str = {"BA_FRMCNTRL_BYTE1"};
   BA_FRMCNTRL_BYTE2  :  formatBAFSMCs_str = {"BA_FRMCNTRL_BYTE2"};
       BA_DURATIONID  :  formatBAFSMCs_str = {"BA_DURATIONID"};
               BA_RA  :  formatBAFSMCs_str = {"BA_RA"};
               BA_TA  :  formatBAFSMCs_str = {"BA_TA"};
          BA_CONTROL  :  formatBAFSMCs_str = {"BA_CONTROL"};
             BA_INFO  :  formatBAFSMCs_str = {"BA_INFO"};
              BA_FCS  :  formatBAFSMCs_str = {"BA_FCS"};
             default  :  formatBAFSMCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

endmodule
                 
