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
// Description      : Module which creates and formats the AMPDU Delimiter. 
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


module formatAMPDUDelimiter (
          //$port_g Clock and Reset interface
          input  wire        macCoreTxClk,          // MAC Core Transmit Clock
          input  wire        macCoreClkHardRst_n, // Hard Reset of the MAC Core Clock domain 
                                                    // active low
          input  wire        macCoreTxClkSoftRst_n, // Soft Reset of the MAC Core Clock domain 
                                                    // active low
          //$port_g Tx Controller Main FSM interface
          input  wire        aMPDUPaddingStart_p,   // indicates that some pad  byte have to be added 
          input  wire        aMPDUDelimiterStart_p, // indicates that the AMPDU Delimiters have to be generated
          input  wire        addBlankDelimiter,     // indicates if blank delimiters shall be added
          output wire        aMPDUDelimiterDone_p,  // indicates that the A-MPDU Delimiter has been sent
          output wire        aMPDUPaddingDone_p,    // indicates that the padding bytes have been sent
          
          //$port_g Tx Parameters Cache interface
          input  wire [15:0] MPDUFrameLengthTx,     // Gives the length of the current MPDU
          input  wire  [9:0] nBlankMDelimiters,     // Indicates the number of blank MPDU delimiters that are inserted
          input  wire        txSingleVHTMPDU,       // Indicates that the AMPDU has only one MPDU
          input  wire  [2:0] formatModTx,           // Indicates that the AMPDU is VHT

          //$port_g MAC-PHY-IF Block interface
          input  wire        mpIfTxFifoFull,        // MAC-PHY FIFO status                      
          output reg   [7:0] aMPDUDelimiterData,    // Data to transmit                 
          output wire        aMPDUDelimiterWriteEn, // Data valid                       

          //$port_g Debug interface
          output reg   [1:0] formatAMPDUDelFSMCs    // formatAMPDUDelFSM FSM Current State
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
localparam DEL_SIGNATURE = 8'h4e;

// formatAMPDUDelFSM FSM states definition
//$fsm_sd formatAMPDUDelFSM
localparam 
                 IDLE  =  2'd0,  // 
      INSERT_BLANKDEL  =  2'd1,  // 
           INSERT_DEL  =  2'd2,  // 
           INSERT_PAD  =  2'd3;  // 


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// formatAMPDUDelFSM FSM signals definition
reg [1:0] formatAMPDUDelFSMNs;  // formatAMPDUDelFSM FSM Next State
  


`ifdef RW_SIMU_ON
// String definition to display formatAMPDUDelFSM current state
reg [15*8:0] formatAMPDUDelFSMCs_str;
`endif // RW_SIMU_ON


reg   [1:0] cnt;
wire  [1:0] delimiterCnt;
wire  [1:0] padCnt;
reg         started;
reg   [7:0] crcCalc;
wire  [7:0] crcCalcInv;
reg   [9:0] nDelimiterSent;
wire        delimiterSent_p;
wire        paddingSent_p;
wire [13:0] length;
reg   [1:0] nPadByte;
reg   [1:0] MPDUFrameLengthTxMod4;


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////



// formatAMPDUDelFSM FSM Current State Logic 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    formatAMPDUDelFSMCs <= IDLE; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    formatAMPDUDelFSMCs <= IDLE; 
  else
    formatAMPDUDelFSMCs <= formatAMPDUDelFSMNs; 
end


// formatAMPDUDelFSM FSM Next State Logic.
always @* 
begin
  case(formatAMPDUDelFSMCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits for a trigger comming for the Tx Controller 
      //main FSM.
      if (aMPDUPaddingStart_p) 
        //$fsm_t When aMPDUPaddingStart_p is received, the state machine goes to INSERT_PAD state
        formatAMPDUDelFSMNs = INSERT_PAD;
      else
      begin
        if (aMPDUDelimiterStart_p)
        begin
          if (addBlankDelimiter)
            //$fsm_t When aMPDUDelimiterStart_p is received and the addBlankDelimiter is set meaning that nBlankMDelimiters 
            //blank delimiters must be inserted, the state machine goes to INSERT_BLANKDEL state.
            formatAMPDUDelFSMNs = INSERT_BLANKDEL;
          else
            //$fsm_t When aMPDUDelimiterStart_p is received and the addBlankDelimiter is reset meaning that no 
            //blank delimiter has to be inserted, the state machine goes to INSERT_PAD state.
            formatAMPDUDelFSMNs = INSERT_DEL;
        end
        else
          //$fsm_t While nothing is not received from the Tx Controller Main FSM, 
          //the state machine stays in IDLE state
          formatAMPDUDelFSMNs = IDLE;
      end  

    INSERT_BLANKDEL:
      //$fsm_s In INSERT_BLANKDEL state, the number of blank delimiters defined in nBlankMDelimiters are inserted.
      // the state machine waits for the completion of the blank delimiters before moving to INSERT_DEL state.
      if (delimiterSent_p && (nBlankMDelimiters - 10'd1 == nDelimiterSent))
        //$fsm_t When delimiterSent_p is received and the number of transmitted delimiters is equal to nBlankMDelimiters, 
        //the state machine goes to INSERT_DEL state.
        formatAMPDUDelFSMNs = INSERT_DEL; 
      else
        //$fsm_t While the number of transmitted delimiters is not equal to nBlankMDelimiters, 
        //the state machine stays in INSERT_BLANKDEL state.
        formatAMPDUDelFSMNs = INSERT_BLANKDEL;

    INSERT_DEL:
      //$fsm_s In INSERT_DEL state, the valid A-MPDU Delimiter is transmitted and the state machine waits until its completion.
      if (delimiterSent_p) 
        //$fsm_t When delimiterSent_p is received, the state machine goes back to IDLE state
        formatAMPDUDelFSMNs = IDLE; 
      else
        //$fsm_t While delimiterSent_p is not received, the state machine stays in INSERT_DEL state
        formatAMPDUDelFSMNs = INSERT_DEL;

    INSERT_PAD:
      //$fsm_s In INSERT_PAD state, the state machine inserts the padding bytes
      if (paddingSent_p) 
        //$fsm_t When paddingSent_p is received indicating that the required number of padding bytes have been successfully
        // transmitted, the state machine goes to IDLE state
        formatAMPDUDelFSMNs = IDLE; 
      else
        //$fsm_t While paddingSent_p is not received, the state machine stays in INSERT_PAD state
        formatAMPDUDelFSMNs = INSERT_PAD;

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
     default:   
        formatAMPDUDelFSMNs = IDLE; 
    // pragma coverage block = on 
  endcase
end


// A-MPDU Delimiter bytes counter.
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    started <= 1'b0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || aMPDUDelimiterDone_p || aMPDUPaddingDone_p)  // Synchronous Reset
    started <= 1'b0; 
  else
    if (aMPDUDelimiterStart_p || aMPDUPaddingStart_p)
      started <= 1'b1; 
end


// A-MPDU bytes counter.
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    cnt <= 2'h0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || !started)  // Synchronous Reset
    cnt <= 2'h0; 
  else
//    if (started && !mpIfTxFifoFull)
    if (!mpIfTxFifoFull)
      cnt <= cnt + 2'h1; 
end

// Count the number of AMPDU Delimiters sent.
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    nDelimiterSent <= 10'h0; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (formatAMPDUDelFSMCs != INSERT_BLANKDEL))  // Synchronous Reset
    nDelimiterSent <= 10'h0; 
  else
    if (delimiterSent_p)
      nDelimiterSent <= nDelimiterSent + 10'h1; 
end

// Assign the length which will be sent in the Delimiter. IN case of Blank delimiter, the length is null.
assign length = (formatAMPDUDelFSMCs == INSERT_BLANKDEL) ? 14'h0000 : MPDUFrameLengthTx[13:0];

assign delimiterCnt = cnt;

assign padCnt = cnt;

// Create the delimiter
always @ *
begin
  if ((formatAMPDUDelFSMCs == INSERT_BLANKDEL) || (formatAMPDUDelFSMCs == INSERT_DEL))
  begin
    case (delimiterCnt)
//      2'h0 : aMPDUDelimiterData = ((formatAMPDUDelFSMCs == INSERT_DEL) && (formatModTx == 3'b100)) ? {length[5:0],1'b0,txSingleVHTMPDU} : {length[3:0],4'b0};
//      2'h1 : aMPDUDelimiterData = ((formatAMPDUDelFSMCs == INSERT_DEL) && (formatModTx == 3'b100)) ? length[13:6] : length[11:4];
      2'h0 : aMPDUDelimiterData = ((formatAMPDUDelFSMCs == INSERT_DEL) && (formatModTx == 3'b100)) ? {length[3:0],length[13:12],1'b0,txSingleVHTMPDU} : {length[3:0],4'b0};
      2'h1 : aMPDUDelimiterData = length[11:4];
      2'h2 : aMPDUDelimiterData = crcCalcInv;
      2'h3 : aMPDUDelimiterData = DEL_SIGNATURE;
    endcase
  end  
  else
    aMPDUDelimiterData = 8'b0;
end


// CRC 8-bit with polynomial x8+x2+x1+1
always @(posedge macCoreTxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    crcCalc <= 8'hff;
  else if ((macCoreTxClkSoftRst_n == 1'b0) || !started || delimiterSent_p)  // Synchronous Reset
    crcCalc <= 8'hff;
//  else if ((started && !mpIfTxFifoFull) && (delimiterCnt < 2'h2))
  else if (!mpIfTxFifoFull && (delimiterCnt < 2'h2))
  begin
    // CRC generation
    crcCalc[0] <= aMPDUDelimiterData[0] ^ aMPDUDelimiterData[1] ^ aMPDUDelimiterData[7] ^ 
                  crcCalc[0] ^ crcCalc[6] ^ crcCalc[7];
    crcCalc[1] <= aMPDUDelimiterData[1] ^ aMPDUDelimiterData[6] ^ aMPDUDelimiterData[7] ^ 
                  crcCalc[0] ^ crcCalc[1] ^ crcCalc[6];
    crcCalc[2] <= aMPDUDelimiterData[1] ^ aMPDUDelimiterData[5] ^ aMPDUDelimiterData[6] ^ 
                  aMPDUDelimiterData[7] ^ crcCalc[0] ^ crcCalc[1] ^ crcCalc[2]  ^
                  crcCalc[6];
    crcCalc[3] <= aMPDUDelimiterData[0] ^ aMPDUDelimiterData[4] ^ aMPDUDelimiterData[5] ^
                  aMPDUDelimiterData[6] ^ crcCalc[1] ^ crcCalc[2] ^ crcCalc[3]  ^ 
                  crcCalc[7];
    crcCalc[4] <= aMPDUDelimiterData[3] ^ aMPDUDelimiterData[4] ^ aMPDUDelimiterData[5] ^
                  crcCalc[2] ^ crcCalc[3] ^ crcCalc[4];
    crcCalc[5] <= aMPDUDelimiterData[2] ^ aMPDUDelimiterData[3] ^ aMPDUDelimiterData[4] ^
                  crcCalc[3] ^ crcCalc[4] ^ crcCalc[5];
    crcCalc[6] <= aMPDUDelimiterData[1] ^ aMPDUDelimiterData[2] ^ aMPDUDelimiterData[3] ^
                  crcCalc[4] ^ crcCalc[5] ^ crcCalc[6];
    crcCalc[7] <= aMPDUDelimiterData[0] ^ aMPDUDelimiterData[1] ^ aMPDUDelimiterData[2] ^
                  crcCalc[5] ^ crcCalc[6] ^ crcCalc[7];
  end
end

assign crcCalcInv = {~crcCalc[0],~crcCalc[1],~crcCalc[2],~crcCalc[3],~crcCalc[4],~crcCalc[5],~crcCalc[6],~crcCalc[7]};


// Modulo 4 of the MPDUFrameLengthTx
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    MPDUFrameLengthTxMod4 <= 2'b00; 
  else if ((macCoreTxClkSoftRst_n == 1'b0) || (paddingSent_p == 1'b1))  // Synchronous Reset
    MPDUFrameLengthTxMod4 <= 2'b00; 
  else
    if (aMPDUPaddingStart_p && (formatAMPDUDelFSMCs != INSERT_PAD))
      MPDUFrameLengthTxMod4 <= MPDUFrameLengthTx[1:0]; 
end

always @ *
begin
  case (MPDUFrameLengthTxMod4[1:0])
    2'b00 : nPadByte = 2'b00;
    2'b01 : nPadByte = 2'b10;
    2'b10 : nPadByte = 2'b01;
    2'b11 : nPadByte = 2'b00;
  endcase
end  



assign aMPDUDelimiterWriteEn = started && !mpIfTxFifoFull;

assign aMPDUDelimiterDone_p = (formatAMPDUDelFSMCs == INSERT_DEL) ? delimiterSent_p : 1'b0;

assign delimiterSent_p = ((delimiterCnt == 2'h3) && !mpIfTxFifoFull) ? 1'b1 : 1'b0;

assign paddingSent_p = ((padCnt == nPadByte) && !mpIfTxFifoFull && (formatAMPDUDelFSMCs == INSERT_PAD)) ? 1'b1 : 1'b0;

assign aMPDUPaddingDone_p = (formatAMPDUDelFSMCs == INSERT_PAD) ? paddingSent_p : 1'b0;



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
// Disable coverage the RW_SIMU_ON part because this code is not functional but 
// here to ease the simulation
// pragma coverage block = off 

// formatAMPDUDelFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (formatAMPDUDelFSMCs)
                 IDLE  :  formatAMPDUDelFSMCs_str = {"IDLE"};
      INSERT_BLANKDEL  :  formatAMPDUDelFSMCs_str = {"INSERT_BLANKDEL"};
           INSERT_DEL  :  formatAMPDUDelFSMCs_str = {"INSERT_DEL"};
           INSERT_PAD  :  formatAMPDUDelFSMCs_str = {"INSERT_PAD"};
              default  :  formatAMPDUDelFSMCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

// System Verilog Assertions
////////////////////////////

`ifdef RW_ASSERT_ON
//$rw_sva This cover point checks if we are adding padding
countIfPaddingAdded: cover property (@(posedge macCoreTxClk) (paddingSent_p));

//$rw_sva This cover point checks if we are adding blank delimiters
countIfBlankDelAdded: cover property (@(posedge macCoreTxClk) (delimiterSent_p && (nBlankMDelimiters > 0)));

`endif // RW_ASSERT_ON

endmodule
                 
