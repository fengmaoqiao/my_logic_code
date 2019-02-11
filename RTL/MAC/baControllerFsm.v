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
// Description      : FSM of baController module
//                    
// Simulation Notes : 
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
`default_nettype none

module baControllerFsm( 
            ///////////////////////////////////////////////
            //$port_g Clock and reset
            ///////////////////////////////////////////////
            input wire         macCoreClk,              // MAC Core Clock
            input wire         macCoreClkHardRst_n,     // Hard Reset of the MAC Core Clock domain active low
            input wire         macCoreClkSoftRst_n,     // Soft Reset of the MAC Core Clock domain
            
            ///////////////////////////////////////////////
            //$port_g TX Controller
            ///////////////////////////////////////////////
            input wire         psBitmapReady,           // PS Bitmap field request

            output reg  [ 7:0] psBitmap,                // PS Bitmap field
            output wire        psBitmapValid,           // PS Bitmap field valid
            
            ///////////////////////////////////////////////
            //$port_g RX Controller
            ///////////////////////////////////////////////
            input wire         psBitmapUpdate_p,        // Update Bitmap request
            input wire         psBitmapDiscard_p,       // Discard Bitmap update request
            input wire         rxQoSEnd_p,              // Rx QoS field end pulse
            input wire         barRcved_p,              // When Bar SeqCntrl end pulse

            input wire         baEnable,                // Enable BA Controller procedure
            
            input wire  [ 3:0] rxTID,                   // TID
            input wire  [11:0] rxSN,                    // Seq number
            input wire  [11:0] rxBASSN,                 // BAR Seq number
            
            ///////////////////////////////////////////////
            //$port_g Key search Engine
            ///////////////////////////////////////////////
            input wire  [ 7:0] keyIndexReturnBA,        // Returned Index
            input wire         keyStorageValid_p,       // Returned Index valid
            input wire         keyStorageError_p,       // Error indicating key not found
            
            ///////////////////////////////////////////////
            //$port_g Control and Status Register
            ///////////////////////////////////////////////
            input wire         baPSBitmapReset,         // Partial state bitmap Reset
            
            output wire        baPSBitmapResetIn,       // baPSBitmapResetIn
            output wire        baPSBitmapResetInValid,  // Clear the baPSBitmapReset bit
            
            ///////////////////////////////////////////////
            //$port_g PS BITMAP RAM 8*32 Single Port SRAM
            ///////////////////////////////////////////////
            input  wire [87:0] psBitmapReadData,        // Partial State Bitmap Read Data bus.
            
            output wire        psBitmapEn,              // Partial State Bitmap Enable. 
                                                        // This signal is asserted for both read and write operations to the Partial State Bitmap.
            output wire        psBitmapWriteEn,         // Partial State Bitmap Write Enable.
                                                        // This signal is asserted for write operations to the Partial State Bitmap.
            output reg  [ 1:0] psBitmapAddr,            // Partial State Bitmap Address bus.
            output reg  [87:0] psBitmapWriteData,       // Partial State Bitmap Write Data bus.

            ///////////////////////////////////////////////
            //$port_g Scoreboard Controller
            ///////////////////////////////////////////////
            input wire         psBitmapUpdateDone_p,    // PS Bitmap update done
            input wire [63:0]  updatedPSBitmap,         // Partial State Bitmap from RAM
            input wire [11:0]  updatedSSN,              // SSN from RAM
            
            output wire        startUpdate_p,           // Start PS Bitmap update
            output wire [63:0] readPSBitmap,            // Partial State Bitmap read from RAM
            output reg  [11:0] readSSN,                 // SSN read from RAM
            output reg         newPsBitmap,             // Flag new Partial State Bitmap is created
            output reg  [11:0] rxSNCapt,                // Latch the current rxSN for bitmap update
            output reg  [11:0] rxBASSNCapt,             // Latch the current rxBASSN for bitmap update

            ///////////////////////////////////////////////
            //$port_g Debug port
            ///////////////////////////////////////////////
            output wire [15:0] debugPortBAController,   // Debug port for validation
            output wire [15:0] debugPortBAController3   // Debug port for validation
            );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

// baController FSM states definition
//$fsm_sd baController
localparam
          INIT_BITMAP  =  4'd0,
                 IDLE  =  4'd1,
        RX_TUPLE_READ  =  4'd2,
           RX_COMPARE  =  4'd3,
         RX_INCR_ADDR  =  4'd4,
         ALLOCATE_ROW  =  4'd5,
//       WAIT_RX_UPDATE  =  4'd6,
        UPDATE_BITMAP  =  4'd6,
   WAIT_BITMAP_UPDATE  =  4'd7,
         WRITE_BITMAP  =  4'd8,
       TX_PASS_BITMAP  =  4'd9;


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// baController FSM signals definition
reg  [3:0] baControllerCs;    // baController FSM Current State
reg  [3:0] baControllerNs;    // baController FSM Next State

// Active when TID/Index tuple matches
wire       tupleFound;        

// Active when keyStorageValid_p and baEnable are active
wire       startBAProcedure;        

// Oldest address which has been updated
reg  [1:0] oldAddrLocation;
reg  [1:0] addr0Order;
reg  [1:0] addr1Order;
reg  [1:0] addr2Order;
reg  [1:0] addr3Order;

// Last address update
reg  [1:0] lastAddr;

// psBitmap row completion
reg        row0Valid;
reg        row1Valid;
reg        row2Valid;
reg        row3Valid;

// Returned Index sampled
reg  [63:0] readPSBitmapHold;

// Common counter
reg  [3:0] baCnt;

// Hold signal
reg        psBitmapReadyHold;
reg        psBitmapUpdateHold;
//reg        psBitmapDiscardHold;

// Memory data readable
reg        psBitmapEn_ff1;
reg        psBitmapEn_ff2;
reg        psBitmapEn_ff3;

// Start memory init after asynchronous reset
reg        psBitmapInitEn;

// Latch the rxQoSEnd_p until FSM moves to RX_TUPLE_READ
reg        rxQoSEnd;  
reg        rxBarRcved;

// Latch the keyStorageValid_p until FSM moves to RX_TUPLE_READ
reg        keyStorageValid;             
reg  [3:0] rxTIDCapt;
reg  [7:0] keyIndexReturnBACapt;

`ifdef RW_SIMU_ON
// String definition to display baController current state
reg [18*8-1:0] baControllerCs_str;
`endif // RW_SIMU_ON


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


// baController FSM Current State Logic 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                                       // Asynchronous Reset
    baControllerCs <= INIT_BITMAP; 
  else if (!macCoreClkSoftRst_n || baPSBitmapReset) // Synchronous Reset
    baControllerCs <= INIT_BITMAP; 
  else
    baControllerCs <= baControllerNs; 
end


// baController FSM Next State Logic.
always @* 
begin
  case(baControllerCs)

    INIT_BITMAP:
      //$fsm_s In INIT_BITMAP state, the state machine waits end of PS Bitmap clear
      if (baPSBitmapResetInValid)
        //$fsm_t When PS Bitmap clear is received, the state machine goes to IDLE state
        baControllerNs = IDLE;
      else
        //$fsm_t While PS Bitmap clear is not finished, the state machine stays in INIT_BITMAP state
        baControllerNs = INIT_BITMAP;

    IDLE:
      //$fsm_s In IDLE state, the state machine waits request from Key search Engine or TX Controller
      if ((psBitmapUpdate_p || psBitmapUpdateHold) && startBAProcedure) 
        //$fsm_t When psBitmapUpdate_p is received and startBAProcedure is valid, the state machine goes to RX_TUPLE_READ state
        baControllerNs = RX_TUPLE_READ; 
      else if (psBitmapReady) 
        //$fsm_t When psBitmapReady is received, the state machine goes to TX_PASS_BITMAP state
        baControllerNs = TX_PASS_BITMAP; 
      else
        //$fsm_t While keyStorageValid_p and psBitmapReady are not received, the state machine stays in IDLE state
        baControllerNs = IDLE;

    RX_TUPLE_READ:
      //$fsm_s In RX_BITMAP_READ state, the state machine read PS Bitmap RAM

        //$fsm_t After one clock cycle, the state machine goes to RX_COMPARE state
        baControllerNs = RX_COMPARE; 

    RX_COMPARE:
      //$fsm_s In RX_COMPARE state, the state machine compare index/TID tuple with RAM
      if (tupleFound)
        //$fsm_t When tupleFound is received, the state machine goes to UPDATE_BITMAP state
        baControllerNs = UPDATE_BITMAP; 
      else if (psBitmapAddr[1:0] == 2'h3)
        //$fsm_t While 4 RAM locations have been checked, the state machine goes to ALLOCATE_ROW state
        baControllerNs = ALLOCATE_ROW;
      else
        //$fsm_t While 4 RAM locations have not been checked, the state machine goes to RX_INCR_ADDR state
        baControllerNs = RX_INCR_ADDR;

    RX_INCR_ADDR:
      //$fsm_s In RX_INCR_ADDR state, the state machine increments PS Bitmap RAM adresses

        //$fsm_t After one clock cycle, the state machine goes to RX_TUPLE_READ state
        baControllerNs = RX_TUPLE_READ; 

    ALLOCATE_ROW:
      //$fsm_s In ALLOCATE_ROW state, the state machine allocate a new row in the PS Bitmap RAM

        //$fsm_t After one clock cycle, the state machine goes to UPDATE_BITMAP state
        baControllerNs = UPDATE_BITMAP; 

//    WAIT_RX_UPDATE:
//      //$fsm_s In WAIT_RX_UPDATE state, the state machine waits update request from RX Controller
//      if (psBitmapDiscardHold) 
//        //$fsm_t When psBitmapDiscard_p is received, the state machine goes to IDLE state
//        baControllerNs = IDLE; 
//      else if (psBitmapUpdateHold) 
//        //$fsm_t When psBitmapUpdate_p is received, the state machine goes to UPDATE_BITMAP state
//        baControllerNs = UPDATE_BITMAP; 
//      else
//        //$fsm_t While request from RX Controller is not received, the state machine stays in WAIT_RX_UPDATE state
//        baControllerNs = WAIT_RX_UPDATE;

    UPDATE_BITMAP:
      //$fsm_s In UPDATE_BITMAP state, the state machine triggers Scoreboard Controller

        //$fsm_t After one clock cycle, the state machine goes to WAIT_BITMAP_UPDATE state
        baControllerNs = WAIT_BITMAP_UPDATE; 

    WAIT_BITMAP_UPDATE:
      //$fsm_s In WAIT_BITMAP_UPDATE state, the state machine waits trigger from Scoreboard Controller
      if (psBitmapUpdateDone_p) 
        //$fsm_t When psBitmapUpdateDone_p is received, the state machine goes to WRITE_BITMAP state
        baControllerNs = WRITE_BITMAP; 
      else
        //$fsm_t While psBitmapUpdateDone_p is not received, the state machine stays in WAIT_BITMAP_UPDATE state
        baControllerNs = WAIT_BITMAP_UPDATE;

    WRITE_BITMAP:
      //$fsm_s In WRITE_BITMAP state, the state machine updates PS Bitmap RAM from Scoreboard Controller result
      if (psBitmapWriteEn)
        //$fsm_t When second word is written into PS Bitmap RAM, the state machine goes to IDLE state
        baControllerNs = IDLE; 
      else
        //$fsm_t While second word is not written into PS Bitmap RAM, the state machine stays in WRITE_BITMAP state.
        baControllerNs = WRITE_BITMAP;

    TX_PASS_BITMAP:
      //$fsm_s In TX_PASS_BITMAP state, the state machine waits end of PS Bitmap sent to TX Controller
      if ((baCnt == 4'h9) && psBitmapValid) 
        //$fsm_t When baCnt is 9, the state machine goes to IDLE state.
        baControllerNs = IDLE; 
      else
        //$fsm_t When baCnt is not 9, the state machine stays in TX_PASS_BITMAP state.
        baControllerNs = TX_PASS_BITMAP;

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
     default:   
        baControllerNs = IDLE; 
    // pragma coverage block = on 
  endcase
end


//////////////////////////////////////////////////////
// Internal control
//////////////////////////////////////////////////////

// Clear of reset from CSReg
assign baPSBitmapResetIn      = 1'b0;
assign baPSBitmapResetInValid = psBitmapEn && psBitmapWriteEn && (psBitmapAddr[1:0] == 2'h3);

// Active when keyStorageValid_p and baEnable are active
assign startBAProcedure = (rxBarRcved || rxQoSEnd) && baEnable && keyStorageValid;

// Set newPsBitmap Flag if there is no save bitmap for the current TID/Tupple
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                    // Asynchronous Reset
    newPsBitmap  <= 1'b0;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP))               // Synchronous Reset
    newPsBitmap <= 1'b0;
  else if (baControllerCs == ALLOCATE_ROW)
    newPsBitmap <= 1'b1;
  else if (psBitmapUpdateDone_p)
    newPsBitmap <= 1'b0;
end 

// Latch the barRcved_p until FSM moves to RX_TUPLE_READ
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                    // Asynchronous Reset
    rxBarRcved  <= 1'b0;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP))               // Synchronous Reset
    rxBarRcved <= 1'b0;
  else if (barRcved_p && baEnable && (baControllerCs == IDLE))
    rxBarRcved <= 1'b1;
  else if ((baControllerCs == RX_TUPLE_READ) || (psBitmapDiscard_p))
    rxBarRcved <= 1'b0;
end        

// Latch the rxQoSEnd_p until FSM moves to RX_TUPLE_READ
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                    // Asynchronous Reset
    rxQoSEnd  <= 1'b0;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP))               // Synchronous Reset
    rxQoSEnd <= 1'b0;
  else if (rxQoSEnd_p && baEnable && (baControllerCs == IDLE))
    rxQoSEnd <= 1'b1;
  else if ((baControllerCs == RX_TUPLE_READ) || (psBitmapDiscard_p))
    rxQoSEnd <= 1'b0;
end        


always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                    // Asynchronous Reset
    rxTIDCapt  <= 4'b0;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP))               // Synchronous Reset
    rxTIDCapt  <= 4'b0;
  else if (rxQoSEnd || rxBarRcved)
    rxTIDCapt  <= rxTID;
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                    // Asynchronous Reset
    rxSNCapt  <= 12'h0;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP))               // Synchronous Reset
    rxSNCapt  <= 12'h0;
  else if (rxQoSEnd)
    rxSNCapt  <= rxSN;
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                    // Asynchronous Reset
    rxBASSNCapt  <= 12'h0;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP))               // Synchronous Reset
    rxBASSNCapt  <= 12'h0;
  else if (rxBarRcved)
    rxBASSNCapt  <= rxBASSN;
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                    // Asynchronous Reset
    keyIndexReturnBACapt  <= 8'b0;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP))               // Synchronous Reset
    keyIndexReturnBACapt  <= 8'b0;
  else if (keyStorageValid_p && !keyStorageError_p && !keyStorageValid && baEnable && (baControllerCs == IDLE))
    keyIndexReturnBACapt  <= keyIndexReturnBA;
end
    


// Latch the keyStorageValid_p until FSM moves to RX_TUPLE_READ
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                    // Asynchronous Reset
    keyStorageValid  <= 1'b0;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP))               // Synchronous Reset
    keyStorageValid <= 1'b0;
  else if (keyStorageValid_p && !keyStorageError_p && baEnable && (baControllerCs == IDLE))
    keyStorageValid <= 1'b1;
  else if ((baControllerCs == RX_TUPLE_READ) || (psBitmapDiscard_p))
    keyStorageValid <= 1'b0;
end        


// tupleFound when Index and TID matches
assign tupleFound = (rxTIDCapt == psBitmapReadData[79:76]) &&
                    (keyIndexReturnBACapt == psBitmapReadData[87:80]) &&
                    (baControllerCs == RX_COMPARE) &&
                     psBitmapEn_ff1;

// Hold rxController signals
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                                            // Asynchronous Reset
  begin
    psBitmapUpdateHold  <= 1'b0;
//    psBitmapDiscardHold <= 1'b0;
  end
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP) || ((baControllerCs != IDLE) && (baControllerNs == IDLE)))           // Synchronous Reset
  begin
    psBitmapUpdateHold  <= 1'b0;
//    psBitmapDiscardHold <= 1'b0;
  end
//  else if (psBitmapDiscard_p)
//    psBitmapDiscardHold <= 1'b1;
  else if (psBitmapUpdate_p)
    psBitmapUpdateHold  <= 1'b1;
end

// psBitmap RAM row valid
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                                         // Asynchronous Reset
  begin
    row0Valid <= 1'b0;
    row1Valid <= 1'b0;
    row2Valid <= 1'b0;
    row3Valid <= 1'b0;
  end
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP)) // Synchronous Reset
  begin
    row0Valid <= 1'b0;
    row1Valid <= 1'b0;
    row2Valid <= 1'b0;
    row3Valid <= 1'b0;
  end
  else if (baControllerCs == WRITE_BITMAP)
  begin
    case (psBitmapAddr[1:0])
      2'h0    : row0Valid <= 1'b1;
      2'h1    : row1Valid <= 1'b1;
      2'h2    : row2Valid <= 1'b1;
      default : row3Valid <= 1'b1;
    endcase
  end
end

// Address 0 re-ordering location
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                                         // Asynchronous Reset
    addr0Order <= 2'h0;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP)) // Synchronous Reset
    addr0Order <= 2'h0;
  else if ((baControllerCs == WRITE_BITMAP) && (baCnt == 4'h0))
  begin
    if (psBitmapAddr[1:0] == 2'h0)
      addr0Order <= 2'h3;
    else if ((psBitmapAddr[1:0] == lastAddr) || (addr0Order == 2'h0) ||
      ((addr0Order == 2'h1) && (((addr1Order == 2'h0) && (psBitmapAddr[1:0] != 2'h1)) ||
                                ((addr2Order == 2'h0) && (psBitmapAddr[1:0] != 2'h2)) ||
                                ((addr3Order == 2'h0) && (psBitmapAddr[1:0] != 2'h3)))))
      addr0Order <= addr0Order;
    else 
      addr0Order <= addr0Order - 2'h1;
  end
end

// Address 1 re-ordering location
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                                         // Asynchronous Reset
    addr1Order <= 2'h1;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP)) // Synchronous Reset
    addr1Order <= 2'h1;
  else if ((baControllerCs == WRITE_BITMAP) && (baCnt == 4'h0))
  begin
    if (psBitmapAddr[1:0] == 2'h1)
      addr1Order <= 2'h3;
    else if ((psBitmapAddr[1:0] == lastAddr) || (addr1Order == 2'h0) ||
      ((addr1Order == 2'h1) && (((addr0Order == 2'h0) && (psBitmapAddr[1:0] != 2'h0)) ||
                                ((addr2Order == 2'h0) && (psBitmapAddr[1:0] != 2'h2)) ||
                                ((addr3Order == 2'h0) && (psBitmapAddr[1:0] != 2'h3)))))
      addr1Order <= addr1Order;
    else 
      addr1Order <= addr1Order - 2'h1;
  end
end

// Address 2 re-ordering location
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                                         // Asynchronous Reset
    addr2Order <= 2'h2;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP)) // Synchronous Reset
    addr2Order <= 2'h2;
  else if ((baControllerCs == WRITE_BITMAP) && (baCnt == 4'h0))
  begin
    if (psBitmapAddr[1:0] == 2'h2)
      addr2Order <= 2'h3;
    else if ((psBitmapAddr[1:0] == lastAddr) || (addr2Order == 2'h0) ||
      ((addr2Order == 2'h1) && (((addr0Order == 2'h0) && (psBitmapAddr[1:0] != 2'h0)) ||
                                ((addr1Order == 2'h0) && (psBitmapAddr[1:0] != 2'h1)) ||
                                ((addr3Order == 2'h0) && (psBitmapAddr[1:0] != 2'h3)))))
      addr2Order <= addr2Order;
    else 
      addr2Order <= addr2Order - 2'h1;
  end
end

// Address 3 re-ordering location
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                                         // Asynchronous Reset
    addr3Order <= 2'h3;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP)) // Synchronous Reset
    addr3Order <= 2'h3;
  else if ((baControllerCs == WRITE_BITMAP) && (baCnt == 4'h0))
  begin
    if (psBitmapAddr[1:0] == 2'h3)
      addr3Order <= 2'h3;
    else if ((psBitmapAddr[1:0] == lastAddr) || (addr3Order == 2'h0) ||
      ((addr3Order == 2'h1) && (((addr0Order == 2'h0) && (psBitmapAddr[1:0] != 2'h0)) ||
                                ((addr1Order == 2'h0) && (psBitmapAddr[1:0] != 2'h1)) ||
                                ((addr2Order == 2'h0) && (psBitmapAddr[1:0] != 2'h2)))))
      addr3Order <= addr3Order;
    else 
      addr3Order <= addr3Order - 2'h1;
  end
end

// Last address updated
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                                         // Asynchronous Reset
    lastAddr <= 2'h3;
  else if (!macCoreClkSoftRst_n || (baControllerCs == INIT_BITMAP)) // Synchronous Reset
    lastAddr <= 2'h3;
  else if (baControllerCs == WRITE_BITMAP)
    lastAddr <= psBitmapAddr[1:0];
end

// Oldest address definition according to row completion and address re-ordering
always @*
begin
  if (!row0Valid)
    oldAddrLocation = 2'h0;
  else if (!row1Valid)
    oldAddrLocation = 2'h1;
  else if (!row2Valid)
    oldAddrLocation = 2'h2;
  else if (!row3Valid)
    oldAddrLocation = 2'h3;
  else
  begin
    if (addr0Order == 2'h0)
      oldAddrLocation = 2'h0;
    else if (addr1Order == 2'h0)
      oldAddrLocation = 2'h1;
    else if (addr2Order == 2'h0)
      oldAddrLocation = 2'h2;
    else
      oldAddrLocation = 2'h3;
  end
end

// Common counter
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                                              // Asynchronous Reset
    baCnt <= 4'b0;
  else if ((psBitmapValid && (baCnt == 4'h9)) || !macCoreClkSoftRst_n || // Synchronous Reset
    (baControllerCs == UPDATE_BITMAP) || (baControllerCs == IDLE))
    baCnt <= 4'b0; 
  else if (psBitmapValid || (baControllerCs == WRITE_BITMAP))
    baCnt <= baCnt + 4'b1; 
end


//////////////////////////////////////////////////////
// Scoreboard Controller
//////////////////////////////////////////////////////

// Start Scoreboard Controller computing
assign startUpdate_p = (baControllerCs == WAIT_BITMAP_UPDATE) && psBitmapEn_ff3;

// Hold psBitmap[7:0] from RAM
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                                          // Asynchronous Reset
    readPSBitmapHold <= 64'b0;
  else if (!macCoreClkSoftRst_n || (baControllerCs == ALLOCATE_ROW)) // Synchronous Reset
    readPSBitmapHold <= 64'b0;
  else if (baControllerCs == RX_COMPARE)
    readPSBitmapHold[63:0]  <= psBitmapReadData[63:0];
end

// Full psBitmap from RAM
assign readPSBitmap = readPSBitmapHold;

// Hold readSSN from RAM or scorboard
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                                          // Asynchronous Reset
    readSSN <= 12'b0;
  else if (!macCoreClkSoftRst_n || (baControllerCs == ALLOCATE_ROW)) // Synchronous Reset
    readSSN <= 12'b0;
  else if (baControllerCs == RX_COMPARE)
    readSSN <= psBitmapReadData[75:64];
//   else if (psBitmapUpdateDone_p)
//     readSSN <= updatedSSN;
end


//////////////////////////////////////////////////////
// TX Controller
//////////////////////////////////////////////////////

// Data valid generation
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)                                            // Asynchronous Reset
    psBitmapReadyHold <= 1'b0;
  else if ((psBitmapValid && (baCnt == 4'h9)) || !macCoreClkSoftRst_n) // Synchronous Reset
    psBitmapReadyHold <= 1'b0;
  else if (psBitmapReady && (baCnt == 4'h0))
    psBitmapReadyHold <= 1'b1; 
end

assign psBitmapValid = psBitmapReadyHold && psBitmapReady;

always @*
begin
  case (baCnt)
    4'h0    : psBitmap = {updatedSSN[3:0], 4'b0};
    4'h1    : psBitmap = updatedSSN[11:4];
    4'h2    : psBitmap = updatedPSBitmap[7:0];
    4'h3    : psBitmap = updatedPSBitmap[15:8];
    4'h4    : psBitmap = updatedPSBitmap[23:16];
    4'h5    : psBitmap = updatedPSBitmap[31:24];
    4'h6    : psBitmap = updatedPSBitmap[39:32];
    4'h7    : psBitmap = updatedPSBitmap[47:40];
    4'h8    : psBitmap = updatedPSBitmap[55:48];
    4'h9    : psBitmap = updatedPSBitmap[63:56];
    // Disable case default state for block coverage
    // pragma coverage block = off
    default : psBitmap = updatedPSBitmap[7:0];
    // pragma coverage block = on
  endcase
end


//////////////////////////////////////////////////////
// PS BITMAP RAM
//////////////////////////////////////////////////////

// PS BITMAP RAM enable
assign psBitmapEn = (baControllerCs == RX_TUPLE_READ)                  ||
                   ((baControllerCs == INIT_BITMAP) && psBitmapInitEn) ||
                    (baControllerCs == UPDATE_BITMAP)                  ||
                    (baControllerCs == WRITE_BITMAP);

// ff1 signals
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)      // Asynchronous Reset
  begin
    psBitmapEn_ff3 <= 1'b0;
    psBitmapEn_ff2 <= 1'b0;
    psBitmapEn_ff1 <= 1'b0;
    psBitmapInitEn <= 1'b0;
  end
  else if (!macCoreClkSoftRst_n) // Synchronous Reset
  begin
    psBitmapEn_ff3 <= 1'b0;
    psBitmapEn_ff2 <= 1'b0;
    psBitmapEn_ff1 <= 1'b0;
    psBitmapInitEn <= 1'b0;
  end
  else
  begin
    psBitmapEn_ff3 <= psBitmapEn_ff2;
    psBitmapEn_ff2 <= psBitmapEn_ff1;
    psBitmapEn_ff1 <= psBitmapEn;
    psBitmapInitEn <= 1'b1;
  end
end

// PS BITMAP RAM write
assign psBitmapWriteEn = (baControllerCs == WRITE_BITMAP) ||
                        ((baControllerCs == INIT_BITMAP) && psBitmapInitEn);

// PS BITMAP RAM write data
// addr2^n    : psBitmap[31:0]
// addr2^n +1 : index / TID / SSN / psBitmap[39:32]
always @*
begin
  if (baControllerCs == INIT_BITMAP)
    psBitmapWriteData = 88'b0;
  else
    //                   [87:80]               [79:76]    [75:64]     [63:0]
    psBitmapWriteData = {keyIndexReturnBACapt, rxTIDCapt, updatedSSN, updatedPSBitmap[63:0]};
end

// PS BITMAP RAM address
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)       // Asynchronous Reset
    psBitmapAddr <= 2'h0;
  else if (!macCoreClkSoftRst_n)  // Synchronous Reset
    psBitmapAddr <= 2'h0;
  else
  begin
    case (baControllerNs)
      INIT_BITMAP    : if (psBitmapInitEn)
                       psBitmapAddr    <= psBitmapAddr + 2'h1;
      IDLE           : psBitmapAddr    <= 2'h0;
      RX_INCR_ADDR   : psBitmapAddr    <= psBitmapAddr + 2'h1;
      ALLOCATE_ROW   : psBitmapAddr    <= oldAddrLocation;
      // Disable case default state for block coverage
      // pragma coverage block = off
      default        : psBitmapAddr    <= psBitmapAddr;
      // pragma coverage block = on
    endcase
  end
end
 
 
//////////////////////////////////////////////////////
// Debug port
//////////////////////////////////////////////////////
assign debugPortBAController = {psBitmapInitEn,
                                lastAddr,
                                oldAddrLocation,
                                startUpdate_p,
                                psBitmapUpdateDone_p,
                                newPsBitmap,
                                psBitmapReady,
                                psBitmapDiscard_p,
                                psBitmapUpdate_p,
                                keyStorageError_p, //tupleFound
                                baControllerCs};

assign debugPortBAController3 = { rxTIDCapt,            // 4 bits
                                  keyIndexReturnBACapt, // 8 bits
                                  psBitmapAddr[1:0],    // 2 bits  
                                  rxQoSEnd,
                                  keyStorageValid};
                                  

///////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////
// System Verilog Assertions
///////////////////////////////////////
///////////////////////////////////////
// System Verilog Assertions
///////////////////////////////////////
`ifdef RW_ASSERT_ON

default clocking cb @(posedge macCoreClk); endclocking

//$rw_sva Checks row order 0 should be different than row order 1
property baRowRule01_prop;
@(posedge macCoreClk)
  (baControllerCs == WRITE_BITMAP) |-> (addr0Order != addr1Order);
endproperty
baRowRule01: assert property (disable iff (!macCoreClkHardRst_n) baRowRule01_prop);

//$rw_sva Checks row order 0 should be different than row order 2
property baRowRule02_prop;
@(posedge macCoreClk)
  (baControllerCs == WRITE_BITMAP) |-> (addr0Order != addr2Order);
endproperty
baRowRule02: assert property (disable iff (!macCoreClkHardRst_n) baRowRule02_prop);

//$rw_sva Checks row order 0 should be different than row order 3
property baRowRule03_prop;
@(posedge macCoreClk)
  (baControllerCs == WRITE_BITMAP) |-> (addr0Order != addr3Order);
endproperty
baRowRule03: assert property (disable iff (!macCoreClkHardRst_n) baRowRule03_prop);

//$rw_sva Checks row order 1 should be different than row order 2
property baRowRule12_prop;
@(posedge macCoreClk)
  (baControllerCs == WRITE_BITMAP) |-> (addr1Order != addr2Order);
endproperty
baRowRule12: assert property (disable iff (!macCoreClkHardRst_n) baRowRule12_prop);

//$rw_sva Checks row order 1 should be different than row order 3
property baRowRule13_prop;
@(posedge macCoreClk)
  (baControllerCs == WRITE_BITMAP) |-> (addr1Order != addr3Order);
endproperty
baRowRule13: assert property (disable iff (!macCoreClkHardRst_n) baRowRule13_prop);

//$rw_sva Checks row order 2 should be different than row order 3
property baRowRule23_prop;
@(posedge macCoreClk)
  (baControllerCs == WRITE_BITMAP) |-> (addr2Order != addr3Order);
endproperty
baRowRule23: assert property (disable iff (!macCoreClkHardRst_n) baRowRule23_prop);

`endif // RW_ASSERT_ON


//////////////////////////////////////////////////////////
// Display FSM State in string for RTL simulation waveform
//////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
// baController FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (baControllerCs)
            INIT_BITMAP  :  baControllerCs_str = {"INIT_BITMAP"};
                   IDLE  :  baControllerCs_str = {"IDLE"};
          RX_TUPLE_READ  :  baControllerCs_str = {"RX_TUPLE_READ"};
             RX_COMPARE  :  baControllerCs_str = {"RX_COMPARE"};
           RX_INCR_ADDR  :  baControllerCs_str = {"RX_INCR_ADDR"};
           ALLOCATE_ROW  :  baControllerCs_str = {"ALLOCATE_ROW"};
//         WAIT_RX_UPDATE  :  baControllerCs_str = {"WAIT_RX_UPDATE"};
          UPDATE_BITMAP  :  baControllerCs_str = {"UPDATE_BITMAP"};
     WAIT_BITMAP_UPDATE  :  baControllerCs_str = {"WAIT_BITMAP_UPDATE"};
           WRITE_BITMAP  :  baControllerCs_str = {"WRITE_BITMAP"};
         TX_PASS_BITMAP  :  baControllerCs_str = {"TX_PASS_BITMAP"};
                default  :  baControllerCs_str = {"XXX"};
   endcase
end
`endif // RW_SIMU_ON

endmodule

