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
// Description      : Scoreboard Controller module
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

module scoreboardController( 
            ///////////////////////////////////////////////
            //$port_g Clock and reset
            ///////////////////////////////////////////////
            input wire         macCoreClk,              // MAC Core Clock
            input wire         macCoreClkHardRst_n,     // Hard Reset of the MAC Core Clock domain active low
            input wire         macCoreClkSoftRst_n,     // Soft Reset of the MAC Core Clock domain
            
            ///////////////////////////////////////////////
            //$port_g RX Controller
            ///////////////////////////////////////////////
            input wire         barRcved,                // BA Request received
            
            input wire  [11:0] rxSN,                    // Sequence Number
            input wire  [11:0] rxBASSN,                 // BA Starting Sequence Number
            
            ///////////////////////////////////////////////
            //$port_g BA Controller FSM
            ///////////////////////////////////////////////
            input wire         startUpdate_p,           // Start PS Bitmap update
            input wire  [63:0] readPSBitmap,            // Partial State Bitmap read from RAM
            input wire  [11:0] readSSN,                 // SSN read from RAM
            input wire         newPsBitmap,             // Flag indicating there is a new bitmap for the current frame
            input wire         baPSBitmapReset,         // bitmap reset

            output reg         psBitmapUpdateDone_p,    // Partial State Bitmap update done
            output reg  [63:0] updatedPSBitmap,         // Partial State Bitmap from RAM
            output reg  [11:0] updatedSSN,              // SSN from RAM
            
            ///////////////////////////////////////////////
            //$port_g Debug port
            ///////////////////////////////////////////////
            output wire [15:0] debugPortBAController2   // Debug port for validation
            );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// Buffer size for the BA
parameter 
  WINSIZE = 7'd64; // WinSize = 64

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
// WinEnd calculation
wire [11:0] winEnd;
// WinStart limit
wire [11:0] winStartLimit;
// SN / SSN mux
wire [11:0] muxSN;

wire baCond;
wire conditionCase1;
wire conditionCase2;
wire conditionCase3;

// Sequence number difference
wire [11:0] diffSN1;
wire [11:0] diffSN2;
wire [6:0]  diffSN1Sat; // Saturated version of diffSN1
wire [6:0]  diffSN2Sat; // Saturated version of diffSN2

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// Partial State Bitmap update done
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)       // Asynchronous Reset
    psBitmapUpdateDone_p <= 1'b0;
  else if (!macCoreClkSoftRst_n)  // Synchronous Reset
    psBitmapUpdateDone_p <= 1'b0;
  else
    psBitmapUpdateDone_p <= startUpdate_p;
end

//From IEEE stabdard, 9.10.7.3 Scoreboard context control during partial-state operation
//b) For each received data MPDU that is related with a specific partial-state operation HT-immediate
//   Block Ack agreement, when no temporary record for the agreement related with the received data
//   MPDU exists at the time of receipt of the data MPDU, a temporary block acknowledgment record is
//   created as follows, where SN is the value of the Sequence Number subfield of the received data
//   MPDU:
//  1) WinEndR = SN.
//  2) WinStartR = WinEndR - WinSizeR + 1.
//  3) Create a bitmap of size WinSizeR, with the first bit corresponding to sequence number
//     WinStartR and the last bit corresponding to sequence number WinEndR, and set all bits in the
//     bitmap to 0.
//  4) Set to 1 the bit in the position in the bitmap that corresponds to SN.
//  c) For each received data MPDU that is related with a specific partial-state
//
//c) For each received data MPDU that is related with a specific partial-state operation HT-immediate
//   Block Ack agreement, when a temporary record for the agreement related with the received data
//   MPDU exists at the time of receipt of the data MPDU, the temporary block acknowledgment record
//   for that agreement is modified in the same manner as the acknowledgment record for a full-state
//   agreement described in 9.21.7.3.
//
//d) For each received BlockAckReq frame that is related with a specific partial-state operation HTimmediate
//   non-Protected Block Ack agreement, when no temporary record for the agreement
//   related with the received frame exists at the time of receipt of the frame, a temporary block
//   acknowledgment record is created as follows, where SSN is the starting value of the Sequence
//   Number subfield of the received BlockAckReq frame:
//   1) WinStartR = SSN.
//   2) WinEndR = WinStartR + WinSizeR ? 1.
//   3) Create a bitmap of size WinSizeR, and set all bits in the bitmap to 0.
//   e) For each received BlockAckReq frame that is related with a specific partial-state operation HTimmediate
//      non-Protected Block Ack agreement, when a temporary record for the agreement related
//      with the received frame exists at the time of receipt of the frame, the temporary block
//      acknowledgment record for that agreement is modified in the same manner as the acknowledgment
//      record for a full-state agreement described in 9.21.7.3.

// The Partial state is done directly through updatedPSBitmap and updatedSSN register 
// when newPsBitmap is detected by baControllerFsm 

// From IEEE stabdard, 9.10.7.3 Scoreboard context control during full-state operation
//
// For each received data MPDU that is related with a specific full-state operation HT-immediate
// Block Ack agreement, the block acknowledgment record for that agreement is modified as follows,
// where SN is the value of the Sequence Number subfield of the received data MPDU:
//
// Case 1) If WinStartR <= SN <= WinEndR, set to 1 the bit in position SN within the bitmap.
//
// Case 2) If WinEndR < SN < WinStartR+2048,
//   i)   Set to 0 the bits corresponding to MPDUs with Sequence Number subfield values from WinEndR+1 to SN-1.
//   ii)  Set WinStartR = SN - WinSizeR + 1.
//   iii) Set WinEndR = SN.
//   iv)  Set to 1 the bit at position SN in the bitmap.
//
// Case 3) If WinStartR+2048 <= SN < WinStartR, make no changes to the record.

// NEW Ref IEEE Std802.11 2012 : 9.21.7.3

// Full -state operation
// SN / SSN mux
assign muxSN = (barRcved) ? rxBASSN : rxSN;

// winEnd
assign winEnd = readSSN + {5'd0,WINSIZE} - 12'h1;

// winStartLimit
//assign winStartLimit = 12'd4095 - {6'd0,WINSIZE} + 12'h1;
assign winStartLimit = readSSN + 12'd2048;

// According to the standard if BAR asking for BA then SN > readSSN else if it is imediate BA then SN >= readSSN
assign baCond = barRcved ? (muxSN > readSSN) : (muxSN >= readSSN);

// Case 1) If WinStartR <= SN <= WinEndR
// Wrapping condition :
// If WinEndR < WinStartR then 
// SN > WinStartR or SN <= WinEndR for BAR response
//.SN >= WinStartR or SN <= WinEndR for imediate response
assign conditionCase1 = (winEnd < readSSN) ? (baCond || (muxSN <= winEnd)) : 
                                             (baCond && (muxSN <= winEnd)) ; 

// Case 2) If WinEndR < SN < (WinStartR+2048) mod 4096
// Wrapping condition :
// If ((WinStartR+2048) mod 4096) < WinEndR then SN > WinEndR or SN < ((WinStartR+2048) mod 4096)
assign conditionCase2 = (winStartLimit < winEnd) ? ((muxSN > winEnd) || (muxSN < winStartLimit)) : 
                                                   ((muxSN > winEnd) && (muxSN < winStartLimit)) ; 

// Case 3) If WinStartR+2048 <= SN < WinStartR, make no changes to the record.
assign conditionCase3 = !conditionCase1 && !conditionCase2;

// Updated SSN selection
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)       // Asynchronous Reset
    updatedSSN <= 12'b0;
  else if (!macCoreClkSoftRst_n || baPSBitmapReset)  // Synchronous Reset
    updatedSSN <= 12'b0;
  else if (startUpdate_p)         // Bitmap update
  begin
    if (barRcved) // BAR case
    begin
      if (newPsBitmap)
        updatedSSN <= rxBASSN;
      else if (conditionCase3)
        updatedSSN <= readSSN;
      else
        updatedSSN <= rxBASSN;
    end
    else         // MPDU case
    begin
      if (newPsBitmap)
        updatedSSN <= rxSN - {5'd0,WINSIZE} + 12'd1;
      else if (conditionCase1 || conditionCase3)
        updatedSSN <= readSSN;
      else
        updatedSSN <= rxSN - {5'd0,WINSIZE} + 12'd1;
    end
  end  
end

// Sequence number difference
assign diffSN1 = muxSN - readSSN;
assign diffSN2 = muxSN - winEnd;

assign diffSN1Sat = (diffSN1 >= 12'd64) ? 7'd64 : diffSN1[6:0];
assign diffSN2Sat = (diffSN2 >= 12'd64) ? 7'd64 : diffSN2[6:0];

// Updated Partial State Bitmap
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (!macCoreClkHardRst_n)       // Asynchronous Reset
    updatedPSBitmap <= 64'b0;
  else if (!macCoreClkSoftRst_n || baPSBitmapReset)  // Synchronous Reset
    updatedPSBitmap <= 64'b0;
  else if (startUpdate_p)         // Bitmap update
  begin
    if (barRcved) // BAR case
    begin
      if (newPsBitmap)
        updatedPSBitmap <= 64'b0;
      else if (conditionCase1)
        updatedPSBitmap <= readPSBitmap >> diffSN1Sat;
      else if (conditionCase2)
        updatedPSBitmap <= 64'b0;
      else
        updatedPSBitmap <= readPSBitmap;
    end
    else          // MPDU case
    begin
      if (newPsBitmap)
        updatedPSBitmap             <= {1'b1,63'b0}; // since SN is WindEndR
      else if (conditionCase1)
      begin
        updatedPSBitmap             <= readPSBitmap;
        updatedPSBitmap[diffSN1Sat] <= 1'b1;
      end
      else if (conditionCase2)
      begin
        updatedPSBitmap     <= readPSBitmap >> diffSN2Sat;
        updatedPSBitmap[63] <= 1'b1;
      end
      else
        updatedPSBitmap <= readPSBitmap;
    end
  end
end

assign debugPortBAController2 = {diffSN2Sat[5:0],diffSN1Sat[5:0],conditionCase3,conditionCase2,conditionCase1,startUpdate_p};

endmodule
