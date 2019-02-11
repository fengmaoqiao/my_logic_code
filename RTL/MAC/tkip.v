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
//   This block implements the tkIP phase I and phase II key mixing functions
//   to generate the seed for PRNG module.
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


module tkip (
  //$port_g Inputs
  input wire            bbClk,          // baseband clock signal
  input wire            hardRstBbClk_n, // reset signal from hardware
  input wire            softRstBbClk_p, // reset signal from software
  input wire            initTKIP_p,     // pulse to trigger TKIP key mixing
  input wire  [127:0]   temporalKey,    // 128-bit temporal key
  input wire  [47:0]    tkipSeqCntr,    // 48-bit tkIP sequence counter
  input wire  [47:0]    txrAddress,     // Transmitter address
  input wire  [15:0]    sBoxDataA,      // Read data from port A of sBox DPRAM
  input wire  [15:0]    sBoxDataB,      // Read data from port B of sBox DPRAM
  input wire            rxError_p,      // Indicates that an error has occured during reception
  input wire            txRxEnd_p,      // Pulse indicating end of transmission/reception

  //$port_g Outputs
  output wire [7:0]     sBoxAddressA,   // Address bus to internal sBox DPRAM port A
  output wire [7:0]     sBoxAddressB,   // Address bus to internal sBox DPRAM port B
  output wire [127:0]   tkipSeed,       // 128-bit seed to be used by PRNG
  output reg            tkipSeedValid   // signal indicating a valid seed is available on the seed lines
                      // 
    );


  //------------------parameter---------------------------------------

  localparam
    IDLE                     = 5'h0,  // idle state
    PH1_ST0                  = 5'h1,  // Phase I mixing, step 1
    PH1_ST1                  = 5'h2,  // Phase I mixing, step 2
    PH1_ST2                  = 5'h3,  // Phase I mixing, step 3
    PH1_ST3                  = 5'h4,  // Phase I mixing, step 4
    PH1_ST4                  = 5'h5,  // Phase I mixing, step 5
    PH2_ST0                  = 5'h6,  // Phase II mixing, step 1
    PH2_ST1                  = 5'h7,  // Phase II mixing, step 2
    PH2_ST2                  = 5'h8,  // Phase II mixing, step 3
    PH2_ST3                  = 5'h9,  // Phase II mixing, step 4
    PH2_ST4                  = 5'hA, // Phase II mixing, step 5
    PH2_ST5                  = 5'hB, // Phase II mixing, step 6
    PH2_ST6                  = 5'hC, // Phase II mixing, step 7
    PH2_ST7                  = 5'hD, // Phase II mixing, step 8
    PH2_ST8                  = 5'hE, // Phase II mixing, step 9
    PH2_ST9                  = 5'hF, // Phase II mixing, step 10
    PH2_ST10                 = 5'h10, // Phase II mixing, step 11
    PH2_ST11                 = 5'h11; // Phase II mixing, step 12

  //------------------reg---------------------------------------------

  reg    [15:0]                               nxtTTAK0orPPK0;
  reg    [15:0]                               nxtTTAK1orPPK1;
  reg    [15:0]                               nxtTTAK2orPPK2;
  reg    [15:0]                               nxtTTAK3orPPK3;
  reg    [15:0]                               nxtTTAK4orPPK4;
  reg    [15:0]                               nxtPPK5;
  reg    [15:0]                               ttak0orPPK0;
  reg    [15:0]                               ttak1orPPK1;
  reg    [15:0]                               ttak2orPPK2;
  reg    [15:0]                               ttak3orPPK3;
  reg    [15:0]                               ttak4orPPK4;
  reg    [15:0]                               ppk5;
  reg    [4:0]                                nxtTKIPState;
  reg    [4:0]                                tkipState;
  reg    [2:0]                                nxtLoopCnt;
  reg    [2:0]                                loopCnt;
  reg    [15:0]                               sBoxAddress;

  //------------------wire--------------------------------------------
  wire   [7:0]                                tk0;
  wire   [7:0]                                tk1;
  wire   [7:0]                                tk2;
  wire   [7:0]                                tk3;
  wire   [7:0]                                tk4;
  wire   [7:0]                                tk5;
  wire   [7:0]                                tk6;
  wire   [7:0]                                tk7;
  wire   [7:0]                                tk8;
  wire   [7:0]                                tk9;
  wire   [7:0]                                tk10;
  wire   [7:0]                                tk11;
  wire   [7:0]                                tk12;
  wire   [7:0]                                tk13;
  wire   [7:0]                                tk14;
  wire   [7:0]                                tk15;
  wire   [15:0]                               tkQuad0;
  wire   [15:0]                               tkQuad1;
  wire   [15:0]                               tkQuad2;
  wire   [15:0]                               tkQuad3;
  wire   [7:0]                                wepseed0;
  wire   [7:0]                                wepseed1;
  wire   [7:0]                                wepseed2;
  wire   [7:0]                                wepseed3;


`ifdef RW_SIMU_ON
  // String definition to display formatMPDUFSM current state
  reg [8*8-1:0] tkipState_str;
`endif // RW_SIMU_ON


  //------------------functions---------------------------------------

// This function rotates the 16-bit value one bit to the right
  function [15:0] RotR1;
     input [15:0] value;

    begin
      RotR1 = {value[0], value[15:1]};
    end
  endfunction
 
    
    
  //--------------Logic Begins----------------------------------------

// Split the key into bytes

  assign tk0 = temporalKey[7:0];
  assign tk1 = temporalKey[15:8];
  assign tk2 = temporalKey[23:16];
  assign tk3 = temporalKey[31:24];
  assign tk4 = temporalKey[39:32];
  assign tk5 = temporalKey[47:40];
  assign tk6 = temporalKey[55:48];
  assign tk7 = temporalKey[63:56];
  assign tk8 = temporalKey[71:64];
  assign tk9 = temporalKey[79:72];
  assign tk10 = temporalKey[87:80];
  assign tk11 = temporalKey[95:88];
  assign tk12 = temporalKey[103:96];
  assign tk13 = temporalKey[111:104];
  assign tk14 = temporalKey[119:112];
  assign tk15 = temporalKey[127:120];

// Logic for determing the key bytes to be used during phase I key mixing

  assign tkQuad0 = (nxtLoopCnt[0] == 1'b0) ? {tk1, tk0} : {tk3, tk2};
  assign tkQuad1 = (loopCnt[0] == 1'b0) ? {tk5, tk4} : {tk7, tk6};
  assign tkQuad2 = (loopCnt[0] == 1'b0) ? {tk9, tk8} : {tk11, tk10};
  assign tkQuad3 = (loopCnt[0] == 1'b0) ? {tk13, tk12} : {tk15, tk14};

// Logic for state machine

  always @*
  begin : p_tkipStateComb
  // Default values
  nxtTKIPState    = tkipState;

// If an error is detected during reception, transition to IDLE
  if (rxError_p)
    nxtTKIPState = IDLE;
  else
    begin
      case (tkipState)

// The state machine powers up in idle state. On initTKIP_p trigger pulse the
// state machine moves to PH1_ST0 to begin phase I of tkip key mixing function  
        IDLE :
          if (initTKIP_p == 1'b1)
            nxtTKIPState     = PH1_ST0;

        PH1_ST0 :
          nxtTKIPState     = PH1_ST1;

        PH1_ST1 :
          nxtTKIPState     = PH1_ST2;
    
        PH1_ST2 :
          nxtTKIPState     = PH1_ST3;
    
        PH1_ST3 :
          nxtTKIPState     = PH1_ST4;
    
// The state machine transitions from this state to PH1_ST0 if the phase I
// key mixing iterations are not complete indicated by LoopCnt being less
// than 7. One the phase I key mixing in over, the state machine transitions
// from this state to PH2_ST0 to begin phase II key mixing.
        PH1_ST4 :
          begin
            if (loopCnt == 3'b111)
              nxtTKIPState     = PH2_ST0;
            else
              nxtTKIPState     = PH1_ST0;
          end
       
        PH2_ST0 :
          nxtTKIPState     = PH2_ST1;
    
        PH2_ST1 :
          nxtTKIPState     = PH2_ST2;
    
        PH2_ST2 :
          nxtTKIPState     = PH2_ST3;
    
        PH2_ST3 :
          nxtTKIPState     = PH2_ST4;
    
        PH2_ST4 :
          nxtTKIPState     = PH2_ST5;
    
        PH2_ST5 :
          nxtTKIPState     = PH2_ST6;
    
        PH2_ST6 :
          nxtTKIPState     = PH2_ST7;
    
        PH2_ST7 :
          nxtTKIPState     = PH2_ST8;
    
        PH2_ST8 :
          nxtTKIPState     = PH2_ST9;
    
        PH2_ST9 :
          nxtTKIPState     = PH2_ST10;
    
        PH2_ST10 :
          nxtTKIPState     = PH2_ST11;
      
        PH2_ST11 :
          nxtTKIPState     = IDLE;
    
        default :
          nxtTKIPState  = IDLE;
    
      endcase
    end
end

// Sequential logic for state machine
  always @(posedge bbClk or negedge hardRstBbClk_n)
    if (!hardRstBbClk_n)
      tkipState <= IDLE;
    else if (softRstBbClk_p)
      tkipState <= IDLE;
    else
      tkipState <= nxtTKIPState;

// Logic for nxtTTAK0orPPK0
  always @*
  begin
    case (tkipState)

      IDLE :
        if (initTKIP_p == 1'b1)
          nxtTTAK0orPPK0 = tkipSeqCntr[31:16];
        else
          nxtTTAK0orPPK0 = ttak0orPPK0;

      PH1_ST0 :
        nxtTTAK0orPPK0   = ttak0orPPK0 + (sBoxDataA ^ sBoxDataB);

      PH2_ST0 :
        nxtTTAK0orPPK0   = ttak0orPPK0 + (sBoxDataA ^ sBoxDataB);
    
      PH2_ST6 :
        nxtTTAK0orPPK0   = ttak0orPPK0 + RotR1(ppk5 ^ {tk13,tk12});
    
      default :
        nxtTTAK0orPPK0   = ttak0orPPK0;
 
    endcase
  end


// sequential Logic for ttak0orPPK0

  always @(posedge bbClk or negedge hardRstBbClk_n)
  if (!hardRstBbClk_n)
    ttak0orPPK0 <= 16'h0000;
  else if (softRstBbClk_p)
    ttak0orPPK0 <= 16'h0000;
  else
    ttak0orPPK0 <= nxtTTAK0orPPK0;
    
// Logic for nxtTTAK1orPPK1
  always @*
  begin
    case (tkipState)

      IDLE :
        if (initTKIP_p == 1'b1)
          nxtTTAK1orPPK1 = tkipSeqCntr[47:32];
        else
          nxtTTAK1orPPK1 = ttak1orPPK1;

      PH1_ST1 :
        nxtTTAK1orPPK1   = ttak1orPPK1 + (sBoxDataA ^ sBoxDataB);

      PH2_ST1 :
        nxtTTAK1orPPK1   = ttak1orPPK1 + (sBoxDataA ^ sBoxDataB);
    
      PH2_ST7 :
        nxtTTAK1orPPK1   = ttak1orPPK1 + RotR1(ttak0orPPK0 ^ {tk15,tk14});
    
      default :
        nxtTTAK1orPPK1   = ttak1orPPK1;
 
    endcase
  end

// sequential Logic for ttak1orPPK1

  always @(posedge bbClk or negedge hardRstBbClk_n)
  if (!hardRstBbClk_n)
    ttak1orPPK1 <= 16'h0000;
  else if (softRstBbClk_p)
    ttak1orPPK1 <= 16'h0000;
  else
    ttak1orPPK1 <= nxtTTAK1orPPK1;
    
// Logic for nxtTTAK2orPPK2
  always @*
  begin
    case (tkipState)

      IDLE :
        if (initTKIP_p == 1'b1)
          nxtTTAK2orPPK2 = txrAddress[15:0];
        else
          nxtTTAK2orPPK2 = ttak2orPPK2;

      PH1_ST2 :
        nxtTTAK2orPPK2   = ttak2orPPK2 + (sBoxDataA ^ sBoxDataB);

      PH2_ST2 :
        nxtTTAK2orPPK2   = ttak2orPPK2 + (sBoxDataA ^ sBoxDataB);
    
      PH2_ST8 :
        nxtTTAK2orPPK2   = ttak2orPPK2 + RotR1(ttak1orPPK1);
    
      default :
        nxtTTAK2orPPK2   = ttak2orPPK2;
 
    endcase
  end

// sequential Logic for ttak2orPPK2

  always @(posedge bbClk or negedge hardRstBbClk_n)
  if (!hardRstBbClk_n)
    ttak2orPPK2 <= 16'h0000;
  else if (softRstBbClk_p)
    ttak2orPPK2 <= 16'h0000;
  else
    ttak2orPPK2 <= nxtTTAK2orPPK2;
    
// Logic for nxtTTAK3orPPK3
  always @*
  begin
    case (tkipState)

      IDLE :
        if (initTKIP_p == 1'b1)
          nxtTTAK3orPPK3 = txrAddress[31:16];
        else
          nxtTTAK3orPPK3 = ttak3orPPK3;

      PH1_ST3 :
        nxtTTAK3orPPK3   = ttak3orPPK3 + (sBoxDataA ^ sBoxDataB);

      PH2_ST3 :
        nxtTTAK3orPPK3   = ttak3orPPK3 + (sBoxDataA ^ sBoxDataB);
    
      PH2_ST9 :
        nxtTTAK3orPPK3   = ttak3orPPK3 + RotR1(ttak2orPPK2);
    
      default :
        nxtTTAK3orPPK3   = ttak3orPPK3;
 
    endcase
  end

// sequential Logic for ttak3orPPK3

  always @(posedge bbClk or negedge hardRstBbClk_n)
  if (!hardRstBbClk_n)
    ttak3orPPK3 <= 16'h0000;
  else if (softRstBbClk_p)
    ttak3orPPK3 <= 16'h0000;
  else
    ttak3orPPK3 <= nxtTTAK3orPPK3;
    
// Logic for nxtTTAK4orPPK4
  always @*
  begin
    case (tkipState)

      IDLE :
        if (initTKIP_p == 1'b1)
          nxtTTAK4orPPK4 = txrAddress[47:32];
        else
          nxtTTAK4orPPK4 = ttak4orPPK4;

      PH1_ST4 :
        nxtTTAK4orPPK4   = ttak4orPPK4 + (sBoxDataA ^ sBoxDataB) + {13'h0,loopCnt};

      PH2_ST4 :
        nxtTTAK4orPPK4   = ttak4orPPK4 + (sBoxDataA ^ sBoxDataB);
    
      PH2_ST10 :
        nxtTTAK4orPPK4   = ttak4orPPK4 + RotR1(ttak3orPPK3);
    
      default :
        nxtTTAK4orPPK4   = ttak4orPPK4;
 
    endcase
  end

// sequential Logic for ttak4orPPK4

  always @(posedge bbClk or negedge hardRstBbClk_n)
  if (!hardRstBbClk_n)
    ttak4orPPK4 <= 16'h0000;
  else if (softRstBbClk_p)
    ttak4orPPK4 <= 16'h0000;
  else
    ttak4orPPK4 <= nxtTTAK4orPPK4;
    
// Logic for nxtPPK5
  always @*
  begin
    case (tkipState)

      PH1_ST4 :
        if (loopCnt == 3'b111)
          nxtPPK5  = nxtTTAK4orPPK4 + tkipSeqCntr[15:0];
        else
          nxtPPK5  = ppk5;

      PH2_ST5 :
        nxtPPK5   = ppk5 + (sBoxDataA ^ sBoxDataB);
    
      PH2_ST11 :
        nxtPPK5   = ppk5 + RotR1(ttak4orPPK4);
    
      default :
        nxtPPK5   = ppk5;
 
    endcase
  end

// sequential Logic for ppk5

  always @(posedge bbClk or negedge hardRstBbClk_n)
  if (!hardRstBbClk_n)
      ppk5        <= 16'h0000;
  else if (softRstBbClk_p)
      ppk5        <= 16'h0000;
  else
      ppk5        <= nxtPPK5;

// Logic for nxtLoopCnt
// This is used to keep track of the number of times the phase I loop is 
// executed. The loop count ranges from 0 - 7 and is incremented every time
// that Phase I step 4 is executed. 
  always @*
  begin
    if (rxError_p)
      nxtLoopCnt   = 3'b000;
    else if (tkipState == PH1_ST4)
      nxtLoopCnt   = loopCnt + 3'b1;
    else
      nxtLoopCnt   = loopCnt;
  end

// Logic for Loop counter
  always @(posedge bbClk or negedge hardRstBbClk_n)
    if (!hardRstBbClk_n)
      loopCnt <= 3'b000;
    else if (softRstBbClk_p)
      loopCnt <= 3'b000;
    else
      loopCnt <= nxtLoopCnt;

// Logic for sBoxAddress
  always @*
  begin
    // Default values
    sBoxAddress     = 16'h0000;

    case (tkipState)
  
      IDLE :
        if (initTKIP_p == 1'b1)
          sBoxAddress      = txrAddress[47:32] ^ tkQuad0;
  
      PH1_ST0 :
        sBoxAddress      = nxtTTAK0orPPK0 ^ tkQuad1; 
  
      PH1_ST1 :
        sBoxAddress      = nxtTTAK1orPPK1 ^ tkQuad2; 
      
      PH1_ST2 :
        sBoxAddress      = nxtTTAK2orPPK2 ^ tkQuad3; 
      
      PH1_ST3 :
        sBoxAddress      = nxtTTAK3orPPK3 ^ tkQuad0; 
      
      PH1_ST4 :
        if (loopCnt == 3'b111)
          sBoxAddress      = nxtPPK5 ^ {tk1, tk0};
        else
          sBoxAddress      = nxtTTAK4orPPK4 ^ tkQuad0; 
         
      PH2_ST0 :
        sBoxAddress      = nxtTTAK0orPPK0 ^ {tk3,tk2};
      
      PH2_ST1 :
        sBoxAddress      = nxtTTAK1orPPK1 ^ {tk5,tk4};
      
      PH2_ST2 :
        sBoxAddress      = nxtTTAK2orPPK2 ^ {tk7,tk6};
      
      PH2_ST3 :
        sBoxAddress      = nxtTTAK3orPPK3 ^ {tk9,tk8};
      
      PH2_ST4 :
        sBoxAddress      = nxtTTAK4orPPK4 ^ {tk11,tk10};
      
      default :
        sBoxAddress  = 16'b00000000_00000000;
    endcase
  end

// Logic for tkipSeed

  assign wepseed0 = tkipSeqCntr[15:8];
  assign wepseed1 = (tkipSeqCntr[15:8] | 8'h20) & 8'h7F;
  assign wepseed2 = tkipSeqCntr[7:0];
  assign wepseed3 = ppk5[8:1] ^ {tk1[0], tk0[7:1]};

  assign tkipSeed = {ppk5, ttak4orPPK4, ttak3orPPK3, ttak2orPPK2, ttak1orPPK1,
                     ttak0orPPK0, wepseed3, wepseed2, wepseed1, wepseed0};

// Logic for tkipSeedValid
always @(posedge bbClk or negedge hardRstBbClk_n)
  if (!hardRstBbClk_n)
    tkipSeedValid <= 1'b0;
  else if (softRstBbClk_p)
    tkipSeedValid <= 1'b0;
  else if (txRxEnd_p || rxError_p || initTKIP_p)
    tkipSeedValid <= 1'b0;
  else if (tkipState == PH2_ST11)
    tkipSeedValid <= 1'b1;
  else
    tkipSeedValid <= tkipSeedValid;

// Assign local copies to output
  assign sBoxAddressA     = sBoxAddress[7:0];
  assign sBoxAddressB     = sBoxAddress[15:8];





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

// tkipState FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (tkipState)
              IDLE  :  tkipState_str = {"IDLE"};
           PH1_ST0  :  tkipState_str = {"PH1_ST0"};
           PH1_ST1  :  tkipState_str = {"PH1_ST1"};
           PH1_ST2  :  tkipState_str = {"PH1_ST2"};
           PH1_ST3  :  tkipState_str = {"PH1_ST3"};
           PH1_ST4  :  tkipState_str = {"PH1_ST4"};
           PH2_ST0  :  tkipState_str = {"PH2_ST0"};
           PH2_ST1  :  tkipState_str = {"PH2_ST1"};
           PH2_ST2  :  tkipState_str = {"PH2_ST2"};
           PH2_ST3  :  tkipState_str = {"PH2_ST3"};
           PH2_ST4  :  tkipState_str = {"PH2_ST4"};
           PH2_ST5  :  tkipState_str = {"PH2_ST5"};
           PH2_ST6  :  tkipState_str = {"PH2_ST6"};
           PH2_ST7  :  tkipState_str = {"PH2_ST7"};
           PH2_ST8  :  tkipState_str = {"PH2_ST8"};
           PH2_ST9  :  tkipState_str = {"PH2_ST9"};
           PH2_ST10 :  tkipState_str = {"PH2_ST10"};
           PH2_ST11 :  tkipState_str = {"PH2_ST11"};
           default  :  tkipState_str = {"XXX"};
   endcase
end
`endif // RW_SIMU_ON

endmodule

//------------------- END OF FILE ----------------//
