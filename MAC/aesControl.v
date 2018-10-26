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
//   This file contains behv model of synchronous dual port RAM with different
//   read and write clocks.  Write data width is 8 bits wide and read data
//   width is 8 bits wide.  This RAM is 4  byte deep  (these
//   are the default values, they can however be overriden using the supported
//   parameters). It is used to model a FIFO in the design.
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

module aesControl (

  //$port_g Clocks and Resets
  input  wire       pClk,          // baseband clock signal
  input  wire       nPRst,         // reset signal from hardware
  input  wire       nSRst,         // reset signal from softreset
  
  //$port_g aesCore
  input  wire       rxError_p,     // Indicates Rx Error
  input  wire       tcTxErrorP,    // Indicates Tx Error
  input  wire       aesInValid,    // Indicates Tx FIFO is not Empty
  input  wire       loadFlag,      // Indicates Tx FIFO is not Empty

  output reg  [3:0] roundCount,    // Enable signal to load New data
  output wire       aesReadData_p, // To Rx Fifo when OutData is valid
  output reg        aesOutValid_p  // Indicates the Round Count
 ); 

  // FSM Parameter
  //$fsm_sd state
  parameter
  IDLE    = 1'b0,
  ENCRYPT = 1'b1;

  // Registers
  reg          state;

  // Nets
  reg  [3:0]   nextroundCount;
  reg          nextstate;
  wire         nextaesOutValid_p;
  wire         roundCountDone;

  // Nets assigment
  assign roundCountDone     = ((roundCount == 4'h9) || ((loadFlag == 1'b1) && (roundCount == 4'h6)));
  assign nextaesOutValid_p  = (state == ENCRYPT) && (roundCountDone == 1'b1);
  assign aesReadData_p      = (state == IDLE) && (aesInValid == 1'b1);

  // Combination logic for FSM
  always @(*)
  begin
    case(state)
      //$fsm_s In IDLE state, the state machine wait for aesInValid
      IDLE:
      begin
        if((tcTxErrorP == 1'b0) && (rxError_p == 1'b0) && (aesInValid == 1'b1))
          //$fsm_t If aesInValid and no errors, the state goes to ENCRYPT
          nextstate = ENCRYPT;
        else
          //$fsm_t While no aesInValid, the state remains in IDLE
          nextstate = IDLE;
      end
      //$fsm_s In ENCRYPT, the state machine waits for roundCountDone
      ENCRYPT:
      begin
        if((tcTxErrorP == 1'b1) || (rxError_p == 1'b1) || (roundCountDone == 1'b1))
          //$fsm_t If roundCountDone or any errors, the state goes to IDLE
          nextstate = IDLE;
        else
          //$fsm_t While roundCountDone is not valid, the state stays in  ENCRYPT
          nextstate = ENCRYPT;
      end
      default:
      begin
        nextstate = IDLE;
      end
    endcase
  end

  // Sequential logic for FSM
  always @(posedge pClk or negedge nPRst)
  begin
    if (nPRst == 1'b0)
      state <= IDLE;
    else if (nSRst == 1'b0)
      state <= IDLE;
    else
      state <= nextstate;
  end

  // Combinatinal logic for  Counter used to  Keep Track of Rounds
  always @(*)
  begin
    if((roundCountDone == 1'b0) && ((state == ENCRYPT) || (nextstate == ENCRYPT)))
      nextroundCount = roundCount + 4'h1;
    else
      nextroundCount = 4'h0;
  end

  // Sequential logic for  Counter uesd to Keep Track of Rounds 
  always@(posedge pClk or negedge nPRst)
  begin
    if (nPRst == 1'b0)
    begin
      roundCount    <= 4'h0;
      aesOutValid_p <= 1'b0;
    end
    else if (nSRst == 1'b0)
    begin
      roundCount    <= 4'h0;
      aesOutValid_p <= 1'b0;
    end
    else
    begin
      roundCount    <= nextroundCount;   
      aesOutValid_p <= nextaesOutValid_p;
    end
  end

endmodule