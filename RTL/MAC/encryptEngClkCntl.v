//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $RCSmodulefile   : Encryption Engine Top
// $Author          : jvanthou
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: 0.1                                                             
// $Date: 4-Dec-2008                                                                
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : clock Controller of Encryption Engine module
//                    
// Simulation Notes : 
//    For simulation, four defines are available
//
//    WEP           : Enable WEP encryption / decryption 
//    TKIP          : Enable TKIP encryption / decryption 
//    CCMP          : Enable CCMP encryption / decryption 
//    RW_WAPI_EN    : Enable WAPI encryption / decryption 
//    RW_SIMU_ON    : which creates string signals to display the FSM states 
//                    on the waveform viewers
//
// Synthesis Notes  :
//
// Application Note : 
//     All the signals are coming from MAC Controller clock domain. Hence, no
//     resynchronizations are needed.
//
// Simulator        :
//     
//
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

module encryptEngClkCntl( 
      //$port_g Clock and Reset interface
      input  wire                               macCoreClk,            // MAC Core Clock

      input  wire                               macCoreClkHardRst_n,   // Active low hard reset signal synchronized to the macCoreClk
      
      input  wire                               macCoreClkSoftRst_n,   // Active low soft reset signal synchronized to the macCoreClk

      output reg                                macCryptClkEn,         // Enable MAC Crypt Clock
      output reg                                macWTClkEn,            // Enable Faster Clock for WEP/TKIP engine

      //$port_g TX Controller Interface
      input  wire                               txCsIsIdle,            // State machine information from TX Controller
      input  wire                               initSBoxIndexDone_p,   // Indicated PRNG has finished initialization 

      //$port_g RX Controller Interface
      input  wire                               rxCsIsIdle,            // Signal to indicate whether core is in TX or RX mode
      input  wire [2:0]                         cipherType,            // Cipher Type Input from TX or RX Controller 

      //$port_g Register Interface
      input  wire                               activeClkGating        // Active Clock Gating This bit is set by SW to turn on 
                                                                       // active clock gating in HW. When reset, the HW does not 
                                                                       // perform active clock gating, i.e. does not turn off 
                                                                       // clocks to save power in ACTIVE state.
      );

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

// cryptoClkCntlFSM FSM states definition
//$fsm_sd cryptoClkCntlFSM
localparam 
                IDLE  =  2'd0,  
             WEPTKIP  =  2'd1,  
            CCMPWAPI  =  2'd2,  
            CLOCKOFF  =  2'd3;  

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// cryptoClkCntlFSM FSM signals definition
reg [1:0] cryptoClkCntlFSMNs;  // cryptoClkCntlFSM FSM Next State
reg [1:0] cryptoClkCntlFSMCs;  // cryptoClkCntlFSM FSM Current State

`ifdef RW_SIMU_ON
// String definition to display cryptoClkCntlFSM current state
reg [17*8-1:0] cryptoClkCntlFSMCs_str;
`endif // RW_SIMU_ON

wire startCrypto_p;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////



// cryptoClkCntlFSM FSM Current State Logic 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    cryptoClkCntlFSMCs <= WEPTKIP; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    cryptoClkCntlFSMCs <= WEPTKIP; 
  else
    cryptoClkCntlFSMCs <= cryptoClkCntlFSMNs; 
end


// cryptoClkCntlFSM FSM Next State Logic.
always @* 
begin
  case(cryptoClkCntlFSMCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits until it is triggered by 
      //the MAC Controller. 
      if (startCrypto_p)
      begin 
        if ((cipherType == 3'd1) || (cipherType == 3'd2))
          //$fsm_t When startCrypto_p is received, the state machine goes to WEPTKIP state.
          cryptoClkCntlFSMNs = WEPTKIP;
`ifdef RW_WAPI_EN
        else if ((cipherType == 3'd3) || (cipherType == 3'd4))
`else
        else if (cipherType == 3'd3)
`endif //RW_WAPI_EN
          //$fsm_t When startCrypto_p is received, the state machine goes to CCMPWAPI state.
          cryptoClkCntlFSMNs = CCMPWAPI;
        else
          //$fsm_t When startCrypto_p is received, the state machine goes to IDLE state.
          cryptoClkCntlFSMNs = IDLE;
      end
      else if (activeClkGating)
          //$fsm_t When initDone_p is received and activeClkGating enabled, the state machine goes to CLOCKOFF state.
          cryptoClkCntlFSMNs = CLOCKOFF;
      else
        //$fsm_t While startCrypto_p is not received, the state machine stays in IDLE state.
        cryptoClkCntlFSMNs = IDLE;

    WEPTKIP:
      //$fsm_s In WEPTKIP state, the state machine waits until the completion of the encryption/decryption and SBOX initialisation 
      //(indicated by initSBoxIndexDone_p pulse)
      if (initSBoxIndexDone_p && !startCrypto_p)
      begin 
        if (activeClkGating)
          //$fsm_t When initDone_p is received and activeClkGating enabled, the state machine goes to CLOCKOFF state.
          cryptoClkCntlFSMNs = CLOCKOFF;
        else
          //$fsm_t When initDone_p is received and activeClkGating disabled, the state machine goes to IDLE state.
          cryptoClkCntlFSMNs = IDLE;
      end
      else
        //$fsm_t While initDone_p is not received, the state machine stays in WEPTKIP state.
        cryptoClkCntlFSMNs = WEPTKIP;


    CCMPWAPI:
      //$fsm_s In CCMPWAPI state, the state machine waits until the completion of CCMPWAPI processing
      //(indicated by initDone_p pulse)
      if (txCsIsIdle && rxCsIsIdle)
      begin 
        if (activeClkGating)
          //$fsm_t When initDone_p is received and activeClkGating enabled, the state machine goes to CLOCKOFF state.
          cryptoClkCntlFSMNs = CLOCKOFF;
        else
          //$fsm_t When initDone_p is received and activeClkGating disabled, the state machine goes to IDLE state.
          cryptoClkCntlFSMNs = IDLE;
      end
      else
        //$fsm_t While sendMPDU_p or skipMPDU_p is not received, the state machine stays in WEPTKIP state.
        cryptoClkCntlFSMNs = CCMPWAPI;

    CLOCKOFF:
      //$fsm_s In CLOCKOFF state, the state machine waits until it is triggered by 
      //the MAC Controller. 
      if (startCrypto_p)
      begin 
        if ((cipherType == 3'd1) || (cipherType == 3'd2))
          //$fsm_t When startCrypto_p is received, the state machine goes to WEPTKIP state.
          cryptoClkCntlFSMNs = WEPTKIP;
`ifdef RW_WAPI_EN
        else if ((cipherType == 3'd3) || (cipherType == 3'd4))
`else
        else if (cipherType == 3'd3)
`endif //RW_WAPI_EN
          //$fsm_t When startCrypto_p is received, the state machine goes to CCMPWAPI state.
          cryptoClkCntlFSMNs = CCMPWAPI;
        else
          //$fsm_t When startCrypto_p is received but cipherType NO Encryption, the state machine goes to IDLE state.
          cryptoClkCntlFSMNs = IDLE;
      end
      else
        //$fsm_t While startCrypto_p is not received, the state machine stays in IDLE state.
        cryptoClkCntlFSMNs = CLOCKOFF;


     // Disable coverage on the default state because it cannot be reached.
     // pragma coverage block = off 
     default:   
        cryptoClkCntlFSMNs = IDLE; 
     // pragma coverage block = on 

  endcase
end


assign startCrypto_p = (!txCsIsIdle || !rxCsIsIdle);


always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macCryptClkEn <= 1'b1; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macCryptClkEn <= 1'b1; 
  else if (!activeClkGating || (cryptoClkCntlFSMCs != CLOCKOFF))
    macCryptClkEn <= 1'b1; 
  else
    macCryptClkEn <= 1'b0; 
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macWTClkEn <= 1'b1; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macWTClkEn <= 1'b1; 
  else if (!activeClkGating || (cryptoClkCntlFSMCs == IDLE) || (cryptoClkCntlFSMCs == WEPTKIP))
    macWTClkEn <= 1'b1; 
  else
    macWTClkEn <= 1'b0; 
end

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

// cryptoClkCntlFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (cryptoClkCntlFSMCs)
              IDLE  :  cryptoClkCntlFSMCs_str = {"IDLE"};
           WEPTKIP  :  cryptoClkCntlFSMCs_str = {"WEPTKIP"};
          CCMPWAPI  :  cryptoClkCntlFSMCs_str = {"CCMPWAPI"};
          CLOCKOFF  :  cryptoClkCntlFSMCs_str = {"CLOCKOFF"};
           default  :  cryptoClkCntlFSMCs_str = {"XXX"};
   endcase
end

// pragma coverage block = on 
`endif // RW_SIMU_ON


endmodule
