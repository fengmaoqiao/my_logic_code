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

module ccmpMux (

                //$port_g Inputs
                rxCsIsIdle,           // Indicates that the rxController is IDLE
                tcTxCCMPWrEnP,        // Write enable signal from TX Controller
                rxCCMPDataWrEn_p,     // Write enable signal from Encr RX Controlle
                tcTxPayLdEndP,        // Pulse indicating end of TX payload
                rxpayloadEnd_p,       // Indicates that last byte of RX payload
                nullKeyFound,         // Signal indicating key not found
                ccmpOutData,          // output data from the CCMP block
                ccmpOutValid_p,       // pulse indicating valid data present on the ccmpOutData lines
                ccmpOutLast_p,        // Last data from CCMP
                cbReadData,           // The data being Read from the CCMP buffer
 
                //$port_g Outputs
                wrCCMPEnP,            // write enable signal to CCMP input register
                payloadEnd_p,         // pulse indicating end of payload
                ccmpOutDataMux,       // Output data bus from CCMP engine
                ccmpOutValidMux_p,    // Valid signal for the output CCMP data
                ccmpOutLastMux_p      // Last data from CCMP
       );

//--------------------------------Input Declaration-----------------------------

  input [7:0]  ccmpOutData;     
  input [7:0]  cbReadData;
  input        rxCsIsIdle;
  input        tcTxCCMPWrEnP;
  input        rxCCMPDataWrEn_p;
  input        tcTxPayLdEndP;
  input        rxpayloadEnd_p;
  input        nullKeyFound;
  input        ccmpOutValid_p;  
  input        ccmpOutLast_p;  

//--------------------------------Output Declaration----------------------------
  output [7:0]  ccmpOutDataMux;     
  output        wrCCMPEnP;
  output        payloadEnd_p;
  output        ccmpOutValidMux_p;  
  output        ccmpOutLastMux_p;  
 
//--------------------------------Inputs Declared as Wires----------------------

  wire [7:0]  ccmpOutData;     
  wire [7:0]  cbReadData;
  wire        rxCsIsIdle;
  wire        tcTxCCMPWrEnP;
  wire        rxCCMPDataWrEn_p;

  wire        tcTxPayLdEndP;
  wire        rxpayloadEnd_p;
  wire        nullKeyFound;
  wire        ccmpOutValid_p;  
  wire        ccmpOutLast_p;  

//--------------------------------Outputs declared as Wires---------------------

  wire [7:0]  ccmpOutDataMux;     
  wire        wrCCMPEnP;
  wire        payloadEnd_p;
  wire        ccmpOutValidMux_p;  
  wire        ccmpOutLastMux_p;  

//--------------------------------Outputs Generation----------------------------

// Logic for wrCCMPEnP.
assign wrCCMPEnP = rxCsIsIdle ? tcTxCCMPWrEnP : (nullKeyFound ?
                     1'b0 : rxCCMPDataWrEn_p);

// Logic for payloadEnd_p.
assign payloadEnd_p = rxCsIsIdle ? tcTxPayLdEndP : (nullKeyFound ?
                        1'b0 : rxpayloadEnd_p);
 
// Logic for ccmpOutValidMux_p.
assign ccmpOutValidMux_p = rxCsIsIdle ? ccmpOutValid_p : (nullKeyFound ? 
                             rxCCMPDataWrEn_p : ccmpOutValid_p);
 
// Logic for ccmpOutDataMux.
assign ccmpOutDataMux = rxCsIsIdle ? ccmpOutData : (nullKeyFound ? 
                          cbReadData : ccmpOutData);
 
// Logic for ccmpOutDataMux.
assign ccmpOutLastMux_p = rxCsIsIdle ? ccmpOutLast_p : (nullKeyFound ? 
                          rxpayloadEnd_p : ccmpOutLast_p);
 
endmodule

//------------------- END OF FILE ----------------//

