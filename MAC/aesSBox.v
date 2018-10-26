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
//   Implements Case statement for LUT implementation
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

module aesSBox (

    //$port_g aesCore 
    input  wire [7:0] inData, // Sbox input  

    output reg  [7:0] outData // Sbox output 
 );



// Case statement for LUT implementation
always @*
begin
  case(inData)
    8'h00: outData = 8'h63;
    8'h01: outData = 8'h7c;
    8'h02: outData = 8'h77;
    8'h03: outData = 8'h7b;
    8'h04: outData = 8'hf2;
    8'h05: outData = 8'h6b;
    8'h06: outData = 8'h6f;
    8'h07: outData = 8'hc5;
    8'h08: outData = 8'h30;
    8'h09: outData = 8'h01;
    8'h0a: outData = 8'h67;
    8'h0b: outData = 8'h2b;
    8'h0c: outData = 8'hfe;
    8'h0d: outData = 8'hd7;
    8'h0e: outData = 8'hab;
    8'h0f: outData = 8'h76;
    8'h10: outData = 8'hca;
    8'h11: outData = 8'h82;
    8'h12: outData = 8'hc9;
    8'h13: outData = 8'h7d;
    8'h14: outData = 8'hfa;
    8'h15: outData = 8'h59;
    8'h16: outData = 8'h47;
    8'h17: outData = 8'hf0;
    8'h18: outData = 8'had;
    8'h19: outData = 8'hd4;
    8'h1a: outData = 8'ha2;
    8'h1b: outData = 8'haf;
    8'h1c: outData = 8'h9c;
    8'h1d: outData = 8'ha4;
    8'h1e: outData = 8'h72;
    8'h1f: outData = 8'hc0;
    8'h20: outData = 8'hb7;
    8'h21: outData = 8'hfd;
    8'h22: outData = 8'h93;
    8'h23: outData = 8'h26;
    8'h24: outData = 8'h36;
    8'h25: outData = 8'h3f;
    8'h26: outData = 8'hf7;
    8'h27: outData = 8'hcc;
    8'h28: outData = 8'h34;
    8'h29: outData = 8'ha5;
    8'h2a: outData = 8'he5;
    8'h2b: outData = 8'hf1;
    8'h2c: outData = 8'h71;
    8'h2d: outData = 8'hd8;
    8'h2e: outData = 8'h31;
    8'h2f: outData = 8'h15;
    8'h30: outData = 8'h04;
    8'h31: outData = 8'hc7;
    8'h32: outData = 8'h23;
    8'h33: outData = 8'hc3;
    8'h34: outData = 8'h18;
    8'h35: outData = 8'h96;
    8'h36: outData = 8'h05;
    8'h37: outData = 8'h9a;
    8'h38: outData = 8'h07;
    8'h39: outData = 8'h12;
    8'h3a: outData = 8'h80;
    8'h3b: outData = 8'he2;
    8'h3c: outData = 8'heb;
    8'h3d: outData = 8'h27;
    8'h3e: outData = 8'hb2;
    8'h3f: outData = 8'h75;
    8'h40: outData = 8'h09;
    8'h41: outData = 8'h83;
    8'h42: outData = 8'h2c;
    8'h43: outData = 8'h1a;
    8'h44: outData = 8'h1b;
    8'h45: outData = 8'h6e;
    8'h46: outData = 8'h5a;
    8'h47: outData = 8'ha0;
    8'h48: outData = 8'h52;
    8'h49: outData = 8'h3b;
    8'h4a: outData = 8'hd6;
    8'h4b: outData = 8'hb3;
    8'h4c: outData = 8'h29;
    8'h4d: outData = 8'he3;
    8'h4e: outData = 8'h2f;
    8'h4f: outData = 8'h84;
    8'h50: outData = 8'h53;
    8'h51: outData = 8'hd1;
    8'h52: outData = 8'h00;
    8'h53: outData = 8'hed;
    8'h54: outData = 8'h20;
    8'h55: outData = 8'hfc;
    8'h56: outData = 8'hb1;
    8'h57: outData = 8'h5b;
    8'h58: outData = 8'h6a;
    8'h59: outData = 8'hcb;
    8'h5a: outData = 8'hbe;
    8'h5b: outData = 8'h39;
    8'h5c: outData = 8'h4a;
    8'h5d: outData = 8'h4c;
    8'h5e: outData = 8'h58;
    8'h5f: outData = 8'hcf;
    8'h60: outData = 8'hd0;
    8'h61: outData = 8'hef;
    8'h62: outData = 8'haa;
    8'h63: outData = 8'hfb;
    8'h64: outData = 8'h43;
    8'h65: outData = 8'h4d;
    8'h66: outData = 8'h33;
    8'h67: outData = 8'h85;
    8'h68: outData = 8'h45;
    8'h69: outData = 8'hf9;
    8'h6a: outData = 8'h02;
    8'h6b: outData = 8'h7f;
    8'h6c: outData = 8'h50;
    8'h6d: outData = 8'h3c;
    8'h6e: outData = 8'h9f;
    8'h6f: outData = 8'ha8;
    8'h70: outData = 8'h51;
    8'h71: outData = 8'ha3;
    8'h72: outData = 8'h40;
    8'h73: outData = 8'h8f;
    8'h74: outData = 8'h92;
    8'h75: outData = 8'h9d;
    8'h76: outData = 8'h38;
    8'h77: outData = 8'hf5;
    8'h78: outData = 8'hbc;
    8'h79: outData = 8'hb6;
    8'h7a: outData = 8'hda;
    8'h7b: outData = 8'h21;
    8'h7c: outData = 8'h10;
    8'h7d: outData = 8'hff;
    8'h7e: outData = 8'hf3;
    8'h7f: outData = 8'hd2;
    8'h80: outData = 8'hcd;
    8'h81: outData = 8'h0c;
    8'h82: outData = 8'h13;
    8'h83: outData = 8'hec;
    8'h84: outData = 8'h5f;
    8'h85: outData = 8'h97;
    8'h86: outData = 8'h44;
    8'h87: outData = 8'h17;
    8'h88: outData = 8'hc4;
    8'h89: outData = 8'ha7;
    8'h8a: outData = 8'h7e;
    8'h8b: outData = 8'h3d;
    8'h8c: outData = 8'h64;
    8'h8d: outData = 8'h5d;
    8'h8e: outData = 8'h19;
    8'h8f: outData = 8'h73;
    8'h90: outData = 8'h60;
    8'h91: outData = 8'h81;
    8'h92: outData = 8'h4f;
    8'h93: outData = 8'hdc;
    8'h94: outData = 8'h22;
    8'h95: outData = 8'h2a;
    8'h96: outData = 8'h90;
    8'h97: outData = 8'h88;
    8'h98: outData = 8'h46;
    8'h99: outData = 8'hee;
    8'h9a: outData = 8'hb8;
    8'h9b: outData = 8'h14;
    8'h9c: outData = 8'hde;
    8'h9d: outData = 8'h5e;
    8'h9e: outData = 8'h0b;
    8'h9f: outData = 8'hdb;
    8'ha0: outData = 8'he0;
    8'ha1: outData = 8'h32;
    8'ha2: outData = 8'h3a;
    8'ha3: outData = 8'h0a;
    8'ha4: outData = 8'h49;
    8'ha5: outData = 8'h06;
    8'ha6: outData = 8'h24;
    8'ha7: outData = 8'h5c;
    8'ha8: outData = 8'hc2;
    8'ha9: outData = 8'hd3;
    8'haa: outData = 8'hac;
    8'hab: outData = 8'h62;
    8'hac: outData = 8'h91;
    8'had: outData = 8'h95;
    8'hae: outData = 8'he4;
    8'haf: outData = 8'h79;
    8'hb0: outData = 8'he7;
    8'hb1: outData = 8'hc8;
    8'hb2: outData = 8'h37;
    8'hb3: outData = 8'h6d;
    8'hb4: outData = 8'h8d;
    8'hb5: outData = 8'hd5;
    8'hb6: outData = 8'h4e;
    8'hb7: outData = 8'ha9;
    8'hb8: outData = 8'h6c;
    8'hb9: outData = 8'h56;
    8'hba: outData = 8'hf4;
    8'hbb: outData = 8'hea;
    8'hbc: outData = 8'h65;
    8'hbd: outData = 8'h7a;
    8'hbe: outData = 8'hae;
    8'hbf: outData = 8'h08;
    8'hc0: outData = 8'hba;
    8'hc1: outData = 8'h78;
    8'hc2: outData = 8'h25;
    8'hc3: outData = 8'h2e;
    8'hc4: outData = 8'h1c;
    8'hc5: outData = 8'ha6;
    8'hc6: outData = 8'hb4;
    8'hc7: outData = 8'hc6;
    8'hc8: outData = 8'he8;
    8'hc9: outData = 8'hdd;
    8'hca: outData = 8'h74;
    8'hcb: outData = 8'h1f;
    8'hcc: outData = 8'h4b;
    8'hcd: outData = 8'hbd;
    8'hce: outData = 8'h8b;
    8'hcf: outData = 8'h8a;
    8'hd0: outData = 8'h70;
    8'hd1: outData = 8'h3e;
    8'hd2: outData = 8'hb5;
    8'hd3: outData = 8'h66;
    8'hd4: outData = 8'h48;
    8'hd5: outData = 8'h03;
    8'hd6: outData = 8'hf6;
    8'hd7: outData = 8'h0e;
    8'hd8: outData = 8'h61;
    8'hd9: outData = 8'h35;
    8'hda: outData = 8'h57;
    8'hdb: outData = 8'hb9;
    8'hdc: outData = 8'h86;
    8'hdd: outData = 8'hc1;
    8'hde: outData = 8'h1d;
    8'hdf: outData = 8'h9e;
    8'he0: outData = 8'he1;
    8'he1: outData = 8'hf8;
    8'he2: outData = 8'h98;
    8'he3: outData = 8'h11;
    8'he4: outData = 8'h69;
    8'he5: outData = 8'hd9;
    8'he6: outData = 8'h8e;
    8'he7: outData = 8'h94;
    8'he8: outData = 8'h9b;
    8'he9: outData = 8'h1e;
    8'hea: outData = 8'h87;
    8'heb: outData = 8'he9;
    8'hec: outData = 8'hce;
    8'hed: outData = 8'h55;
    8'hee: outData = 8'h28;
    8'hef: outData = 8'hdf;
    8'hf0: outData = 8'h8c;
    8'hf1: outData = 8'ha1;
    8'hf2: outData = 8'h89;
    8'hf3: outData = 8'h0d;
    8'hf4: outData = 8'hbf;
    8'hf5: outData = 8'he6;
    8'hf6: outData = 8'h42;
    8'hf7: outData = 8'h68;
    8'hf8: outData = 8'h41;
    8'hf9: outData = 8'h99;
    8'hfa: outData = 8'h2d;
    8'hfb: outData = 8'h0f;
    8'hfc: outData = 8'hb0;
    8'hfd: outData = 8'h54;
    8'hfe: outData = 8'hbb;
    8'hff: outData = 8'h16;
    default: outData = 8'h63;
  endcase
end
endmodule

//------------------- END OF FILE ----------------//
