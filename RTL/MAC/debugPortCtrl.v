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
// Description      : DebugPort multiplexing module
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
// -------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

module debugPortCtrl( 
          //$port_g Register Interface
          input  wire    [7:0] debugPortSel1,  // Debug Port Selection 1
          input  wire    [7:0] debugPortSel2,  // Debug Port Selection 2
          output wire   [31:0] debugPortRead,  // Reflect to register the value of debugPort output

          //$port_g Debug Interface
          output reg    [31:0] debugPort,      // Debug Port

          //$port_g Internal Signal Interface
          input  wire   [15:0] debugPortInt1,  // Debug Port 1 
          input  wire   [15:0] debugPortInt2,  // Debug Port 2 
          input  wire   [15:0] debugPortInt3,  // Debug Port 3 
          input  wire   [15:0] debugPortInt4,  // Debug Port 4 
          input  wire   [15:0] debugPortInt5,  // Debug Port 5 
          input  wire   [15:0] debugPortInt6,  // Debug Port 6 
          input  wire   [15:0] debugPortInt7,  // Debug Port 7 
          input  wire   [15:0] debugPortInt8,  // Debug Port 8 
          input  wire   [15:0] debugPortInt9,  // Debug Port 9 
          input  wire   [15:0] debugPortInt10, // Debug Port 10
          input  wire   [15:0] debugPortInt11, // Debug Port 11
          input  wire   [15:0] debugPortInt12, // Debug Port 12
          input  wire   [15:0] debugPortInt13, // Debug Port 13
          input  wire   [15:0] debugPortInt14, // Debug Port 14
          input  wire   [15:0] debugPortInt15, // Debug Port 15
          input  wire   [15:0] debugPortInt16, // Debug Port 16
          input  wire   [15:0] debugPortInt17, // Debug Port 17
          input  wire   [15:0] debugPortInt18, // Debug Port 18
          input  wire   [15:0] debugPortInt19, // Debug Port 19
          input  wire   [15:0] debugPortInt20, // Debug Port 20
          input  wire   [15:0] debugPortInt21, // Debug Port 21
          input  wire   [15:0] debugPortInt22, // Debug Port 22
          input  wire   [15:0] debugPortInt23, // Debug Port 23
          input  wire   [15:0] debugPortInt24, // Debug Port 24
          input  wire   [15:0] debugPortInt25, // Debug Port 25
          input  wire   [15:0] debugPortInt26, // Debug Port 26
          input  wire   [15:0] debugPortInt27, // Debug Port 27
          input  wire   [15:0] debugPortInt28, // Debug Port 28
          input  wire   [15:0] debugPortInt29, // Debug Port 29
          input  wire   [15:0] debugPortInt30, // Debug Port 30
          input  wire   [15:0] debugPortInt31, // Debug Port 31
          input  wire   [15:0] debugPortInt32, // Debug Port 32
          input  wire   [15:0] debugPortInt33, // Debug Port 33
          input  wire   [15:0] debugPortInt34, // Debug Port 34
          input  wire   [15:0] debugPortInt35, // Debug Port 35
          input  wire   [15:0] debugPortInt36, // Debug Port 36
          input  wire   [15:0] debugPortInt37, // Debug Port 37
          input  wire   [15:0] debugPortInt38, // Debug Port 38
          input  wire   [15:0] debugPortInt39, // Debug Port 39
          input  wire   [15:0] debugPortInt40, // Debug Port 40
          input  wire   [15:0] debugPortInt41, // Debug Port 41
          input  wire   [15:0] debugPortInt42, // Debug Port 42
          input  wire   [15:0] debugPortInt43, // Debug Port 43
          input  wire   [15:0] debugPortInt44, // Debug Port 44
          input  wire   [15:0] debugPortInt45, // Debug Port 45
          input  wire   [15:0] debugPortInt46, // Debug Port 46
          input  wire   [15:0] debugPortInt47, // Debug Port 47
          `ifdef RW_WAPI_EN
          input  wire   [15:0] debugPortInt49, // Debug Port 49
          `endif
          input  wire   [15:0] debugPortInt48  // Debug Port 48
                 );



//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

always @ *
begin
  case (debugPortSel1)
        8'd0 : debugPort[15:0] = debugPortInt1;
        8'd1 : debugPort[15:0] = debugPortInt2;
        8'd2 : debugPort[15:0] = debugPortInt3;
        8'd3 : debugPort[15:0] = debugPortInt4;
        8'd4 : debugPort[15:0] = debugPortInt5;
        8'd5 : debugPort[15:0] = debugPortInt6;
        8'd6 : debugPort[15:0] = debugPortInt7;
        8'd7 : debugPort[15:0] = debugPortInt8;
        8'd8 : debugPort[15:0] = debugPortInt9;
        8'd9 : debugPort[15:0] = debugPortInt10;
       8'd10 : debugPort[15:0] = debugPortInt11;
       8'd11 : debugPort[15:0] = debugPortInt12;
       8'd12 : debugPort[15:0] = debugPortInt13;
       8'd13 : debugPort[15:0] = debugPortInt14;
       8'd14 : debugPort[15:0] = debugPortInt15;
       8'd15 : debugPort[15:0] = debugPortInt16;
       8'd16 : debugPort[15:0] = debugPortInt17;
       8'd17 : debugPort[15:0] = debugPortInt18;
       8'd18 : debugPort[15:0] = debugPortInt19;
       8'd19 : debugPort[15:0] = debugPortInt20;
       8'd20 : debugPort[15:0] = debugPortInt21;
       8'd21 : debugPort[15:0] = debugPortInt22;
       8'd22 : debugPort[15:0] = debugPortInt23;
       8'd23 : debugPort[15:0] = debugPortInt24;
       8'd24 : debugPort[15:0] = debugPortInt25;
       8'd25 : debugPort[15:0] = debugPortInt26;
       8'd26 : debugPort[15:0] = debugPortInt27;
       8'd27 : debugPort[15:0] = debugPortInt28;
       8'd28 : debugPort[15:0] = debugPortInt29;
       8'd29 : debugPort[15:0] = debugPortInt30;
       8'd30 : debugPort[15:0] = debugPortInt31;
       8'd31 : debugPort[15:0] = debugPortInt32;
       8'd32 : debugPort[15:0] = debugPortInt33;
       8'd33 : debugPort[15:0] = debugPortInt34;
       8'd34 : debugPort[15:0] = debugPortInt35;
       8'd35 : debugPort[15:0] = debugPortInt36;
       8'd36 : debugPort[15:0] = debugPortInt37;
       8'd37 : debugPort[15:0] = debugPortInt38;
       8'd38 : debugPort[15:0] = debugPortInt39;
       8'd39 : debugPort[15:0] = debugPortInt40;
       8'd40 : debugPort[15:0] = debugPortInt41;
       8'd41 : debugPort[15:0] = debugPortInt42;
       8'd42 : debugPort[15:0] = debugPortInt43;
       8'd43 : debugPort[15:0] = debugPortInt44;
       8'd44 : debugPort[15:0] = debugPortInt45;
       8'd45 : debugPort[15:0] = debugPortInt46;
       8'd46 : debugPort[15:0] = debugPortInt47;
       8'd47 : debugPort[15:0] = debugPortInt48;
       `ifdef RW_WAPI_EN
       8'd48 : debugPort[15:0] = debugPortInt49;
       `endif //RW_WAPI_EN
     default : debugPort[15:0] = debugPortInt1; 
  endcase
end

always @ *
begin
  case (debugPortSel2)
        8'd0 : debugPort[31:16] = debugPortInt1;
        8'd1 : debugPort[31:16] = debugPortInt2;
        8'd2 : debugPort[31:16] = debugPortInt3;
        8'd3 : debugPort[31:16] = debugPortInt4;
        8'd4 : debugPort[31:16] = debugPortInt5;
        8'd5 : debugPort[31:16] = debugPortInt6;
        8'd6 : debugPort[31:16] = debugPortInt7;
        8'd7 : debugPort[31:16] = debugPortInt8;
        8'd8 : debugPort[31:16] = debugPortInt9;
        8'd9 : debugPort[31:16] = debugPortInt10;
       8'd10 : debugPort[31:16] = debugPortInt11;
       8'd11 : debugPort[31:16] = debugPortInt12;
       8'd12 : debugPort[31:16] = debugPortInt13;
       8'd13 : debugPort[31:16] = debugPortInt14;
       8'd14 : debugPort[31:16] = debugPortInt15;
       8'd15 : debugPort[31:16] = debugPortInt16;
       8'd16 : debugPort[31:16] = debugPortInt17;
       8'd17 : debugPort[31:16] = debugPortInt18;
       8'd18 : debugPort[31:16] = debugPortInt19;
       8'd19 : debugPort[31:16] = debugPortInt20;
       8'd20 : debugPort[31:16] = debugPortInt21;
       8'd21 : debugPort[31:16] = debugPortInt22;
       8'd22 : debugPort[31:16] = debugPortInt23;
       8'd23 : debugPort[31:16] = debugPortInt24;
       8'd24 : debugPort[31:16] = debugPortInt25;
       8'd25 : debugPort[31:16] = debugPortInt26;
       8'd26 : debugPort[31:16] = debugPortInt27;
       8'd27 : debugPort[31:16] = debugPortInt28;
       8'd28 : debugPort[31:16] = debugPortInt29;
       8'd29 : debugPort[31:16] = debugPortInt30;
       8'd30 : debugPort[31:16] = debugPortInt31;
       8'd31 : debugPort[31:16] = debugPortInt32;
       8'd32 : debugPort[31:16] = debugPortInt33;
       8'd33 : debugPort[31:16] = debugPortInt34;
       8'd34 : debugPort[31:16] = debugPortInt35;
       8'd35 : debugPort[31:16] = debugPortInt36;
       8'd36 : debugPort[31:16] = debugPortInt37;
       8'd37 : debugPort[31:16] = debugPortInt38;
       8'd38 : debugPort[31:16] = debugPortInt39;
       8'd39 : debugPort[31:16] = debugPortInt40;
       8'd40 : debugPort[31:16] = debugPortInt41;
       8'd41 : debugPort[31:16] = debugPortInt42;
       8'd42 : debugPort[31:16] = debugPortInt43;
       8'd43 : debugPort[31:16] = debugPortInt44;
       8'd44 : debugPort[31:16] = debugPortInt45;
       8'd45 : debugPort[31:16] = debugPortInt46;
       8'd46 : debugPort[31:16] = debugPortInt47;
       8'd47 : debugPort[31:16] = debugPortInt48;
       `ifdef RW_WAPI_EN
       8'd48 : debugPort[31:16] = debugPortInt49;
       `endif
     default : debugPort[31:16] = debugPortInt1; 
  endcase
end

assign debugPortRead = debugPort;

endmodule
