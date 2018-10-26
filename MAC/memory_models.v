//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author: jvanthou $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: $
// $Date: 2014-10-15 23:16:58 +0200 (Wed, 15 Oct 2014) $
// ---------------------------------------------------------------------------
// Dependencies     : None
// Description      : memory models
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
// $HeadURL: https://svn.frso.rivierawaves.com/svn/rw_wlan_nx/trunk/Projects/WLAN_NX_REF_IP/HW/SB/rw_nx_fpga_a_tl4/verilog/tb/memory_models.v $
//
//////////////////////////////////////////////////////////////////////////////

/*****************************************************************************
* sram_sp_64x187
*****************************************************************************/
module sram_sp_64x187
(
  input  wire           clka,
  input  wire           ena,
  input  wire           wea,
  input  wire  [5:0]    addra,
  input  wire  [186:0]  dina,
  output reg   [186:0]  douta
);
  (* ram_style = "block" *)
  reg [186:0]   mem [0:63];
  integer i;
  
  initial
  begin
    for (i = 0; i <= 63; i = i + 1)
    begin
        mem[i]=32'b0;
    end  
  end

  // write port
  always @(posedge clka)
  begin
  
    if(ena==1)
    begin
    
      douta <= mem[addra];
      
      if(wea==1) mem[addra][186: 0] <= dina[186: 0];
    end
    else
      douta <= 0;
  
  end

endmodule
/*****************************************************************************
* sram_sp_4096x32
*****************************************************************************/
//module sram_sp_4096x32
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire  [ 3:0]   wea,
//  input  wire  [11:0]   addra,
//  input  wire  [31:0]   dina,
//  output reg   [31:0]   douta
//);
//
//  reg [31:0]   mem [0:4095];
//  integer i;
//  
//  initial
//  begin
//    for (i = 0; i <= 4095; i = i + 1)
//    begin
//        mem[i]=32'b0;
//    end  
//  end
//
//  // write port
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      douta <= mem[addra];
//      
//      if(wea[0]==1) mem[addra][ 7: 0] <= dina[ 7: 0];
//      if(wea[1]==1) mem[addra][15: 8] <= dina[15: 8];
//      if(wea[2]==1) mem[addra][23:16] <= dina[23:16];
//      if(wea[3]==1) mem[addra][31:24] <= dina[31:24];
//      
//    end
//    else
//      douta <= 0;
//  
//  end
//
//endmodule
/*****************************************************************************
* sram_sp_8192x32
*****************************************************************************/
//module sram_sp_8192x32
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire  [ 3:0]   wea,
//  input  wire  [12:0]   addra,
//  input  wire  [31:0]   dina,
//  output reg   [31:0]   douta
//);
//
//  reg [31:0]   mem [0:8191];
//  integer i;
//  
//  initial
//  begin
//    for (i = 0; i <= 8191; i = i + 1)
//    begin
//        mem[i]=32'b0;
//    end  
//  end
//
//  // write port
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      douta <= mem[addra];
//      
//      if(wea[0]==1) mem[addra][ 7: 0] <= dina[ 7: 0];
//      if(wea[1]==1) mem[addra][15: 8] <= dina[15: 8];
//      if(wea[2]==1) mem[addra][23:16] <= dina[23:16];
//      if(wea[3]==1) mem[addra][31:24] <= dina[31:24];
//      
//    end
//    else
//      douta <= 0;
//  
//  end
//
//endmodule

/*****************************************************************************
* sram_sp_8192x16
*****************************************************************************/
//module sram_sp_8192x16
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire  [ 1:0]   wea,
//  input  wire  [12:0]   addra,
//  input  wire  [15:0]   dina,
//  output reg   [15:0]   douta
//);
//
//  reg [15:0]   mem [0:8191];
//  integer i;
//
//  initial
//  begin
//    for (i = 0; i <= 8191; i = i + 1)
//    begin
//        mem[i]=32'b0;
//    end  
//  end
//  // write port
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      douta <= mem[addra];
//      
//      if(wea[0]==1) mem[addra][ 7: 0] <= dina[ 7: 0];
//      if(wea[1]==1) mem[addra][15: 8] <= dina[15: 8];
//      
//    end
//    else
//      douta <= 0;
//  
//  end
//
//endmodule
/*****************************************************************************
* sram_sp_16384x16
*****************************************************************************/
//module sram_sp_16384x16
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire  [ 1:0]   wea,
//  input  wire  [13:0]   addra,
//  input  wire  [15:0]   dina,
//  output reg   [15:0]   douta
//);
//
//  reg [15:0]   mem [0:16383];
//  integer i;
//
//  initial
//  begin
//    for (i = 0; i <= 16383; i = i + 1)
//    begin
//        mem[i]=32'b0;
//    end  
//  end
//  // write port
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      douta <= mem[addra];
//      
//      if(wea[0]==1) mem[addra][ 7: 0] <= dina[ 7: 0];
//      if(wea[1]==1) mem[addra][15: 8] <= dina[15: 8];
//      
//    end
//    else
//      douta <= 0;
//  
//  end
//
//endmodule

/*****************************************************************************
* sram_sp_65536x32
*****************************************************************************/
//module sram_sp_65536x32
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire  [ 3:0]   wea,
//  input  wire  [15:0]   addra,
//  input  wire  [31:0]   dina,
//  output reg   [31:0]   douta
//);
//
//  reg [31:0]   mem [0:65535];
//  // write port
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      douta <= mem[addra];
//      
//      if(wea[0]==1) mem[addra][ 7: 0] <= dina[ 7: 0];
//      if(wea[1]==1) mem[addra][15: 8] <= dina[15: 8];
//      if(wea[2]==1) mem[addra][23:16] <= dina[23:16];
//      if(wea[3]==1) mem[addra][31:24] <= dina[31:24];
//      
//    end
//  
//  end
//
//endmodule

/*****************************************************************************
* sram_sp_32768x64
*****************************************************************************/


	
module sram_sp_32768x64
(
  input  wire           clka,
  input  wire           ena,
  input  wire  [ 7:0]   wea,
  input  wire  [14:0]   addra,
  input  wire  [63:0]   dina,
  output reg   [63:0]   douta
);
  

  (* ram_style = "block" *)
  reg [63:0]   mem [0:32767];
  // write port
  always @(posedge clka)
  begin
  

  	
    if(ena==1)
    begin
    
      douta <= mem[addra];
      
      
      if(wea[0]==1) mem[addra][ 7: 0] <= dina[ 7: 0];
      if(wea[1]==1) mem[addra][15: 8] <= dina[15: 8];
      if(wea[2]==1) mem[addra][23:16] <= dina[23:16];
      if(wea[3]==1) mem[addra][31:24] <= dina[31:24];
      if(wea[4]==1) mem[addra][39:32] <= dina[39:32];
      if(wea[5]==1) mem[addra][47:40] <= dina[47:40];
      if(wea[6]==1) mem[addra][55:48] <= dina[55:48];
      if(wea[7]==1) mem[addra][63:56] <= dina[63:56];
      
    end
  
  end

endmodule


/*****************************************************************************
* sram_sp_256x32
*****************************************************************************/
module sram_sp_256x32
(
  input  wire           clka,
  input  wire           ena,
  input  wire           wea,
  input  wire  [ 7:0]   addra,
  input  wire  [31:0]   dina,
  output reg   [31:0]   douta
);
  (* ram_style = "block" *)
  reg [31:0]   mem [0:255];

  always @(posedge clka)
  begin
  
    if(ena==1)
    begin
    
      douta <= mem[addra];
      
      if(wea==1) mem[addra] <= dina;
      
    end
  
  end

endmodule

/*****************************************************************************
* sram_sp_8x32
*****************************************************************************/
//module sram_sp_8x32
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire           wea,
//  input  wire  [ 2:0]   addra,
//  input  wire  [31:0]   dina,
//  output reg   [31:0]   douta
//);
//
//  reg [31:0]   mem [0:7];
//
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      douta <= mem[addra];
//      
//      if(wea==1) mem[addra] <= dina;
//      
//    end
//  
//  end
//
//endmodule

/*****************************************************************************
* sram_sp_4x88
*****************************************************************************/
module sram_sp_4x88
(
  input  wire           clka,
  input  wire           ena,
  input  wire           wea,
  input  wire  [ 1:0]   addra,
  input  wire  [87:0]   dina,
  output reg   [87:0]   douta
);
  (* ram_style = "block" *)
  reg [87:0]   mem [0:3];

  always @(posedge clka)
  begin
  
    if(ena==1)
    begin
    
      douta <= mem[addra];
      
      if(wea==1) mem[addra] <= dina;
      
    end
  
  end

endmodule

/*****************************************************************************
* sram_sp_64x186
*****************************************************************************/
//module sram_sp_64x186
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire           wea,
//  input  wire  [  5:0]  addra,
//  input  wire  [185:0]  dina,
//  output reg   [185:0]  douta
//);
//
//  reg [185:0]   mem [0:63];
//
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      douta <= mem[addra];
//      
//      if(wea==1) mem[addra] <= dina;
//      
//    end
//  
//  end
//
//endmodule

/*****************************************************************************
* sram_dp_64x38
*****************************************************************************/
module sram_dp_64x38
(
  input  wire           clka,
  input  wire           wea,
  input  wire [ 5:0]    addra,
  input  wire [37:0]    dina,

  input  wire           clkb,
  input  wire           enb,
  input  wire [ 5:0]    addrb,
  output reg  [37:0]    doutb
);
  (* ram_style = "block" *)
  reg [37:0]     mem [0:63];

  // port a
  always @(posedge clka)
  begin
  
    if(wea==1)
    begin
    
      mem[addra] <= dina;
    
    end
        
  end
 
  // port b
  always @(posedge clkb)
  begin
  
    if(enb==1)
    begin
    
      doutb <= mem[addrb];
      
    end
  
  end
  
endmodule


/*****************************************************************************
* sram_dp_64x36
*****************************************************************************/
module sram_dp_64x36
(
  input  wire           clka,
  input  wire           wea,
  input  wire [ 5:0]    addra,
  input  wire [35:0]    dina,

  input  wire           clkb,
  input  wire           enb,
  input  wire [ 5:0]    addrb,
  output reg  [35:0]    doutb
);
(* ram_style = "block" *)
  reg [35:0]     mem [0:63];

  // port a
  always @(posedge clka)
  begin
  
    if(wea==1)
    begin
    
      mem[addra] <= dina;
    
    end
        
  end
 
  // port b
  always @(posedge clkb)
  begin
  
    if(enb==1)
    begin
    
      doutb <= mem[addrb];
      
      
    end
  
  end
  
endmodule

/*****************************************************************************
* sram_dp_64x8
*****************************************************************************/
//module sram_dp_64x8
//(
//  input  wire           clka,
//  input  wire           wea,
//  input  wire [ 5:0]    addra,
//  input  wire [ 7:0]    dina,
//
//  input  wire           clkb,
//  input  wire           enb,
//  input  wire [ 5:0]    addrb,
//  output reg  [ 7:0]    doutb
//);
//
//  reg [7:0]     mem [0:63];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(wea==1)
//    begin
//    
//      mem[addra] <= dina;
//    
//    end
//        
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    if(enb==1)
//    begin
//    
//      doutb <= mem[addrb];
//      
//      
//    end
//  
//  end
//  
//endmodule

/*****************************************************************************
* sram_dp_64x26
*****************************************************************************/
//module sram_dp_64x26
//(
//  input  wire           clka,
//  input  wire           wea,
//  input  wire [ 5:0]    addra,
//  input  wire [25:0]    dina,
//
//  input  wire           clkb,
//  input  wire           enb,
//  input  wire [ 5:0]    addrb,
//  output reg  [25:0]    doutb
//);
//
//  reg [25:0]     mem [0:63];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(wea==1)
//    begin
//    
//      mem[addra] <= dina;
//    
//    end
//        
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    if(enb==1)
//    begin
//    
//      doutb <= mem[addrb];
//      
//      
//    end
//  
//  end
//  
//endmodule

/*****************************************************************************
* sram_dp_128x26
*****************************************************************************/
//module sram_dp_128x26
//(
//  input  wire           clka,
//  input  wire           wea,
//  input  wire [ 6:0]    addra,
//  input  wire [25:0]    dina,
//
//  input  wire           clkb,
//  input  wire           enb,
//  input  wire [ 6:0]    addrb,
//  output reg  [25:0]    doutb
//);
//
//  reg [25:0]     mem [0:127];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(wea==1)
//    begin
//    
//      mem[addra] <= dina;
//    
//    end
//        
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    if(enb==1)
//    begin
//    
//      doutb <= mem[addrb];
//      
//      
//    end
//  
//  end
//  
//endmodule

/*****************************************************************************
* sram_dp_128x8
*****************************************************************************/
module sram_dp_128x8
(
  input  wire           clka,
  input  wire           wea,
  input  wire [ 6:0]    addra,
  input  wire [ 7:0]    dina,

  input  wire           clkb,
  input  wire           enb,
  input  wire [ 6:0]    addrb,
  output reg  [ 7:0]    doutb
);
(* ram_style = "block" *)
  reg [7:0]     mem [0:127];

  // port a
  always @(posedge clka)
  begin
  
    if(wea==1)
    begin
    
      mem[addra] <= dina;
    
    end
        
  end
 
  // port b
  always @(posedge clkb)
  begin
  
    if(enb==1)
    begin
    
      doutb <= mem[addrb];
      
      
    end
  
  end
  
endmodule


/*****************************************************************************
* sram_tdp_4096x32
*****************************************************************************/
//module sram_tdp_4096x32
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire           wea,
//  input  wire [11:0]    addra,
//  input  wire [31:0]    dina,
//  output reg  [31:0]    douta,
//
//  input  wire           clkb,
//  input  wire           enb,
//  input  wire           web,
//  input  wire [11:0]    addrb,
//  input  wire [31:0]    dinb,
//  output reg  [31:0]    doutb
//);
//
//  reg [31:0]     mem [0:4095];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      if(wea==1)
//      begin
//    
//        mem[addra] <= dina;
//    
//      end
//      else
//      begin
//      
//        douta <= mem[addra];
//      
//      end
//      
//    end
//  
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    if(enb==1)
//    begin
//    
//      if(web==1)
//      begin
//    
//        mem[addrb] <= dinb;
//    
//      end
//      else
//      begin
//      
//        doutb <= mem[addrb];
//      
//      end
//      
//    end
//  
//  end
//  
//
//endmodule
/*****************************************************************************
* sram_tdp_16kx32
*****************************************************************************/
//module sram_tdp_16kx32
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire           wea,
//  input  wire [13:0]    addra,
//  input  wire [31:0]    dina,
//  output reg  [31:0]    douta,
//
//  input  wire           clkb,
//  input  wire           enb,
//  input  wire           web,
//  input  wire [13:0]    addrb,
//  input  wire [31:0]    dinb,
//  output reg  [31:0]    doutb
//);
//
//  reg [31:0]     mem [0:16383];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      if(wea==1)
//      begin
//    
//        mem[addra] <= dina;
//    
//      end
//      else
//      begin
//      
//        douta <= mem[addra];
//      
//      end
//      
//    end
//  
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    if(enb==1)
//    begin
//    
//      if(web==1)
//      begin
//    
//        mem[addrb] <= dinb;
//    
//      end
//      else
//      begin
//      
//        doutb <= mem[addrb];
//      
//      end
//      
//    end
//  
//  end
//  
//endmodule

/*****************************************************************************
* sram_tdp_256x8
*****************************************************************************/
module sram_tdp_256x8
(
  input  wire           clka,
  input  wire           ena,
  input  wire           wea,
  input  wire [ 7:0]    addra,
  input  wire [ 7:0]    dina,
  output reg  [ 7:0]    douta,

  input  wire           clkb,
  input  wire           enb,
  input  wire           web,
  input  wire [ 7:0]    addrb,
  input  wire [ 7:0]    dinb,
  output reg  [ 7:0]    doutb
);
(* ram_style = "block" *)
  reg [7:0]     mem [0:256];

  // port a
  always @(posedge clka)
  begin
  
    if(ena==1)
    begin
    
      if(wea==1)
      begin
    
        mem[addra] <= dina;
    
      end
      else
      begin
      
        douta <= mem[addra];
      
      end
      
    end
  
  end
 
  // port b
  always @(posedge clkb)
  begin
  
    if(enb==1)
    begin
    
      if(web==1)
      begin
    
        mem[addrb] <= dinb;
    
      end
      else
      begin
      
        doutb <= mem[addrb];
      
      end
      
    end
  
  end
  

endmodule

/*****************************************************************************
* sram_dp_128x10
*****************************************************************************/
//module sram_dp_128x10
//(
//  input  wire           clka,
//  input  wire           wea,
//  input  wire [ 6:0]    addra,
//  input  wire [ 9:0]    dina,
//
//  input  wire           clkb,
//  input  wire           enb,
//  input  wire [ 6:0]    addrb,
//  output reg  [ 9:0]    doutb
//);
//
//  reg [ 9:0]     mem [0:127];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(wea==1)
//    begin
//    
//      mem[addra] <= dina;
//    
//    end
//        
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    if(enb==1)
//    begin
//    
//      doutb <= mem[addrb];
//      
//    end
//  
//  end
//  
//endmodule


/*****************************************************************************
* sram_dp_64x10
*****************************************************************************/
//module sram_dp_64x10
//(
//  input  wire           clka,
//  input  wire           wea,
//  input  wire [ 5:0]    addra,
//  input  wire [ 9:0]    dina,
//
//  input  wire           clkb,
//  input  wire           enb,
//  input  wire [ 5:0]    addrb,
//  output reg  [ 9:0]    doutb
//);
//
//  reg [ 9:0]     mem [0:63];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(wea==1)
//    begin
//    
//      mem[addra] <= dina;
//    
//    end
//        
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    if(enb==1)
//    begin
//    
//      doutb <= mem[addrb];
//      
//    end
//  
//  end
//  
//endmodule

/*****************************************************************************
* sram_dp_32x31
*****************************************************************************/
//module sram_dp_32x31
//(
//  input  wire           clka,
//  input  wire           wea,
//  input  wire [ 4:0]    addra,
//  input  wire [30:0]    dina,
//
//  input  wire           clkb,
//  input  wire           enb,
//  input  wire [ 4:0]    addrb,
//  output reg  [30:0]    doutb
//);
//
//  reg [30:0]     mem [0:31];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(wea==1)
//    begin
//    
//      mem[addra] <= dina;
//    
//    end
//        
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    if(enb==1)
//    begin
//      doutb <= mem[addrb];
//    end
//  
//  end
//  
//endmodule
/*****************************************************************************
* sram_tdp_32x72
*****************************************************************************/
//module sram_tdp_32x72
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire           wea,
//  input  wire [ 4:0]    addra,
//  input  wire [71:0]    dina,
//  output reg  [71:0]    douta,
//
//  input  wire           clkb,
//  input  wire           enb,
//  input  wire           web,
//  input  wire [ 4:0]    addrb,
//  input  wire [71:0]    dinb,
//  output reg  [71:0]    doutb
//);
//
//  reg [71:0]     mem [0:31];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      if(wea==1)
//      begin
//    
//        mem[addra] <= dina;
//    
//      end
//      else
//      begin
//      
//        douta <= mem[addra];
//      
//      end
//      
//    end
//  
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    if(enb==1)
//    begin
//    
//      if(web==1)
//      begin
//    
//        mem[addrb] <= dinb;
//    
//      end
//      else
//      begin
//      
//        doutb <= mem[addrb];
//      
//      end
//      
//    end
//  
//  end
//  
//
//endmodule

/*****************************************************************************
* sram_tdp_32x52
*****************************************************************************/
//module sram_tdp_32x52
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire           wea,
//  input  wire [ 4:0]    addra,
//  input  wire [51:0]    dina,
//  output reg  [51:0]    douta,
//
//  input  wire           clkb,
//  input  wire           enb,
//  input  wire           web,
//  input  wire [ 4:0]    addrb,
//  input  wire [51:0]    dinb,
//  output reg  [51:0]    doutb
//);
//
//  reg [51:0]     mem [0:31];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      if(wea==1)
//      begin
//    
//        mem[addra] <= dina;
//    
//      end
//      else
//      begin
//      
//        douta <= mem[addra];
//      
//      end
//      
//    end
//  
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    if(enb==1)
//    begin
//    
//      if(web==1)
//      begin
//    
//        mem[addrb] <= dinb;
//    
//      end
//      else
//      begin
//      
//        doutb <= mem[addrb];
//      
//      end
//      
//    end
//  
//  end
//  
//
//endmodule


/*****************************************************************************
* sram_tdp_256x26
*****************************************************************************/
//module sram_tdp_256x26
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire           wea,
//  input  wire [ 7:0]    addra,
//  input  wire [25:0]    dina,
//  output reg  [25:0]    douta,
//
//  input  wire           clkb,
//  input  wire           enb,
//  input  wire           web,
//  input  wire [ 7:0]    addrb,
//  input  wire [25:0]    dinb,
//  output reg  [25:0]    doutb
//);
//
//  reg [25:0]     mem [0:255];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      if(wea==1)
//      begin
//    
//        mem[addra] <= dina;
//    
//      end
//      else
//      begin
//      
//        douta <= mem[addra];
//      
//      end
//      
//    end
//  
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    if(enb==1)
//    begin
//    
//      if(web==1)
//      begin
//    
//        mem[addrb] <= dinb;
//    
//      end
//      else
//      begin
//      
//        doutb <= mem[addrb];
//      
//      end
//      
//    end
//  
//  end
//
//endmodule  
  
/*****************************************************************************
* sram_sp_128x76
*****************************************************************************/
//module sram_sp_128x76
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire           wea,
//  input  wire  [ 6:0]   addra,
//  input  wire  [75:0]   dina,
//  output reg   [75:0]   douta
//);
//
//  reg [75:0]   mem [0:127];
//
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      douta <= mem[addra];
//      
//      if(wea==1) mem[addra] <= dina;
//      
//    end
//  
//  end
//
//endmodule

/*****************************************************************************
* sram_sp_512x10
*****************************************************************************/
//module sram_sp_512x10
//(
//  input  wire          clka,
//  input  wire          ena,
//  input  wire          wea,
//  input  wire  [8:0]   addra,
//  input  wire  [9:0]   dina,
//  output reg   [9:0]   douta
//);
//
//  reg [9:0]   mem [0:511];
//
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      douta <= mem[addra];
//      
//      if(wea==1) mem[addra] <= dina;
//      
//    end
//  
//  end
//
//endmodule

/*****************************************************************************
* sram_sp_256x76
*****************************************************************************/
//module sram_sp_256x76
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire           wea,
//  input  wire  [ 7:0]   addra,
//  input  wire  [75:0]   dina,
//  output reg   [75:0]   douta
//);
//
//  reg [75:0]   mem [0:255];
//
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      douta <= mem[addra];
//      
//      if(wea==1) mem[addra] <= dina;
//      
//    end
//  
//  end
//
//endmodule

/*****************************************************************************
* sram_sp_512x32
*****************************************************************************/
//module sram_sp_512x32
//(
//  input  wire           clka,
//  input  wire           ena,
//  input  wire           wea,
//  input  wire   [8:0]   addra,
//  input  wire  [31:0]   dina,
//  output reg   [31:0]   douta
//);
//
//  reg [31:0]   mem [0:511];
//
//  always @(posedge clka)
//  begin
//  
//    if(ena==1)
//    begin
//    
//      douta <= mem[addra];
//      
//      if(wea==1) mem[addra] <= dina;
//      
//    end
//  
//  end
//
//endmodule

/*****************************************************************************
* sram_dp_65536x64
*****************************************************************************/
//module sram_dp_65536x64
//(
//  input  wire           clka,
//  input  wire           wea,
//  input  wire [15:0]    addra,
//  input  wire [63:0]    dina,
//
//  input  wire           clkb,
//  input  wire [15:0]    addrb,
//  output reg  [63:0]    doutb
//);
//
//  reg [63:0]     mem [0:65535];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(wea==1)
//    begin
//    
//      mem[addra] <= dina;
//    
//    end
//        
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    doutb <= mem[addrb];
//  
//  end
//  
//endmodule

/*****************************************************************************
* sram_dp_65536x98
*****************************************************************************/
//module sram_dp_65536x98
//(
//  input  wire           clka,
//  input  wire           wea,
//  input  wire [15:0]    addra,
//  input  wire [97:0]    dina,
//
//  input  wire           clkb,
//  input  wire [15:0]    addrb,
//  output reg  [97:0]    doutb
//);
//
//  reg [97:0]     mem [0:65535];
//    integer i_v;
//
//
//  initial
//  begin
//    
//    for (i_v = 0; i_v < 65536; i_v = i_v +1)
//    begin
//      mem[i_v][7:0]   = (12*i_v);
//      mem[i_v][15:8]  = (12*i_v+1);
//      mem[i_v][23:16] = (12*i_v+2);
//      mem[i_v][31:24] = (12*i_v+3);
//
//      mem[i_v][39:32] = (12*i_v+4);
//      mem[i_v][47:40] = (12*i_v+5);
//      mem[i_v][55:48] = (12*i_v+6);
//      mem[i_v][63:56] = (12*i_v+7);
//
//      mem[i_v][71:64] = (12*i_v+8);
//      mem[i_v][79:72] = (12*i_v+9);
//      mem[i_v][87:80] = (12*i_v+10);
//      mem[i_v][95:88] = (12*i_v+11);
//  
//      mem[i_v][97:96] = (i_v % 4);
//    end
//  end
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(wea==1)
//    begin
//    
//      mem[addra] <= dina;
//    
//    end
//        
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    doutb <= mem[addrb];
//  
//  end
//  
//endmodule

/*****************************************************************************
* sram_dp_65536x128
*****************************************************************************/
//module sram_dp_65536x128
//(
//  input  wire           clka,
//  input  wire           wea,
//  input  wire [15:0]    addra,
//  input  wire [127:0]   dina,
//
//  input  wire           clkb,
//  input  wire [15:0]    addrb,
//  output reg  [127:0]   doutb
//);
//
//  reg [127:0]     mem [0:65535];
//    integer i_v;
//
//
//  initial
//  begin
//    
//    for (i_v = 0; i_v < 65536; i_v = i_v +1)
//    begin
//      mem[i_v][7:0]     = (16*i_v);
//      mem[i_v][15:8]    = (16*i_v+1);
//      mem[i_v][23:16]   = (16*i_v+2);
//      mem[i_v][31:24]   = (16*i_v+3);
//
//      mem[i_v][39:32]   = (16*i_v+4);
//      mem[i_v][47:40]   = (16*i_v+5);
//      mem[i_v][55:48]   = (16*i_v+6);
//      mem[i_v][63:56]   = (16*i_v+7);
//
//      mem[i_v][71:64]   = (16*i_v+8);
//      mem[i_v][79:72]   = (16*i_v+9);
//      mem[i_v][87:80]   = (16*i_v+10);
//      mem[i_v][95:88]   = (16*i_v+11);
//  
//      mem[i_v][103:96]  = (16*i_v+12);
//      mem[i_v][111:104] = (16*i_v+13);
//      mem[i_v][119:112] = (16*i_v+14);
//      mem[i_v][127:120] = (16*i_v+15);
//  
//    end
//  end
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(wea==1)
//    begin
//    
//      mem[addra] <= dina;
//    
//    end
//        
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    doutb <= mem[addrb];
//  
//  end
//  
//endmodule

/*****************************************************************************
* sram_dp_256x10
*****************************************************************************/
//module sram_dp_256x10
//(
//  input  wire           clka,
//  input  wire           wea,
//  input  wire [ 7:0]    addra,
//  input  wire [ 9:0]    dina,
//
//  input  wire           clkb,
//  input  wire           enb,
//  input  wire [ 7:0]    addrb,
//  output reg  [ 9:0]    doutb
//);
//
//  reg [9:0]     mem [0:255];
//
//  // port a
//  always @(posedge clka)
//  begin
//  
//    if(wea==1)
//    begin
//    
//      mem[addra] <= dina;
//    
//    end
//        
//  end
// 
//  // port b
//  always @(posedge clkb)
//  begin
//  
//    if(enb==1)
//    
//      doutb <= mem[addrb];
//  
//  end
//  
//endmodule

`default_nettype wire
