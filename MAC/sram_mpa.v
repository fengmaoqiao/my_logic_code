//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission 
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author          : $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: $
// $Date: $
// ---------------------------------------------------------------------------
// Dependencies     : None
// Description      : sram__mpa module
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
// $HeadURL: $
//
//////////////////////////////////////////////////////////////////////////////

module sram_mpa
#(
  /*****************************************************************************
  * AHB addres bus length (byte address)
  *****************************************************************************/
  parameter g_addr_width=17
)
(
  /*****************************************************************************
  * System
  *****************************************************************************/
  input  wire                    clk,
  input  wire                    rst_n,

  /*****************************************************************************
  * Processor AHB bus 
  *****************************************************************************/
  input  wire                    proc_hready_in,
  input  wire                    proc_hsel,
  input  wire [g_addr_width-1:0] proc_haddr,
  input  wire [ 1:0]             proc_htrans,
  input  wire                    proc_hwrite,
  input  wire [ 1:0]             proc_hsize,      
  output wire [31:0]            proc_hrdata,
  input  wire [31:0]             proc_hwdata,
  output wire [ 1:0]             proc_hresp,
  output wire                    proc_hready,
 
  /*****************************************************************************
  * MAC AHB bus 
  *****************************************************************************/
  input  wire                    mac_hready_in,
  input  wire                    mac_hsel,
  input  wire [g_addr_width-1:0] mac_haddr,
  input  wire [ 1:0]             mac_htrans,
  input  wire                    mac_hwrite,
  input  wire [ 1:0]             mac_hsize,     
  output wire [31:0]             mac_hrdata,
  input  wire [31:0]             mac_hwdata,
  output wire [ 1:0]             mac_hresp,
  output wire                    mac_hready,
  
  /*****************************************************************************
  * LLI AHB bus interface
  *****************************************************************************/
  input  wire [g_addr_width-1:0] lli_haddr,
  input  wire [ 1:0]             lli_htrans,
  output wire [31:0]             lli_hrdata,
  output wire                    lli_hready,

  /*****************************************************************************
  * UPSTREAM bus interface
  *****************************************************************************/
  input  wire [g_addr_width-1:0] dma0_addr,
  input  wire                    dma0_trans,
  input  wire                    dma0_write,
  output wire [63:0]             dma0_rdata,
  input  wire [63:0]             dma0_wdata,
  input  wire [ 7:0]             dma0_we,
  output wire                    dma0_ready,

  /*****************************************************************************
  * DOWN bus interface
  *****************************************************************************/
  input  wire [g_addr_width-1:0] dma1_addr,
  input  wire                    dma1_trans,
  input  wire                    dma1_write,
  input  wire [ 7:0]             dma1_we,
  output wire [63:0]             dma1_rdata,
  input  wire [63:0]             dma1_wdata,
  output wire                    dma1_ready,
    
  /*****************************************************************************
  * 64 bits sram interface
  *****************************************************************************/
  output wire                    ram_cs,
  output wire [g_addr_width-4:0] ram_a,
  output wire [7:0]              ram_we,
  output wire [63:0]             ram_d,
  input  wire [63:0]             ram_q
);
  /*****************************************************************************
  * wire declarations
  *****************************************************************************/
  /* request */
  wire     proc_req;
  wire     mac_req;
  wire     lli_req;
  wire     dma0_req;
  wire     dma1_req;
  /* grant */
  reg      proc_gnt;
  reg      mac_gnt;
  reg      lli_gnt;
  reg      dma0_gnt;
  reg      dma1_gnt;
  /* cs */
  wire     proc_ram_cs; 
  wire     mac_ram_cs;
  wire     lli_ram_cs;
  wire     dma0_ram_cs;
  wire     dma1_ram_cs;
  /* asel */
  wire     proc_ram_asel;
  wire     mac_ram_asel; 
  wire     lli_ram_asel; 
  wire     dma0_ram_asel;
  wire     dma1_ram_asel;
  /* a */
  wire [g_addr_width-4:0] proc_ram_a0;
  wire [g_addr_width-4:0] proc_ram_a1;
  wire [g_addr_width-4:0] mac_ram_a0; 
  wire [g_addr_width-4:0] mac_ram_a1; 
  wire [g_addr_width-4:0] lli_ram_a0; 
  wire [g_addr_width-4:0] lli_ram_a1; 
  wire [g_addr_width-4:0] dma0_ram_a0;
  wire [g_addr_width-4:0] dma0_ram_a1;
  wire [g_addr_width-4:0] dma1_ram_a0;
  wire [g_addr_width-4:0] dma1_ram_a1;  
  /* we */
  wire [ 7:0] proc_ram_we0;
  wire [ 7:0] proc_ram_we1;
  wire [ 7:0] mac_ram_we0; 
  wire [ 7:0] mac_ram_we1; 
  wire [ 7:0] dma0_ram_we0;
  wire [ 7:0] dma0_ram_we1;
  wire [ 7:0] dma1_ram_we0;
  wire [ 7:0] dma1_ram_we1;
  /* 32 bits lane tracking */
  wire [ 1:0] proc_ram_lane;
  wire [ 1:0] mac_ram_lane;
  wire [ 1:0] lli_ram_lane;
  /* AHH size decoding and enable */
  wire        proc_trans;
  wire        mac_trans;
  
  wire        pri_req_0;
  wire        pri_req_1;
  wire        pri_req_2;
  wire        pri_req_3;
  wire        pri_req_4;
  reg  [4:0]  pri_en;
  
  /*****************************************************************************
  * registers declarations
  *****************************************************************************/
  /* data bus owner */
  reg         proc_gnt_1t;
  reg         mac_gnt_1t;
  reg         lli_gnt_1t;
  reg         dma0_gnt_1t;
  reg         dma1_gnt_1t;
  /* queue arbitration */
  reg [4:0]   pri_0;
  reg [4:0]   pri_1;
  reg [4:0]   pri_2;
  reg [4:0]   pri_3;
  reg [4:0]   pri_4;
 
  /*****************************************************************************
  * multiplexers
  *****************************************************************************/
  assign ram_cs      = proc_gnt_1t & proc_ram_cs |
                       mac_gnt_1t  & mac_ram_cs  |
                       lli_gnt_1t  & lli_ram_cs  |
                       dma0_gnt_1t & dma0_ram_cs |
                       dma1_gnt_1t & dma1_ram_cs;

  assign ram_a       = {g_addr_width{proc_gnt_1t & ~proc_ram_asel}} & proc_ram_a0 |
                       {g_addr_width{proc_gnt_1t &  proc_ram_asel}} & proc_ram_a1 |
                       {g_addr_width{mac_gnt_1t  & ~mac_ram_asel}}  & mac_ram_a0  |
                       {g_addr_width{mac_gnt_1t  &  mac_ram_asel}}  & mac_ram_a1  |
                       {g_addr_width{lli_gnt_1t  & ~lli_ram_asel}}  & lli_ram_a0  |
                       {g_addr_width{lli_gnt_1t  &  lli_ram_asel}}  & lli_ram_a1  |
                       {g_addr_width{dma0_gnt_1t & ~dma0_ram_asel}} & dma0_ram_a0 |
                       {g_addr_width{dma0_gnt_1t &  dma0_ram_asel}} & dma0_ram_a1 |
                       {g_addr_width{dma1_gnt_1t & ~dma1_ram_asel}} & dma1_ram_a0 |
                       {g_addr_width{dma1_gnt_1t &  dma1_ram_asel}} & dma1_ram_a1;

  assign ram_we      = {8{proc_gnt_1t  & ~proc_ram_asel}} & proc_ram_we0 |
                       {8{proc_gnt_1t  &  proc_ram_asel}} & proc_ram_we1 |
                       {8{mac_gnt_1t   & ~mac_ram_asel}}  & mac_ram_we0  |
                       {8{mac_gnt_1t   &  mac_ram_asel}}  & mac_ram_we1  |
                       {8{dma0_gnt_1t  & ~dma0_ram_asel}} & dma0_we & dma0_ram_we0 |
                       {8{dma0_gnt_1t  &  dma0_ram_asel}} & dma0_we & dma0_ram_we1 |
                       {8{dma1_gnt_1t  & ~dma1_ram_asel}} & dma1_we & dma1_ram_we0 |
                       {8{dma1_gnt_1t  &  dma1_ram_asel}} & dma1_we & dma1_ram_we1;
 
  assign ram_d       = {64{proc_gnt_1t}} & {proc_hwdata,proc_hwdata} |
                       {64{mac_gnt_1t}}  & {mac_hwdata,mac_hwdata}   |
                       {64{dma0_gnt_1t}} & dma0_wdata                |
                       {64{dma1_gnt_1t}} & dma1_wdata;
  
  assign proc_hrdata = {32{proc_ram_lane[1]}} & ram_q[63:32] |
                       {32{proc_ram_lane[0]}} & ram_q[31:0];

  assign mac_hrdata  = {32{mac_ram_lane[1]}} & ram_q[63:32] |
                       {32{mac_ram_lane[0]}} & ram_q[31:0];

  assign lli_hrdata  = {32{lli_ram_lane[1]}} & ram_q[63:32] |
                       {32{lli_ram_lane[0]}} & ram_q[31:0];
                    
  assign dma0_rdata  = ram_q;
  assign dma1_rdata  = ram_q;
  
  assign proc_hresp  = 2'b00;
  assign mac_hresp   = 2'b00;
  
 
  /*****************************************************************************
  * arbitration
  *****************************************************************************/
  always @(posedge clk , negedge rst_n)
  begin
     
    if(rst_n==1'b0)
    begin

      proc_gnt_1t    <= 1'b0;
      mac_gnt_1t     <= 1'b0;
      dma0_gnt_1t    <= 1'b0;
      dma1_gnt_1t    <= 1'b0; 
      lli_gnt_1t     <= 1'b0; 
     
      pri_0          <= 5'b00001;
      pri_1          <= 5'b00010;
      pri_2          <= 5'b00100;
      pri_3          <= 5'b01000;
      pri_4          <= 5'b10000;
      
    end
    else
    begin
    
      /* track which master owns the data read bus */
      proc_gnt_1t    <= proc_gnt;
      mac_gnt_1t     <= mac_gnt;
      dma0_gnt_1t    <= dma0_gnt;
      dma1_gnt_1t    <= dma1_gnt; 
      lli_gnt_1t     <= lli_gnt; 
      
      /* priority queue */
      if(pri_en[0]) pri_0 <= pri_1;
      if(pri_en[1]) pri_1 <= pri_2;
      if(pri_en[2]) pri_2 <= pri_3;
      if(pri_en[3]) pri_3 <= pri_4;
      if(pri_en[4]) pri_4 <= {dma1_gnt,dma0_gnt,lli_gnt,mac_gnt,proc_gnt};
      
    end
    
  end
  
  /* determine which entry of the priority table is request pending */
  assign pri_req_0 = (pri_0==5'b00001) & proc_req |
                     (pri_0==5'b00010) & mac_req  |
                     (pri_0==5'b00100) & lli_req  |
                     (pri_0==5'b01000) & dma0_req |
                     (pri_0==5'b10000) & dma1_req; 
  
  assign pri_req_1 = (pri_1==5'b00001) & proc_req |
                     (pri_1==5'b00010) & mac_req |
                     (pri_1==5'b00100) & lli_req |
                     (pri_1==5'b01000) & dma0_req |
                     (pri_1==5'b10000) & dma1_req; 

  assign pri_req_2 = (pri_2==5'b00001) & proc_req |
                     (pri_2==5'b00010) & mac_req |
                     (pri_2==5'b00100) & lli_req |
                     (pri_2==5'b01000) & dma0_req |
                     (pri_2==5'b10000) & dma1_req; 

  assign pri_req_3 = (pri_3==5'b00001) & proc_req |
                     (pri_3==5'b00010) & mac_req |
                     (pri_3==5'b00100) & lli_req |
                     (pri_3==5'b01000) & dma0_req |
                     (pri_3==5'b10000) & dma1_req; 
  
  assign pri_req_4 = (pri_4==5'b00001) & proc_req |
                     (pri_4==5'b00010) & mac_req |
                     (pri_4==5'b00100) & lli_req |
                     (pri_4==5'b01000) & dma0_req |
                     (pri_4==5'b10000) & dma1_req; 
  
  /* select the request with the highest priority */
  always @(*)
  begin    
    
    casez({pri_req_4,pri_req_3,pri_req_2,pri_req_1,pri_req_0})
    
      5'b????1: {pri_en,dma1_gnt,dma0_gnt,lli_gnt,mac_gnt,proc_gnt} = {5'b11111,pri_0};
      5'b???10: {pri_en,dma1_gnt,dma0_gnt,lli_gnt,mac_gnt,proc_gnt} = {5'b11110,pri_1};
      5'b??100: {pri_en,dma1_gnt,dma0_gnt,lli_gnt,mac_gnt,proc_gnt} = {5'b11100,pri_2};
      5'b?1000: {pri_en,dma1_gnt,dma0_gnt,lli_gnt,mac_gnt,proc_gnt} = {5'b11000,pri_3};
      5'b10000: {pri_en,dma1_gnt,dma0_gnt,lli_gnt,mac_gnt,proc_gnt} = {5'b10000,pri_4};
      default:  {pri_en,dma1_gnt,dma0_gnt,lli_gnt,mac_gnt,proc_gnt} = {5'b00000,pri_0};
    
    endcase

  end
  
  /*****************************************************************************
  * PROC bus interface
  *****************************************************************************/
  assign proc_trans = proc_hsel & proc_htrans[1] & proc_hready_in;
  
  bus2ram 
  #(
    .g_addr_width(   g_addr_width)
  ) 
  bus2ram_proc
  (
    /***************************************************************************
    * System
    ***************************************************************************/
    .clk(            clk),
    .rst_n(          rst_n),
    
    /***************************************************************************
    * Arbitration signaling
    ***************************************************************************/
    .req(            proc_req),
    .gnt(            proc_gnt),
    
    /***************************************************************************
    * AHB interface
    ***************************************************************************/
    .bus_addr(       proc_haddr),
    .bus_trans(      proc_trans),
    .bus_write(      proc_hwrite),
    .bus_size(       proc_hsize),
    .bus_ready(      proc_hready),
   
    /***************************************************************************
    * sram_ interface
    ***************************************************************************/
    .ram_cs(         proc_ram_cs),
    .ram_asel(       proc_ram_asel),
    .ram_a0(         proc_ram_a0),
    .ram_a1(         proc_ram_a1),
    .ram_we0(        proc_ram_we0),
    .ram_we1(        proc_ram_we1),
    .ram_lane(       proc_ram_lane)
  );
 
  /*****************************************************************************
  * MAC bus interface
  *****************************************************************************/
  assign mac_trans = mac_hsel & mac_htrans[1] & mac_hready_in;
  
  bus2ram 
  #(
    .g_addr_width(   g_addr_width)
  ) 
  bus2ram_mac
  (
    /***************************************************************************
    * System
    ***************************************************************************/
    .clk(            clk),
    .rst_n(          rst_n),
    
    /***************************************************************************
    * Arbitration signaling
    ***************************************************************************/
    .req(            mac_req),
    .gnt(            mac_gnt),
    
    /***************************************************************************
    * bus interface
    ***************************************************************************/
    .bus_addr(       mac_haddr),
    .bus_trans(      mac_trans),
    .bus_write(      mac_hwrite),
    .bus_size(       mac_hsize),
    .bus_ready(      mac_hready),
   
    /***************************************************************************
    * ram interface
    ***************************************************************************/
    .ram_cs(         mac_ram_cs),
    .ram_asel(       mac_ram_asel),
    .ram_a0(         mac_ram_a0),
    .ram_a1(         mac_ram_a1),
    .ram_we0(        mac_ram_we0),
    .ram_we1(        mac_ram_we1),
    .ram_lane(       mac_ram_lane)
  );
 
  /*****************************************************************************
  * LLI bus interface
  *****************************************************************************/
  bus2ram 
  #(
    .g_addr_width(   g_addr_width)
  ) 
  bus2ram_lli
  (
    /***************************************************************************
    * System
    ***************************************************************************/
    .clk(            clk),
    .rst_n(          rst_n),
    
    /***************************************************************************
    * Arbitration signaling
    ***************************************************************************/
    .req(            lli_req),
    .gnt(            lli_gnt),
    
    /***************************************************************************
    * bus interface
    ***************************************************************************/
    .bus_addr(       lli_haddr),
    .bus_trans(      lli_htrans[1]),
    .bus_write(      1'b0),
    .bus_size(       2'b10),
    .bus_ready(      lli_hready),
   
    /***************************************************************************
    * ram interface
    ***************************************************************************/
    .ram_cs(         lli_ram_cs),
    .ram_asel(       lli_ram_asel),
    .ram_a0(         lli_ram_a0),
    .ram_a1(         lli_ram_a1),
    .ram_we0(        ),
    .ram_we1(        ),
    .ram_lane(       lli_ram_lane)
  );

  /*****************************************************************************
  * upstream bus interface
  *****************************************************************************/
  bus2ram 
  #(
    .g_addr_width(   g_addr_width)
  ) 
  bus2ram_dma0
  (
    /***************************************************************************
    * System
    ***************************************************************************/
    .clk(            clk),
    .rst_n(          rst_n),
    
    /***************************************************************************
    * Arbitration signaling
    ***************************************************************************/
    .req(            dma0_req),
    .gnt(            dma0_gnt),
   
    /***************************************************************************
    * bus interface
    ***************************************************************************/
    .bus_addr(       dma0_addr),
    .bus_trans(      dma0_trans),
    .bus_write(      dma0_write),
    .bus_size(       2'b11),
    .bus_ready(      dma0_ready),
   
    /***************************************************************************
    * ram interface
    ***************************************************************************/
    .ram_cs(         dma0_ram_cs),
    .ram_asel(       dma0_ram_asel),
    .ram_a0(         dma0_ram_a0),
    .ram_a1(         dma0_ram_a1),
    .ram_we0(        dma0_ram_we0),
    .ram_we1(        dma0_ram_we1),
    .ram_lane(       )
  );
 
  /*****************************************************************************
  * downstream bus interface
  *****************************************************************************/
  bus2ram 
  #(
    .g_addr_width(   g_addr_width)
  ) 
  bus2ram_dma1
  (
    /***************************************************************************
    * System
    ***************************************************************************/
    .clk(            clk),
    .rst_n(          rst_n),
    
    /***************************************************************************
    * Arbitration signaling
    ***************************************************************************/
    .req(            dma1_req),
    .gnt(            dma1_gnt),
    
    /***************************************************************************
    * bus interface
    ***************************************************************************/
    .bus_addr(       dma1_addr),
    .bus_trans(      dma1_trans),
    .bus_write(      dma1_write),
    .bus_size(       2'b11),
    .bus_ready(      dma1_ready),
   
    /***************************************************************************
    * ram interface
    ***************************************************************************/
    .ram_cs(         dma1_ram_cs),
    .ram_asel(       dma1_ram_asel),
    .ram_a0(         dma1_ram_a0),
    .ram_a1(         dma1_ram_a1),
    .ram_we0(        dma1_ram_we0),
    .ram_we1(        dma1_ram_we1),
    .ram_lane(       )
  );

endmodule
