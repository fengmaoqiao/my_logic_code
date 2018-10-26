`timescale 1ns/10ps
`define multiple 10

module rw_nx_platform_sim(

);

wire clk_32k;
wire clk_30m;
wire clk_80m;
wire clk_200m;

reg clk_80m_in;
reg rst_n;

wire proc_hready;
reg [31:0] proc_haddr;
reg [1:0] proc_htrans;
reg proc_hwrite;
reg [1:0] proc_hsize;
wire [31:0] proc_hrdata;
reg [31:0] proc_hwdata;
wire [1:0] proc_hresp;

wire m0_axis_tohost_tvalid;
wire m0_axis_tohost_tready;
wire [63:0] m0_axis_tohost_tdata;
wire [7:0] m0_axis_tohost_tkeep;
wire m0_axis_tohost_tlast;

reg s1_axis_fromhost_tvalid;
wire s1_axis_fromhost_tready;
reg [63:0] s1_axis_fromhost_tdata;
reg [7:0] s1_axis_fromhost_tkeep;
reg s1_axis_fromhost_tlast;

parameter PERIOD_30m = 33.33;
parameter PERIOD_80m = 12.5;
parameter PERIOD_200m = 5;


clk_wiz_0 u_clk_wiz_0(
    .clk_in1          (clk_80m_in),
    
    .clk_out1         (clk_30m),        //set 30m
    .clk_out2         (clk_80m),        //set 80m       
    .clk_out3         (clk_240m),       //set 240m
    .clk_out4         (clk_20p32m),
    
    .resetn           (rst_n)
);

rw_nx_platform u_rw_nx_platform(
    .clk_32k                  (0),
    .clk_30m                  (clk_30m),
    .clk_80m                  (clk_80m),
    .clk_200m                 (clk_80m),
    
    //.pci_clk33m               (clk_30m                ),
    //.pll_clk240m              (clk_240m               ),
    //.clk_20p32                (clk_20p32m             ),
    //.error_count              (error_count            ),
    
    .por_rst_n    (rst_n),
    
    .proc_hready              (proc_hready),
    .proc_haddr               (proc_haddr),
    .proc_htrans              (proc_htrans),
    .proc_hwrite              (proc_hwrite),
    .proc_hsize               (proc_hsize),
    .proc_hrdata              (proc_hrdata),
    .proc_hwdata              (proc_hwdata),
    .proc_hresp               (proc_hresp),
    
    .m0_axis_tohost_tvalid    (m0_axis_tohost_tvalid),
    .m0_axis_tohost_tready    (m0_axis_tohost_tready),
    .m0_axis_tohost_tkeep     (m0_axis_tohost_tkeep),
    .m0_axis_tohost_tdata     (m0_axis_tohost_tdata),
    .m0_axis_tohost_tlast     (m0_axis_tohost_tlast),
    
    .s1_axis_fromhost_tvalid  (s1_axis_fromhost_tvalid),
    .s1_axis_fromhost_tready  (s1_axis_fromhost_tready),
    .s1_axis_fromhost_tdata   (s1_axis_fromhost_tdata),
    .s1_axis_fromhost_tkeep   (s1_axis_fromhost_tkeep),
    .s1_axis_fromhost_tlast   (s1_axis_fromhost_tlast)
  
  
);



always begin
  clk_80m_in = 1'b0;
  #(PERIOD_80m/2) clk_80m_in = 1'b1;
  #(PERIOD_80m/2);
end

reg [31:0] counter;
reg [31:0] down_data_counter;

initial begin
rst_n = 1'b0;
#200
rst_n = 1'b1;
end
task REG_WR;
    input [31:0] addr;
    input [31:0] data;
    begin
        proc_hwrite = 1'b1;
        proc_htrans = 2'b10;
        proc_haddr  = addr;
        proc_hwdata = data;
        proc_hwrite = 1'b1;
    end
endtask

task REG_RD;
    input [31:0] addr;
    input [31:0] data;
    begin
        proc_hwrite = 1'b0;
        proc_htrans = 2'b10;
        proc_haddr  = addr;
        proc_hwdata = data;
    end
endtask
//write lli into the sram
always@(posedge clk_80m or negedge rst_n)
begin

  if(!rst_n)
  begin
    //proc_hwrite = 1'b1;
    proc_htrans = 2'b00;
    counter     = 16'd0;
    s1_axis_fromhost_tvalid = 1'b0;
    s1_axis_fromhost_tdata  = 64'b0;
    s1_axis_fromhost_tkeep  = 8'b0;
    s1_axis_fromhost_tlast  = 8'b0;
    down_data_counter       = 32'b0;
  end
  else begin
    proc_hsize = 2'b10;
    if(counter  != 16'd65530)
    counter     = counter + 1;

    case(counter)
    /////////////////////////////////////////////////////////////////////////////////
    11:REG_WR(32'h60000000,32'h20000001);    
        
    21:REG_WR(32'h60000004,32'h60000100);
    
    31:REG_WR(32'h60000008,32'h44);
        
    41:REG_WR(32'h6000000c,32'h60000020);    
    //////////////////////////////////////////////////////////////////////////////////
    51:REG_WR(32'h60000010,32'h20000200);
        
    61:REG_WR(32'h60000014,32'h60000200);
        
    71:REG_WR(32'h60000018,32'h40);
    
    81:REG_WR(32'h6000001c,32'h60000020);
    //////////////////////////////////////////////////////////////////////////////////
    91:REG_WR(32'h60000020,32'h20000300);
    
    101:REG_WR(32'h60000024,32'h20000300);
        
    111:REG_WR(32'h60000028,32'h40);
    
    121:REG_WR(32'h6000002c,32'h2000030);
    //////////////////////////////////////////////////////////////////////////////////
    131:REG_WR(32'h60000030,32'h20000400);
    
    141:REG_WR(32'h60000034,32'h60000400);
    
    151:REG_WR(32'h60000038,32'h40);
    
    161:REG_WR(32'h6000003c,32'h60000040);
    //////////////////////////////////////////////////////////////////////////////////
    //          write the last lli          //
    171:REG_WR(32'h60000040,32'h20000500);
    
    181:REG_WR(32'h60000044,32'h60000500);
    
    191:REG_WR(32'h60000048,32'h20000040);
    
    201:REG_WR(32'h6000004c,32'h00);
    //////////////////////////////////////////////////////////////////////////////////
    //          start the dinidma           //
    500:REG_WR(32'h60000034,32'h60000000);
    
    505:REG_WR(32'h60000018,32'h0000000c);
    
    510:REG_WR(32'h60000000,32'h00000000);
    
    515:REG_WR(32'h60000004,32'h00000000);
    
    520:REG_WR(32'h60000008,32'h60000000);

    525:REG_WR(32'h6000000c,32'h00000000);
    /////////////////////////////////////////////////////////
    //          start the mac init          //
    
    `multiple*600:REG_WR(32'h60900068,32'h8000000c);
    
    `multiple*605:REG_WR(32'h60900068,32'h8000000c); 
    
    `multiple*610:REG_WR(32'h609000E0,32'h0x1ff02);
    
    `multiple*615:REG_WR(32'h60800114,32'hffff2a04);
    
    `multiple*620:REG_WR(32'h6080010c,32'hef22);
   
    `multiple*625:REG_WR(32'h60A00034,32'hc);
   
    `multiple*630:REG_WR(32'h60A00018,32'hffff);
   
    `multiple*635:REG_WR(32'h60B08050,32'h1);
   
    `multiple*640:REG_WR(32'h60B08074,32'h8333f10c);
    
    `multiple*645:REG_WR(32'h60B08080,32'h800A07C0);
    
    `multiple*650:REG_WR(32'h60B0004C,32'hcfc1);
    
    `multiple*655:REG_WR(32'h60B00054,32'h10000);
   
    `multiple*660:REG_WR(32'h60B00060,32'h7fffffde);
   
    `multiple*665:REG_WR(32'h60B00114,32'h401A);
    
    `multiple*670:REG_WR(32'h60B00064,32'hff900064);
    
    `multiple*675:REG_WR(32'h60B00150,32'h1000);
    
    `multiple*680:REG_WR(32'h60B0004C,32'h4fc1);
    
    `multiple*685:REG_WR(32'h60B00224,32'h0);
    
    `multiple*690:REG_WR(32'h60B000A0,32'h2020);
    
    `multiple*695:REG_WR(32'h60B0004C,32'h5fc1);
    
    `multiple*670:REG_WR(32'h60B0004C,32'h5fc1);
    
    `multiple*675:REG_WR(32'h60B0004C,32'h5fc1);
    
    `multiple*680:REG_WR(32'h60B0004C,32'h5fc1);
    
    `multiple*700:REG_WR(32'h60B0004C,32'h6fc1);
    
    `multiple*705:REG_WR(32'h60B00510,32'h1c25);
    
    `multiple*710:REG_WR(32'h60B081B8,32'h60000060);
    
    `multiple*715:REG_WR(32'h60B08180,32'h4000000);
    
    `multiple*720:REG_WR(32'h60B081BC,32'h60000884);
    
    `multiple*725:REG_WR(32'h60B08180,32'h8000000);
    
    `multiple*730:REG_WR(32'h60B0004c,32'h4fc1);
    
    `multiple*735:REG_WR(32'h60B0004c,32'h4fc1);
    
    `multiple*740:REG_WR(32'h60B0001c,32'h0);
    
    `multiple*745:REG_WR(32'h60B08074,32'h8333f10c);
    
    `multiple*750:REG_WR(32'h60B080A4,32'h0);
    
    `multiple*755:REG_WR(32'h60B080A8,32'h0);
    
    `multiple*760:REG_WR(32'h60B00010,32'h3344e022);
    
    `multiple*765:REG_WR(32'h60B00014,32'h55e0);
    
    `multiple*770:REG_WR(32'h60B0004C,32'h48c1);
    
    `multiple*775:REG_WR(32'h60B00060,32'h3503859c);
    
    `multiple*780:REG_WR(32'h60B000E8,32'h70809);
    
    `multiple*785:REG_WR(32'h60B00038,32'h30);
    
    `multiple*790:REG_WR(32'h60B000E8,32'h70809);
    
    `multiple*800:REG_WR(32'h60B00038,32'h30);
    
    //`multiple*805:REG_RD(32'h60B00038);
    
    //Construct header and payload
    //1.payload of MAC header= 28 bytes
    `multiple*810:REG_WR(32'h60008bb0,32'h00000148);
    //`multiple*810:REG_WR(32'h60008bb0,32'h000001C8);change to Qos NULL frame
    
    `multiple*820:REG_WR(32'h60008bb4,32'h56781234);
    
    `multiple*830:REG_WR(32'h60008bb8,32'h11221234);
    
     `multiple*840:REG_WR(32'h60008bbc,32'h55663344);
     
     `multiple*850:REG_WR(32'h60008bc0,32'h56781234);
     
     `multiple*860:REG_WR(32'h60008bc4,32'h00101234);
     
     `multiple*870:REG_WR(32'h60008bc8,32'h00000000);      
     //`multiple*870:REG_WR(32'h60008bc8,32'h00000007);change to Qos NULL frame
    
    //2.header descriptor
    
    `multiple*880:REG_WR(32'h60009fb4,32'hcafebabe);//upatterntx
    
    `multiple*890:REG_WR(32'h60009fb8,32'h00000000);
    
    `multiple*900:REG_WR(32'h60009fbc,32'h00000000);
    
    `multiple*910:REG_WR(32'h60009fc0,32'h00000000);
    
    `multiple*920:REG_WR(32'h60009fc4,32'h60008bb0);//datastartptr
    
    `multiple*930:REG_WR(32'h60009fc8,32'h60008bc7);//dataendptr
    //`multiple*930:REG_WR(32'h60009fc8,32'h60008bc9);//dataendptr change to Qos NULL frame
    
    `multiple*940:REG_WR(32'h60009fcc,32'h0000001c);//framelength 
    
   // `multiple*940:REG_WR(32'h60009fcc,32'h0000001e);//framelength,change to Qos NULL frame
    
    `multiple*950:REG_WR(32'h60009fd0,32'h00000000);//framelife time
    
    `multiple*960:REG_WR(32'h60009fd4,32'h00000000);
    
    `multiple*970:REG_WR(32'h60009fd8,32'h6000a100);//policytable addr
    
    `multiple*980:REG_WR(32'h60009fdc,32'h00000000);
    
    `multiple*990:REG_WR(32'h60009fe0,32'h00000000);
    
    `multiple*1000:REG_WR(32'h60009fe4,32'h00000000);
    
    `multiple*1010:REG_WR(32'h60009fe8,32'h00000200);//macctrlinfo1
    
    `multiple*1020:REG_WR(32'h60009fec,32'h00000000);//macctrlinfo2
    
    `multiple*1030:REG_WR(32'h60009ff0,32'h00000000);
    
    `multiple*1040:REG_WR(32'h60009ff4,32'h00000000);
    /////////////////////////////////////////////////////////////////
    //3.policy table
     `multiple*1050:REG_WR(32'h6000a100,32'hBADCAB1E);
     
     `multiple*1060:REG_WR(32'h6000a104,32'h00000000);
     
     `multiple*1070:REG_WR(32'h6000a108,32'h00000001);
     
     `multiple*1080:REG_WR(32'h6000a10c,32'h00000000);
     
     `multiple*1090:REG_WR(32'h6000a110,32'hFFFF0704);
     
     `multiple*1100:REG_WR(32'h6000a114,32'h00000405);/////////rate
     
     `multiple*1110:REG_WR(32'h6000a118,32'h00000000);
     
     `multiple*1120:REG_WR(32'h6000a11c,32'h00000000);
     
     `multiple*1130:REG_WR(32'h6000a120,32'h00000000);
     
     `multiple*1140:REG_WR(32'h6000a124,32'h00000023);
     
     `multiple*1150:REG_WR(32'h6000a128,32'h00000000);
     
     `multiple*1160:REG_WR(32'h6000a12c,32'h00000000);
     
     `multiple*1170:REG_WR(32'h6000a130,32'h00000000);
     
     
    /////////////////////////////////////////////////////////////////
    
    `multiple*1180:REG_WR(32'h60B081A8,32'h60009fb4);//set TX AC3 head ptr
    
    `multiple*1190:REG_WR(32'h60B08180,32'h00001000);
    
        ////////////////////// phy ////////////////////////////////////////
    
    530:REG_WR(32'h60C00000,32'h011EAD8F);
    535:REG_WR(32'h60C00004,32'h00000100);
    540:REG_WR(32'h60C00018,32'h6a6a6a6a);
    545:REG_WR(32'h60C0001C,32'h6a6a6a6a);
    550:REG_WR(32'h60C00020,32'h00040000);
    555:REG_WR(32'h60C00034,32'h00000020);
    560:REG_WR(32'h60C00024,32'h00000000);
    565:REG_WR(32'h60C00028,32'h00000000);
    570:REG_WR(32'h60C02004,32'h00000001);
    575:REG_WR(32'h60C02008,32'h0c0c1900);
    580:REG_WR(32'h60C0200c,32'h00020d0b);
    585:REG_WR(32'h60C09008,32'h00000000);
    590:REG_WR(32'h60C09010,32'h10080212);
    
    595:REG_WR(32'h60C0000C,32'h00017000);
    600:REG_WR(32'h60C00008,32'h59141165);
    605:REG_WR(32'h60C0002c,32'h01192a30);
    610:REG_WR(32'h60C0a020,32'h400131f3);
    615:REG_WR(32'h60C08000,32'h00000002);
    620:REG_WR(32'h60C08004,32'h00000001);
    625:REG_WR(32'h60C08008,32'h00000019);
    630:REG_WR(32'h60C0800C,32'h00000123);
    635:REG_WR(32'h60C08010,32'h00000025);    
    640:REG_WR(32'h60C08014,32'h01020304);
    645:REG_WR(32'h60C08018,32'h00000063);
    650:REG_WR(32'h60C0801C,32'h12345678);
    
    655:REG_RD(32'h60C00000,32'h00000123);
    660:REG_RD(32'h60C00004,32'h00000123);
    665:REG_RD(32'h60C00008,32'h00000123);
    
    670:REG_RD(32'h60C02004,32'h00000001);
    675:REG_RD(32'h60C02008,32'h0c0c1900);
    680:REG_RD(32'h60C0200c,32'h00020d0b);
    
    685:REG_RD(32'h60C09008,32'h00000000);
    690:REG_RD(32'h60C09010,32'h10080212); 
    
    695:REG_WR(32'h60C08014,32'h01020304);
    700:REG_WR(32'h60C08018,32'h00000063);
    705:REG_WR(32'h60C0801C,32'h12345678);  
    
    //////////////////////////////////////////////////////////////////////////////////
    //set phyRdy signal to 1
    `multiple*2500:REG_WR(32'h60B00538,32'h1);    
   
    //////////////////////////////////////////////////////////////////////////////////
    default:begin
        proc_htrans = 2'b00;
        end 
                                            
  endcase;
     if(s1_axis_fromhost_tready)
        begin
        s1_axis_fromhost_tvalid = 1'b1;
        s1_axis_fromhost_tkeep  = 8'b11111111;
        s1_axis_fromhost_tdata  = 64'heb900000;
        down_data_counter       = down_data_counter + 1;
            if(down_data_counter == 32'h6)
            begin
                down_data_counter = 0;
                s1_axis_fromhost_tlast = 1'b1;
            end  
            else
                s1_axis_fromhost_tlast = 1'b0;  
        end   
  end
end

//start the dinidma
//initial begin

    
//  #20000
//  proc_haddr    = 32'h60a00034;
//  proc_hwdata   = 32'h0000000c;
//  proc_htrans   = 2'b10;  
//  #400
//  proc_htrans  = 2'b00;
//  #400
//  proc_haddr    = 32'h60a00018;
//  proc_hwdata   = 32'h0000FFFF;
//  proc_htrans   = 2'b10;
//  #400
//  proc_htrans   = 2'b00;
//  #400
//  proc_haddr    = 32'h60a00000;
//  proc_hwdata   = 32'h60000000;
//  proc_htrans   = 2'b10;
//  #400
//  proc_htrans   = 2'b00;
//    #400
//  proc_haddr    = 32'h60a00004;
//  proc_hwdata   = 32'h60000000;
//  proc_htrans   = 2'b10;
//  #400
//  proc_htrans   = 2'b00;
//    #400
//  proc_haddr    = 32'h60a00008;
//  proc_hwdata   = 32'h60000000;
//  proc_htrans   = 2'b10;
//  #400
//  proc_htrans   = 2'b00;
//    #400
//  proc_haddr    = 32'h60a0000c;
//  proc_hwdata   = 32'h60000000;
//  proc_htrans   = 2'b10;
//  #400
//  proc_htrans   = 2'b00;
//end



endmodule
