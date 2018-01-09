`timescale 1ns/10ps
`define multiple 2

module rw_nx_platform_sim(

);

wire clk_32k;
wire clk_30m;
wire clk_80m;
wire clk_200m;
wire AD9361_clk;

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

parameter PERIOD_15m = 66.66;
parameter PERIOD_30m = 33.33;
parameter PERIOD_80m = 12.5;
parameter PERIOD_200m = 5;


clk_wiz_0 u_clk_wiz_0(
    .clk_in1          (clk_80m_in),
    
    .clk_out1         (clk_30m),        //set 30m
    .clk_out2         (clk_80m),        //set 80m       
    .clk_out3         (AD9361_clk),        //set 80m 
    .resetn           (rst_n)
);

rw_nx_platform u_rw_nx_platform(
    .clk_32k                  (0),
    .clk_30m                  (clk_30m),
    .clk_80m                  (clk_80m),
    .clk_200m                 (clk_80m),
    .AD9361_clk               (AD9361_clk ),
    
 //   .pci_clk33m               (clk_30m                ),
 //   .pll_clk240m              (clk_240m               ),
 //   .clk_20p32                (clk_20p32m             ),
    
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
        
        `multiple*655:REG_WR(32'h60B00054,32'h000000);//WL:disable rxFlowCntrlEn bit
       
        `multiple*660:REG_WR(32'h60B00060,32'h7ffffffe);//receive contrl register
       
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
        
        //`multiple*775:REG_WR(32'h60B00060,32'h3503859c);
         `multiple*775:REG_WR(32'h60B00060,32'h7ffffffe);
        
        `multiple*780:REG_WR(32'h60B000E8,32'h70809);
        
        `multiple*785:REG_WR(32'h60B00038,32'h30);
        
        `multiple*790:REG_WR(32'h60B000E8,32'h70809);
        
        `multiple*800:REG_WR(32'h60B00038,32'h30);
        
        //`multiple*805:REG_RD(32'h60B00038);
        
        //Construct header and payload
        //1.payload of MAC header= 28 bytes
        `multiple*810:REG_WR(32'h60008bb0,32'h00000148);
        //`multiple*810:REG_WR(32'h60008bb0,32'h000001C8);change to Qos NULL frame
        
        `multiple*820:REG_WR(32'h60008bb4,32'hFFFFFFFF);
        
        `multiple*830:REG_WR(32'h60008bb8,32'h1122FFFF);
        
         `multiple*840:REG_WR(32'h60008bbc,32'h55663344);
         
         `multiple*850:REG_WR(32'h60008bc0,32'h56781234);
         
         `multiple*860:REG_WR(32'h60008bc4,32'h00101234);
         
           
         //`multiple*870:REG_WR(32'h60008bc8,32'h00000007);change to Qos NULL frame
        
        //2.tx header descriptor
        
        `multiple*880:REG_WR(32'h60009fb4,32'hcafebabe);//upatterntx
        
        `multiple*890:REG_WR(32'h60009fb8,32'h00000000);
        
        `multiple*900:REG_WR(32'h60009fbc,32'h00000000);
        
        `multiple*910:REG_WR(32'h60009fc0,32'h6000b000);//first payload buffer descriptor pointer
        
        `multiple*920:REG_WR(32'h60009fc4,32'h60008bb0);//datastartptr
        
        `multiple*930:REG_WR(32'h60009fc8,32'h60008bc7);//dataendptr
        //`multiple*930:REG_WR(32'h60009fc8,32'h60008bc9);//dataendptr change to Qos NULL frame
        
        `multiple*940:REG_WR(32'h60009fcc,32'h0000002c);//framelength 
        
       // `multiple*940:REG_WR(32'h60009fcc,32'h0000001e);//framelength,change to Qos NULL frame
        
        `multiple*950:REG_WR(32'h60009fd0,32'h00000000);//framelife time
        
        `multiple*960:REG_WR(32'h60009fd4,32'h00000000);
        
        `multiple*970:REG_WR(32'h60009fd8,32'h6000a100);//policytable addr
        
        `multiple*980:REG_WR(32'h60009fdc,32'h00000000);
        
        `multiple*990:REG_WR(32'h60009fe0,32'h00000000);
        
        `multiple*1000:REG_WR(32'h60009fe4,32'h00000000);
        
        `multiple*1010:REG_WR(32'h60009fe8,32'h00000000);//macctrlinfo1
        
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
         
         //////////////////////////////////////////////////////////////////////
         //tx payload descriptor
         `multiple*1180:REG_WR(32'h6000b000,32'hCAFEFADE); //upatternrx
         `multiple*1190:REG_WR(32'h6000b004,32'h00000000);
         `multiple*1200:REG_WR(32'h6000b008,32'h60008bc8);
         `multiple*1210:REG_WR(32'h6000b00C,32'h60008dc8);
         `multiple*1220:REG_WR(32'h6000b010,32'h00000000);
         ////////////////////////////////////////////////////////////////
         //set payload
         `multiple*1230:REG_WR(32'h60008bc8,32'hF0E0D0C0);
         `multiple*1240:REG_WR(32'h60008bcc,32'hB0A09080);
         `multiple*1250:REG_WR(32'h60008bd0,32'h70605040);
         `multiple*1260:REG_WR(32'h60008bd4,32'h30201099);
    
        /////////////////////////////////////////////////////////////////
        
        `multiple*1270:REG_WR(32'h60B081A8,32'h60009fb4);//set TX AC3 head ptr
        
        `multiple*1280:REG_WR(32'h60B08180,32'h00001000);
        
              
         //2.rx header descriptor
         //sram中60000060为头部描述符
         `multiple*1510:REG_WR(32'h60000060,32'hBAADF00D);//upatternrx
         `multiple*1520:REG_WR(32'h60000064,32'h00000000);//next header descriptor pointer
         //payload地址
         `multiple*1530:REG_WR(32'h60000068,32'h60000884);//first payload buffer descriptor pointer
         `multiple*1540:REG_WR(32'h6000006C,32'h60022246);//sw descriptor pointer
         `multiple*1550:REG_WR(32'h60000070,32'h60012264);//data start pointer
         `multiple*1560:REG_WR(32'h60000074,32'h6001227C);//data end pointer
         `multiple*1570:REG_WR(32'h60000078,32'h00000001);//header control information: enbaleRXInt
         `multiple*1580:REG_WR(32'h6000007C,32'h0000002c);//lengtgh
         `multiple*1590:REG_WR(32'h60000080,32'h00000000);//TSFLow
         `multiple*1600:REG_WR(32'h60000084,32'h00000000);//TSFHi
         `multiple*1610:REG_WR(32'h60000088,32'h00000000);
         `multiple*1620:REG_WR(32'h6000008C,32'h00000000);
         `multiple*1630:REG_WR(32'h60000090,32'h00000000);
         `multiple*1640:REG_WR(32'h60000094,32'h00000000);
         `multiple*1650:REG_WR(32'h60000098,32'h00000000);
         `multiple*1660:REG_WR(32'h6000009C,32'h00000000);
         `multiple*1670:REG_WR(32'h60000100,32'h00000000);
             
          // set rx header head pointer register
          // 向mac寄存器写入头部信息
         `multiple*1680:REG_WR(32'h60B081B8,32'h60000060);
         `multiple*1690:REG_WR(32'h60B08180,32'h04000000);//set RX header new Head 
         //////////////////////////////////////////////////////////////////////////////
         //rx payload descriptor
         `multiple*1700:REG_WR(32'h60000884,32'hC0DEDBAD);//upatternrx
         `multiple*1710:REG_WR(32'h60000888,32'h00000000);
         `multiple*1720:REG_WR(32'h6000088C,32'h60012280);
         `multiple*1730:REG_WR(32'h60000890,32'h60012480);
         `multiple*1740:REG_WR(32'h60000894,32'h00000000);
         
         
       
           //////////////////////////////////////////////////////////////////////////////////
       
           `multiple*1750:REG_WR(32'h60B081BC,32'h60000884);
           
          `multiple*1760:REG_WR(32'h60B08180,32'h08000000);//new payload new head bit
          
           `multiple*1770:REG_WR(32'h60B00138,32'h00000100);
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
        
        655:REG_WR(32'h60C08F04,32'h00000001); //change model
        // -- just for test
        660:REG_WR(32'h60C10000,32'h00004411);
        665:REG_WR(32'h60C10004,32'h00008822);
        
        670:REG_WR(32'h60C10008,32'h0000CC33);
        675:REG_WR(32'h60C1000C,32'h00011044);
        680:REG_WR(32'h60C10010,32'h00015455);
        
        685:REG_WR(32'h60C10014,32'h00019866);
        690:REG_WR(32'h60C10018,32'h0001DC77); 
        
        695:REG_WR(32'h60C1001C,32'h00022088);
        700:REG_WR(32'h60C10020,32'h00026499);
        705:REG_RD(32'h60C10024,32'h12345603); 
        
       
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

//-------------------- random data ---------------------




endmodule

