//**********************************************************
//
// Copyright(c) 2017 . Outwitcom Technology Co., LTD.
// All rights reserved.
//
// ProjectName :
// target      :
// FileName    : 
// Author      :fengmaoqiao 
// E_mail      :fengmaoqiao@outwitcom.com 
// Date        :
// Version     :
//
// Modification history
//--------------------------------------------------------
// $Log:$
//
//**********************************************************
`timescale 1ns/10ps
`define multiple 10

module rw_nx_platform_sim(

);
//clock and reset
wire clk_32k;
wire clk_30m;
wire clk_80m;
wire clk_200m;
wire AD9361_clk;

reg clk_80m_in;
reg rst_n;
//user port
wire          proc_hready;
reg   [31:0]  proc_haddr;
reg   [1:0]   proc_htrans;
reg           proc_hwrite;
reg   [1:0]   proc_hsize;
wire  [31:0]  proc_hrdata;
reg   [31:0]  proc_hwdata;
wire  [1:0]   proc_hresp;

wire          m0_axis_tohost_tvalid;
wire          m0_axis_tohost_tready;
wire [63:0]   m0_axis_tohost_tdata;
wire [7:0]    m0_axis_tohost_tkeep;
wire          m0_axis_tohost_tlast;

wire          s1_axis_fromhost_tvalid;
wire          s1_axis_fromhost_tready;
wire [63:0]   s1_axis_fromhost_tdata;
wire [7:0]    s1_axis_fromhost_tkeep;
wire          s1_axis_fromhost_tlast;
//input simulate data interface
reg [31:0]    simu_axis_tdata;
reg [3:0]     simu_axis_tkeep;
reg           simu_axis_tlast;
reg           simu_axis_tvalid;
wire          simu_axis_tready;

parameter PERIOD_15m = 66.66;
parameter PERIOD_30m = 33.33;
parameter PERIOD_80m = 12.5;
parameter PERIOD_200m = 5;

wire [63:0] axis_fifo_tdata;
wire        axis_fifo_tvalid;
wire [7:0]  axis_fifo_tkeep;
wire        axis_fifo_tready;
wire        axis_fifo_tlast;


//**********************************************************
// DCM declare
//**********************************************************

clk_wiz_0 u_clk_wiz_0(
    .clk_in1          (clk_80m_in),
    
    .clk_out1         (clk_30m),        //set 30m
    .clk_out2         (clk_80m),        //set 80m       
    .clk_out3         (AD9361_clk),        //set 80m 
    .resetn           (rst_n)
);


//**********************************************************
// down channel begin
//**********************************************************
dma_if_32to64_0 u_dma_if_32to64(


    .clk                        (clk_80m)               ,
    .rst_n                      (rst_n)                 ,
    
    .s1_axis_fromhost_tdata     (simu_axis_tdata)   ,
    .s1_axis_fromhost_tkeep     (simu_axis_tkeep)   ,
    .s1_axis_fromhost_tvalid    (simu_axis_tvalid)  ,
    .s1_axis_fromhost_tready    (simu_axis_tready)  ,
    .s1_axis_fromhost_tlast     (simu_axis_tlast)   ,
    
    .m1_axis_fromhost_tvalid      (axis_fifo_tvalid),
    .m1_axis_fromhost_tready      (axis_fifo_tready),
    .m1_axis_fromhost_tkeep       (axis_fifo_tkeep),
    .m1_axis_fromhost_tdata       (axis_fifo_tdata),
    .m1_axis_fromhost_tlast       (axis_fifo_tlast)
);


axis_data_fifo_0 u_axis_data_fifo_0(

    .s_axis_aclk        (clk_80m)                   ,
    .s_axis_aresetn     (rst_n)                     ,
    
    .s_axis_tdata       (axis_fifo_tdata),
    .s_axis_tkeep       (axis_fifo_tkeep),
    .s_axis_tlast       (axis_fifo_tlast),
    .s_axis_tvalid      (axis_fifo_tvalid),
    .s_axis_tready      (axis_fifo_tready),
    
    //      down stream fifo port to dinidma        // 
    .m_axis_tdata       (s1_axis_fromhost_tdata)    ,
    .m_axis_tkeep       (s1_axis_fromhost_tkeep)   ,
    .m_axis_tlast       (s1_axis_fromhost_tlast)    ,
    .m_axis_tvalid      (s1_axis_fromhost_tvalid)   ,
    .m_axis_tready      (s1_axis_fromhost_tready)   
    //      datain port to this fifo                //

);
//**********************************************************
// up channel wire connect
//**********************************************************
wire [63:0] axis_upfifO_tdata;
wire        axis_upfifo_tvalid;
wire [7:0]  axis_upfifo_tkeep;
wire        axis_upfifo_tready;
wire        axis_upfifo_tlast;

wire [31:0] view_upfifO_tdata;
wire        view_upfifo_tvalid;
wire [3:0]  view_upfifo_tkeep;
reg         view_upfifo_tready;
wire        view_upfifo_tlast;

//**********************************************************
// upstream 64b axi_stream data fifo,
// receive the data from main instance
//**********************************************************
axis_data_fifo_0 u_axis_data_fifo_up_0(

    .s_axis_aclk        (clk_80m)           ,
    .s_axis_aresetn     (rst_n)             ,
    
    .m_axis_tdata       (axis_upfifO_tdata),
    .m_axis_tkeep       (axis_upfifo_tkeep),
    .m_axis_tlast       (axis_upfifo_tlast),
    .m_axis_tvalid      (axis_upfifo_tvalid),
    .m_axis_tready      (axis_upfifo_tready),
    
    // this port wait for the data come from dinidma
    .s_axis_tdata       (m0_axis_tohost_tdata),
    .s_axis_tkeep       (m0_axis_tohost_tkeep),
    .s_axis_tlast       (m0_axis_tohost_tlast),
    .s_axis_tvalid      (m0_axis_tohost_tvalid),
    .s_axis_tready      (m0_axis_tohost_tready)
    
);


//**********************************************************
// upstream  64 convert the 64b fifo data to 32b data instance
//**********************************************************
dma_if_64to32_0 u_dma_if_64to32(

    .clk                        (clk_80m)               ,
    .rst_n                      (rst_n)                 ,
    //net from up fifo
    .s0_axis_tohost_tdata     (axis_upfifO_tdata)       ,
    .s0_axis_tohost_tkeep     (axis_upfifo_tkeep)       ,
    .s0_axis_tohost_tvalid    (axis_upfifo_tvalid)      ,
    .s0_axis_tohost_tready    (axis_upfifo_tready)      ,
    .s0_axis_tohost_tlast     (axis_upfifo_tlast)       ,
    //net to simu
    .m0_axis_tohost_tvalid      (view_upfifo_tvalid)    ,
    .m0_axis_tohost_tready      (view_upfifo_tready)    ,
    .m0_axis_tohost_tkeep       (view_upfifo_tkeep)     ,
    .m0_axis_tohost_tdata       (view_upfifo_tdata)     ,
    .m0_axis_tohost_tlast       (view_upfifo_tlast)
);
//**********************************************************
//generate main instance and connect signal
//**********************************************************
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
        
    //      up stream fifo channel              //
    .m0_axis_tohost_tvalid    (m0_axis_tohost_tvalid),
    .m0_axis_tohost_tready    (m0_axis_tohost_tready),
    .m0_axis_tohost_tkeep     (m0_axis_tohost_tkeep),
    .m0_axis_tohost_tdata     (m0_axis_tohost_tdata),
    .m0_axis_tohost_tlast     (m0_axis_tohost_tlast),
    
    //      down stream fifo channel            //
    .s1_axis_fromhost_tvalid  (s1_axis_fromhost_tvalid),
    .s1_axis_fromhost_tready  (s1_axis_fromhost_tready),
    .s1_axis_fromhost_tdata   (s1_axis_fromhost_tdata),
    .s1_axis_fromhost_tkeep   (s1_axis_fromhost_tkeep),
    .s1_axis_fromhost_tlast   (s1_axis_fromhost_tlast)
  
  
);


//**********************************************************
//simulate time generate,this send to DCM
//**********************************************************
always begin
  clk_80m_in = 1'b0;
  #(PERIOD_80m/2) clk_80m_in = 1'b1;
  #(PERIOD_80m/2);
end


reg [31:0] counter;
reg [31:0] down_data_counter;

//**********************************************************
//generate reset signal
//**********************************************************
initial begin
rst_n = 1'b0;
#200
rst_n = 1'b1;
end

//**********************************************************
//register write and read task
//**********************************************************
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
//**********************************************************
//main process to simulate
//**********************************************************
always@(posedge clk_80m or negedge rst_n)
begin

  if(!rst_n)
  begin
    //proc_hwrite = 1'b1;
    proc_htrans = 2'b00;
    counter     = 16'd0;

    down_data_counter       = 32'b0;
    down_data_counter       = 32'b0;
    simu_axis_tdata         = 64'b0;
    simu_axis_tlast         = 1'b0;
    simu_axis_tvalid        = 1'b0;
    simu_axis_tkeep         = 8'b0;
    
    view_upfifo_tready      = 1'b1;
    
    end
    else begin
    proc_hsize = 2'b10;
    if(counter  != 16'd65530)
    counter     = counter + 1;
    

        //**********************************************************
        // write simulate date to down fifo and start dinidma to tran data from
        // data to sram
        //**********************************************************
        //add node one
        if(counter == 7)
        begin
            simu_axis_tvalid = 1'b1;
            simu_axis_tdata  =  counter;
            simu_axis_tkeep  =  4'hf;
            simu_axis_tlast  =  1'b0;
        end
        else if(counter == 8)
        begin
            simu_axis_tvalid  = 1'b1;
            simu_axis_tdata   = counter;
            simu_axis_tkeep   = 4'hf;
            simu_axis_tlast   = 1'b1;
        end
        //node two
        else if(counter==9)
        begin
            simu_axis_tvalid  = 1'b1;
            simu_axis_tdata   = counter;
            simu_axis_tkeep   = 4'hf;
            simu_axis_tlast   = 1'b0;
        end
        else if(counter==10)
        begin
            simu_axis_tvalid  = 1'b1;
            simu_axis_tdata   = counter;
            simu_axis_tkeep   = 4'hf;
            simu_axis_tlast   = 1'b1;
        end
        //node three
        else if(counter >= 12 && counter <=14)  //4x8=40 bytes
        begin
            simu_axis_tvalid  = 1'b1;
            simu_axis_tdata   = counter;
            simu_axis_tkeep   = 4'hf;
            simu_axis_tlast   = 1'b0;            
        end
        else if(counter == 15)  //0x06
        begin
             simu_axis_tvalid  = 1'b1;
             simu_axis_tdata   = counter;
             simu_axis_tkeep   = 4'hf;
             simu_axis_tlast   = 1'b1;            
        end
        //node four
        else if(counter >= 16 && counter <=18)  //4x8=40 bytes
        begin
            simu_axis_tvalid  = 1'b1;
            simu_axis_tdata   = counter;
            simu_axis_tkeep   = 4'hf;
            simu_axis_tlast   = 1'b0;            
        end
        else if(counter == 19)  //0x06
        begin
             simu_axis_tvalid  = 1'b1;
             simu_axis_tdata   = counter;
             simu_axis_tkeep   = 4'hf;
             simu_axis_tlast   = 1'b1;            
        end
        //node five
        else if(counter >= 20 && counter <=25)  //4x8=40 bytes
        begin
            simu_axis_tvalid  = 1'b1;
            simu_axis_tdata   = counter;
            simu_axis_tkeep   = 4'hf;
            simu_axis_tlast   = 1'b0;            
        end
        else if(counter == 26)  //0x06
        begin
             simu_axis_tvalid  = 1'b1;
             simu_axis_tdata   = counter;
             simu_axis_tkeep   = 4'hf;
             simu_axis_tlast   = 1'b1;            
        end
        
//        else if(counter == 18 ) //0x08
//        begin
//            downfifo_axis_tvalid  = 1'b1;
//            downfifo_axis_tdata   = 64'h0B;
//            downfifo_axis_tkeep   = 8'b11111111;
//            downfifo_axis_tlast   = 1'b1;
//        end
//        else if(counter == 19 ) //0x08
//        begin
//             downfifo_axis_tvalid  = 1'b1;
//             downfifo_axis_tdata   = 64'h0C;
//             downfifo_axis_tkeep   = 8'b00001111;
//             downfifo_axis_tlast   = 1'b1;
//        end
        /*
        else if(counter == 16)
        begin
            downfifo_axis_tvalid  = 1'b1;
            downfifo_axis_tdata   = counter;
            downfifo_axis_tkeep   = 8'b00001111;
            downfifo_axis_tlast   = 1'b1;    
        end
        else if(counter >=20 && counter <= 26)
        begin
            downfifo_axis_tvalid  = 1'b1;
            downfifo_axis_tdata   = counter;
            downfifo_axis_tkeep   = 8'b11111111;
            downfifo_axis_tlast   = 1'b0;        
        end
        else if(counter == 27)
        begin
            downfifo_axis_tvalid  = 1'b1;
            downfifo_axis_tdata   = counter;
            downfifo_axis_tkeep   = 8'b11111111;
            downfifo_axis_tlast   = 1'b1;
        end
        /*
        else if(counter == 24)
        begin
             downfifo_axis_tvalid  = 1'b1;
             downfifo_axis_tdata   = counter;
             downfifo_axis_tkeep   = 8'b11111111;
             downfifo_axis_tlast   = 1'b0;
        end
        else if(counter == 25)
        begin
              downfifo_axis_tvalid  = 1'b1;
              downfifo_axis_tdata   = counter;
              downfifo_axis_tkeep   = 8'b00001111;
              downfifo_axis_tlast   = 1'b1;
        end
        */
        else
        begin
            simu_axis_tvalid  = 1'b0;
            simu_axis_tlast   = 1'b0;
            simu_axis_tkeep   = 8'b0;
        end
    case(counter)
        //write five lli node to sram
        //one node                
        //**********************************************************
        //  添加LLI链表节点到SRAM中
        //**********************************************************
        11:REG_WR(32'h60000000,32'h20000100);            
        21:REG_WR(32'h60000004,32'h60000100);    
        31:REG_WR(32'h60000008,32'h08);        
        41:REG_WR(32'h6000000c,32'h60000020);
        //two node                
        51:REG_WR(32'h60000020,32'h20000200);        
        61:REG_WR(32'h60000024,32'h60000200);        
        71:REG_WR(32'h60000028,32'h08);    
        81:REG_WR(32'h6000002c,32'h60000040);
        //three node                
        91:REG_WR(32'h60000040,32'h20000300);    
        101:REG_WR(32'h60000044,32'h60000300);        
        111:REG_WR(32'h60000048,32'h10);    
        121:REG_WR(32'h6000004c,32'h20000060);
        //four node       
        131:REG_WR(32'h60000060,32'h20000400);    
        141:REG_WR(32'h60000064,32'h60000400);    
        151:REG_WR(32'h60000068,32'h10);    
        161:REG_WR(32'h6000006c,32'h60000080);
        //five node
        //the last node
        171:REG_WR(32'h60000080,32'h20000500);    
        181:REG_WR(32'h60000084,32'h60000500);    
        191:REG_WR(32'h60000088,32'h18);    
        201:REG_WR(32'h6000008c,32'h0); 
        ///////////////////////////////////////////////////////////////////////////////////
        //          start the dinidma           //
        //configure lli
        300:REG_WR(32'h60A00034,32'h60000000);         
        305:REG_WR(32'h60A00018,32'h0000000c);    
        //write lli_root_reg3
        310:REG_WR(32'h60A00000,32'h00000000);    
        315:REG_WR(32'h60A00004,32'h00000000);    
        320:REG_WR(32'h60A00008,32'h60000000);          
        325:REG_WR(32'h60A0000c,32'h00000000);
        /////////////////////////////////////////////////////////////////////////////////
        //          update the lli list         //
        400:REG_WR(32'h60000000,32'h60000100);            
        410:REG_WR(32'h60000004,32'h20000100);
        
        420:REG_WR(32'h60000020,32'h60000200);        
        430:REG_WR(32'h60000024,32'h20000200);
        
        440:REG_WR(32'h60000040,32'h60000300);    
        450:REG_WR(32'h60000044,32'h20000300); 
        
        460:REG_WR(32'h60000060,32'h60000400);    
        470:REG_WR(32'h60000064,32'h20000400);
            
        480:REG_WR(32'h60000080,32'h60000500);    
        490:REG_WR(32'h60000084,32'h20000500);  
        //**********************************************************
        //  当DiniDMA发送完成以及接收LLI配置后启动上行DiniDMA
        //**********************************************************
        500:REG_WR(32'h60A00008,32'h00000000);
        510:REG_WR(32'h60A00000,32'h60000000);     
        //**********************************************************
        //  MAC寄存器初始化
        //**********************************************************
        `multiple*600:REG_WR(32'h60900068,32'h8000000c);
        
        `multiple*605:REG_WR(32'h60900068,32'h8000000c); 
        
        `multiple*610:REG_WR(32'h609000E0,32'h0x1ff02);
        
        `multiple*615:REG_WR(32'h60800114,32'hffff2a04);
        
        `multiple*620:REG_WR(32'h6080010c,32'hef22);
       
        `multiple*625:REG_WR(32'h60A00034,32'hc);             //DiniDMA set
       
        `multiple*630:REG_WR(32'h60A00018,32'hffff);          //DiniDMA set
       
        `multiple*635:REG_WR(32'h60B08050,32'h1);             //MAC控制器寄存器
       
        `multiple*640:REG_WR(32'h60B08074,32'h8333f10c);     //通用中断设置
        
        `multiple*645:REG_WR(32'h60B08080,32'h800A07C0);     //收发中断设置
        
        `multiple*650:REG_WR(32'h60B0004C,32'hcfc1);         //MAC控制器寄存器1
        
        `multiple*655:REG_WR(32'h60B00054,32'h000000);//WL:disable rxFlowCntrlEn bit        MAC错误恢复寄存器
       
        `multiple*660:REG_WR(32'h60B00060,32'h7ffffffe);//receive contrl register           接收控制寄存器
       
        `multiple*665:REG_WR(32'h60B00114,32'h401A);         //接收触发时间寄存器
        
        `multiple*670:REG_WR(32'h60B00064,32'hff900064);     //Beacon控制寄存器
        
        `multiple*675:REG_WR(32'h60B00150,32'h1000);         //最大接收长度寄存器
        
        `multiple*680:REG_WR(32'h60B0004C,32'h4fc1);         //MAC控制寄存器
        
        `multiple*685:REG_WR(32'h60B00224,32'h0);            //EDCA控制寄存器
        
        `multiple*690:REG_WR(32'h60B000A0,32'h2020);         //最大功率级别寄存器
        
        `multiple*695:REG_WR(32'h60B0004C,32'h5fc1);         //MAC控制器寄存器1
        
        `multiple*670:REG_WR(32'h60B0004C,32'h5fc1);         //MAC控制器寄存器1
        
        `multiple*675:REG_WR(32'h60B0004C,32'h5fc1);         //MAC控制器寄存器1
        
        `multiple*680:REG_WR(32'h60B0004C,32'h5fc1);         //MAC控制器寄存器1
        
        `multiple*700:REG_WR(32'h60B0004C,32'h6fc1);         //MAC控制器寄存器1
        
        `multiple*705:REG_WR(32'h60B00510,32'h1c25);         //调试接口选择
        
        `multiple*710:REG_WR(32'h60B081B8,32'h60000060);     //接收头部指针
        
        `multiple*715:REG_WR(32'h60B08180,32'h4000000);      //DMA Engine设置
        
        `multiple*720:REG_WR(32'h60B081BC,32'h60000884);     //接收Payload指针
        
        `multiple*725:REG_WR(32'h60B08180,32'h8000000);      //DMA Engine设置
        
        `multiple*730:REG_WR(32'h60B0004c,32'h4fc1);         //MAC控制器寄存器1
        
        `multiple*735:REG_WR(32'h60B0004c,32'h4fc1);         //MAC控制器寄存器1
        
        `multiple*740:REG_WR(32'h60B0001c,32'h0);            //MAC地址高位
        
        `multiple*745:REG_WR(32'h60B08074,32'h8333f10c);     //通用中断掩码
        
        `multiple*750:REG_WR(32'h60B080A4,32'h0);            //TSF Timer Low
        
        `multiple*755:REG_WR(32'h60B080A8,32'h0);            //TSF Timer High
        
        `multiple*760:REG_WR(32'h60B00010,32'h3344e022);     //MAC地址低位
        
        `multiple*765:REG_WR(32'h60B00014,32'h55e0);         //MAC地址高位
        
        `multiple*770:REG_WR(32'h60B0004C,32'h48c1);         //MAC控制器寄存器1
        
        //`multiple*775:REG_WR(32'h60B00060,32'h3503859c);
         `multiple*775:REG_WR(32'h60B00060,32'h7ffffffe);    //接收控制
        
        `multiple*780:REG_WR(32'h60B000E8,32'h70809);        //Timings 2
        
        `multiple*785:REG_WR(32'h60B00038,32'h30);           //MAC core状态寄存器
        
        `multiple*790:REG_WR(32'h60B000E8,32'h70809);        //Timing 2
        
        `multiple*800:REG_WR(32'h60B00038,32'h30);           //MAC core状态寄存器
        
        //`multiple*805:REG_RD(32'h60B00038);
        
        //**********************************************************
        //  为MAC TX构造发送数据包
        //**********************************************************
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
         `multiple*1510:REG_WR(32'h60000060,32'hBAADF00D);//upatternrx
         `multiple*1520:REG_WR(32'h60000064,32'h00000000);//next header descriptor pointer
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
        
        //**********************************************************
        //  初始化物理层
        //**********************************************************
        530:REG_WR(32'h60C00000,32'h011EAD8F);        //MDMaTXCNTL
        535:REG_WR(32'h60C00004,32'h00000100);        //MDMaTXIQCOMP
        540:REG_WR(32'h60C00018,32'h6a6a6a6a);        //MDMaRXCNTL0
        545:REG_WR(32'h60C0001C,32'h6a6a6a6a);        //MDMaRXCNTL1
        550:REG_WR(32'h60C00020,32'h00040000);        //MDMaEQCNTL2
        555:REG_WR(32'h60C00034,32'h00000020);        //MDMaTXCONST
        560:REG_WR(32'h60C00024,32'h00000000);
        565:REG_WR(32'h60C00028,32'h00000000);
        570:REG_WR(32'h60C02004,32'h00000001);
        575:REG_WR(32'h60C02008,32'h0c0c1900);
        580:REG_WR(32'h60C0200c,32'h00020d0b);
        585:REG_WR(32'h60C09008,32'h00000000);
        590:REG_WR(32'h60C09010,32'h10080212);
        
        595:REG_WR(32'h60C0000C,32'h00017000);
        600:REG_WR(32'h60C00008,32'h59141165);        //MDMaRXCNTL0
        605:REG_WR(32'h60C0002c,32'h01192a30);        //MDMaRXCNTL1
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
        660:REG_WR(32'h60C10000,32'h00000012);
        665:REG_WR(32'h60C10004,32'h00000034);
        
        670:REG_WR(32'h60C10008,32'h00000056);
        675:REG_WR(32'h60C1000C,32'h00000078);
        680:REG_WR(32'h60C10010,32'h0000009A);
        
        685:REG_WR(32'h60C10014,32'h000000BC);
        690:REG_WR(32'h60C10018,32'h000000DE); 
        
        695:REG_WR(32'h60C1001C,32'h00000001);
        700:REG_WR(32'h60C10020,32'h00000002);
        705:REG_RD(32'h60C10024,32'h12345603); 
    //////////////////////////////////////////////////////////////////////////////////
    default:begin
        proc_htrans = 2'b00;
        end 
                                            
  endcase;     
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
