`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/30/2017 11:25:36 AM
// Design Name: 
// Module Name: tx_rx_fifo
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

`default_nettype wire

module tx_rx_fifo(

    input                   clk_80m                 ,
    input                   source_clk              ,
    input                   AD9361_clk              ,
    input                   plf_clk                 ,
    input                   txv_immstop             ,
    input                   rst_n                   ,

    input          [3:0]            sourcedata_ch   ,
    input                           cap_data_en     ,

  /***********************************************************
  * 数据到9361为16位
  ***********************************************************/
  /* tx channel */
    output  reg   [15:0]          modem_tx_a_i_rf_o         ,    //to rf
    output  reg   [15:0]          modem_tx_a_q_rf_o         ,    //to rf

  /***********************************************************
  * 从Phy来的发送数据 
  ***********************************************************/
    input         [9:0]           modem_tx_a_i_phy        ,
    input         [9:0]           modem_tx_a_q_phy        ,  
    input                         modem_tx_a_tog           ,
  
  /* 接收通道 */
  /***********************************************************
  * 从9361来的接收数据
  ***********************************************************/
    input        [15:0]          modem_rx_a_i_rf_in            ,
    input        [15:0]          modem_rx_a_q_rf_in            ,  
  /***********************************************************
  * 从phy发送通道来的数据
  ***********************************************************/
    output  reg  [10:0]          modem_rx_a_i_phy           , //to phy
    output  reg  [10:0]          modem_rx_a_q_phy           , //to phy
    output  reg                  modem_rx_a_tog,



    output  reg             rx_start,

    output                  dac_dovf,
    output                  dac_dunf,
    output                  adc_dovf,
    output                  adc_dunf,
    input                   rf_rst              ,
    input                   adc_enable_i0       ,
    input                   adc_valid_i0        , 
    input                   adc_enable_q0       ,
    input                   adc_valid_q0        ,   
    input                   dac_enable_i0       ,
    input                   dac_valid_i0        , 
    input                   dac_enable_q0       ,
    input                   dac_valid_q0        ,  
    output                  txfifo_empty        ,  
    output                  rxfifo_full         ,
    output                  rxfifo_almost_empty ,
    output                  txfifo_almost_full  
   
    );

wire    [10:0]      modem_tx_a_i_phy_ex;
wire    [10:0]      modem_tx_a_q_phy_ex;  
wire    [10:0]      modem_tx_a_i_rf;
wire    [10:0]      modem_tx_a_q_rf;
wire                rx_wen; 
wire                rxfifo_empty;

wire    [10:0]      modem_rx_a_i_phy_normal   ;
wire    [10:0]      modem_rx_a_q_phy_normal   ;
 
wire    [9:0]       modem_rx_a_i_loopback     ;
wire    [9:0]       modem_rx_a_q_loopback     ;
wire                modem_rx_a_toggle_loopback; 
wire                modem_rx_a_toggle_loopback1;  
  
reg                 modem_tx_a_tog_d = 1'b0;
reg     [9:0]       modem_tx_a_i_phy_d;
reg     [9:0]       modem_tx_a_q_phy_d;

reg     [15:0]      rx_data_count   = 16'd0;
 
//reg                 rx_start;  
reg    [11:0]       rx_start_delay_cnt  ;
    
reg                 wr_en; 
reg                 rd_en_loop;
wire                txfifo_full;
reg                 txfifo_empty_d1;
  
wire    [15:0]      modem_tx_a_i_rf_normal;
wire    [15:0]      modem_tx_a_q_rf_normal;
reg                 modem_rx_a_toggle_normal;

wire    [15:0]      modem_tx_a_i_rf_rom;
wire    [15:0]      modem_tx_a_q_rf_rom;
wire    [10:0]      modem_rx_a_i_rf_rom;
wire    [10:0]      modem_rx_a_q_rf_rom;

wire   [9:0]        modem_tx_a_i_rf_ram_temp;
wire   [9:0]        modem_tx_a_q_rf_ram_temp;

wire   [15:0]       modem_tx_a_i_rf_ram;
wire   [15:0]       modem_tx_a_q_rf_ram;

wire        [5:0]       rd_data_count;
wire        [5:0]       wr_data_count; 
reg    [1:0]           rx_cnt = 2'b0; 

reg                         modem_rx_a_toggle_rom;
reg     data_wren;



reg [10:0]     rand_i   = 'd0;
reg [10:0]     rand_q   = 'd0;
reg            rand_tog = 1'b0;

//---------- delay with tx change to rx ----------------------
always @(posedge clk_80m) begin
  if(txv_immstop == 1'b0)
        rx_start_delay_cnt <= 16'd0;
  else 
    if(rx_start_delay_cnt < 16'd100)
        rx_start_delay_cnt <= rx_start_delay_cnt + 1'b1;
    else
        ;
end
  
always @(posedge clk_80m) begin
  if(rx_start_delay_cnt >= 16'd40)
      rx_start <= 1'b1;
  else 
      rx_start <= 1'b0;
end

always @(posedge clk_80m) begin
    if(rx_start == 1'b0)
        rx_cnt <= 2'd0;
    else
        rx_cnt <= rx_cnt + 1'b1;
end
//------------------- tx choice ----------------------------------------
always @(posedge AD9361_clk) begin
    case(sourcedata_ch)
        /* 正常模式  */
        4'b0000   :  begin  modem_tx_a_i_rf_o  <= modem_tx_a_i_rf_normal;
        modem_tx_a_q_rf_o  <= modem_tx_a_q_rf_normal; end
        /* 不发送 */
        4'b0001   :  begin  modem_tx_a_i_rf_o  <= 16'd0;
                            modem_tx_a_q_rf_o  <= 16'd0;  end               
        /* 从ROM发送数据 */                    
        4'b0010   :  begin  modem_tx_a_i_rf_o  <= modem_tx_a_i_rf_rom;
                            modem_tx_a_q_rf_o  <= modem_tx_a_q_rf_rom;  end
     endcase;
end 
 
//------------------- rx choice ---------------------------------------- 
always @(posedge clk_80m) begin
    case(sourcedata_ch)
      
  /***********************************************************
  * 正常模式
  ***********************************************************/
        4'b0000   :  begin  modem_rx_a_i_phy   <= modem_rx_a_i_phy_normal;
                            modem_rx_a_q_phy   <= modem_rx_a_q_phy_normal; 
                            modem_rx_a_tog     <= modem_rx_a_toggle_normal;end
                              
  /***********************************************************
  * 回环
  ***********************************************************/
        4'b0001   :  begin  modem_rx_a_i_phy   <= {modem_rx_a_i_loopback[9],modem_rx_a_i_loopback};   
                            modem_rx_a_q_phy   <= {modem_rx_a_q_loopback[9],modem_rx_a_q_loopback};  
                            modem_rx_a_tog     <= modem_rx_a_toggle_loopback; end               

  /***********************************************************
  * 从ROM接收数据
  ***********************************************************/
        4'b0010   :  begin  modem_rx_a_i_phy   <= modem_rx_a_i_rf_rom;
                            modem_rx_a_q_phy   <= modem_rx_a_q_rf_rom;
                            modem_rx_a_tog     <= modem_rx_a_toggle_rom;end

  /***********************************************************
  * 从随机数接收数据
  ***********************************************************/
        4'b0011   :  begin  modem_rx_a_i_phy   <= rand_i;
                            modem_rx_a_q_phy   <= rand_q;
                            modem_rx_a_tog     <= rand_tog; end
     endcase;
end 
 
always @(posedge clk_80m) begin
    if(rst_n == 1'b0 || txv_immstop == 1'b0)
        modem_rx_a_toggle_normal <= 1'b0;
    else if(rx_cnt == 2'b11)
        modem_rx_a_toggle_normal <= ~modem_rx_a_toggle_normal;
    else
        ;
end 
    
//----------------------------------------------------------------------
//------------------ normal model---------------------------------------
//----------------------------------------------------------------------
wire           rx_en_nomal      ;


assign rx_wen = adc_enable_i0&adc_valid_i0&adc_enable_q0&adc_valid_q0;
  
//---------------------- write data ------------------------------------
  always @(posedge clk_80m) begin
          modem_tx_a_tog_d        <= modem_tx_a_tog;
          modem_tx_a_i_phy_d      <= modem_tx_a_i_phy;
          modem_tx_a_q_phy_d      <= modem_tx_a_q_phy;
  end
  

  always @(posedge clk_80m) begin
      if((modem_tx_a_tog_d == 1'b0 && modem_tx_a_tog == 1'b1) || 
         (modem_tx_a_tog_d == 1'b1 && modem_tx_a_tog == 1'b0))begin
            wr_en <= 1'b1;
      end
      else 
            wr_en <= 1'b0;
  end
    
  
  assign   modem_tx_a_i_phy_ex = {modem_tx_a_i_phy_d[9],modem_tx_a_i_phy_d};
  assign   modem_tx_a_q_phy_ex = {modem_tx_a_q_phy_d[9],modem_tx_a_q_phy_d};
  
  assign   modem_tx_a_i_rf_normal = (txfifo_empty && txfifo_empty_d1) ? 16'd0 : {modem_tx_a_i_rf,5'd0};
  assign   modem_tx_a_q_rf_normal = (txfifo_empty && txfifo_empty_d1) ? 16'd0 : {modem_tx_a_q_rf,5'd0};

// --------------- debug -----------
wire [10:0]  modem_rx_a_q_rf_in_debug;
wire [10:0]  modem_rx_a_i_rf_in_debug;

assign tx_fifo_rd_en = (~txfifo_empty)&dac_enable_i0&dac_valid_i0&dac_enable_q0&dac_valid_q0;

   RF_TXRX_FIFO tx_iq_fifo(
    .rst         (~rst_n),
    .wr_clk      (clk_80m),
    .wr_en       (wr_en),      
    .din         ({modem_tx_a_i_phy_ex,modem_tx_a_q_phy_ex}),
    
    .rd_clk      (AD9361_clk),
    .rd_en       (tx_fifo_rd_en), 
    .dout        ({modem_tx_a_i_rf,modem_tx_a_q_rf}),
    
    .full        (txfifo_full),
    .almost_full (txfifo_almost_full),
    .overflow    (dac_dovf),
    .empty       (txfifo_empty),
    .almost_empty(), 
    .underflow   (dac_dunf)
    );

  RF_TXRX_FIFO rx_iq_fifo(
    .rst         (~rst_n),
    .wr_clk      (AD9361_clk),
    .wr_en       (rx_wen), 
    //.din         ({modem_rx_a_i_rf_in_debug,modem_rx_a_q_rf_in_debug}), //just for debug    
    .din         ({modem_rx_a_i_rf_in[11:1],modem_rx_a_q_rf_in[11:1]}),
    
    .rd_clk      (clk_80m),
    .rd_en       (rx_en_nomal), 
    .dout        ({modem_rx_a_i_phy_normal,modem_rx_a_q_phy_normal}),
    
    .full        (rxfifo_full),
    .almost_full (rxfifo_almost_full),
    .overflow    (adc_dovf),
    .empty       (rxfifo_empty),
    .almost_empty(rxfifo_almost_empty), 
    .underflow   (adc_dunf),
    
    .rd_data_count (rd_data_count),
    .wr_data_count (wr_data_count)
    );
    
  assign rx_en_nomal = (rx_cnt == 2'b11) && (~rxfifo_empty);   
    
always @(posedge AD9361_clk) begin
      txfifo_empty_d1 <=  txfifo_empty;
end   
    
  /***********************************************************
  *  回环
  ***********************************************************/
wire                   loopback_fifo_full   ;
wire                   loopback_fifo_empty  ;
    
 
always @(posedge clk_80m) begin
    if(rx_start == 1'b0)
        rd_en_loop <= 1'd0;
    else if (rx_cnt == 2'b11 && loopback_fifo_empty == 1'b0)begin
        rd_en_loop <= 1'd1;
    end
    else begin
        rd_en_loop <= 1'd0;
    end
end 

  
  loopback_fifo i_loopback_fifo(
      .wr_clk        ( clk_80m                       ),
      .full          ( loopback_fifo_full            ),
      .din           ( {modem_tx_a_tog_d,modem_tx_a_i_phy_d}      ),
      .wr_en         ( wr_en                         ),
      
      .rd_clk        ( clk_80m                     ),
      .empty         ( loopback_fifo_empty           ),
      .dout          ( {modem_rx_a_toggle_loopback,modem_rx_a_i_loopback}   ),
      .rd_en         ( rd_en_loop                         )
    );
    
  loopback_fifo q_loopback_fifo(
      .wr_clk        ( clk_80m                       ),
      .full          (                               ),
      .din           ( {modem_tx_a_tog_d,modem_tx_a_q_phy_d}      ),
      .wr_en         ( wr_en                         ),
    
      .rd_clk        ( clk_80m                     ),
      .empty         (                               ),
      .dout          ( {modem_rx_a_toggle_loopback1,modem_rx_a_q_loopback}   ),
      .rd_en         ( rd_en_loop                         )
  );  
    
  /***********************************************************
  * ROM模式
  ***********************************************************/
wire   [23:0]               basedata_tx;
wire   [23:0]               basedata_rx;
reg    [10:0]               basedata_addr_tx = 11'd0  ;
reg    [10:0]               basedata_addr_rx = 11'd0  ;
reg                         modem_rx_a_toggle_rom_temp = 1'b0;
 
//reg   [1:0]       cnt = 2'd0;
//always @(posedge clk_80m) begin
//    cnt <= cnt + 1'b1;
//end
 
 
always @(posedge AD9361_clk) begin
    if(basedata_addr_tx == 11'd1281)
        basedata_addr_tx <= 11'd0;
    else
        if((dac_enable_i0 && dac_valid_i0) == 1'b1)
            basedata_addr_tx <= basedata_addr_tx + 1'b1;
        else
            basedata_addr_tx <= 11'd0;
end 

always @(posedge clk_80m) begin
    if(rx_cnt == 2'b11) begin
        if(basedata_addr_rx == 11'd1281)
            //basedata_addr_rx <= basedata_addr_rx;
            basedata_addr_rx <= 11'd0;
        else begin
                basedata_addr_rx <= basedata_addr_rx + 1'b1;
                modem_rx_a_toggle_rom_temp <= ~modem_rx_a_toggle_rom_temp;
            end
    end
    else
        ;
end

always @(posedge clk_80m) begin
    modem_rx_a_toggle_rom <= modem_rx_a_toggle_rom_temp;
end 

  baseband_data tx_baseband_data(
    .clka       ( AD9361_clk            ),
    .addra      ( basedata_addr_tx      ),
    .douta      ( basedata_tx           )
  );
  
    baseband_data rx_baseband_data(
    .clka       ( clk_80m               ),
    .addra      ( basedata_addr_rx      ),
    .douta      ( basedata_rx           )
  );
  
assign   modem_tx_a_i_rf_rom = {basedata_tx[9],basedata_tx[9:0],5'd0};
assign   modem_tx_a_q_rf_rom = {basedata_tx[21],basedata_tx[21:12],5'd0};
assign   modem_rx_a_i_rf_rom = {basedata_rx[9],basedata_rx[9:0]};
assign   modem_rx_a_q_rf_rom = {basedata_rx[21],basedata_rx[21:12]};


////------------------------------------------------------------------
////----------------- debug cap data ---------------------------------
////------------------------------------------------------------------    
//integer     tx_data;
//integer     rx_data; 

//integer     loopbank_data;   
    
//initial begin
//    tx_data = $fopen("/home/xielong/Documents/mac_phy_9361/SVN/mustang_phy/test_data/tx_data_15.txt","w");
//    rx_data = $fopen("/home/xielong/Documents/mac_phy_9361/SVN/mustang_phy/test_data/rx_data_15.txt","w");
//    loopbank_data = $fopen("/home/xielong/Documents/mac_phy_9361/SVN/mustang_phy/test_data/loopbank_data.txt","w");
//end  
           
    
//reg  [11:0]   counter_debug  = 12'd0;
    
//always @(posedge AD9361_clk) begin
//    if((txfifo_empty && txfifo_empty_d1) == 1'b0)begin
//        $fwrite(tx_data,"%h,%h,%d\n",modem_tx_a_q_rf_normal,modem_tx_a_i_rf_normal,counter_debug);
//     //   counter_debug <= counter_debug + 1'b1;
//    end
//end

//always @(posedge modem_rx_a_toggle_loopback or negedge modem_rx_a_toggle_loopback) begin
//        $fwrite(loopbank_data,"%h,%h,%d\n",modem_rx_a_q_loopback,modem_rx_a_i_loopback,counter_debug);
//        counter_debug <= counter_debug + 1'b1;
//end    
////------------------------------------------------------------------
////----------------- debug inj data ---------------------------------
////------------------------------------------------------------------    
//reg    [31:0]     rx_data_inj_mem[1280:0];   
//reg    [10:0]     rx_inj_addr = 12'd0;
   
//always @(posedge AD9361_clk) begin
//    if(txv_immstop == 1'd1)
//    //if(rx_start_delay_cnt > 'd0)
//        if(rx_inj_addr < 1280)
//            rx_inj_addr <= rx_inj_addr + 1'b1;
//       // else if(rx_start == 1'b0)
//       //     rx_inj_addr <= 12'd0;
//        else
//            rx_inj_addr <= 12'd0;
//    else 
//        rx_inj_addr <= 12'd0;
//end

//wire [31:0]  injtction_data;



//assign injtction_data = rx_data_inj_mem[rx_inj_addr];
//assign modem_rx_a_q_rf_in_debug = injtction_data[31:21];
//assign modem_rx_a_i_rf_in_debug = injtction_data[15:5];

//initial begin
//    $readmemh("/home/xielong/Documents/mac_phy_9361/SVN/mustang_phy/test_data/rx_data_injection.txt",rx_data_inj_mem);
//end    
       
//---------- random data ----------------------------

always @(posedge AD9361_clk) begin
    if(txv_immstop == 1'd1)begin
        rand_i   <= $random%72;  
        rand_q   <= $random%72;
        //rand_i   <= 64;  
        //rand_q   <= 64;
        rand_tog <= ~rand_tog;
    end
    else begin
        rand_i   <= 'd0;  
        rand_q   <= 'd0;
        rand_tog <= 'd0;
    end
end
        
       
        
endmodule
