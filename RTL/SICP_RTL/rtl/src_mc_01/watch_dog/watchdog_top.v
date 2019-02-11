// *********************************************************************************/
// Project Name : 
// Author       : huangjunjie
// Email        : 475667558@qq.com
// Creat Time   : 2018/07/20 14:06:47
// File Name    : watchdog_top.v
// Module Name  : 
// Abstract     : 
//
// CopyRight(c) 2014, Zhimingda digital equipment Co., Ltd.. 
// All Rights Reserved
//
// *********************************************************************************/
//
//             #############                    -------------------------------      
//         #####################                |                             |      
//       #########################              |     Author: dongjun         |      
//      ####           ############             |                             |      
//      #### ########  ############             |     Phone: 028-69981523-6172|      
//      ### * #######  ############             |                             |      
//      #############  #######  ###             -------------------------------      
//      ####           ############                                                  
//      ####  #####################                                                  
//      ####  ####### * ###########                                                  
//      ####  ######## ############            **********  **** ****  ********       
//      ####           ############            ********** *********** *********      
//      ########################                    ****  *********** ***   ***      
//      ########################                  ****    *** *** *** ***   ***      
//      ########################                ****      *** *** *** ***   ***      
//      #################                      ********** *** *** *** *********      
//      #################                      ********** *** *** *** ********       
//
// Modification History:
// 1. initial
// *********************************************************************************/
`timescale 1ns/1ps

module watchdog_top #(
    parameter   U_DLY = 1'b1          
)(
    input                               clk_sys                 ,   
    input                               rst_n                   ,   
    
    input      [15:0]                   run_cycle               ,   
    input      [15:0]                   enable_slot             ,   
    input                               cfg_finish_flag         ,   
    
    input                               wd_uart_rx              ,
    output                              wd_uart_tx              ,
    //watchdog feed symbol
    input      [5:0]                    slink_rx_eop            ,   
    output reg [5:0]                    channel_feeddog
);
//-----------------------------------------------------------------------------------//
//  Parameter definitions
//-----------------------------------------------------------------------------------//



//-----------------------------------------------------------------------------------//
//  Reg declarations
//-----------------------------------------------------------------------------------//



//-----------------------------------------------------------------------------------//
//  Wire declarations
//-----------------------------------------------------------------------------------//
reg  [15:0]                     channel_feeddog_cnt [5:0]           ;
wire [5:0]                      channel_enable                      ;   
wire                            wd_cfg_done                         ;   

//-----------------------------------------------------------------------------------//
//  Logic Function
//-----------------------------------------------------------------------------------//

genvar i ;
generate
for(i=0;i<6;i=i+1) begin

    always @(posedge clk_sys or negedge rst_n)
    begin
        if(rst_n == 1'b0) begin
            channel_feeddog_cnt[i] <= 8'h00;
        end
        else if(channel_feeddog_cnt[i][7] == 1'b1) begin
            channel_feeddog_cnt[i] <= 8'h00;
        end
        else if(channel_feeddog[i] == 1'b1) begin
            channel_feeddog_cnt[i] <= channel_feeddog_cnt[i] + 1'b1;
        end
    end
    
    always @(posedge clk_sys or negedge rst_n)
    begin
        if(rst_n == 1'b0) begin
            channel_feeddog[i] <= 1'b0;
        end
        else if(channel_feeddog_cnt[i][7] == 1'b1) begin
            channel_feeddog[i] <= 1'b0;
        end
        else if(slink_rx_eop[i] == 1'b1) begin
            channel_feeddog[i] <= 1'b1;
        end
    end
    
end
endgenerate



assign  channel_enable = { enable_slot[11:8] , enable_slot[3:0] , enable_slot[13] , enable_slot[12] } ;

wdg_tx_frame            
u_wdg_tx_frame
(

    .clk_sys                    ( clk_sys                   ),
    .rst_n                      ( rst_n                     ),

    .cfg_done                   ( cfg_finish_flag           ),

    .chn0_data                  ( run_cycle                 ),
    .chn1_data                  ( run_cycle                 ),
    .chn2_data                  ( run_cycle                 ),
    .chn3_data                  ( run_cycle                 ),
    .chn4_data                  ( run_cycle                 ), // 202
    .chn5_data                  ( run_cycle                 ),
    .chn6_data                  ( 16'd0                     ),
    .chn7_data                  ( 16'd0                     ),
    .chn8_data                  ( 16'd0                     ),
    .chn9_data                  ( 16'd0                     ),
    .chn10_data                 ( 16'd0                     ),
    .chn11_data                 ( 16'd0                     ),
    .chn12_data                 ( 16'd0                     ),
    .chn13_data                 ( 16'd0                     ),
    .chn0_en                    ( channel_enable[0]         ),
    .chn1_en                    ( channel_enable[1]         ),
    .chn2_en                    ( channel_enable[2]         ),
    .chn3_en                    ( channel_enable[3]         ),
    .chn4_en                    ( channel_enable[4]         ),
    .chn5_en                    ( channel_enable[5]         ),
    .chn6_en                    ( 1'b0                      ),
    .chn7_en                    ( 1'b0                      ),
    .chn8_en                    ( 1'b0                      ),
    .chn9_en                    ( 1'b0                      ),
    .chn10_en                   ( 1'b0                      ),
    .chn11_en                   ( 1'b0                      ),
    .chn12_en                   ( 1'b0                      ),
    .chn13_en                   ( 1'b0                      ),

    .rx                         ( wd_uart_rx                ),
    .tx                         ( wd_uart_tx                ),
    .wd_cfg_done                ( wd_cfg_done               )

);


endmodule 




