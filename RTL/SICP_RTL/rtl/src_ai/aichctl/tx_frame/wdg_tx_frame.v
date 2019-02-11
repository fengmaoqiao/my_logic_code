// *********************************************************************************/
// Project Name : 
// Author       : huangjunjie
// Email        : 475667558@qq.com
// Creat Time   : 2018/06/08 08:24:36
// File Name    : tx_frame_top.v
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

module wdg_tx_frame #(
    parameter   U_DLY               = 1'b1          
)(
//===================================================================================
// Global  signal 
//===================================================================================
    input                               clk_sys                 ,   
    input                               rst_n                   ,   
//===================================================================================
//
//===================================================================================
    input                               cfg_done                ,   

    input       [15:0]                  chn0_data               ,   
    input       [15:0]                  chn1_data               ,   
    input       [15:0]                  chn2_data               ,   
    input       [15:0]                  chn3_data               ,   
    input       [15:0]                  chn4_data               ,   
    input       [15:0]                  chn5_data               ,   
    input       [15:0]                  chn6_data               ,   
    input       [15:0]                  chn7_data               ,   
    input       [15:0]                  chn8_data               ,   
    input       [15:0]                  chn9_data               ,   
    input       [15:0]                  chn10_data              ,   
    input       [15:0]                  chn11_data              ,   
    input       [15:0]                  chn12_data              ,   
    input       [15:0]                  chn13_data              ,   
    input                               chn0_en                 ,   
    input                               chn1_en                 ,   
    input                               chn2_en                 ,   
    input                               chn3_en                 ,   
    input                               chn4_en                 ,   
    input                               chn5_en                 ,   
    input                               chn6_en                 ,   
    input                               chn7_en                 ,   
    input                               chn8_en                 ,   
    input                               chn9_en                 ,   
    input                               chn10_en                ,   
    input                               chn11_en                ,   
    input                               chn12_en                ,   
    input                               chn13_en                ,   

    input                               rx                      ,   
    output                              tx                      ,
    output      reg                        wd_cfg_done 

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
wire    [7:0]                   tx_data                             ;   
wire                            tx_start                            ;   
wire    [7:0]                   rx_data                             ;   
wire                            rx_dat_val                          ;   
wire                            frame_send                          ;   
wire    [7:0]                   wr_addr                             ;   
wire    [23:0]                  wr_data                             ;   
wire                            tx_done                             ;   
wire    [23:0]                  chn0_data_temp                      ;   
wire    [23:0]                  chn1_data_temp                      ;   
wire    [23:0]                  chn2_data_temp                      ;   
wire    [23:0]                  chn3_data_temp                      ;   
wire    [23:0]                  chn4_data_temp                      ;   
wire    [23:0]                  chn5_data_temp                      ;   
wire    [23:0]                  chn6_data_temp                      ;   
wire    [23:0]                  chn7_data_temp                      ;   
wire    [23:0]                  chn8_data_temp                      ;   
wire    [23:0]                  chn9_data_temp                      ;   
wire    [23:0]                  chn10_data_temp                     ;   
wire    [23:0]                  chn11_data_temp                     ;   
wire    [23:0]                  chn12_data_temp                     ;   
wire    [23:0]                  chn13_data_temp                     ;   
wire                            tx_busy                             ;   




//-----------------------------------------------------------------------------------//
//  Logic Function
//-----------------------------------------------------------------------------------//

assign chn0_data_temp = {7'd0,chn0_en,chn0_data};
assign chn1_data_temp = {7'd0,chn1_en,chn1_data};
assign chn2_data_temp = {7'd0,chn2_en,chn2_data};
assign chn3_data_temp = {7'd0,chn3_en,chn3_data};
assign chn4_data_temp = {7'd0,chn4_en,chn4_data};
assign chn5_data_temp = {7'd0,chn5_en,chn5_data};
assign chn6_data_temp = {7'd0,chn6_en,chn6_data};
assign chn7_data_temp = {7'd0,chn7_en,chn7_data};
assign chn8_data_temp = {7'd0,chn8_en,chn8_data};
assign chn9_data_temp = {7'd0,chn9_en,chn9_data};
assign chn10_data_temp = {7'd0,chn10_en,chn10_data};
assign chn11_data_temp = {7'd0,chn11_en,chn11_data};
assign chn12_data_temp = {7'd0,chn12_en,chn12_data};
assign chn13_data_temp = {7'd0,chn13_en,chn13_data};

always @ ( posedge clk_sys or negedge rst_n ) begin
    if( rst_n == 1'b0 ) begin
        wd_cfg_done <=   1'b0 ;
    end
    else begin
        if ( wr_addr == 7'h0E ) begin
            wd_cfg_done <=   1'b1 ;
        end
    end
end

 pol_chn u_pol_chn
 (
//===================================================================================
// Global  signal 
//===================================================================================
    .clk_sys                    ( clk_sys                   ),
    .rst_n                      ( rst_n                     ),
//===================================================================================
//
//===================================================================================
   
    .cfg_done                   ( cfg_done                  ),

    .rx_data                    ( rx_data                   ),
    .rx_val                     ( rx_dat_val                ),

    .chn0_data                  ( chn0_data_temp            ),
    .chn1_data                  ( chn1_data_temp            ),
    .chn2_data                  ( chn2_data_temp            ),
    .chn3_data                  ( chn3_data_temp            ),
    .chn4_data                  ( chn4_data_temp            ),
    .chn5_data                  ( chn5_data_temp            ),
    .chn6_data                  ( chn6_data_temp            ),
    .chn7_data                  ( chn7_data_temp            ),
    .chn8_data                  ( chn8_data_temp            ),
    .chn9_data                  ( chn9_data_temp            ),
    .chn10_data                 ( chn10_data_temp           ),
    .chn11_data                 ( chn11_data_temp           ),
    .chn12_data                 ( chn12_data_temp           ),
    .chn13_data                 ( chn13_data_temp           ),
//===================================================================================
//
//===================================================================================
    .wr_data                    ( wr_data                   ),
    .wr_addr                    ( wr_addr                   ),
    .frame_send                 ( frame_send                )
);

 frame_ctl u_frame_ctl
 (
//===================================================================================
// Global  signal 
//===================================================================================
    .clk_sys                    ( clk_sys                   ),
    .rst_n                      ( rst_n                     ),
//===================================================================================
//
//===================================================================================
    .frame_send                 ( frame_send                ),
    .wr_addr                    ( wr_addr                   ),
    .wr_data                    ( wr_data                   ),
//===================================================================================
//
//===================================================================================
    .tx_done                    ( tx_done                   ),
    .tx_data                    ( tx_data                   ),
    .tx_busy                    ( tx_busy                   ),
    .tx_start                   ( tx_start                  )
 

);

 uart_top  #(
    .U_DLY                      ( U_DLY                     )
)u3_uart_top(
//===================================================================================
// Global  signal 
//===================================================================================
    .clk_sys                    ( clk_sys                   ),
    .rst_n                      ( rst_n                     ),
//===================================================================================
//
//===================================================================================
    .tx_data                    ( tx_data                   ),
    .tx_start                   ( tx_start                  ),
    .rx                         ( rx                        ),

    .rx_data                    ( rx_data                   ),
    .rx_dat_val                 ( rx_dat_val                ),

    .tx_done                    ( tx_done                   ),
    .tx_busy                    ( tx_busy                   ),
    .tx                         ( tx                        )
);
endmodule 




