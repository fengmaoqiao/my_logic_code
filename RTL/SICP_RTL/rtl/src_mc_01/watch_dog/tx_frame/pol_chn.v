// *********************************************************************************/
// Project Name : 
// Author       : huangjunjie
// Email        : 475667558@qq.com
// Creat Time   : 2018/06/08 09:33:11
// File Name    : pol_chn.v
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

module pol_chn #(
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

    input       [7:0]                   rx_data                 ,   
    input                               rx_val                  ,   

    input       [23:0]                  chn0_data               ,   
    input       [23:0]                  chn1_data               ,   
    input       [23:0]                  chn2_data               ,   
    input       [23:0]                  chn3_data               ,   
    input       [23:0]                  chn4_data               ,   
    input       [23:0]                  chn5_data               ,   
    input       [23:0]                  chn6_data               ,   
    input       [23:0]                  chn7_data               ,   
    input       [23:0]                  chn8_data               ,   
    input       [23:0]                  chn9_data               ,   
    input       [23:0]                  chn10_data              ,   
    input       [23:0]                  chn11_data              ,   
    input       [23:0]                  chn12_data              ,   
    input       [23:0]                  chn13_data              ,   
//===================================================================================
//
//===================================================================================
    output  reg [23:0]                  wr_data                 ,   
    output  reg [7:0]                   wr_addr                 ,   
    output  reg                         wd_wr_done              ,   
    output  reg                         frame_send                 

);
//-----------------------------------------------------------------------------------//
//  Parameter definitions
//-----------------------------------------------------------------------------------//



//-----------------------------------------------------------------------------------//
//  Reg declarations
//-----------------------------------------------------------------------------------//
reg                             cfg_done_dly                        ;   
reg [7:0]                       wr_addr_dly                         ;   
reg                             cfg_done_1dly                       ;   
reg                             cfg_done_2dly                       ;   



//-----------------------------------------------------------------------------------//
//  Wire declarations
//-----------------------------------------------------------------------------------//




//-----------------------------------------------------------------------------------//
//  Logic Function
//-----------------------------------------------------------------------------------//


always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       wr_addr  <= #U_DLY 8'd0;
    else if((cfg_done_1dly == 1'd1) && (cfg_done_2dly == 1'd0))
       wr_addr     <= #U_DLY 8'd0;
    else if(( rx_data == 8'h55 ) && ( rx_val == 1'd1 )  )
       wr_addr  <= #U_DLY wr_addr + 8'd1;
    else
        ;
end

always @(posedge clk_sys)
begin

        cfg_done_dly     <= #U_DLY cfg_done;   
        cfg_done_1dly    <= #U_DLY cfg_done_dly;   
        cfg_done_2dly    <= #U_DLY cfg_done_1dly;   
        wr_addr_dly         <= #U_DLY wr_addr;
 
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       frame_send   <= #U_DLY 1'd0;
    else if( (cfg_done_1dly == 1'd1) && (cfg_done_2dly == 1'd0))
       frame_send   <= #U_DLY 1'd1;
    else if((wr_addr != 8'd13) && ( rx_val == 1'd1 ))
       frame_send   <= #U_DLY 1'd1;
   else
       frame_send   <= #U_DLY 1'd0;
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
        wd_wr_done  <= #U_DLY 1'd0;
    else if((wr_addr == 8'd13) && ( rx_val == 1'd1 ))
        wd_wr_done  <= #U_DLY 1'd1;
    else
        wd_wr_done  <= #U_DLY 1'd0;

end

always @(posedge clk_sys or negedge rst_n)
begin
  if(rst_n == 1'b0)
      wr_data   <= #U_DLY 24'd0;
  else begin
    case(wr_addr)
        8'd0  : begin  wr_data   <= #U_DLY   chn0_data ; end
        8'd1  : begin  wr_data   <= #U_DLY   chn1_data ; end
        8'd2  : begin  wr_data   <= #U_DLY   chn2_data ; end
        8'd3  : begin  wr_data   <= #U_DLY   chn3_data ; end
        8'd4  : begin  wr_data   <= #U_DLY   chn4_data ; end
        8'd5  : begin  wr_data   <= #U_DLY   chn5_data ; end
        8'd6  : begin  wr_data   <= #U_DLY   chn6_data ; end
        8'd7  : begin  wr_data   <= #U_DLY   chn7_data ; end
        8'd8  : begin  wr_data   <= #U_DLY   chn8_data ; end
        8'd9  : begin  wr_data   <= #U_DLY   chn9_data ; end
        8'd10 : begin  wr_data   <= #U_DLY   chn10_data ; end
        8'd11 : begin  wr_data   <= #U_DLY   chn11_data ; end
        8'd12 : begin  wr_data   <= #U_DLY   chn12_data ; end
        8'd13 : begin  wr_data   <= #U_DLY   chn13_data ; end
        default:begin  wr_data   <= #U_DLY   24'd0     ;end
    endcase
  end

end


endmodule 




