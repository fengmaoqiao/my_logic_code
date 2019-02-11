// *********************************************************************************/
// Project Name : 
// Author       : huangjunjie
// Email        : 475667558@qq.com
// Creat Time   : 2018/06/08 08:28:27
// File Name    : frame_ctl.v
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

module frame_ctl #(
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
    input                               frame_send              ,   
    input       [7:0]                   wr_addr                 ,   
    input       [23:0]                  wr_data                 ,   
//===================================================================================
//
//===================================================================================
    input                               tx_done                 ,   
    output  reg [7:0]                   tx_data                 ,   
    input                               tx_busy                 ,   
    output  reg                         tx_start                   
 

);
//-----------------------------------------------------------------------------------//
//  Parameter definitions
//-----------------------------------------------------------------------------------//
parameter FRAME_HEAD   = 24'hffaa55                                ;

localparam IDLE        = 6'd0                                      ;
localparam FRAME_HEAD1 = 6'd1                                      ;
localparam FRAME_HEAD2 = 6'd2                                      ;
localparam FRAME_HEAD3 = 6'd3                                      ;
localparam WR_ADDR     = 6'd4                                      ;
localparam WR_DATA_MSB = 6'd5                                      ;
localparam WR_DATA_2   = 6'd6                                      ;
localparam WR_DATA_LSB = 6'd7                                      ;
localparam WR_DATA_CRC1 = 6'd8                                     ;
localparam WR_DATA_CRC2 = 6'd9                                     ;
localparam CLEAR_CRC   = 6'd10                                     ;


//-----------------------------------------------------------------------------------//
//  Reg declarations
//-----------------------------------------------------------------------------------//
reg                             crc_eop                             ;   
reg                             crc_sop                             ;   
reg [5:0]                       cur_st_dly                          ;   
reg [5:0]                       next_st                             ;   
reg [5:0]                       cur_st                              ;   
reg                             tx_busy_dly                         ;   
reg                             tx_start_dly                        ;   
reg [15:0]                      cal_crc                             ;   
reg                             crc_eop_dly                         ;   
reg                             crc_eop_1dly                        ;   



//-----------------------------------------------------------------------------------//
//  Wire declarations
//-----------------------------------------------------------------------------------//
wire                                crc_din_vld;
wire    [7:0]                       crc_din;
wire    [15:0]                      cal_crc_temp;




//-----------------------------------------------------------------------------------//
//  Logic Function
//-----------------------------------------------------------------------------------//


always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
        cur_st     <= #U_DLY IDLE;
    else
        cur_st     <= #U_DLY next_st;

end

always @(*)
begin
    if(rst_n == 1'b0)
       next_st   = IDLE;
   else begin
       case(cur_st)
          IDLE :begin
              if(frame_send == 1'd1)
                 next_st = FRAME_HEAD1 ;
              else
                 next_st = IDLE;
          end  
          FRAME_HEAD1 :begin
              if(tx_done == 1'd1)
                 next_st = FRAME_HEAD2 ;
              else
                 next_st = FRAME_HEAD1;
          end  
          FRAME_HEAD2 :begin
              if(tx_done == 1'd1)
                 next_st = FRAME_HEAD3 ;
              else
                 next_st = FRAME_HEAD2;
          end  
          FRAME_HEAD3 :begin
              if(tx_done == 1'd1)
                 next_st = WR_ADDR ;
              else
                 next_st = FRAME_HEAD3;
          end  
          WR_ADDR :begin
              if(tx_done == 1'd1)
                 next_st = WR_DATA_MSB ;
              else
                 next_st = WR_ADDR;
          end  
          WR_DATA_MSB :begin
              if(tx_done == 1'd1)
                 next_st = WR_DATA_2 ;
              else
                 next_st = WR_DATA_MSB;
          end  
          WR_DATA_2 :begin
              if(tx_done == 1'd1)
                 next_st = WR_DATA_LSB ;
              else
                 next_st = WR_DATA_2;
          end  
          WR_DATA_LSB :begin
              if(tx_done == 1'd1)
                 next_st = WR_DATA_CRC1 ;
              else
                 next_st = WR_DATA_LSB;
          end  
          WR_DATA_CRC1 :begin
              if(tx_done == 1'd1)
                 next_st = WR_DATA_CRC2 ;
              else
                 next_st = WR_DATA_CRC1;
          end  
          WR_DATA_CRC2 :begin
              if(tx_done == 1'd1)
                 next_st = IDLE ;
              else
                 next_st = WR_DATA_CRC2;
          end  
          default: next_st = IDLE;
       endcase
   end
end


always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
      cur_st_dly  <= #U_DLY IDLE;
    else
      cur_st_dly    <= #U_DLY cur_st;
end

always @(posedge clk_sys )
begin
    tx_busy_dly     <= #U_DLY tx_busy; 
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
      tx_start  <= #U_DLY 1'd0;
    else if( (cur_st != IDLE ) && ( cur_st !=cur_st_dly))
      tx_start  <= #U_DLY 1'd1;
    else if((tx_busy == 1'd1) && (tx_busy_dly == 1'd0))
      tx_start  <= #U_DLY 1'd0;
end

always @(posedge clk_sys or negedge rst_n)
begin
  if(rst_n == 1'b0)
      tx_data   <= #U_DLY 8'd0;
  else begin
    case(cur_st)
          IDLE :begin
             tx_data    <= #U_DLY 8'd0; 
          end  
          FRAME_HEAD1 :begin
             tx_data    <= #U_DLY 8'hff;
          end  
          FRAME_HEAD2 :begin
             tx_data    <= #U_DLY 8'haa;
          end  
          FRAME_HEAD3 :begin
             tx_data    <= #U_DLY 8'h55;
          end  
          WR_ADDR :begin
               tx_data    <= #U_DLY wr_addr;
          end  
          WR_DATA_MSB :begin
               tx_data    <= #U_DLY wr_data[23:16];
          end  
          WR_DATA_2 :begin
               tx_data    <= #U_DLY wr_data[15:8];
          end  
          WR_DATA_LSB :begin
               tx_data    <= #U_DLY wr_data[7:0];
           end
          WR_DATA_CRC1 :begin
               tx_data      <= #U_DLY cal_crc[15:8];
           end
          WR_DATA_CRC2 :begin
               tx_data      <= #U_DLY cal_crc[7:0];
           end  
    endcase
  end
end

//===================================================================================
// crc ctl
//===================================================================================

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       crc_eop  <= #U_DLY 1'd0;
    else if((cur_st == WR_DATA_LSB ) && ( cur_st !=cur_st_dly))
       crc_eop      <= #U_DLY 1'd1;
    else
       crc_eop     <= #U_DLY 1'd0;
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       crc_sop  <= #U_DLY  1'd0;
    else if( cur_st == IDLE )
       crc_sop  <= #U_DLY  1'd1;
    else
       crc_sop  <= #U_DLY  1'd0;

end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       tx_start_dly     <= #U_DLY 1'd0;
    else
       tx_start_dly     <= #U_DLY tx_start;
end

always @(posedge clk_sys)
begin
   crc_eop_dly  <= #U_DLY crc_eop;
   crc_eop_1dly  <= #U_DLY crc_eop_dly;
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
        cal_crc     <= #U_DLY 16'd0;
    else if( crc_eop_1dly == 1'd1 )
        cal_crc     <= #U_DLY cal_crc_temp;
end



assign crc_din_vld = (tx_start == 1'd1) && (tx_start_dly == 1'd0 ) ? 1'd1 : 1'd0;
assign crc_din = tx_data;

//CRC8D8 U_CRC8D8
//    (
//    //input port
//    .clk_sys                    ( clk_sys                   ),
//    .rst_sys                    ( rst_n                     ),
//
//    .crc_din                    ( crc_din                   ),
//    .crc_cap                    ( crc_eop                   ),
//    .crc_sop                    ( crc_sop                   ),
//    .crc_din_vld                ( crc_din_vld               ),
//
//    //output port
//    .crc_dout                   ( cal_crc_temp                   )
//    );
    IO_FCS16     U_FCS16
    (
    //input port
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_n                     ),

    .crc_din                    ( crc_din                   ),
    .crc_cap                    ( crc_eop                   ),
    .crc_sop                    ( crc_sop                   ),
    .crc_din_vld                ( crc_din_vld               ),

    //output port
    .crc_dout                   ( cal_crc_temp              )
    );


endmodule 




