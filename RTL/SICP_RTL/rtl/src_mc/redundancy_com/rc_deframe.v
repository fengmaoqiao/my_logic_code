`timescale 1ns/1ps
module  rc_deframe #(
    parameter   U_DLY               = 1'b1          
)(
//===================================================================================
// Global  signal 
//===================================================================================
    input                               clk_sys                 ,   
    input                               rst_n                   ,   
//===================================================================================
//data in 
//===================================================================================
    input       [7:0]                   data_i                  ,   
    input                               data_i_val              ,   
    input                               frame_send_en           ,   
//===================================================================================
//wr data 
//===================================================================================
    output  reg [32:0]                  rx_frame_data           ,   
    output  reg                         crc_check_ok            ,   
    output  reg                         remot_time_out          ,   
    output  reg                         rx_frame_done             

);
//-----------------------------------------------------------------------------------//
//  Parameter definitions
//-----------------------------------------------------------------------------------//
parameter FRAME_HEAD   = 16'h5ad5                                ;

localparam BAUD_60MS = 32'd7500000                               ; //@125m 60ms   
//localparam BAUD_60MS = 32'd10000                               ; //@125m 60ms   

//-----------------------------------------------------------------------------------//
//  Reg declarations
//-----------------------------------------------------------------------------------//
reg [7:0]                       data_i_dly                          ;   
reg                             data_i_val_dly                      ;   
reg                             rx_eop                              ;   
reg                             rx_eop_1dly                         ;   
reg                             rx_eop_2dly                         ;   
reg [23:0]                      data_shift                          ;   
reg [7:0]                       wr_cnt                              ;   
reg                             crc_clear                           ;   
reg                             clc_crc                             ;   
reg [7:0]                       rx_crc1                             ;   
reg [7:0]                       rx_crc2                             ;   
reg [31:0]                      wait_cnt                            ;   



//-----------------------------------------------------------------------------------//
//  Wire declarations
//-----------------------------------------------------------------------------------//
wire    [15:0]                  cal_crc                             ;   
wire    [15:0]                  rx_crc                              ;   




//-----------------------------------------------------------------------------------//
//  Logic Function
//-----------------------------------------------------------------------------------//


//===================================================================================
// frame detect
//===================================================================================

//===================================================================================
// rx data 
//===================================================================================

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       data_shift       <= #U_DLY 16'h0;
    else if( data_i_val == 1'd1 )
       data_shift       <= #U_DLY {data_shift[7:0] , data_i}; 
end


always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
      wr_cnt    <= #U_DLY 8'd0; 
    else if(( data_i_val == 1'd1)  && (data_shift == FRAME_HEAD ))
      wr_cnt    <= #U_DLY 8'd1;
    else if(( data_i_val == 1'd1)  && (wr_cnt == 8'd5 ))
      wr_cnt    <= #U_DLY 8'd0;
     else if(( data_i_val == 1'd1 ) && (wr_cnt > 8'd0) )
      wr_cnt   <= #U_DLY wr_cnt + 8'd1;   
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       rx_frame_data[31:24]   <= #U_DLY  8'd0;
    else if( ( data_i_val == 1'd1)  && (data_shift == FRAME_HEAD ))
       rx_frame_data[31:24]   <= #U_DLY  data_i;
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       rx_frame_data[23:16]   <= #U_DLY  8'd0;
    else if((data_i_val == 1'd1 ) && ( wr_cnt == 8'd1))
       rx_frame_data[23:16]   <= #U_DLY  data_i;
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       rx_frame_data[15:8]   <= #U_DLY  8'd0;
    else if( (data_i_val == 1'd1 ) && ( wr_cnt == 8'd2))
       rx_frame_data[15:8]   <= #U_DLY  data_i;
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       rx_frame_data[7:0]   <= #U_DLY  8'd0;
    else if( (data_i_val == 1'd1 ) && ( wr_cnt == 8'd3))
       rx_frame_data[7:0]   <= #U_DLY  data_i;
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       rx_crc1[7:0]   <= #U_DLY  8'd0;
    else if( (data_i_val == 1'd1 ) && ( wr_cnt == 8'd4))
       rx_crc1[7:0]   <= #U_DLY  data_i;
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       rx_crc2[7:0]   <= #U_DLY  8'd0;
    else if( (data_i_val == 1'd1 ) && ( wr_cnt == 8'd5))
       rx_crc2[7:0]   <= #U_DLY  data_i;
end

assign rx_crc={rx_crc1,rx_crc2};



//===================================================================================
// crc_crl 
//===================================================================================

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'd0) begin
        data_i_val_dly     <= #U_DLY 1'd0 ;
    end
    else begin
        data_i_val_dly     <= #U_DLY data_i_val ;
    end
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'd0) begin
        data_i_dly     <= #U_DLY 8'd0 ;
    end
    else if( data_i_val == 1'd1) begin
        data_i_dly     <= #U_DLY data_i ;
    end
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       rx_eop   <= #U_DLY 1'd0;
    else if((data_i_val == 1'd1 ) && ( wr_cnt == 8'd3))
       rx_eop   <= #U_DLY 1'd1;
    else
       rx_eop   <= #U_DLY 1'd0; 
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       clc_crc   <= #U_DLY 1'd0;
    else if((data_i_val == 1'd1 ) && ( wr_cnt == 8'd5))
       clc_crc   <= #U_DLY 1'd1;
    else
       clc_crc   <= #U_DLY 1'd0; 
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'd0) begin
        rx_eop_1dly     <= #U_DLY 1'd0;
        rx_eop_2dly     <= #U_DLY 1'd0 ;
    end
    else begin
        rx_eop_1dly     <= #U_DLY rx_eop;
        rx_eop_2dly     <= #U_DLY rx_eop_1dly ;
    end
end


//===================================================================================
// crc check
//===================================================================================
always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       crc_check_ok     <= #U_DLY 1'd0;
    else if( (clc_crc == 1'd1) &&  ( cal_crc == rx_crc) )
       crc_check_ok     <= #U_DLY 1'd1;
    else
       crc_check_ok     <= #U_DLY 1'd0;
end

always @(posedge clk_sys )
begin
       rx_frame_done    <= #U_DLY clc_crc;
end

//===================================================================================
// check time out
//===================================================================================

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
       wait_cnt     <= #U_DLY 32'd0;
    else if((frame_send_en == 1'd0) || (rx_frame_done == 1'd1))
       wait_cnt     <= #U_DLY 32'd0;
    else
       wait_cnt    <= #U_DLY wait_cnt +32'd1;
end

always @(posedge clk_sys or negedge rst_n)
begin
    if(rst_n == 1'b0)
        remot_time_out  <= #U_DLY  1'd0;
    else if((frame_send_en == 1'd0) || (rx_frame_done == 1'd1))
        remot_time_out   <= #U_DLY 1'd0;
    else if(wait_cnt == ( BAUD_60MS - 1 ))
        remot_time_out  <= #U_DLY  1'd1;
    else
        ;
end


FCS16     U_FCS16
    (
    //input port
    .clk_sys                    ( clk_sys                   ),
    .rst_sys                    ( ~rst_n                    ),

    .crc_din                    ( data_i_dly                ),
    .crc_cap                    ( rx_eop                    ),
    .crc_sop                    ( clc_crc                   ),
    .crc_din_vld                ( data_i_val_dly            ),

    //output port
    .crc_dout                   ( cal_crc                  )
    );

endmodule 




