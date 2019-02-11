// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-06-10
// DEPARTMENT       :   R&D
// AUTHOR           :   YongjunZhang
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-06-10  YongjunZhang        Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active hign
// Clock Domains    :   clk_125m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`include "DEFINES.v"
`define BOARD_ADDR      = 8'b00010000 ;

module WR_EEPROM
(   
        rst_sys_n               ,   
        clk_sys                 ,   
    
        cur_state               ,   
        rx_cnt                  ,   
        uart_rx_ren             ,   
        uart_rx_rdata           ,   
        data_fun_sel            ,   

        acq_data_trig           , 
        acq_data_sel            ,
        cal_ch_index            ,   
        acq_ch_num              ,   
        kb_crc_trig             ,   
        rd_en                   ,
        wr_en                   ,   
        wr_value0               ,   
        wr_value1               ,   
        wr_value2               ,   
        wr_value3               ,   
        wr_addr                 ,   
        wr_done                 ,   
        e2p_busy                   

 );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
localparam  IDLE        =   12'b000000000000  ;
localparam  FUN_SEL     =   12'b000000000010  ;
localparam  RD_FST      =   12'b000000000100  ;
localparam  RD_SCD      =   12'b000000001000  ;
localparam  RD_THD      =   12'b000000010000  ;
localparam  RD_FTH      =   12'b000000100000  ;
localparam  CRC_DLY     =   12'b000001000000  ;
localparam  FUN_SUS     =   12'b000010000000  ;
localparam  FUN_ERR     =   12'b000100000000  ;

localparam  WR_IDLE     =   5'b00000 ;
localparam  WR_RDY      =   5'b00001 ;
localparam  WR_CH       =   5'b00010 ;
localparam  WR_K        =   5'b00100 ;
localparam  WR_B        =   5'b01000 ;
localparam  WR_CRC      =   5'b10000 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire    [11:0]          cur_state                           ;   
input   wire                    uart_rx_ren                         ;   
input   wire    [7:0]           uart_rx_rdata                       ;   
input   wire                    wr_done                             ;   
input   wire                    e2p_busy                            ;   
input   wire    [1:0]           rx_cnt                              ;   
input   wire    [2:0]           data_fun_sel                        ;   
// declare input singal
output  reg                     wr_en                               ;   
output  reg     [31:0]          wr_value0                           ;   
output  reg     [31:0]          wr_value1                           ;   
output  reg     [31:0]          wr_value2                           ;   
output  reg     [31:0]          wr_value3                           ;   
output  reg     [15:0]          wr_addr                             ;   
output  reg                     kb_crc_trig                         ;   
output  reg                     rd_en                               ;
output  reg                     acq_data_trig                       ;   
output  reg     [7:0]           acq_ch_num                          ;   
output  reg     [1:0]           acq_data_sel                        ;   
output  reg     [11:0]          cal_ch_index                        ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [15:0]                  crc_dout                            ;
wire                            ch_vld                              ;
wire                            acqcmd_vld                          ;
wire                            kdata_vld                           ;   
wire                            bdata_vld                           ;   
wire                            crc_vld                             ;
// reg signal
reg     [31:0]                  cal_kcoe                            ;   
reg     [31:0]                  cal_bcoe                            ;   
reg     [15:0]                  con_addr                            ;   
reg     [7:0]                   crc_din                             ;   
reg                             crc_din_vld                         ;   
reg                             crc_eop                             ;   
reg                             crc_eop_d1                          ;   
reg     [15:0]                  crc_data                            ;   
reg                             crc_sop                             ;   
reg     [15:0]                  crc_value                           ;   
reg     [4:0]                   crc_dly_cnt                         ;   
reg     [31:0]                  acq_chn_value                       ;   
reg                             rd_trig                             ;
reg                             crc_cmp_en                          ;   
/**********************************************************************************\
******************************** debug code ****************************************
                                                                        
/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign  ch_vld          = ( cur_state == RD_FST && uart_rx_ren == 1'b1 ) ? 1'b1 : 1'b0 ;
assign  kdata_vld       = ( cur_state == RD_SCD && uart_rx_ren == 1'b1 && data_fun_sel == 3'b001 ) ? 1'b1 : 1'b0 ;
assign  bdata_vld       = ( cur_state == RD_THD && uart_rx_ren == 1'b1 && data_fun_sel == 3'b001 ) ? 1'b1 : 1'b0 ;
assign  crc_vld         = ( cur_state == RD_FTH && uart_rx_ren == 1'b1 ) ? 1'b1 : 1'b0 ;
assign  acqcmd_vld      = ( cur_state == RD_SCD && uart_rx_ren == 1'b1 && data_fun_sel == 3'b011 ) ? 1'b1 : 1'b0 ;

//----------------------------------------------------------------------------------
// recieve the parameter of calibrate number
//----------------------------------------------------------------------------------

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        con_addr <=  16'd0;
    end
    else begin
        if ( ch_vld == 1'b1 ) begin
            if ( rx_cnt == 2'd0 ) begin
                con_addr[7:0] <=  uart_rx_rdata ;
            end
            else if ( rx_cnt == 2'd1 ) begin
                con_addr[15:8] <=  uart_rx_rdata ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        acq_ch_num <=  8'd0;
    end
    else begin
        acq_ch_num[7:0] <=  con_addr[7:0] ;
    end
end
//----------------------------------------------------------------------------------
// recieve the parameter of calibrate K coe
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_kcoe <=  32'd0;
    end
    else begin
        if ( kdata_vld == 1'b1 ) begin
            if ( rx_cnt == 2'd0 ) begin
                cal_kcoe[7:0] <=  uart_rx_rdata ;
            end
            else if ( rx_cnt == 2'd1 ) begin
                cal_kcoe[15:8] <=  uart_rx_rdata ;
            end
            else if ( rx_cnt == 2'd2 ) begin
                cal_kcoe[23:16] <=  uart_rx_rdata ;
            end
            else if ( rx_cnt == 2'd3 ) begin
                cal_kcoe[31:24] <=  uart_rx_rdata ;
            end
            else ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// recieve the parameter of calibrate K coe
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_bcoe <=  32'd0;
    end
    else begin
        if ( bdata_vld == 1'b1 ) begin
            if ( rx_cnt == 2'd0 ) begin
                cal_bcoe[7:0] <=  uart_rx_rdata ;
            end
            else if ( rx_cnt == 2'd1 ) begin
                cal_bcoe[15:8] <=  uart_rx_rdata ;
            end
            else if ( rx_cnt == 2'd2 ) begin
                cal_bcoe[23:16] <=  uart_rx_rdata ;
            end
            else if ( rx_cnt == 2'd3 ) begin
                cal_bcoe[31:24] <=  uart_rx_rdata ;
            end
            else ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// the commond of acquire channel data
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        acq_chn_value <= 32'd0;
    end
    else begin
        if ( acqcmd_vld == 1'b1 ) begin
            if ( rx_cnt == 2'd0 ) begin
                acq_chn_value[7:0] <= uart_rx_rdata ;
            end
            else if ( rx_cnt == 2'd1 ) begin
                acq_chn_value[15:8] <= uart_rx_rdata ;
            end
            else if ( rx_cnt == 2'd2 ) begin
                acq_chn_value[23:16] <= uart_rx_rdata ;
            end
            else if ( rx_cnt == 2'd3 ) begin
                acq_chn_value[31:24] <= uart_rx_rdata ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        acq_data_sel    <=   2'b00 ;
    end
    else begin
        if ( acq_chn_value == 32'h00000011 ) begin
            acq_data_sel    <=   2'b01 ; // calibrate data
        end
        else if ( acq_chn_value == 32'h00000022 ) begin
            acq_data_sel    <=   2'b10 ; // con dac data
        end
        else if ( acq_chn_value == 32'h00000033 ) begin
            acq_data_sel    <=   2'b11 ; // memery data
        end
        else begin
            acq_data_sel    <=   2'b00 ;
        end
    end
end

//----------------------------------------------------------------------------------
// recieve the parameter of calibrate K coe
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_data <=  16'd0;
    end
    else begin
        if ( crc_vld == 1'b1 ) begin
            if ( rx_cnt == 2'd0 ) begin
                crc_data[7:0] <=  uart_rx_rdata ;
            end
            else if ( rx_cnt == 2'd1 ) begin
                crc_data[15:8] <=  uart_rx_rdata ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_dly_cnt <=   5'd0 ;
    end
    else begin
        if ( cur_state == CRC_DLY ) begin
            if ( crc_dly_cnt == 5'd20 ) begin
                crc_dly_cnt <= 5'd0 ;
            end
            else begin
                crc_dly_cnt <=   crc_dly_cnt + 1'b1 ;
            end
        end
        else begin
            crc_dly_cnt <=   5'd0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_cmp_en  <=   1'b0 ;
    end
    else begin
        if ( cur_state == CRC_DLY && crc_dly_cnt == 5'd3 ) begin
            crc_cmp_en  <=   1'b1 ;
        end
        else begin
            crc_cmp_en  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        acq_data_trig <=   1'b0 ;
    end
    else begin
        if ( crc_cmp_en == 1'b1 && data_fun_sel == 3'b011 && acq_data_sel == 2'b01 ) begin
            if ( crc_value == crc_data ) begin
                acq_data_trig <=   1'b1 ;
            end
            else begin
                acq_data_trig <=   1'b0 ;
            end
        end
        else begin
            acq_data_trig  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_trig <=   1'b0 ;
    end
    else begin
        if ( crc_cmp_en == 1'b1 && data_fun_sel == 3'b011 && acq_data_sel == 2'b11 ) begin
            if ( crc_value == crc_data ) begin
                rd_trig <=   1'b1 ;
            end
            else begin
                rd_trig <=   1'b0 ;
            end
        end
        else begin
            rd_trig  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        kb_crc_trig <=   1'b0 ;
    end
    else begin
        if ( cur_state == CRC_DLY && crc_dly_cnt == 5'd3 && data_fun_sel == 3'b001 ) begin
            if ( crc_value == crc_data ) begin
                kb_crc_trig <=   1'b1 ;
            end
            else begin
                kb_crc_trig <=   1'b0 ;
            end
        end
        else begin
            kb_crc_trig  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_en <=   1'b0 ;
    end
    else begin
        rd_en <=   rd_trig ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_addr    <=  16'h0000 ;
    end
    else begin
        if ( kb_crc_trig == 1'b1 ) begin
            wr_addr    <=  con_addr << 4 ;
        end
        else if ( rd_trig == 1'b1 ) begin
            wr_addr    <=  con_addr << 2 ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_ch_index    <=   12'd0 ;
    end
    else begin
        if ( acq_data_trig == 1'b1 ) begin
            cal_ch_index    <=  ( 1 << acq_ch_num[3:0] ) ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_en    <=  1'b0 ;
    end
    else begin
        if ( kb_crc_trig == 1'b1 ) begin
            wr_en    <= 1'b1 ;
        end
        else begin
            wr_en   <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_value0    <=  32'h00000000 ;
    end
    else begin
        if ( kb_crc_trig == 1'b1 ) begin
            wr_value0    <= { 16'h0000 , con_addr } ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_value1    <=  32'h00000000 ;
    end
    else begin
        if ( kb_crc_trig == 1'b1 ) begin
            wr_value1    <= cal_kcoe ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_value2    <=  32'h00000000 ;
    end
    else begin
        if ( kb_crc_trig == 1'b1 ) begin
            wr_value2    <= cal_bcoe ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_value3    <=  32'h00000000 ;
    end
    else begin
        if ( kb_crc_trig == 1'b1 ) begin
            wr_value3    <= crc_data ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// read data form eeprom to CRC
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_din <=   8'd0 ;
    end
    else begin
        if ( cur_state == RD_FST || cur_state == RD_SCD || cur_state == RD_THD ) begin 
            crc_din <=   uart_rx_rdata ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_din_vld <=   1'b0 ;
    end
    else begin
        if ( cur_state == RD_FST || cur_state == RD_SCD || cur_state == RD_THD ) begin
            crc_din_vld <=   uart_rx_ren ;
        end
        else begin
            crc_din_vld <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_sop <=   1'b0 ;
    end
    else begin
        if ( cur_state == CRC_DLY ) begin
            crc_sop <=   1'b1 ;
        end
        else begin
            crc_sop <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_eop <=   1'b0 ;
    end
    else begin
        if ( cur_state == RD_THD && uart_rx_ren == 1'b1 && rx_cnt == 2'd3 ) begin
            crc_eop <=   1'b1 ;
        end
        else begin
            crc_eop <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_eop_d1 <= 1'b0 ;  
    end
    else begin
        crc_eop_d1  <=   crc_eop ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_value <= 16'h0000 ;  
    end
    else begin
        if ( crc_eop_d1 == 1'b1 ) begin
            crc_value  <=   crc_dout ;
        end
        else ;
    end
end

    IO_FCS16                       U_FCS16
    (
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),

    .crc_din                    ( crc_din                   ),
    .crc_cap                    ( crc_eop                   ),
    .crc_sop                    ( crc_eop_d1                ),
    .crc_din_vld                ( crc_din_vld               ),

    .crc_dout                   ( crc_dout                  )
    );

endmodule
