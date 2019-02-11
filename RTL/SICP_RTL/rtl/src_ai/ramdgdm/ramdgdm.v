// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-12-12
// DEPARTMENT       :   R&D
// AUTHOR           :   Zhang Yongjun
// AUTHOR'S EMAIL   :   zhangyongjun@cgnpc.com.cn
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-12-12  Zhang Yongjun       Original
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
`timescale 1 ns / 1 ps
`include "DEFINES.v"
module  RAMDGDM
    (
        clk_wr                  ,   
        rst_wr_n                ,   
        clk_rd                  ,   
        rst_rd_n                ,   

        slink_prd_err           ,   
        din_sop                 ,   
        din_eop                 ,   
        dout_sop                ,   
        dout_eop                ,   
        ram_din_val             ,   
        ram_dout_val            ,   
        ram_din_data            ,   
        ram_dout_data           ,   
 
        ram_dgd_err
    
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   CRC_LEN_L       = 10'h1     ;
parameter   CRC_LEN_H       = 10'h38    ;
parameter   FUN_SEL         = 1'b0      ; // distinguish sop from start 0x78 or 0xff
parameter   BIT_WIDTH       = 16        ;
parameter   RAM_DGD_TYPE    = 1'b0      ; // TX_RAM or RX_RAM
localparam  RAM_DGD_CNT     = 5'd5      ;
localparam  TX_RAM          = 1'b1      ;
localparam  RX_RAM          = 1'b0      ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input interface signal
input   wire                    rst_wr_n                            ;   
input   wire                    clk_wr                              ;   
input   wire                    rst_rd_n                            ;   
input   wire                    clk_rd                              ;   

input   wire                    din_sop                             ;   
input   wire                    din_eop                             ;   
input   wire                    dout_sop                            ;   
input   wire                    dout_eop                            ;   
input   wire                    ram_din_val                         ;   
input   wire                    ram_dout_val                        ;   
input   wire   [BIT_WIDTH-1:0]  ram_din_data                        ;   
input   wire   [BIT_WIDTH-1:0]  ram_dout_data                       ;   
input   wire                    slink_prd_err                       ;   
// output interface signal
output  reg                     ram_dgd_err                         ;   

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [15:0]                  din_crc_dout                        ;   
wire    [15:0]                  dout_crc_dout                       ;   
// reg signal
reg     [9:0]                   din_cnt                             ;   
reg                             din_crc_cap                         ;   
reg                             din_crc_cap_d1                      ;   
reg                             din_crc_cap_d2                      ;   
reg                             din_crc_sop                         ;   
reg     [4:0]                   dgd_err_cnt                         ;   
reg     [15:0]                  din_crc_value                       ;   
reg                             din_crc_vld                         ;   
reg     [BIT_WIDTH-1:0]         din_crc_din                         ;   
reg     [BIT_WIDTH-1:0]         dout_crc_din                        ;   
reg     [15:0]                  din_crc_value_d                     ;   
reg     [15:0]                  din_crc_value_d1                    ;   
reg     [15:0]                  din_crc_value_d2                    ;   
reg     [4:0]                   din_ftch_cnt                        ;   
reg     [15:0]                  din_ptk_type                        ;   
reg                             din_crc_en                          ;   
reg     [4:0]                   dout_ftch_cnt                       ;   
reg     [15:0]                  dout_ptk_type                       ;   
reg                             din_ftch_en                         ;   
reg                             dout_ftch_en                        ;   
reg                             dout_crc_en                         ;   
reg     [4:0]                   dgd_cnt                             ;   
reg                             dgd_trig                            ;   
reg                             dgd_err_trig                        ;   

reg     [9:0]                   dout_cnt                            ;   
reg                             dout_crc_cap                        ;   
reg                             dout_crc_cap_d1                     ;   
reg                             dout_crc_cap_d2                     ;   
reg                             dout_crc_sop                        ;   
reg                             dout_crc_vld                        ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// fetch the pkt_type form frame
//----------------------------------------------------------------------------------
always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        din_ftch_en <=   1'b0 ;
    end
    else begin
        if ( din_sop == 1'b1 ) begin
            din_ftch_en <=   1'b1 ;
        end
        else if ( din_eop == 1'b1 || FUN_SEL == 1'b0 ) begin
            din_ftch_en <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        din_ftch_cnt    <=   5'd0 ;
    end
    else begin
        if ( din_sop == 1'b1 ) begin
            din_ftch_cnt    <=   5'd0 ;
        end
        else if ( din_ftch_en == 1'b1 && ram_din_val == 1'b1 ) begin
            if ( din_ftch_cnt == 5'd16 ) begin
                din_ftch_cnt    <=   5'd16 ;
            end
            else begin
                din_ftch_cnt    <=   din_ftch_cnt + 1'b1 ;
            end
        end
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        din_ptk_type    <=   16'd0 ;
    end
    else begin
        if ( din_eop ==  1'b1 ) begin
            din_ptk_type    <=   16'd0 ;
        end
        else if ( din_ftch_en == 1'b1 && ram_din_val == 1'b1 ) begin
            if ( BIT_WIDTH == 8 ) begin
                if ( din_ftch_cnt == 5'd7 ) begin
                    din_ptk_type[15:8]    <=   ram_din_data ;
                end
                else if ( din_ftch_cnt == 5'd8 ) begin
                    din_ptk_type[7:0]    <=   ram_din_data ;
                end
            end
            else if ( BIT_WIDTH == 16 ) begin
                if ( din_ftch_cnt == 5'd3 ) begin
                    din_ptk_type    <=   ram_din_data ;
                end
            end
        end
    end
end

//----------------------------------------------------------------------------------
// cuculate the CRC in write to ram of down data stream
//----------------------------------------------------------------------------------
always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        din_cnt <=   10'd0 ;
    end
    else begin
        if ( din_eop == 1'b1 && FUN_SEL == 1'b1 ) begin
            din_cnt <=   1'b0 ;
        end
        else if ( ram_din_val == 1'b1 && (( din_ptk_type == `DATA_TYPE && FUN_SEL == 1'b1) || FUN_SEL == 1'b0 )) begin
            din_cnt <=   din_cnt + 1'b1 ;
        end
        else if ( FUN_SEL == 1'b0 ) begin
            din_cnt <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        din_crc_din <=   { BIT_WIDTH{1'b0} } ;
    end
    else begin
        din_crc_din <=   ram_din_data ;
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        din_crc_en  <=   1'b0 ;
    end
    else begin
        if ( din_cnt == 10'd4 && BIT_WIDTH == 8 || din_cnt == 10'd1 && BIT_WIDTH == 16 ) begin
            din_crc_en  <=   1'b1 ;
        end
        else if ( ( din_sop == 1'b1 || din_eop == 1'b1 ) && RAM_DGD_TYPE == RX_RAM ) begin
            din_crc_en  <=   1'b0 ;
        end
        else if ( din_cnt == CRC_LEN_H && (RAM_DGD_TYPE == TX_RAM || RAM_DGD_TYPE == RX_RAM) ) begin
            din_crc_en  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        din_crc_vld  <=   1'b0 ;
    end
    else begin
        if ( FUN_SEL == 1'b0 ) begin
            if ( din_sop == 1'b1 ) begin
                din_crc_vld  <=   1'b1 ;
            end
            else if ( din_cnt == CRC_LEN_H ) begin
                din_crc_vld  <=   1'b0 ;
            end
        end
        else begin
            if ( din_ptk_type == `DATA_TYPE && din_crc_en  == 1'b1 ) begin
                din_crc_vld  <=   ram_din_val ;
            end
            else begin
                din_crc_vld <=   1'b0 ;
            end
        end
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        din_crc_cap   <=   1'b0 ;
    end
    else begin
        if ( din_cnt == CRC_LEN_H - 1'b1 && din_crc_vld == 1'b1 && RAM_DGD_TYPE == TX_RAM ) begin
            din_crc_cap  <=   1'b1 ;
        end
        else if ( din_cnt == CRC_LEN_H - 1'b1 && ram_din_val == 1'b1 && RAM_DGD_TYPE == RX_RAM ) begin
            din_crc_cap  <=   1'b1 ;
        end
        else begin
            din_crc_cap  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        din_crc_cap_d1  <=   1'b0 ;
    end
    else begin
        din_crc_cap_d1  <=   din_crc_cap ;
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        din_crc_cap_d2  <=   1'b0 ;
    end
    else begin
        din_crc_cap_d2  <=   din_crc_cap_d1 ;
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        din_crc_sop   <=   1'b0 ;
    end
    else begin
        din_crc_sop   <=   din_crc_cap_d2 ;
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        din_crc_value   <=   16'd0 ;
    end
    else begin
        if ( din_crc_cap_d2 == 1'b1 ) begin
            din_crc_value    <=   din_crc_dout[15:0] ;
        end
    end
end

generate
if( RAM_DGD_TYPE == RX_RAM ) begin

    IO_FCS16                       U_RAM_INCRC
    (
    //input port
    .clk_sys                    ( clk_wr                    ),
    .rst_sys_n                  ( rst_wr_n                  ),

    .crc_din                    ( din_crc_din               ),
    .crc_cap                    ( din_crc_cap               ),
    .crc_sop                    ( din_crc_sop               ),
    .crc_din_vld                ( din_crc_vld               ),

    //output port
    .crc_dout                   ( din_crc_dout              )
    );

end
endgenerate

generate
if( RAM_DGD_TYPE == TX_RAM ) begin
    IO_CRC16D16                    U_RAM_INCRC
    (
    //input port
    .clk_sys                    ( clk_wr                    ),
    .rst_sys_n                  ( rst_wr_n                  ),

    .crc_din                    ( din_crc_din               ),
    .crc_cap                    ( din_crc_cap               ),
    .crc_sop                    ( din_crc_sop               ),
    .crc_din_vld                ( din_crc_vld               ),

    //output port
    .crc_dout                   ( din_crc_dout              )
    );
end
endgenerate
//----------------------------------------------------------------------------------
// cuculate the CRC in write to ram of down data stream
//----------------------------------------------------------------------------------
always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        dout_ftch_en <=   1'b0 ;
    end
    else begin
        if ( dout_sop == 1'b1 ) begin
            dout_ftch_en <=   1'b1 ;
        end
        else if ( dout_eop == 1'b1 || FUN_SEL == 1'b0 ) begin
            dout_ftch_en <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        dout_ftch_cnt    <=   5'd0 ;
    end
    else begin
        if ( dout_sop == 1'b1 ) begin
            dout_ftch_cnt    <=   5'd0 ;
        end
        else if ( dout_ftch_en == 1'b1 && ram_dout_val == 1'b1 ) begin
            if ( dout_ftch_cnt == 5'd16 ) begin
                dout_ftch_cnt    <=   5'd16 ;
            end
            else begin
                dout_ftch_cnt    <=   dout_ftch_cnt + 1'b1 ;
            end
        end
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        dout_ptk_type    <=   16'd0 ;
    end
    else begin
        if ( dout_eop ==  1'b1 ) begin
            dout_ptk_type    <=   16'd0 ;
        end
        else if ( dout_ftch_en == 1'b1 && ram_dout_val == 1'b1 ) begin
            if ( BIT_WIDTH == 8 ) begin
                if ( dout_ftch_cnt == 5'd7 ) begin
                    dout_ptk_type[15:8]    <=   ram_dout_data ;
                end
                else if ( dout_ftch_cnt == 5'd8 ) begin
                    dout_ptk_type[7:0]    <=   ram_dout_data ;
                end
            end
            else if ( BIT_WIDTH == 16 ) begin
                if ( dout_ftch_cnt == 5'd3 ) begin
                    dout_ptk_type    <=   ram_dout_data ;
                end
            end
        end
    end
end

//----------------------------------------------------------------------------------
// cuculate the CRC in write to ram of down data stream
//----------------------------------------------------------------------------------
always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        dout_cnt <=   10'd0 ;
    end
    else begin
        if ( dout_eop == 1'b1 && FUN_SEL == 1'b1 ) begin
            dout_cnt <=   1'b0 ;
        end
        else if ( ram_dout_val == 1'b1 && (( dout_ptk_type == `DATA_TYPE && FUN_SEL == 1'b1) || FUN_SEL == 1'b0 )) begin
            dout_cnt <=   dout_cnt + 1'b1 ;
        end
        else if ( FUN_SEL == 1'b0 ) begin
            dout_cnt <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        dout_crc_din <=   { BIT_WIDTH{1'b0} } ;
    end
    else begin
        dout_crc_din <=   ram_dout_data ;
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        dout_crc_en  <=   1'b0 ;
    end
    else begin
        if ( (BIT_WIDTH == 8 && dout_cnt == 10'd3&&FUN_SEL==1'b1) || dout_cnt == 10'd2 && BIT_WIDTH == 16 ) begin
            dout_crc_en  <=   1'b1 ;
        end
        else if ( ( dout_sop == 1'b1 || dout_eop == 1'b1 ) && RAM_DGD_TYPE == RX_RAM ) begin
            dout_crc_en  <=   1'b0 ;
        end
        else if ( dout_cnt == CRC_LEN_H && ( RAM_DGD_TYPE == TX_RAM || RAM_DGD_TYPE == RX_RAM ) ) begin
            dout_crc_en  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_wr or negedge rst_wr_n ) begin
    if( rst_wr_n == 1'b0 ) begin
        dout_crc_vld  <=   1'b0 ;
    end
    else begin
        if ( FUN_SEL == 1'b0 ) begin
            if ( dout_sop == 1'b1 ) begin
                dout_crc_vld  <=   1'b1 ;
            end
            else if ( dout_cnt == CRC_LEN_H ) begin
                dout_crc_vld  <=   1'b0 ;
            end
        end
        else begin
            if ( dout_ptk_type == `DATA_TYPE && dout_crc_en  == 1'b1 ) begin
                dout_crc_vld  <=   ram_dout_val ;
            end
            else begin
                dout_crc_vld <=   1'b0 ;
            end
        end
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        dout_crc_cap   <=   1'b0 ;
    end
    else begin
        if ( ( dout_cnt == CRC_LEN_H - 1'b1)  && (( dout_crc_vld == 1'b0 && RAM_DGD_TYPE == TX_RAM ) || RAM_DGD_TYPE == RX_RAM) ) begin
            dout_crc_cap  <=   1'b1 ;
        end
        else begin
            dout_crc_cap  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        dout_crc_cap_d1  <=   1'b0 ;
    end
    else begin
        dout_crc_cap_d1  <=   dout_crc_cap ;
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        dout_crc_cap_d2  <=   1'b0 ;
    end
    else begin
        dout_crc_cap_d2  <=   dout_crc_cap_d1 ;
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        dout_crc_sop   <=   1'b0 ;
    end
    else begin
        dout_crc_sop   <=   dout_crc_cap_d2 ;
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        din_crc_value_d <=   16'd0 ;
    end
    else begin
        din_crc_value_d   <=   din_crc_value ;
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        din_crc_value_d1 <=   16'd0 ;
    end
    else begin
        din_crc_value_d1   <=   din_crc_value_d ;
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        din_crc_value_d2 <=   16'd0 ;
    end
    else begin
        din_crc_value_d2   <=   din_crc_value_d1 ;
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        dgd_err_cnt   <=   5'd0 ;
    end
    else begin
        if ( dout_crc_cap_d2 == 1'b1 && dout_crc_dout != din_crc_value_d2 && slink_prd_err == 1'b0 ) begin
            if ( dgd_err_cnt == RAM_DGD_CNT ) begin
                dgd_err_cnt <=   RAM_DGD_CNT ;
            end
            else begin
                dgd_err_cnt   <=   dgd_err_cnt + 1'b1 ;
            end
        end
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        dgd_trig   <=   1'b0 ;
    end
    else begin
        if ( dout_crc_cap_d2 == 1'b1 && dout_crc_dout != din_crc_value_d2 ) begin
            dgd_trig    <=   1'b1 ;
        end
        else begin
            dgd_trig    <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        dgd_cnt   <=   5'd0 ;
    end
    else begin
        if ( dout_crc_cap_d2 == 1'b1 && dout_crc_dout != din_crc_value_d2 ) begin
            if ( dgd_cnt == RAM_DGD_CNT ) begin
                dgd_cnt <=   RAM_DGD_CNT ;
            end
            else begin
                dgd_cnt   <=   dgd_cnt + 1'b1 ;
            end
        end
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        dgd_err_trig   <=   1'b0 ;
    end
    else begin
        if ( dout_crc_cap_d2 == 1'b1 && dout_crc_dout != din_crc_value_d2 && slink_prd_err == 1'b0 ) begin
            dgd_err_trig    <=   1'b1 ;
        end
        else begin
            dgd_err_trig    <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_rd or negedge rst_rd_n ) begin
    if( rst_rd_n == 1'b0 ) begin
        ram_dgd_err <=   1'b0 ;
    end
    else begin
        if ( dgd_err_cnt == RAM_DGD_CNT ) begin
            ram_dgd_err <=   1'b1 ;
        end
    end
end

generate
if( RAM_DGD_TYPE == RX_RAM ) begin

    IO_FCS16                       U_RAM_INCRC
    (
    //input port
    .clk_sys                    ( clk_rd                    ),
    .rst_sys_n                  ( rst_rd_n                  ),
                                                
    .crc_din                    ( dout_crc_din              ),
    .crc_cap                    ( dout_crc_cap              ),
    .crc_sop                    ( dout_crc_sop              ),
    .crc_din_vld                ( dout_crc_vld              ),
                                                
    //output port                               
    .crc_dout                   ( dout_crc_dout             )
    );

end
endgenerate

generate
if( RAM_DGD_TYPE == TX_RAM ) begin
    IO_CRC16D16                    U_RAM_INCRC
    (
    //input port
    .clk_sys                    ( clk_rd                    ),
    .rst_sys_n                  ( rst_rd_n                  ),
                                                
    .crc_din                    ( dout_crc_din              ),
    .crc_cap                    ( dout_crc_cap              ),
    .crc_sop                    ( dout_crc_sop              ),
    .crc_din_vld                ( dout_crc_vld              ),
                                                
    //output port                               
    .crc_dout                   ( dout_crc_dout             )
    );
end
endgenerate


endmodule
