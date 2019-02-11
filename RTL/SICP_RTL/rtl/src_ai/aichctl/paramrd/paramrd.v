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
//============================================================================
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
`timescale 1 ns / 1 ns
`include "DEFINES.v"

module PARAMRD 
(
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 
        
        // input signal
        e2p_paramrd_en          ,   
        e2p_reg_addr            ,   
        e2p_rd_dval             ,   
        e2p_rd_value            ,   
        e2p_busy                ,   
        e2p_con_done            ,   // the parameter of calibrate in done 

        e2p_rw_sel              ,  // juged in the model of calibrate 
        param_rd_done           ,   
        param_crc_err           ,   
        param_rd_en             ,   

        b_factor0               ,   
        b_factor1               ,   
        b_factor2               ,   
        b_factor3               ,   
        b_factor4               ,   
        b_factor5               ,  
        b_factor6               ,   
        b_factor7               ,   
        b_factor8               ,   
        b_factor9               ,   
        b_factor10              ,   
        b_factor11              ,

        k_factor0               ,   
        k_factor1               ,   
        k_factor2               ,   
        k_factor3               ,   
        k_factor4               ,   
        k_factor5               , 
        k_factor6               ,   
        k_factor7               ,   
        k_factor8               ,   
        k_factor9               ,   
        k_factor10              ,   
        k_factor11              

);

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
`ifdef SIM
    localparam  PWN_DLY         =   16'd200    ;
`else
    localparam  PWN_DLY         =   16'd65000    ;
`endif

localparam  IDLE        = 12'b000000000000    ;
localparam  RD_TRIG     = 12'b000000000011    ;
localparam  RD_RDY      = 12'b000000000001    ;
localparam  RD_CHN      = 12'b000000000010    ;
localparam  WRH_CRC     = 12'b000000000100    ;
localparam  RD_K        = 12'b000000001000    ;
localparam  WRK_CRC     = 12'b000000010000    ;
localparam  RD_B        = 12'b000000100000    ;
localparam  WRB_CRC     = 12'b000001000000    ;
localparam  RD_CRC      = 12'b000010000000    ;
localparam  CRC_CMP     = 12'b000100000000    ;
localparam  CH_NEXT     = 12'b001000000000    ;
localparam  RD_CPL      = 12'b010000000000    ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input ineterface signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;    
input   wire                    e2p_rd_dval                         ;   
input   wire    [31:0]          e2p_rd_value                        ;   
input   wire                    e2p_busy                            ;   
input   wire                    e2p_con_done                        ;   
input   wire                    e2p_rw_sel                          ;   
// output ineterface signal
output  reg     [15:0]          e2p_reg_addr                        ;   
output  reg                     e2p_paramrd_en                      ;   
output  reg                     param_rd_done                       ;   
output  reg     [11:0]          param_crc_err                       ;   
output  reg     [31:0]          b_factor0                           ;   
output  reg     [31:0]          b_factor1                           ;   
output  reg     [31:0]          b_factor2                           ;   
output  reg     [31:0]          b_factor3                           ;   
output  reg     [31:0]          b_factor4                           ;   
output  reg     [31:0]          b_factor5                           ;   
output  reg     [31:0]          b_factor6                           ;   
output  reg     [31:0]          b_factor7                           ;   
output  reg     [31:0]          b_factor8                           ;   
output  reg     [31:0]          b_factor9                           ;   
output  reg     [31:0]          b_factor10                          ;   
output  reg     [31:0]          b_factor11                          ; 

output  reg     [31:0]          k_factor0                           ;   
output  reg     [31:0]          k_factor1                           ;   
output  reg     [31:0]          k_factor2                           ;   
output  reg     [31:0]          k_factor3                           ; 
output  reg     [31:0]          k_factor4                           ;   
output  reg     [31:0]          k_factor5                           ; 
output  reg     [31:0]          k_factor6                           ;   
output  reg     [31:0]          k_factor7                           ;   
output  reg     [31:0]          k_factor8                           ;   
output  reg     [31:0]          k_factor9                           ; 
output  reg     [31:0]          k_factor10                          ;   
output  reg     [31:0]          k_factor11                          ; 
output  reg                     param_rd_en                         ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [15:0]                  crc_dout                            ; 
wire    [15:0]                  cal_chnk_addr                       ; 
wire    [15:0]                  cal_chnh_addr                       ; 
wire    [15:0]                  cal_chnb_addr                       ;   
wire    [15:0]                  cal_chnc_addr                       ; 
// reg signal
reg     [15:0]                  pwn_dly_cnt                         ;   
reg     [6:0]                   dly_us                              ;   
reg     [1:0]                   wr_cnt                              ;   
reg     [3:0]                   rd_ch_cnt                           ;   
reg     [11:0]                  cur_state                           ;   
reg     [11:0]                  next_state                          ;   
reg     [7:0]                   crc_din                             ;   
reg                             crc_din_vld                         ;   
reg                             crc_eop                             ;   
reg                             crc_eop_d1                          ;   
reg                             crc_eop_d2                          ;   
reg     [15:0]                  crc_data                            ;   
reg     [11:0]                  ch_crc_err                          ;   
reg     [4:0]                   rd_chn_num                          ;   
reg     [11:0]                  chn_num_err                         ;   
reg     [31:0]                  k_factor                            ;   
reg     [31:0]                  b_factor                            ;  

// test
reg     [15:0]                  rd_dly_cnt                          ;   
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// power on to delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dly_us  <=   7'd0 ;
    end
    else begin
        if (  e2p_con_done == 1'b1 ) begin //param_con_done == 1'b1 &&
            if ( dly_us == 7'd99 ) begin
                dly_us  <=   7'd0 ;
            end
            else begin
                dly_us  <=   dly_us + 1'b1 ;
            end
        end
        else begin
            dly_us  <=   7'd0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        param_rd_en <=   1'b0 ;
    end
    else begin
        if ( cur_state == IDLE && pwn_dly_cnt == PWN_DLY ) begin
            param_rd_en <=   1'b1 ;
        end
        else if ( cur_state == RD_CPL ) begin
            param_rd_en <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pwn_dly_cnt <=   16'd0 ;
    end
    else begin
        if ( dly_us == 7'd99 ) begin
            if ( pwn_dly_cnt == PWN_DLY ) begin
                pwn_dly_cnt <=   PWN_DLY ;
            end
            else begin
                pwn_dly_cnt <=   pwn_dly_cnt + 1'b1 ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cur_state <= IDLE ;
    end
    else begin
        cur_state <= next_state ;
    end
end

always @ ( * ) begin
    case ( cur_state )
        IDLE : begin
            if ( pwn_dly_cnt == PWN_DLY ) begin
                next_state = RD_RDY ;
            end
            else begin
                next_state = IDLE ;
            end
        end
        RD_RDY : begin
            next_state = RD_CHN ;
        end
        RD_CHN : begin
            if ( e2p_rd_dval == 1'b1 ) begin
                next_state = WRH_CRC ;
            end
            else begin
                next_state = RD_CHN ;
            end
        end
        WRH_CRC : begin
            if ( wr_cnt == 2'd3 ) begin
                next_state = RD_K ;
            end
            else begin
                next_state = WRH_CRC ;
            end
        end
        RD_K : begin
            if ( e2p_rd_dval == 1'b1 ) begin
                next_state = WRK_CRC ;
            end
            else begin
                next_state = RD_K ;
            end
        end
        WRK_CRC : begin
            if ( wr_cnt == 2'd3 ) begin
                next_state = RD_B ;
            end
            else begin
                next_state = WRK_CRC ;
            end
        end
        RD_B : begin
            if ( e2p_rd_dval == 1'b1 ) begin
                next_state = WRB_CRC ;
            end
            else begin
                next_state = RD_B ;
            end
        end
        WRB_CRC : begin
            if ( wr_cnt == 2'd3 ) begin
                next_state = RD_CRC ;
            end
            else begin
                next_state = WRB_CRC ;
            end
        end
        RD_CRC : begin
            if ( e2p_rd_dval == 1'b1 ) begin
                next_state = CRC_CMP ;
            end
            else begin
                next_state = RD_CRC ;
            end
        end
        CRC_CMP : begin
            next_state = CH_NEXT ;
        end
        CH_NEXT : begin
            if ( rd_ch_cnt == 4'd11 ) begin
                next_state = RD_CPL ;
            end
            else begin
                next_state = RD_RDY ;
            end
        end
        RD_CPL : begin
            next_state = RD_CPL ;
        end
        default : begin
            next_state = IDLE ;
        end
    endcase
end

assign cal_chnh_addr =  rd_ch_cnt << 4 ;
assign cal_chnk_addr =  ( rd_ch_cnt << 4 ) + 16'd4 ;
assign cal_chnb_addr =  ( rd_ch_cnt << 4 ) + 16'd8 ;
assign cal_chnc_addr =  ( rd_ch_cnt << 4 ) + 16'd12 ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        e2p_paramrd_en   <=   1'b0 ;
    end
    else begin
        if ( cur_state == RD_RDY ) begin
            e2p_paramrd_en   <=   1'b1 ;
        end
        else if ( cur_state == WRH_CRC && wr_cnt == 2'd3 ) begin
            e2p_paramrd_en   <=   1'b1 ;
        end
        else if ( cur_state == WRK_CRC && wr_cnt == 2'd3 ) begin
            e2p_paramrd_en   <=   1'b1 ;
        end
        else if ( cur_state == WRB_CRC && wr_cnt == 2'd3 ) begin
            e2p_paramrd_en   <=   1'b1 ;
        end
        else begin
            e2p_paramrd_en   <=   1'b0 ;
        end
    end
end


always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        e2p_reg_addr    <=  16'h0000 ;
    end
    else begin
        if ( cur_state == RD_RDY ) begin
            e2p_reg_addr    <= `CAL_BASE_ADDR + cal_chnh_addr ;
        end
        else if ( cur_state == WRH_CRC && wr_cnt == 2'd3 ) begin
            e2p_reg_addr    <= `CAL_BASE_ADDR + cal_chnk_addr ;
        end
        else if ( cur_state == WRK_CRC && wr_cnt == 2'd3 ) begin
            e2p_reg_addr    <= `CAL_BASE_ADDR + cal_chnb_addr ;
        end
        else if ( cur_state == WRB_CRC && wr_cnt == 2'd3 ) begin
            e2p_reg_addr    <= `CAL_BASE_ADDR + cal_chnc_addr ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_chn_num   <=   5'b00000 ;
    end
    else begin
        if ( e2p_rd_dval == 1'b1 && cur_state == RD_CHN ) begin
            rd_chn_num   <=   e2p_rd_value[4:0] ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        chn_num_err <=   12'h000 ;
    end
    else begin
        if ( cur_state == WRH_CRC ) begin
            if ( rd_chn_num != rd_ch_cnt ) begin
                chn_num_err[rd_ch_cnt] <=  1'b1 ;
            end
            else begin
                chn_num_err[rd_ch_cnt] <= 1'b0 ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor   <=   32'h00000000 ;
    end
    else begin
        if ( e2p_rd_dval == 1'b1 && cur_state == RD_K ) begin
            k_factor   <=   e2p_rd_value ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor   <=   32'h00000000 ;
    end
    else begin
        if ( e2p_rd_dval == 1'b1 && cur_state == RD_B ) begin
            b_factor   <=  e2p_rd_value ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor0   <=   32'h3f800000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[0] == 1'b0 && ch_crc_err[0] == 1'b0 && rd_ch_cnt == 4'd0 ) begin
            k_factor0   <=   k_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor0   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[0] == 1'b0 && ch_crc_err[0] == 1'b0 && rd_ch_cnt == 4'd0 ) begin
            b_factor0   <=   b_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor1   <=   32'h3f800000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[1] == 1'b0 && ch_crc_err[1] == 1'b0 && rd_ch_cnt == 4'd1 ) begin
            k_factor1   <=   k_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor1   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[1] == 1'b0 && ch_crc_err[1] == 1'b0 && rd_ch_cnt == 4'd1 ) begin
            b_factor1   <=   b_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor2   <=   32'h3f800000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[2] == 1'b0 && ch_crc_err[2] == 1'b0 && rd_ch_cnt == 4'd2 ) begin
            k_factor2   <=   k_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor2   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[2] == 1'b0 && ch_crc_err[2] == 1'b0 && rd_ch_cnt == 4'd2 ) begin
            b_factor2   <=   b_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor3   <=   32'h3f800000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[3] == 1'b0 && ch_crc_err[3] == 1'b0 && rd_ch_cnt == 4'd3) begin
            k_factor3   <=   k_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor3   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[3] == 1'b0 && ch_crc_err[3] == 1'b0 && rd_ch_cnt == 4'd3 ) begin
            b_factor3   <=   b_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor4   <=   32'h3f800000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[4] == 1'b0 && ch_crc_err[4] == 1'b0 && rd_ch_cnt == 4'd4 ) begin
            k_factor4   <=   k_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor4   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[4] == 1'b0 && ch_crc_err[4] == 1'b0 && rd_ch_cnt == 4'd4 ) begin
            b_factor4   <=   b_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor5   <=   32'h3f800000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[5] == 1'b0 && ch_crc_err[5] == 1'b0 && rd_ch_cnt == 4'd5 ) begin
            k_factor5   <=   k_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor5   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[5] == 1'b0 && ch_crc_err[5] == 1'b0 && rd_ch_cnt == 4'd5 ) begin
            b_factor5   <=   b_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor6   <=   32'h3f800000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[6] == 1'b0 && ch_crc_err[6] == 1'b0 && rd_ch_cnt == 4'd6 ) begin
            k_factor6   <=   k_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor6   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[6] == 1'b0 && ch_crc_err[6] == 1'b0 && rd_ch_cnt == 4'd6 ) begin
            b_factor6   <=   b_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor7   <=   32'h3f800000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[7] == 1'b0 && ch_crc_err[7] == 1'b0 && rd_ch_cnt == 4'd7 ) begin
            k_factor7   <=   k_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor7   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[7] == 1'b0 && ch_crc_err[7] == 1'b0 && rd_ch_cnt == 4'd7 ) begin
            b_factor7   <=   b_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor8   <=   32'h3f800000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[8] == 1'b0 && ch_crc_err[8] == 1'b0 && rd_ch_cnt == 4'd8 ) begin
            k_factor8   <=   k_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor8   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[8] == 1'b0 && ch_crc_err[8] == 1'b0 && rd_ch_cnt == 4'd8 ) begin
            b_factor8   <=   b_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor9   <=   32'h3f800000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[9] == 1'b0 && ch_crc_err[9] == 1'b0 && rd_ch_cnt == 4'd9 ) begin
            k_factor9   <=   k_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor9   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[9] == 1'b0 && ch_crc_err[9] == 1'b0 && rd_ch_cnt == 4'd9 ) begin
            b_factor9   <=   b_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor10   <=   32'h3f800000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[10] == 1'b0 && ch_crc_err[10] == 1'b0 && rd_ch_cnt == 4'd10 ) begin
            k_factor10   <=   k_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor10   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[10] == 1'b0 && ch_crc_err[10] == 1'b0 && rd_ch_cnt == 4'd10 ) begin
            b_factor10   <=   b_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        k_factor11   <=   32'h3f800000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[11] == 1'b0 && ch_crc_err[11] == 1'b0 && rd_ch_cnt == 4'd11 ) begin
            k_factor11   <=   k_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        b_factor11   <=   32'h00000000 ;
    end
    else begin
        if ( cur_state == CH_NEXT && chn_num_err[11] == 1'b0 && ch_crc_err[11] == 1'b0 && rd_ch_cnt == 4'd11 ) begin
            b_factor11   <=   b_factor ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_cnt  <=   2'd0 ;
    end
    else begin
        if ( cur_state == WRH_CRC || cur_state == WRK_CRC || cur_state == WRB_CRC ) begin
            wr_cnt  <=   wr_cnt + 1'b1 ;
        end
        else begin
            wr_cnt  <=   2'd0 ;
        end
    end
end


always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_ch_cnt   <=   4'd0 ;
    end
    else begin
        if ( cur_state == CH_NEXT ) begin
            rd_ch_cnt   <=   rd_ch_cnt + 1'b1 ;
        end
        else if ( cur_state == RD_CPL ) begin
            rd_ch_cnt   <=   4'd0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        param_rd_done <=   1'b0 ;
    end
    else begin
        if ( cur_state == RD_CPL ) begin
            param_rd_done <=   1'b1 ;
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
        if ( cur_state == WRH_CRC || cur_state == WRK_CRC || cur_state == WRB_CRC ) begin 
            case ( wr_cnt )
                2'd0 : begin
                    crc_din <=   e2p_rd_value[7:0] ;
                end
                2'd1 : begin
                    crc_din <=   e2p_rd_value[15:8] ;
                end
                2'd2 : begin
                    crc_din <=   e2p_rd_value[23:16] ;
                end
                2'd3 : begin
                    crc_din <=   e2p_rd_value[31:24] ;
                end
                default : begin
                    crc_din <=   8'd0 ;
                end
            endcase
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_din_vld <=   1'b0 ;
    end
    else begin
        if ( cur_state == WRH_CRC || cur_state == WRK_CRC || cur_state == WRB_CRC ) begin
            crc_din_vld <=   1'b1 ;
        end
        else begin
            crc_din_vld <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_eop <=   1'b0 ;
    end
    else begin
        if ( cur_state == WRB_CRC && wr_cnt == 2'd3 ) begin
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
        crc_eop_d2 <= 1'b0 ;  
    end
    else begin
        crc_eop_d2  <=   crc_eop_d1 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_data    <=   16'd0 ;
    end
    else begin
        if ( cur_state == RD_CRC && e2p_rd_dval == 1'b1 ) begin
            crc_data    <=   e2p_rd_value[15:0] ;
        end
        else ;
    end
end


always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ch_crc_err <=   12'h000 ;
    end
    else begin
        if ( cur_state == CRC_CMP ) begin
            if ( crc_dout == crc_data ) begin
                ch_crc_err[rd_ch_cnt] <=   1'b0 ;
            end
            else begin
                ch_crc_err[rd_ch_cnt] <=   1'b1 ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        param_crc_err   <=   1'b0 ;
    end
    else begin
        param_crc_err   <=  ch_crc_err ;
    end
end

    IO_FCS16                       U_FCS16
    (
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),
    .crc_din                    ( crc_din                   ),
    .crc_cap                    ( crc_eop                   ),
    .crc_sop                    ( crc_eop_d2                ),
    .crc_din_vld                ( crc_din_vld               ),
    .crc_dout                   ( crc_dout                  )
    );

endmodule
