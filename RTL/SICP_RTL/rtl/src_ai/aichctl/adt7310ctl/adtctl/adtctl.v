// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-06-10
// DEPARTMENT       :   R&D
// AUTHOR           :   Zhang Yongjun
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com.cn
// AUTHOR'S TEL     :   18283432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-06  Zhang Yongjun       Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active low
// Clock Domains    :   clk_100m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`timescale 1 ns / 1 ns
`include "DEFINES.v"

module ADTCTL
    (	
        clk_sys                 ,   // system clock
        rst_sys_n               ,   // system reset
        
        wr_en                   ,   // read enable , active high & only one cycle
        wr_value                ,   
        rd_en                   ,   
        done                    ,   
        rd_data                 ,   
        pw_on_en                ,   
        cfg_done                ,   
        // output port
        rd_dval                 ,   // read data dvalid
        rd_dvalue                ,   
        spi_busy                ,   // spi bus busy
        cur_state               ,   
        wr_cnt                  ,   
        wr_done                 ,
        con_done                ,   
        chip_err
	) ;

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   CON_CNT         =   5'd16                ; // the times of register configure

localparam  IDLE            =   12'b000000000000     ;
localparam  CON_RDY         =   12'b000000000001     ;
localparam  CON_INIT        =   12'b000000000010     ;
localparam  RD_CON          =   12'b000000000100     ;
localparam  RD_CDATA        =   12'b000000001000     ;
localparam  CHK_CON         =   12'b000000010000     ;
localparam  RDY_IDLE        =   12'b000000100000     ;
localparam  RD_STU_RDY      =   12'b000001000000     ;
localparam  RD_STU          =   12'b000010000000     ;
localparam  RD_RDY          =   12'b000100000000     ;
localparam  RD_NEXT         =   12'b001000000000     ;
localparam  DLY_CNT         =   12'b100000000000     ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   
input   wire                    wr_en                               ;   
input   wire    [15:0]          wr_value                            ;   
input   wire                    rd_en                               ;   
input   wire                    done                                ; 
input   wire    [15:0]          rd_data                             ;   
input   wire                    pw_on_en                            ;   
input   wire                    cfg_done                            ;   
// declare output signal
output  reg                     spi_busy                            ;   
output  reg     [4:0]           wr_cnt                              ;   
output  reg                     rd_dval                             ;   
output  reg     [15:0]          rd_dvalue                            ;   
output  reg     [11:0]          cur_state                           ;   
output  reg                     wr_done                             ;   
output  reg                     chip_err                            ;   
output  reg                     con_done                            ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
// reg signal
reg     [11:0]                  next_state                          ;   
reg     [8:0]                   dly_cnt                             ;   
reg                             rd_op                               ;   
reg                             chk_err                             ;  
reg     [2:0]                   chk_cnt                             ;   
reg                             rd_en_vld                           ;   
reg     [15:0]                  rd_con_value                        ;   
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// generate wr_done after the dly_cnt
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_done   <=  1'b0 ;
    end
    else begin
        if ( cur_state == DLY_CNT && dly_cnt[8] == 1'b1 ) begin
            wr_done  <=  1'b1 ;
        end
        else begin
            wr_done  <=  1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// state machine
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cur_state   <=  IDLE ;
    end
    else begin
        cur_state   <=  next_state ;
    end
end

always @ ( * ) begin
    case ( cur_state )
        IDLE : begin
            if ( pw_on_en == 1'b1 && cfg_done == 1'b1 ) begin
                next_state = CON_RDY ;
            end
            else begin
                next_state = IDLE ;
            end
        end
        CON_RDY : begin
            next_state = CON_INIT ;
        end
        CON_INIT : begin
            if ( done == 1'b1 ) begin
                if ( wr_cnt != CON_CNT - 1'b1 ) begin
                    next_state = DLY_CNT ;
                end
                else if ( wr_cnt == CON_CNT - 1'b1 ) begin
                    next_state = RDY_IDLE ;
                end
                else begin
                    next_state = CON_INIT ;
                end
            end else begin
                next_state = CON_INIT ;
            end   
        end
        RD_CON : begin
            next_state = RD_CDATA ;
        end
        RD_CDATA : begin
            if ( done == 1'b1 ) begin
                next_state = CHK_CON ;
            end
            else begin
                next_state = RD_CDATA ;
            end
        end
        CHK_CON : begin
            if ( chk_err == 1'b1 ) begin
                if ( chk_cnt != 3'd2 ) begin
                    next_state = DLY_CNT ;
                end
                else begin
                    next_state = RDY_IDLE ;
                end
            end
            else begin
                next_state = RDY_IDLE ;
            end
        end
        RDY_IDLE : begin
            if ( rd_en == 1'b1 ) begin
                next_state = RD_STU_RDY ;
            end
            else begin
                next_state = RDY_IDLE ;
            end
        end
        RD_STU_RDY : begin
            next_state = RD_STU ;
        end
        RD_STU : begin
            if ( done ==  1'b1 ) begin
                next_state = DLY_CNT ;
            end
            else begin
                next_state = RD_STU ;
            end
        end
        RD_RDY : begin
            next_state = RD_NEXT ;
        end
        RD_NEXT : begin
            if ( done == 1'b1 ) begin
                next_state = DLY_CNT ;
            end
            else begin
                next_state = RD_NEXT ;
            end
        end
        DLY_CNT : begin
            if ( dly_cnt[8] == 1'b1 ) begin
                if ( con_done == 1'b1 ) begin
                    if ( rd_en_vld == 1'b0 ) begin
                        next_state = RD_RDY  ;
                    end
                    else begin
                        next_state =  RDY_IDLE ;
                    end
                end
                else begin
                    if ( wr_cnt == CON_CNT - 2'd2 ) begin
                        next_state = RD_CON ;
                    end
                    else begin
                        next_state = CON_RDY ;
                    end
                end
            end
            else begin
                next_state = DLY_CNT ;
            end
        end
        default : begin
            next_state = next_state ;
        end
    endcase
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_en_vld   <=   1'b0 ;
    end
    else begin
        if ( cur_state == RDY_IDLE ) begin 
            rd_en_vld   <=   1'b0 ;
        end
        else if ( cur_state == RD_RDY ) begin
            rd_en_vld   <=   1'b1 ;
        end
    end
end

// test code
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_con_value    <=   16'h0000 ;
    end
    else begin
        if ( cur_state == RD_CDATA && done == 1'b1 ) begin
            rd_con_value <=   rd_data ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        chk_err   <=  16'h0000 ;
    end
    else begin
        if ( cur_state == RD_CDATA && done == 1'b1 ) begin
            if ( rd_data[7:3] == 5'b11000 ) begin
                chk_err <=   1'b0 ;
            end
            else begin
                chk_err <=   1'b1 ;
            end
        end
        else if ( cur_state == CON_RDY || cur_state == RDY_IDLE ) begin
            chk_err <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        chk_cnt <=   3'd0 ;
    end
    else begin
        if ( cur_state == CHK_CON ) begin
            chk_cnt <=   chk_cnt  + 1'b1 ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        chip_err    <=   1'b0 ;
    end
    else begin
        if ( cur_state == CHK_CON && chk_cnt == 3'd2 ) begin
            chip_err    <=   1'b1 ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// interval delay of two configuration
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dly_cnt   <=  9'h00 ;
    end
    else begin
        if ( cur_state == DLY_CNT ) begin 
            dly_cnt   <=  dly_cnt + 1'b1 ;
        end
        else begin
            dly_cnt   <=  9'h00 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_op   <=  1'b0 ;
    end
    else begin
        if ( cur_state == RD_RDY ) begin
            rd_op   <=  1'b1 ;
        end
        else if ( cur_state == RDY_IDLE ) begin
            rd_op   <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_dval   <=  1'b0 ;
    end
    else begin
        if ( cur_state == DLY_CNT &&  dly_cnt[8] == 1'b1 && rd_en_vld == 1'b1 && con_done == 1'b1 ) begin
            rd_dval   <=  1'b1 ;
        end
        else begin
            rd_dval   <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_dvalue   <=  16'h0000 ;
    end
    else begin
        if ( cur_state == DLY_CNT &&  dly_cnt[8] == 1'b1 ) begin
            rd_dvalue   <=  rd_data ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_cnt   <=  5'b00000 ;
    end
    else begin
        case ( cur_state ) 
            IDLE : begin
                wr_cnt <= 5'd0 ;
            end
            CON_RDY : begin
                wr_cnt <= wr_cnt + 1'b1 ;
            end
            RD_CON : begin
                wr_cnt <= wr_cnt + 1'b1 ;
            end
            CHK_CON : begin
                if ( chk_err == 1'b1 ) begin
                    wr_cnt  <=   5'd0 ;
                end
                else ;
            end
            RDY_IDLE : begin
                wr_cnt <= CON_CNT ;
            end
            RD_RDY : begin
                wr_cnt <= wr_cnt + 1'b1 ;
            end
            default : begin
            end
        endcase
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        con_done    <=  1'b0;
    end
    else begin
        if ( cur_state == RDY_IDLE ) begin
            con_done    <=  1'b1 ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        spi_busy   <=  1'b0 ;
    end
    else begin
        if ( cur_state == RDY_IDLE && ( wr_en == 1'b0 || rd_en == 1'b0 ) ) begin 
            spi_busy   <=  1'b0 ;
        end
        else begin
            spi_busy    <=  1'b1 ;
        end
    end
end

endmodule
