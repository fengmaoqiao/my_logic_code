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

module ADCTL
    (	
        clk_sys                 ,   // system clock
        rst_sys_n               ,   // system reset
        pw_on_en                ,   
        rd_en                   ,   
        done                    ,   
        rd_value                ,   
        // output port
        rd_dval                 ,   // read data dvalid
        rd_data                 ,   
        spi_busy                ,   // spi bus busy
        cur_state               ,   
        wr_cnt                  ,   
        wr_done                 ,   
        con_done
	) ;

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   CON_CNT         =   5'd16           ; // the times of register configure
localparam  ITV_CNT         =   8'd255          ;

localparam  IDLE            =   8'b00000000     ;
localparam  CON_RDY         =   8'b00000001     ;
localparam  CON_INIT        =   8'b00000010     ;
localparam  RDY_IDLE        =   8'b00000100     ;
localparam  RD_RDY          =   8'b00100000     ;
localparam  RD_NEXT         =   8'b01000000     ;
localparam  DLY_CNT         =   8'b10000000     ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   
input   wire                    rd_en                               ;   
input   wire                    done                                ; 
input   wire    [31:0]          rd_value                            ;   
input   wire                    pw_on_en                            ;   
// declare output signal
output  reg                     spi_busy                            ;   
output  reg     [4:0]           wr_cnt                              ;   
output  reg                     rd_dval                             ;   
output  reg     [15:0]          rd_data                             ;   
output  reg     [7:0]           cur_state                           ;   
output  reg                     wr_done                             ;   
output  reg                     con_done                            ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
// reg signal
reg     [7:0]                   next_state                          ;   
reg     [7:0]                   dly_cnt                             ;   
reg                             rd_op_en                            ;   
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
        if ( cur_state == DLY_CNT && dly_cnt == ITV_CNT && rd_op_en == 1'b0 ) begin
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
            if ( pw_on_en == 1'b1 ) begin
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
            if ( done == 1'b1 && wr_cnt != CON_CNT ) begin
                next_state = DLY_CNT ;
            end
            else if ( done == 1'b1 && wr_cnt == CON_CNT ) begin
                next_state = RDY_IDLE ;
            end
            else begin
                next_state = CON_INIT ;
            end
        end
        RDY_IDLE : begin
            if( rd_en == 1'b1 ) begin
                next_state = RD_RDY ;
            end
            else begin
                next_state = RDY_IDLE ;
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
           if ( dly_cnt == ITV_CNT && con_done == 1'b1 ) begin
                next_state = RDY_IDLE ;
           end
           else if ( dly_cnt == ITV_CNT && con_done == 1'b0 ) begin
               next_state = CON_RDY ;
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

//----------------------------------------------------------------------------------
// interval delay of two configuration
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dly_cnt   <=  8'h00 ;
    end
    else begin
        if ( cur_state == DLY_CNT ) begin 
            dly_cnt   <=  dly_cnt + 1'b1 ;
        end
        else begin
            dly_cnt   <=  8'h00 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_op_en   <=  1'b0 ;
    end
    else begin
        if ( cur_state == RD_RDY ) begin
            rd_op_en   <=  1'b1 ;
        end
        else if ( cur_state == RDY_IDLE || cur_state == CON_RDY ) begin
            rd_op_en   <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_dval   <=  1'b0 ;
    end
    else begin
        if ( cur_state == DLY_CNT &&  dly_cnt == ITV_CNT && con_done == 1'b1  && rd_op_en == 1'b1 ) begin
            rd_dval   <=  1'b1 ;
        end
        else begin
            rd_dval   <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_data   <=  16'h0000 ;
    end
    else begin
        if ( cur_state == DLY_CNT &&  dly_cnt == ITV_CNT && con_done == 1'b1 ) begin
            rd_data   <=  rd_value[31:16] ;
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
        if ( cur_state == RDY_IDLE && rd_en == 1'b0 ) begin 
            spi_busy   <=  1'b0 ;
        end
        else begin
            spi_busy    <=  1'b1 ;
        end
    end
end

endmodule
