// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-12-18
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
`timescale 1 ns / 1 ns
`include "DEFINES.v"

module INT_FLOATM
    (
        rst_sys_n               ,   
        clk_sys                 ,   
        start_trig              ,   
        data_int                ,   

        result_float            ,
        done
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   INT_WIDTH         =   5'd16   ;

localparam  cal_step0       = 2'b00   ;
localparam  cal_step1       = 2'b01   ;
localparam  cal_step2       = 2'b10   ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire    [15:0]          data_int                            ;   
input   wire                    start_trig                          ;   
// declare output signal
output  reg     [31:0]          result_float                        ;   
output  reg                     done                                ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            sign                                ;   
wire    [4:0]                   data_bit                            ;   
// reg signal
reg     [7:0]                   expon                               ;   
reg     [22:0]                  mtisa                               ;   
reg     [1:0]                   cur_state                           ;   
reg     [1:0]                   next_state                          ;   
reg     [4:0]                   loc_dot                             ;   
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

assign sign     =   1'b0 ;
assign data_bit = INT_WIDTH - loc_dot - 5'd1 ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cur_state  <=  cal_step0 ;
    end
    else begin
        cur_state  <=  next_state ;
    end
end

always @ ( * ) begin
    case ( cur_state ) 
        cal_step0 : begin
            if ( start_trig == 1'b1 ) begin
                next_state = cal_step1 ;
            end
            else begin
                next_state = cal_step0 ;
            end
        end
        cal_step1 : begin
            if ( data_int[data_bit] == 1'b1 || loc_dot == INT_WIDTH - 1'b1 ) begin
                next_state = cal_step2 ;
            end
            else begin
                next_state = cal_step1 ;
            end
        end
        cal_step2 : begin
            next_state = cal_step0 ;
        end
        default : begin
            next_state = cal_step0 ;
        end
    endcase
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        loc_dot <=  5'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            loc_dot <=  5'd0 ;
        end
        else if ( cur_state == cal_step1 ) begin
            loc_dot <=  loc_dot + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// exponential partial processing
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        expon   <=  8'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            expon   <=  8'd0 ;
        end
        else if ( cur_state == cal_step1 && data_int[data_bit] == 1'b1 ) begin
            expon   <=  8'd127 + INT_WIDTH - 1'b1 - loc_dot ;
        end
    end
end

//----------------------------------------------------------------------------------
// fractional partial processing
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        mtisa   <=  23'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            mtisa   <=  23'd0 ;
        end
        else if ( cur_state == cal_step1 && data_int[data_bit] == 1'b1 ) begin
            mtisa[22:24-INT_WIDTH]   <=  data_int << loc_dot ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        result_float    <=  32'h00000000 ; 
    end
    else begin
        if ( cur_state == cal_step2 ) begin
            result_float    <=  { sign , expon,  mtisa } ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        done    <=  1'b0 ;
    end
    else begin
        if ( cur_state == cal_step2 ) begin
            done    <=  1'b1 ;
        end
        else begin
            done    <=  1'b0 ;
        end
    end
end

endmodule
