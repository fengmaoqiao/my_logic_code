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
// Others           :   STREAMLINED_DIVIDER_MODULE
// -FHDR***********************************************************************
`timescale 1 ns / 1 ns
`include "DEFINES.v"
module STRMLND_DIVM
    (
        clk_sys                 ,   
        rst_sys_n               ,   
        
        start_trig              ,   
        data_a                  ,  // the dividend 
        data_b                  ,  // the divisor 
        
        result_quot             ,   // the quotient 
        result_rmn              ,   // the reminder
        done                       
  );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
localparam  cal_step0       = 4'b0001   ;
localparam  cal_step1       = 4'b0010   ;
localparam  cal_step2       = 4'b0100   ;
localparam  cal_step3       = 4'b1000   ;
localparam  CNT_STEP        = 7'd48     ;
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   
input   wire                    start_trig                          ;   
input   wire    [48:0]          data_a                              ;   // the dividend 
input   wire    [48:0]          data_b                              ;   // the divisor 
        

// declare output signal
output  wire    [47:0]          result_quot                         ;   // the quotient 
output  wire    [47:0]          result_rmn                          ;   // the reminder
output  reg                     done                                ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [97:0]                  diff                                ;  
// reg signal
reg     [3:0]                   cur_state                           ;   
reg     [3:0]                   next_state                          ; 
reg     [6:0]                   cal_cnt                             ;
reg     [49:0]                  temp_s                              ;
reg     [97:0]                  temp                                ;   
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cur_state  <=  cal_step0;
    end
    else begin
        cur_state  <=  next_state;
    end
end

always @ ( * ) begin
    case ( cur_state ) 
        cal_step0 : begin
            if ( start_trig == 1'b1 ) begin
                next_state = cal_step1;
            end
            else begin
                next_state = cal_step0;
            end
        end
        cal_step1 : begin
            next_state = cal_step2 ;
        end
        cal_step2 : begin
            if ( cal_cnt == CNT_STEP ) begin
                next_state = cal_step3 ;
            end
            else begin
                next_state = cal_step2 ;
            end
        end
        cal_step3 : begin
            next_state = cal_step0 ;
        end
        default : begin
            next_state = cal_step0;
        end
    endcase
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        temp_s  <=  50'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            temp_s  <=  50'd0 ;
        end
        else if ( cur_state == cal_step1 ) begin
            temp_s  <= ( data_b[48] == 1'b1 ) ? { 1'b1, data_b } : { 1'b1, ~data_b + 1'b1 } ;
        end
        else ;
    end
end
//assign diff = temp + { temp_s, 48'd0 } ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        temp    <=  98'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            temp    <=  98'd0 ;
        end
        else if ( cur_state == cal_step1 ) begin
            temp    <=  ( data_a[48] ==1'b1 ) ? { 49'd0, ~data_a + 1'b1 } : { 49'd0, data_a } ;
        end
        else if ( cur_state == cal_step2 ) begin
            if ( diff[97] == 1'b1 ) begin
                temp    <=  { temp[96:0], 1'b0 } ;
            end
            else begin
                temp    <=  { diff[96:0], 1'b1 } ;
            end
        end
        else ; 
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_cnt    <=  7'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            cal_cnt    <=  7'd0 ;
        end
        else if ( cur_state == cal_step2 ) begin
            if ( cal_cnt == CNT_STEP ) begin
                cal_cnt <=  7'd0 ;
            end
            else begin
                cal_cnt <=  cal_cnt + 1'b1 ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        done    <=  1'b0 ;
    end
    else begin
        if ( cur_state == cal_step3 ) begin
            done    <=  1'b1 ;
        end
        else begin
            done    <=  1'b0 ;
        end
    end
end

assign diff = temp + { temp_s, 48'd0 } ;
assign result_quot  = temp[47:0] ;
assign result_rmn   = temp[96:49] ;

endmodule
