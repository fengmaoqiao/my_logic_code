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
`timescale 1 ns / 1 ns
`include "DEFINES.v"
module BOOTH_MULTIM
    (
        clk_sys                 ,   
        rst_sys_n               ,   
        start_trig              ,   
        data_a                  ,   
        data_b                  ,   
        result                  ,   
        done
     ) ;

/**********************************************************************************\
***************************** declare parameter ************************************/
localparam  cal_step0       = 4'b0001    ;
localparam  cal_step1       = 4'b0010    ;
localparam  cal_step2       = 4'b0100    ;
localparam  cal_step3       = 4'b1000    ;
localparam  CNT = 5'd25; 
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   
input   wire                    start_trig                          ;   
input   wire    [24:0]          data_a                              ;   
input   wire    [24:0]          data_b                              ;   

// declare output signal
output  wire    [47:0]          result                              ;   
output  reg                     done                                ;   

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
wire    [24:0]                  diff1                               ;   
wire    [24:0]                  diff2                               ;   

// reg signal
reg     [24:0]                  temp_a                              ;   // [24]Sign ,A result 
reg     [24:0]                  temp_s                              ;   // [24]Sign ,reverse result of A
reg     [50:0]                  temp_p                              ;   // operation register 
reg     [4:0]                   cal_cnt                             ;   
reg     [3:0]                   cur_state                           ;   
reg     [3:0]                   next_state                          ;   
/**********************************************************************************\
******************************** debug code ****************************************

/**********************************************************************************\
********************************* main code ****************************************/
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
            next_state = cal_step2 ;
        end
        cal_step2 : begin
            if ( cal_cnt == CNT ) begin
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
            next_state = cal_step0 ;
        end
    endcase
end

//----------------------------------------------------------------------------------
// calculation of start steps
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        temp_a  <=  25'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            temp_a  <=  25'd0 ;
        end
        else if ( cur_state == cal_step1 ) begin
            temp_a  <=  data_a ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        temp_s  <=  25'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            temp_s  <=  25'd0 ;
        end
        else if ( cur_state == cal_step1 ) begin
            temp_s  <=  ( ~data_a + 1'b1 );
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        temp_p  <=  51'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            temp_p  <=  51'd0 ;
        end
        else if ( cur_state == cal_step1 ) begin
            temp_p  <=  {25'd0, data_b, 1'b0 } ;
        end
        else if ( cur_state == cal_step2 && cal_cnt != CNT ) begin
            if ( temp_p[1:0] == 2'b01 ) begin
                temp_p  <=  { diff1[24], diff1, temp_p[25:1] } ; // + data_a
            end
            else if ( temp_p[1:0] == 2'b10 ) begin
                temp_p  <=  { diff2[24], diff2, temp_p[25:1] } ; // - data_a
            end 
            else begin
                temp_p  <=  { temp_p[50], temp_p[50:1] } ;
            end
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_cnt <=  5'd0 ;
    end
    else begin
        if ( cur_state == cal_step2 ) begin
            cal_cnt <=  cal_cnt + 1'b1 ;
        end
        else if ( cur_state == cal_step0 ) begin
            cal_cnt <=  5'd0 ;
        end
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

assign diff1 = temp_p[50:26] + temp_a ;
assign diff2 = temp_p[50:26] + temp_s ;
assign result = temp_p[48:1] ;

endmodule
