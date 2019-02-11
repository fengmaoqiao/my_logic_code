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

module FLOAT_DIVM
    (
        rst_sys_n               ,   
        clk_sys                 ,   
        data_a                  ,   
        data_b                  ,   
        start_trig              ,   

        done                    ,   
        result                     
    ) ;

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
localparam  cal_step0       = 5'b00000   ;
localparam  cal_step1       = 5'b00001   ;
localparam  cal_step2       = 5'b00010   ;
localparam  cal_step3       = 5'b00100   ;
localparam  cal_step4       = 5'b01000   ;
localparam  cal_step5       = 5'b10000   ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire    [31:0]          data_a                              ;   
input   wire    [31:0]          data_b                              ;   
input   wire                    start_trig                          ;   
// declare output signal
output  wire    [3:0]           done                                ;   
output  wire    [31:0]          result                              ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [47:0]                  result_quot                         ;   
wire    [48:0]                  div_data_a                          ;   
wire    [48:0]                  div_data_b                          ;   
wire    [9:0]                   expdiff                             ;   
wire                            div_done                            ;   
// reg signal
reg     [32:0]                  pre_data_a                          ;   
reg     [32:0]                  pre_data_b                          ;   
reg     [47:0]                  temp                                ;   
reg     [31:0]                  result_t                            ;   
reg     [9:0]                   expon                               ;   

reg                             issign                              ;   
reg                             isover                              ;   
reg                             isunder                             ;   
reg                             iszero                              ;   
reg                             isdone                              ;   
reg     [4:0]                   cur_state                           ;   
reg     [4:0]                   next_state                          ;   

reg                             div_start_trig                      ;   
   
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

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
                if ( data_b == 32'd0 ) begin
                    next_state = cal_step5 ;
                end
                else begin
                    next_state = cal_step1 ;
                end
            end
            else begin
                next_state = cal_step0 ;
            end
        end
        cal_step1 : begin
            next_state = cal_step2 ;
        end
        cal_step2 : begin
            next_state = cal_step3 ;
        end
        cal_step3 : begin
            if ( div_done == 1'b1 ) begin
                next_state = cal_step4 ;
            end
            else begin
                next_state = cal_step3 ;
            end
        end
        cal_step4 : begin
            next_state = cal_step5 ;
        end
        cal_step5 : begin
            next_state = cal_step0 ;
        end
        default : begin
            next_state = cal_step0 ;
        end
    endcase
end

//----------------------------------------------------------------------------------
// calculation of start steps
// judgment condition of shift treatment
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pre_data_a   <=   33'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            pre_data_a   <=   33'd0 ;
        end
        else if ( cur_state == cal_step1 ) begin
            pre_data_a  <=  { data_a[31], data_a[30:23], 1'b1, data_a[22:0] } ;
        end
        else ; 
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pre_data_b   <=   33'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            pre_data_b   <=   33'd0 ;
        end
        else if ( cur_state == cal_step1 ) begin
            pre_data_b  <=  { data_b[31], data_b[30:23], 1'b1, data_b[22:0] } ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        issign  <=  1'b0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            issign  <=  1'b0 ;
        end
        else if ( cur_state == cal_step1 ) begin
            issign  <=  data_a[31] ^ data_b[31] ;
        end
        else ;
    end
end

assign expdiff = pre_data_b[31:24] - 8'd127 ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        expon <=  10'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            expon <=  10'd0 ;
        end
        else if ( cur_state == cal_step2 ) begin
            expon <=  pre_data_a[31:24] - expdiff ; 
        end
        else if ( cur_state == cal_step4 ) begin
            if ( temp[25] == 1'b1 || temp[24] == 1'b1 ) begin
                expon <=  expon ;
            end
            else if ( temp[23] == 1'b1 ) begin
                expon <=  expon - 1'b1 ;
            end
            else ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// calculation of second steps
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        div_start_trig  <=  1'b0 ;
    end
    else begin
        if ( cur_state == cal_step2 ) begin
            div_start_trig  <=  1'b1 ;
        end
        else begin
            div_start_trig  <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        temp <=  48'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            temp <=  48'd0 ;
        end
        else if ( cur_state == cal_step3 && div_done == 1'b1 ) begin //   
            temp <= result_quot ;
        end
        else if ( cur_state == cal_step4 ) begin
            if( temp[25] == 1'b1 ) begin 
                temp  <=  temp << 22 ; 
            end
            else if( temp[24] == 1'b1 ) begin 
                temp  <=  temp << 23 ; 
            end
            else if( temp[23] == 1'b1 ) begin 
                temp  <=  temp << 24 ; 
            end
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// calculation of fifth steps
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        isover   <= 1'd0 ; 
    end
    else begin
        if ( cur_state == cal_step5 ) begin
            if( expon[9:8] == 2'b01 ) begin 
                isover  <=  1'b1 ; 
            end         // E Overflow
            else ;
        end
        else if ( cur_state == cal_step0 ) begin
            isover  <=  1'b0 ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        isunder   <= 1'd0 ; 
    end
    else begin
        if ( cur_state == cal_step5 ) begin
            if( expon[9:8] == 2'b11 ) begin 
                isunder <=  1'b1 ; 
            end  
            else ;
        end
        else if ( cur_state == cal_step0 ) begin
            isunder  <=  1'b0 ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        iszero   <= 1'd0 ; 
    end
    else begin
        if ( cur_state == cal_step5 ) begin
            if( temp[47:24] == 24'd0 ) begin 
                iszero  <=  1'b1 ; 
            end
            else ;
        end
        else if ( cur_state == cal_step0 ) begin
            iszero  <=  1'b0 ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        result_t   <= 32'h00000000 ; 
    end
    else begin
        if ( cur_state == cal_step5 ) begin
            if( expon[9:8] == 2'b01 ) begin
                result_t    <=  {1'b0,8'd127, 23'd0} ; 
            end
            else if ( expon[9:8] == 2'b11 ) begin
                result_t    <=  {1'b0,8'd127, 23'd0} ; 
            end
            else if ( temp[47:24] == 24'd0 ) begin
                result_t    <=  {1'b0, 8'd0, 23'd0} ;
            end
            else begin
                result_t    <=  { issign, expon[7:0], temp[46:24] } ; 
            end
        end
        else  ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        isdone    <=  1'b0 ;
    end
    else begin
        if ( cur_state == cal_step5 ) begin
            isdone    <=  1'b1 ;
        end
        else begin
            isdone    <=  1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// the streamlined divider
//----------------------------------------------------------------------------------
assign div_data_a = { 1'b0, pre_data_a[23:0], 24'd0 } ;
assign div_data_b = { 1'b0, 24'd0, pre_data_b[23:0] } ;

    STRMLND_DIVM                U_STRMLND_DIVM
    (
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),
        
    .start_trig                 ( div_start_trig            ),
    .data_a                     ( div_data_a                ),
    .data_b                     ( div_data_b                ),
        
    .result_quot                ( result_quot               ),
    .result_rmn                 (                           ),
    .done                       ( div_done                  )
  ) ;

assign done = { isover, isunder, iszero, isdone } ;
assign result = result_t ;

endmodule
