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

module FLOAT_MULTIM
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

localparam  cal_step0       = 6'b000001    ;
localparam  cal_step1       = 6'b000010    ;
localparam  cal_step2       = 6'b000100    ;
localparam  cal_step3       = 6'b001000    ;
localparam  cal_step4       = 6'b010000    ;
localparam  cal_step5       = 6'b100000    ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    rst_sys_n                            ;   
input   wire                    clk_sys                              ;   
input   wire    [31:0]          data_a                               ;   
input   wire    [31:0]          data_b                               ;   
input   wire                    start_trig                           ;   
// declare output signal
output  wire    [3:0]           done                                 ;   
output  wire    [31:0]          result                               ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [47:0]                  fbm_result                           ;   
wire                            fbm_done                             ;  
wire     [9:0]                  expdiff                              ;   

// reg signal
reg     [32:0]                  pre_data_a                           ;   
reg     [32:0]                  pre_data_b                           ;   
reg     [47:0]                  temp                                 ;   
reg     [31:0]                  result_t                             ;   
reg     [9:0]                   expon                                ;   
reg                             issign                               ;   
reg                             isover                               ;   
reg                             isunder                              ;   
reg                             iszero                               ;   
reg                             isdone                               ;   
reg     [7:0]                   cur_state                            ;   
reg     [7:0]                   next_state                           ;   
reg                             fbm_start_trig                       ;   
reg     [24:0]                  fbm_data_a                           ;   
reg     [24:0]                  fbm_data_b                           ;   

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
            next_state = cal_step3 ;
        end
        cal_step3 : begin
            if ( fbm_done == 1'b1 ) begin
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
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pre_data_a   <=   33'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            if ( data_a[30:0] == 31'h00000000 ) begin // added in 2018/1/19 14:07:45 for multi 0
                pre_data_a  <=   33'd0 ;
            end
            else begin
                pre_data_a  <=  { data_a[31], data_a[30:23], 1'b1, data_a[22:0] } ;
            end
        end
        else ; 
    end
end

//----------------------------------------------------------------------------------
// calculation of firest steps
// judgment condition of shift treatment
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pre_data_b   <=   33'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            if ( data_b[30:0] == 31'h00000000 ) begin // added in 2018/1/19 14:07:45 for multi 0
                pre_data_b  <=   33'd0 ;
            end
            else begin
                pre_data_b  <=  { data_b[31], data_b[30:23], 1'b1, data_b[22:0] } ;
            end
        end
        else if ( cur_state == cal_step1 ) begin 
            if( pre_data_a[31:24] == pre_data_b[31:24] && ( pre_data_a[22:0] != 23'd0 & pre_data_b[22:0] != 23'd0 ) || pre_data_a[32] ^ pre_data_b[32] ) begin
                pre_data_b[31:24] <= pre_data_b[31:24] + 1'b1 ; 
                pre_data_b[23:0] <= pre_data_b[23:0] >> 1 ;
            end
            else ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        issign  <=  1'b0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            issign  <=  data_a[31] ^ data_b[31] ;
        end
        else ;
    end
end


//----------------------------------------------------------------------------------
// calculation of second steps
//----------------------------------------------------------------------------------
assign expdiff = pre_data_b[31:24] - 8'd127 ; // + (~8'd127 + 1)

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        expon <=  10'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            expon <=  10'd0 ;
        end
        else if ( cur_state == cal_step2 ) begin
            expon <=  pre_data_a[31:24] + expdiff ; 
        end
        else if ( cur_state == cal_step4 ) begin
            if( temp[47] == 1'b1 ) begin 
                expon <=  expon + 1'b1 ;  
            end
            else if( temp[46] == 1'b1 ) begin 
                expon <=  expon ; 
            end
            else if( temp[45] == 1'b1 ) begin 
                expon <=  expon - 1'b1 ; 
            end 
            else if ( temp == 47'd0 ) begin  // repaired in 2018/1/19 14:07:45 for multi 0
                expon   <=   10'd0 ;
            end
        end
        else  ;
    end
end

//----------------------------------------------------------------------------------
// calculation of third steps
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        temp <=  48'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            temp <=  48'd0 ;
        end
        else if ( cur_state == cal_step3 && fbm_done == 1'b1 ) begin
            temp <=  fbm_result ;
        end
        else if ( cur_state == cal_step4 ) begin
            if( temp[47] == 1'b1 ) begin 
                temp  <=  temp ; 
            end
            else if( temp[46] == 1'b1 ) begin 
                temp  <=  temp << 1 ; 
            end
            else if( temp[45] == 1'b1 ) begin 
                temp  <=  temp << 2 ; 
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fbm_start_trig  <=  1'b0 ;
    end
    else begin
        if ( cur_state == cal_step2 ) begin
            fbm_start_trig  <=  1'b1 ; 
        end
        else begin
            fbm_start_trig  <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fbm_data_a  <=  25'd0 ;
        fbm_data_b  <=  25'd0 ;
    end
    else begin
        if ( cur_state == cal_step2 ) begin
            fbm_data_a  <=  { 1'b0, pre_data_a[23:0]} ;
            fbm_data_b  <=  { 1'b0, pre_data_b[23:0]} ;
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
            end         
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
                result_t    <=  {1'b0, 8'd0, 23'd0} ; // repaired in 2018/1/19 14:11:10 for multi 0
            end
            else if ( temp[23] == 1'b1 && temp[47:24] == 24'hffffff ) begin 
                result_t    <=  { issign, expon[7:0] + 1'b1, temp[46:24] + 1'b1 } ; 
            end
            else if ( temp[23] == 1'b1 ) begin
                result_t    <=  { issign, expon[7:0], temp[46:24] + 1'b1 } ; 
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
// BOOTH_MULTIM
//----------------------------------------------------------------------------------
assign done = { isover, isunder, iszero, isdone } ;
assign result = result_t ;

    BOOTH_MULTIM                U_BOOTH_MULTIM
    (
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),
    .start_trig                 ( fbm_start_trig            ),
    .data_a                     ( fbm_data_a                ),
    .data_b                     ( fbm_data_b                ),
    .result                     ( fbm_result                ),
    .done                       ( fbm_done                  )
     ) ;

endmodule
