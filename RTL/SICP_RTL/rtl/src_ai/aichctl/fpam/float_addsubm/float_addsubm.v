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

module FLOAT_ADDSUBM
    (
        rst_sys_n               ,   
        clk_sys                 ,   

        add_sub_sel             ,   
        data_a                  ,   
        data_b                  ,   
        start_trig              ,   

        done                    ,   
        result                     
    ) ;

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
localparam  cal_step0       = 9'b000000000    ;
localparam  cal_step1       = 9'b000000001    ;
localparam  cal_step2       = 9'b000000010    ;
localparam  cal_step3       = 9'b000000100    ;
localparam  cal_step4       = 9'b000001000    ;
localparam  cal_step5       = 9'b000010000    ;
localparam  cal_step6       = 9'b000100000    ;
localparam  cal_step7       = 9'b001000000    ;
localparam  cal_step8       = 9'b010000000    ;
localparam  cal_step9       = 9'b100000000    ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire    [31:0]          data_a                              ;   
input   wire    [31:0]          data_b                              ;   
input   wire                    start_trig                          ;   
input   wire                    add_sub_sel                         ;   
// declare output signal
output  wire    [3:0]           done                                ;   
output  wire    [31:0]          result                              ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg     [56:0]                  pre_data_a                          ;   
reg     [56:0]                  pre_data_b                          ;   
reg     [48:0]                  temp                                ;   
reg     [48:0]                  tempa                               ;   
reg     [48:0]                  tempb                               ;   
reg     [31:0]                  result_t                            ;   
reg     [9:0]                   expon                               ;   
reg     [7:0]                   expdiff                             ;   
reg                             issign                              ;   
reg                             isover                              ;   
reg                             isunder                             ;   
reg                             iszero                              ;   
reg                             isdone                              ;   
reg     [8:0]                   cur_state                           ;   
reg     [8:0]                   next_state                          ;   
reg     [4:0]                   bit_cnt                             ;   
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
            next_state = cal_step4 ;
        end
        cal_step4 : begin
            next_state = cal_step5 ;
        end
        cal_step5 : begin
            next_state = cal_step6 ;
        end
        cal_step6 : begin
            next_state = cal_step7 ;
        end
        cal_step7 : begin
            if ( bit_cnt == 5'd25 || temp[47-bit_cnt] == 1'b1 ) begin
                next_state = cal_step8 ;
            end
            else begin
                next_state = cal_step7 ;
            end
        end
        cal_step8 : begin
            next_state = cal_step9 ;
        end
        cal_step9 : begin
            next_state = cal_step0 ;
        end
        default : begin
            next_state = cal_step0 ;
        end
    endcase
end

//----------------------------------------------------------------------------------
// calculation of firest steps
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pre_data_a   <=   57'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            pre_data_a   <=   57'd0 ;
        end
        else if ( cur_state == cal_step1 ) begin
            if ( data_a[30:0] == 31'd0 ) begin
                pre_data_a  <=   57'd0 ;
            end
            else begin
                pre_data_a  <=  { data_a[31], data_a[30:23], 2'b01, data_a[22:0], 23'd0 } ;
            end
        end
        else if ( cur_state == cal_step3 ) begin 
            if ( expon[8] == 1'b1 ) begin
                pre_data_a[47:0]  <=  pre_data_a[47:0] >> expdiff ; 
                pre_data_a[55:48]  <=  pre_data_b[55:48] ;
            end
            else ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pre_data_b   <=   57'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            pre_data_b   <=   57'd0 ;
        end
        else if ( cur_state == cal_step1 ) begin
            if ( data_b[30:0] == 31'd0 ) begin
                pre_data_b  <=   57'd0 ;
            end
            else begin
                pre_data_b  <=  { data_b[31], data_b[30:23], 2'b01, data_b[22:0], 23'd0 } ;
            end
        end
        else if ( cur_state == cal_step3 ) begin 
            if ( expon[8] == 1'b0 ) begin
                pre_data_b[47:0]  <=  pre_data_b[47:0] >> expdiff ; 
                pre_data_b[55:48]  <=  pre_data_a[55:48] ;
            end
            else ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        expon   <=   10'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            expon   <=  10'd0 ;
        end
        else if ( cur_state == cal_step1 ) begin 
            expon  <=  data_a[30:23] - data_b[30:23] ;
        end
        else if ( cur_state == cal_step6 ) begin
            expon  <=  {2'b00, pre_data_a[55:48]} ;
        end
        else if ( cur_state == cal_step8 ) begin
            if ( bit_cnt == 5'd0 ) begin
                expon    <=  expon + 1'b1 ;
            end
            else if ( bit_cnt == 5'd25 ) begin
                expon   <=   10'd0 ;
            end
            else begin
                expon    <=  expon - (bit_cnt-1'b1) ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        expdiff  <=  8'h00 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            expdiff  <=  8'h00 ;
        end
        else if ( cur_state == cal_step2 ) begin
            if ( expon[8] == 1'b1 ) begin 
                expdiff  <=  ~expon[7:0] + 1'b1 ;
            end
            else begin 
                expdiff  <=  expon[7:0] ;
            end
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// calculation of thirth steps
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        tempa  <= 49'd0 ; 
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            tempa  <= 49'd0 ;
        end
        else if ( cur_state == cal_step4 ) begin
            if ( pre_data_a[47:0] == 48'd0 ) begin // repaired in 2018.07.03
                tempa   <=   49'd0 ;
            end
            else begin
                tempa  <=  pre_data_a[56] ? { pre_data_a[56], (~pre_data_a[47:0] + 1'b1) } : { pre_data_a[56], pre_data_a[47:0] } ; 
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        tempb  <=  49'd0 ; 
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            tempb  <= 49'd0 ;
        end
        else if ( cur_state == cal_step4 ) begin
            if ( pre_data_b[47:0] == 48'd0 ) begin // repaired in 2018.07.03
                tempb   <=   49'd0 ;
            end
            else begin
                tempb  <=  pre_data_b[56] ? { pre_data_b[56], (~pre_data_b[47:0] + 1'b1) } : { pre_data_b[56], pre_data_b[47:0] } ; 
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
        temp   <= 49'd0 ; 
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            temp  <= 49'd0 ;
        end
        else if ( cur_state == cal_step5 ) begin
            if ( add_sub_sel == 1'b1 ) begin
                temp <=  tempa + tempb ;
            end
            else begin
                temp <=  tempa - tempb ;
            end
        end
        else if ( cur_state == cal_step6 ) begin
            if( temp[48] == 1'b1) begin
                temp    <=  ~temp + 1'b1 ; 
                //temp <= ~(~temp - 1'b1 ) ;
            end
            else if ( temp[22] == 1'b1 ) begin
                temp[47:23] <=  temp[47:23] + 1'b1 ; // repaired in 2017.10.02
            end
        end
        else if ( cur_state == cal_step8 ) begin
            if ( bit_cnt == 5'd0 ) begin
                temp    <=  temp >> 1 ;
            end
            else begin
                temp    <=  temp << (bit_cnt-1'b1) ;
            end
        end
    end
end

//----------------------------------------------------------------------------------
// calculation of sixth steps
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        issign  <=  1'b0 ;
    end
    else begin
        if ( cur_state == cal_step6 ) begin
            issign  <=  temp[48] ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// calculation of seventh steps
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        bit_cnt <=  5'd0 ;
    end
    else begin
        if ( cur_state == cal_step0 ) begin
            bit_cnt <=  5'd0 ;
        end
        else if ( cur_state == cal_step7 && ( bit_cnt != 5'd25 && temp[47-bit_cnt] == 1'b0 ) ) begin
            bit_cnt <=  bit_cnt + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// calculation of ninth steps
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        isover   <= 1'd0 ; 
    end
    else begin
         if ( cur_state == cal_step9 ) begin
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
        if ( cur_state == cal_step9 ) begin
            if( expon[9:8] == 2'b11 ) begin 
                isunder <=  1'b1 ; 
            end  // E Underflow
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
        if ( cur_state == cal_step9 ) begin
            if( temp[46:23] == 24'd0 ) begin 
                iszero  <=  1'b1 ; // M Zero
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
        if ( cur_state == cal_step9 ) begin
            if( expon[9:8] == 2'b01 ) begin
                result_t    <=  {1'b0,8'd127, 23'd0} ; // E Overflow
            end
            else if ( expon[9:8] == 2'b11 ) begin
                result_t    <=  {1'b0,8'd127, 23'd0} ; // E Underflow
            end
            else if ( temp[46:23] == 24'd0 ) begin
                result_t    <=  {1'b0, 8'd0, 23'd0} ; // M Zero
            end
            else begin
                result_t    <=  { issign, expon[7:0], temp[45:23] } ; // okay without normalise
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        isdone    <=  1'b0 ;
    end
    else begin
        if ( cur_state == cal_step9 ) begin
            isdone    <=  1'b1 ;
        end
        else begin
            isdone    <=  1'b0 ;
        end
    end
end

assign done = { isover, isunder, iszero, isdone } ;
assign result = result_t ;

endmodule
