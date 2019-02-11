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

module ADTREG
    (	
        clk_sys                 ,   // system clock
        rst_sys_n               ,   // system reset
       
        wr_value                ,   
        wr_cnt                  ,
        cur_state               ,   
        wr_trig                 ,   
        rd_trig                 ,   
        rw_len                  ,   
        wr_data
	) ;

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

parameter  CON_RDY         =   12'b000000000001     ;
parameter  RD_CON          =   12'b000000000100     ;
parameter  RD_STU_RDY      =   12'b000001000000     ;
parameter  RD_RDY          =   12'b000100000000     ;

localparam  WR              = 1'b0 ;
localparam  RD              = 1'b1 ;


localparam  STU_REG         = 3'b000             ; // CONTROL Register
localparam  CON_REG         = 3'b001             ; // DATA Register
localparam  DATA_REG        = 3'b010             ; // Readback register value as per Read Address
localparam  ID_REG          = 3'b011             ; // RESET Register
localparam  TCRIT_REG       = 3'b100             ; // RESET Register
localparam  THYSY_REG       = 3'b101             ; // RESET Register
localparam  THIGH_REG       = 3'b110             ; // RESET Register
localparam  TLOW_REG        = 3'b111             ; // RESET Register

//----------------------------------------------------------------------------------
// the configure register
//----------------------------------------------------------------------------------
localparam  PIN_AHIGH       = 1'b1              ;
localparam  PIN_ALOW        = 1'b0              ;
localparam  FAULT_QUE_ONE   = 2'b00             ; // the number of undertemperature/overtemperature faults that can occur before setting the INT and CT pins
                                                  //localparam  FAULT_QUE_TWO   = 2'b01             ; // continuous conversion
localparam  FAULT_QUE_THREE = 2'b10             ; // 
localparam  FAULT_QUE_FOUR  = 2'b11             ; // 
localparam  INT_MODE        = 1'b0              ; // 0 = interrupt mode
localparam  COM_MODE        = 1'b1              ; // 1 = comparator mode

localparam  OP_MODE_CTS     = 2'b00             ; // continuous conversion
localparam  OP_MODE_ONS     = 2'b01             ; // one shot Conversion time is typically 240 ms
localparam  OP_MODE_SPS     = 2'b10             ; // 1 SPS mode. Conversion time is typically 60 ms.
localparam  OP_MODE_SHD     = 2'b11             ; // shutdown. All circuitry except interface circuitry is powered down.
localparam  ADC_CONV_13BIT  = 1'b0              ; // 0 = 13-bit resolution Sign bit + 12 bits gives a temperature resolution of 0.0625°C.
localparam  ADC_CONV_16BIT  = 1'b0              ; // 1 = 16-bit resolution. Sign bit + 15 bits gives a temperature resolution of 0.0078125°C.

//----------------------------------------------------------------------------------
// ID resister
//----------------------------------------------------------------------------------
localparam  MAN_ID          = 5'b11000          ; // Contains the manufacturer identification number

localparam  TCRIT_VALUE     = 16'h4980          ; // 16-bit critical overtemperature limit, stored in twos complement format
localparam  THYST_VALUE     = 8'h05             ; // Hysteresis value, from 0°C to 15°C. Stored in straight binary format. The default setting is 5°C.
localparam  THIGH_VALUE     = 16'h2000          ; // 16-bit overtemperature limit, stored in twos complement format.
localparam  THLOW_VALUE     = 16'h0500          ; // 16-bit undertemperature limit, stored in twos complement format
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   
input   wire    [11:0]          cur_state                           ;   
input   wire    [4:0]           wr_cnt                              ;   
input   wire    [15:0]          wr_value                            ; 
// declare output signal
output  reg     [24:0]          wr_data                             ;   
output  reg                     wr_trig                             ;   
output  reg                     rd_trig                             ;   
output  reg     [5:0]           rw_len                              ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_trig   <=  1'b0 ;
    end
    else begin
        if ( cur_state == CON_RDY || cur_state == RD_RDY ) begin
            wr_trig   <=  1'b1 ;
        end
        else begin
            wr_trig   <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_trig  <=  1'b0 ;
    end
    else begin
        if ( cur_state == RD_CON || cur_state == RD_RDY || cur_state == RD_STU_RDY ) begin
            rd_trig  <=  1'b1 ;
        end
        else begin
            rd_trig  <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rw_len   <=  8'd0 ;
    end
    else begin
        if ( cur_state == CON_RDY ) begin
            case ( wr_cnt )
                5'd0 : begin
                    rw_len   <=  8'd16 ;
                end
                5'd1 : begin
                    rw_len   <=  8'd24 ;
                end
                5'd2 : begin
                    rw_len   <=  8'd16 ;
                end
                5'd3 : begin
                    rw_len   <=  8'd24 ;
                end
                5'd4 : begin
                    rw_len   <=  8'd24 ;
                end
                default : begin
                end
            endcase
        end
        else if ( cur_state == RD_CON ) begin
            rw_len   <=  8'd16 ;
        end
        else if ( cur_state == RD_STU_RDY ) begin
            rw_len   <=  8'd16 ;
        end
        else if ( cur_state == RD_RDY ) begin
            rw_len   <=  8'd24 ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_data   <=  24'h000000 ;
    end
    else begin
        if ( cur_state == CON_RDY ) begin
            case ( wr_cnt )
                5'd0 : begin
                    wr_data   <=  { 1'b0, WR, CON_REG, 3'd0, ADC_CONV_13BIT, OP_MODE_CTS, INT_MODE, PIN_AHIGH, PIN_AHIGH, FAULT_QUE_ONE } ; // 82c 16'h0820 ;//
                end
                5'd1 : begin
                    wr_data   <=  { 1'b0, WR, TCRIT_REG, 3'd0, TCRIT_VALUE } ; // 204980
                end
                5'd2 : begin
                    wr_data   <=  { 1'b0, WR, THYSY_REG, 3'd0, THYST_VALUE } ;
                end
                5'd3 : begin
                    wr_data   <=  { 1'b0, WR, THIGH_REG, 3'd0, THIGH_VALUE } ;
                end
                5'd4 : begin
                    wr_data   <=  { 1'b0, WR, TLOW_REG, 3'd0, THLOW_VALUE } ;
                end
                default : begin
                end
            endcase
        end
        else if ( cur_state == RD_CON ) begin
            wr_data   <=  16'd0 ;//{ 1'b0, RD, ID_REG, 3'd0 , 8'd0 } ;
        end
        else if ( cur_state == RD_STU_RDY ) begin
            wr_data   <=  { 8'd0, 1'b0, RD, STU_REG, 3'd0 , 8'd0 } ;
        end
        else if ( cur_state == RD_RDY ) begin
            wr_data   <=  { 1'b0, RD, DATA_REG, 3'd0 , 16'd0 } ;
            //wr_data <=   {  1'b0, RD, STU_REG, 3'd0 , 8'd0 } ;
        end
        else ;
    end
end

endmodule
