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

module E2PREG
    (	
        clk_sys                 ,   // system clock
        rst_sys_n               ,   // system reset
       
        wr_dly_trig             ,   
        reg_addr                ,
        wr_en                   ,   
        wr_value0               ,   
        wr_value1               ,   
        wr_value2               ,   
        wr_value3               ,   
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
parameter   CON_CNT         =   5'd16             ;

parameter   RDY_IDLE        =   16'b0000000000100000 ;
parameter   CON_RDY         =   16'b0000000000000001 ;
parameter   RD_CON          =   16'b0000000000000100 ;
parameter   WR_RDY          =   16'b0000001000000000 ;
parameter   WR_DLY          =   16'b0000100000000000 ;
parameter   RD_RDY          =   16'b0010000000000000 ;
parameter   RD_STU_RDY      =   16'b0000000010000000 ; 
parameter   WR_WREN         =   16'b0000000001000000 ;

localparam  CTL_REG         =   8'h55             ; // CONTROL Register
localparam  DATA_REG        =   8'h01             ; // DATA Register
localparam  RDBK_REG        =   8'h02             ; // Readback register value as per Read Address
localparam  RST_REG         =   8'h56             ; // RESET Register

localparam  WREN            =   8'h06             ; // Set Write Enable Latch
localparam  WRDI            =   8'h04             ; // Reset Write Enable Latch
localparam  RDSR            =   8'h05             ; // Read Status Register
localparam  WRSR            =   8'h01             ; // Write Status Register
localparam  READ            =   8'h03             ; // Read Data from Memory Array
localparam  WRITE           =   8'h02             ; // Write Data to Memory Array

localparam  SR_CON          =   8'h02             ; // WPEN , WEN

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   
input   wire    [13:0]          cur_state                           ;   
input   wire    [4:0]           wr_cnt                              ;   
input   wire    [15:0]          reg_addr                            ;  
input   wire                    wr_en                               ;   
input   wire    [31:0]          wr_value0                           ;   
input   wire    [31:0]          wr_value1                           ;   
input   wire    [31:0]          wr_value2                           ;   
input   wire    [31:0]          wr_value3                           ;   
input   wire                    wr_dly_trig                         ;   
// declare output signal
output  reg     [151:0]         wr_data                             ;   
output  reg                     wr_trig                             ;   
output  reg                     rd_trig                             ;   
output  reg     [7:0]           rw_len                              ;   

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
        if ( cur_state == CON_RDY && ( wr_cnt == 5'd0 || wr_cnt == 5'd1 || wr_cnt == 5'd2 ) || cur_state == WR_RDY || cur_state == RDY_IDLE && wr_en == 1'b1 || cur_state == WR_DLY && wr_dly_trig == 1'b1 ) begin
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
        case ( cur_state )
            CON_RDY : begin
                if ( wr_cnt == 5'd0 ) begin
                    rw_len   <=  8'd8 ;
                end
                else if ( wr_cnt == 5'd1 ) begin
                    rw_len   <=  8'd56 ;
                end
                else if ( wr_cnt == 5'd2 ) begin
                    rw_len   <=  8'd8 ;
                end
                else ;
            end
            RD_CON : begin
                rw_len   <=  8'd56 ;
            end
            RDY_IDLE : begin
                if ( wr_en == 1'b1 ) begin
                    rw_len   <=  8'd8 ;
                end
                else ;
            end
            RD_STU_RDY : begin
                rw_len   <=  8'd16 ;
            end
            WR_RDY : begin
                rw_len   <=  8'd56 ;
                rw_len   <=  8'd152 ;
            end
            WR_DLY : begin
                if ( wr_dly_trig == 1'b1 ) begin
                    rw_len  <=   8'd8 ;
                end
                else ;
            end
            RD_RDY : begin
                rw_len   <=  8'd56 ;
            end
        endcase 
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_data   <=  152'd0 ;
    end
    else begin
        case ( cur_state )
            CON_RDY : begin
                if ( wr_cnt == 5'd0 ) begin
                    wr_data   <=  152'd0 ; //{ 48'd0, WREN } ;// 
                end
                else if ( wr_cnt == 5'd1 ) begin
                    wr_data   <=  152'd0 ; //{ WRITE, 16'h1000, 32'h87654321 } ; // 56'h000000 ; // 
                end
                else if ( wr_cnt == 5'd2 ) begin
                    wr_data   <=  152'd0 ; //{ 48'd0, WRDI } ; //
                end
                else ;
            end
            RD_CON : begin
                wr_data   <=  { 96'd0, READ, 16'h1004, 32'h00000000 } ;
            end
            RDY_IDLE : begin
                if ( wr_en == 1'b1 ) begin
                    wr_data   <=  { 144'd0, WREN } ;
                end
                else ;
            end
            RD_STU_RDY : begin
                wr_data   <=  { 136'd0, RDSR, 8'b00 } ;
            end
            WR_RDY : begin
                wr_data   <=  { WRITE, reg_addr, wr_value0, wr_value1, wr_value2, wr_value3 } ;
            end
            WR_DLY : begin
                if ( wr_dly_trig == 1'b1 ) begin
                    wr_data   <= 152'd0 ; // { 48'd0, WRDI } ;  // 
                end
                else ;
            end
            RD_RDY : begin
                wr_data   <=  { 96'd0, READ, reg_addr, 32'h00000000 } ;
            end
        endcase
    end
end

endmodule
