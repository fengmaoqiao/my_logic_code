// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SLINK_DIAG
// CREATE DATE      :   2017-12-12
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-12-12  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   SLINK diagnose
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active hign
// Clock Domains    :   clk_125m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`include "DEFINES.v"

module  COM_SLINK_DIAG
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   

    chn_enable                  ,   

    chn_break_err               ,   
    chn_pkt_len_err             ,   
    chn_pkt_tick_err            ,   
    chn_pkt_crc_err             ,   
    chn_pkt_delay_err           ,
    chn_pkt_eop                 ,   
   
    slink_err                   , 

    debug_bus 
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   LEN_ERR_THRESHOLD   =   8'd5 ;
parameter   TICK_ERR_THRESHOLD  =   8'd50 ;
parameter   CRC_ERR_THRESHOLD   =   8'd5 ;
parameter   DELAY_ERR_THRESHOLD =   8'd5 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   

input   wire                    chn_enable                          ;   
input   wire                    chn_break_err                       ;   
input   wire                    chn_pkt_len_err                     ;   
input   wire                    chn_pkt_tick_err                    ;   
input   wire                    chn_pkt_crc_err                     ;   
input   wire                    chn_pkt_delay_err                   ;   
input   wire                    chn_pkt_eop                         ;   

// declare output signal
output  wire                    slink_err                           ;   
output  wire        [15:0]      debug_bus                           ;  

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [4:0]               chn_err                             ;   
wire                            slink_err_tmp                       ;   

// reg signal
reg         [7:0]               pkt_len_err_cnt                     ;   
reg         [7:0]               pkt_tick_err_cnt                    ;   
reg         [7:0]               pkt_crc_err_cnt                     ;   
reg         [7:0]               pkt_delay_err_cnt                   ;   

reg                             pkt_len_err                         ;   
reg                             pkt_tick_err                        ;   
reg                             pkt_crc_err                         ;  
reg                             pkt_delay_err                       ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// fault judge
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_len_err_cnt  <=   8'h00 ;
    end
    else if( pkt_len_err_cnt == 8'hff ) begin
        pkt_len_err_cnt  <=   pkt_len_err_cnt ;
    end
    else if( chn_pkt_len_err == 1'b1 && chn_pkt_eop == 1'b1 ) begin
        pkt_len_err_cnt  <=   pkt_len_err_cnt + 1'b1 ;
    end
    else ;
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_len_err  <=   1'b0 ;
    end
    else if( pkt_len_err_cnt >= LEN_ERR_THRESHOLD ) begin
        pkt_len_err  <=   1'b1 ;
    end
    else begin
        pkt_len_err  <=   1'b0 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_tick_err_cnt  <=   8'h00 ;
    end
    else if( pkt_tick_err_cnt == 8'hff ) begin
        pkt_tick_err_cnt  <=   pkt_tick_err_cnt ;
    end
    else if( chn_pkt_tick_err == 1'b1 && chn_pkt_eop == 1'b1 ) begin
        pkt_tick_err_cnt  <=   pkt_tick_err_cnt + 1'b1 ;
    end
    else ;
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_tick_err  <=   1'b0 ;
    end
    else if( pkt_tick_err_cnt >= TICK_ERR_THRESHOLD ) begin
        pkt_tick_err  <=   1'b1 ;
    end
    else begin
        pkt_tick_err  <=   1'b0 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_crc_err_cnt  <=   8'h00 ;
    end
    else if( pkt_crc_err_cnt == 8'hff ) begin
        pkt_crc_err_cnt  <=   pkt_crc_err_cnt ;
    end
    else if( chn_pkt_crc_err == 1'b1 && chn_pkt_eop == 1'b1 ) begin
        pkt_crc_err_cnt  <=   pkt_crc_err_cnt + 1'b1 ;
    end
    else ;
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_crc_err  <=   1'b0 ;
    end
    else if( pkt_crc_err_cnt >= CRC_ERR_THRESHOLD ) begin
        pkt_crc_err  <=   1'b1 ;
    end
    else begin
        pkt_crc_err  <=   1'b0 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_delay_err_cnt  <=   8'h00 ;
    end
    else if( pkt_delay_err_cnt == 8'hff ) begin
        pkt_delay_err_cnt  <=   pkt_delay_err_cnt ;
    end
    else if( chn_pkt_delay_err == 1'b1 ) begin
        pkt_delay_err_cnt  <=   pkt_delay_err_cnt + 1'b1 ;
    end
    else ;
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_delay_err  <=   1'b0 ;
    end
    else if( pkt_delay_err_cnt >= DELAY_ERR_THRESHOLD ) begin
        pkt_delay_err  <=   1'b1 ;
    end
    else begin
        pkt_delay_err  <=   1'b0 ;
    end
end

//----------------------------------------------------------------------------------
// slink error generator
//----------------------------------------------------------------------------------
assign  chn_err =   { chn_break_err , pkt_len_err , pkt_tick_err , pkt_crc_err , pkt_delay_err } ;
assign  slink_err   =   chn_enable == 1'b1 ? ( | chn_err ) : 1'b0 ;   


endmodule

