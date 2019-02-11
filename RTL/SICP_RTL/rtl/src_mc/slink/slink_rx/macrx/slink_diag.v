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

module  SLINK_DIAG
    (
    // clock & reset
    clk_125m                    ,   
    rst_125m                    ,   

    chn_break_err               ,   
    chn_pkt_len_err             ,   
    chn_pkt_tick_err            ,   
    chn_pkt_crc_err             ,   
    chn_pkt_delay_err           ,
    chn_pkt_eop                 ,   
   
    slink_err                    
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   LEN_ERR_THRESHOLD   =   8'd10 ;
parameter   TICK_ERR_THRESHOLD  =   8'd10 ;
parameter   CRC_ERR_THRESHOLD   =   8'd10 ;
parameter   DELAY_ERR_THRESHOLD =   8'd100 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_125m                            ;   
input   wire                    rst_125m                            ;   

input   wire                    chn_break_err                       ;   
input   wire                    chn_pkt_len_err                     ;   
input   wire                    chn_pkt_tick_err                    ;   
input   wire                    chn_pkt_crc_err                     ;   
input   wire                    chn_pkt_delay_err                   ;   
input   wire                    chn_pkt_eop                         ;   

// declare output signal
output  wire                    slink_err                           ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [4:0]               chn_err                             ;   
wire                            slink_err_tmp                       ;   
wire                            online_detect                       ;  
wire                            delay_err_fall                      ;   

// reg signal
reg                             chn_break_err_d1                    ;   
reg         [7:0]               pkt_len_err_cnt                     ;   
reg         [7:0]               pkt_tick_err_cnt                    ;   
reg         [7:0]               pkt_crc_err_cnt                     ;   
reg         [7:0]               pkt_delay_err_cnt                   ;   

reg                             pkt_len_err                         ;   
reg                             pkt_tick_err                        ;   
reg                             pkt_crc_err                         ;  
reg                             delay_err_d1                        ;   
reg                             pkt_delay_err                       ;   

reg                             slink_err_tmp_d1                    ;   
reg                             slink_err_tmp_d2                    ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

always @ ( posedge clk_125m ) begin
    chn_break_err_d1  <=   chn_break_err ;
end

assign  online_detect   =   ( chn_break_err == 1'b0 && chn_break_err_d1 == 1'b1 ) ? 1'b1 : 1'b0 ;    

//----------------------------------------------------------------------------------
// fault judge
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        pkt_len_err_cnt  <=   8'h00 ;
    end
    else begin
        if ( online_detect == 1'b1 ) begin
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
end

always @ ( posedge clk_125m ) begin
    if( pkt_len_err_cnt >= LEN_ERR_THRESHOLD ) begin
        pkt_len_err  <=   1'b1 ;
    end
    else begin
        pkt_len_err  <=   1'b0 ;
    end
end

always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        pkt_tick_err_cnt  <=   8'h00 ;
    end
    else begin
        if ( online_detect == 1'b1 ) begin
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
end

always @ ( posedge clk_125m ) begin
    if( pkt_tick_err_cnt >= TICK_ERR_THRESHOLD ) begin
        pkt_tick_err  <=   1'b1 ;
    end
    else begin
        pkt_tick_err  <=   1'b0 ;
    end
end

always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        pkt_crc_err_cnt  <=   8'h00 ;
    end
    else begin
        if ( online_detect == 1'b1 ) begin
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
end

always @ ( posedge clk_125m ) begin
    if( pkt_crc_err_cnt >= CRC_ERR_THRESHOLD ) begin
        pkt_crc_err  <=   1'b1 ;
    end
    else begin
        pkt_crc_err  <=   1'b0 ;
    end
end

always @ ( posedge clk_125m ) begin
    delay_err_d1  <=   chn_pkt_delay_err ;
end

assign  delay_err_fall   =   ( chn_pkt_delay_err == 1'b0 && delay_err_d1 == 1'b1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        pkt_delay_err_cnt  <=   8'h00 ;
    end
    else begin
        if ( online_detect == 1'b1 ) begin
            pkt_delay_err_cnt  <=   8'h00 ;
        end
        else if( pkt_delay_err_cnt == 8'hff ) begin
            pkt_delay_err_cnt  <=   pkt_delay_err_cnt ;
        end
        else if( delay_err_fall == 1'b1 ) begin
            pkt_delay_err_cnt  <=   pkt_delay_err_cnt + 1'b1 ;
        end
        else ;
    end
end

always @ ( posedge clk_125m ) begin
    if( pkt_delay_err_cnt >= DELAY_ERR_THRESHOLD || delay_err_d1 == 1'b1 ) begin
        pkt_delay_err  <=   1'b1 ;
    end
    else begin
        pkt_delay_err  <=   1'b0 ;
    end
end

//----------------------------------------------------------------------------------
// slink error generator
//----------------------------------------------------------------------------------
assign  chn_err =   { chn_break_err , pkt_len_err , pkt_tick_err , pkt_crc_err , delay_err_d1 } ;
assign  slink_err_tmp   = | chn_err ;   

always @ ( posedge clk_125m ) begin
    slink_err_tmp_d1  <=   slink_err_tmp ;
    slink_err_tmp_d2  <=   slink_err_tmp_d1 ;
end

assign  slink_err   =   slink_err_tmp_d2 ;   

endmodule

