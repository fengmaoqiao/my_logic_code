// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-06-20
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-06-20  TingtingGan     Original
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
`include "DEFINES.v"

module PMATX
    (
    clk_125m                    ,   
    rst_125m                    ,   

    pcstx_pmatx_data            ,   
    lvds_txp_out                ,   
    lvds_txn_out                  
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_125m                            ;   
input   wire                    rst_125m                            ;   
input   wire        [9:0]       pcstx_pmatx_data                    ;   

// declare output signal
output  wire                    lvds_txp_out                        ;   
output  wire                    lvds_txn_out                        ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg         [9:0]               pmatx_data_d1                       ;   
reg         [9:0]               pmatx_data_d2                       ;   
reg         [9:0]               pmatx_data_d3                       ;   
reg         [9:0]               pmatx_data_d4                       ;   
reg                             lvds_tx_out                         ;  
reg         [3:0]               bit_cnt                             ;   

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// LVDS sigle-ended convert to difference
//----------------------------------------------------------------------------------
    OUTBUF_DIFF                 #               
    ( 
    .IOSTD                      ( "LVDS33"                  )
    ) 
    U_OUTBUF_DIFF
    (
    .D                          ( lvds_tx_out               ), 
    .PADP                       ( lvds_txp_out              ), 
    .PADN                       ( lvds_txn_out              )
    );
        
//----------------------------------------------------------------------------------
// parallel to serial
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        pmatx_data_d1    <=   10'h00 ;
        pmatx_data_d2    <=   10'h00 ;
        pmatx_data_d3    <=   10'h00 ;
    end
    else begin
        pmatx_data_d1    <=   pcstx_pmatx_data ;
        pmatx_data_d2    <=   pmatx_data_d1 ;
        pmatx_data_d3    <=   pmatx_data_d2 ;
    end
end

always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        bit_cnt    <=   4'h0 ;
    end
    else begin
        if( bit_cnt == 4'h9 ) begin
            bit_cnt    <=   4'h0 ;
        end
        else begin
            bit_cnt    <=   bit_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        pmatx_data_d4    <=   10'h00 ;
    end
    else begin
        if( bit_cnt == 4'h9 ) begin
            pmatx_data_d4    <=   pmatx_data_d3 ;
        end
        else begin
            pmatx_data_d4    <=   { pmatx_data_d4[0] , pmatx_data_d4[9:1] } ;
        end
    end
end

always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        lvds_tx_out <=   1'b1 ;
    end
    else begin
        lvds_tx_out <=   pmatx_data_d4[0] ;
    end
end

endmodule

