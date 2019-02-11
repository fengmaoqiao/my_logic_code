// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SLINK_TX
// CREATE DATE      :   2017-08-22
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-22  TingtingGan     Original
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

module  COM_SLINK_TX
    (
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    clk_125m                    ,   
    rst_125m                    ,  

    mmtx_mactx_data             ,   
    mmtx_mactx_dval             ,   
    mactx_mmtx_rdreq            ,   

    lvds_txp_out                ,   
    lvds_txn_out                ,  

    slink_tx_eop    
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   
input   wire                    clk_125m                            ;   
input   wire                    rst_125m                            ;   
input   wire    [17:0]          mmtx_mactx_data                     ;   
input   wire                    mmtx_mactx_dval                     ;   

// declare output signal
output  wire                    lvds_txp_out                        ;   
output  wire                    lvds_txn_out                        ;   
output  wire                    mactx_mmtx_rdreq                    ;  
output  wire                    slink_tx_eop                        ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            mactx_pcstx_dval                    ;   
wire        [7:0]               mactx_pcstx_data                    ;   
wire        [9:0]               pcstx_pmatx_data                    ;  

// reg signal

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

    COM_MACTX                       U_MACTX
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .mmtx_mactx_data            ( mmtx_mactx_data           ),
	.mmtx_mactx_dval            ( mmtx_mactx_dval           ),   
    .mactx_mmtx_rdreq           ( mactx_mmtx_rdreq          ),
    .mactx_pcstx_data           ( mactx_pcstx_data          ),
    .mactx_pcstx_dval           ( mactx_pcstx_dval          ),
    .slink_tx_eop               ( slink_tx_eop              )
    );

    PCSTX                       U_PCSTX
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .mactx_pcstx_data           ( mactx_pcstx_data          ),
    .mactx_pcstx_dval           ( mactx_pcstx_dval          ),
    .pcstx_pmatx_data           ( pcstx_pmatx_data          )
    );

    PMATX                       U_PMATX
    (
    .clk_125m                   ( clk_125m                  ),
    .rst_125m                   ( rst_125m                  ),
    .pcstx_pmatx_data           ( pcstx_pmatx_data          ),
    .lvds_txp_out               ( lvds_txp_out              ),
    .lvds_txn_out               ( lvds_txn_out              )
    );

endmodule

