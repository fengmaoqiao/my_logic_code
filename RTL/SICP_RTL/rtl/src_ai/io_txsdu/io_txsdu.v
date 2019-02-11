// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   IO_TXSDU
// CREATE DATE      :   2017-09-26
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-26  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   receive path schedule machine
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

module IO_TXSDU
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m_n                 ,   
  
    // status feedback frame interface
    txsdu_sfm_rdreq             ,   
    sfm_txsdu_empty             ,   
    sfm_txsdu_dval              ,   
    sfm_txsdu_data              ,  

    // data frame 
    txsdu_upm_rdreq             ,   
    upm_txsdu_empty             ,   
    upm_txsdu_dval              ,   
    upm_txsdu_data              ,   

    // slink interface  
    slink_txsdu_rdreq0          ,   
    slink_txsdu_rdreq1          ,   
    txsdu_slink_dval0           ,   
    txsdu_slink_data0           ,   
    txsdu_slink_dval1           ,   
    txsdu_slink_data1           , 
    txsdu_ram_err
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m_n                         ;   

input   wire                    sfm_txsdu_empty                     ;   
input   wire                    sfm_txsdu_dval                      ;   
input   wire    [17:0]          sfm_txsdu_data                      ;   
input   wire                    upm_txsdu_empty                     ;   
input   wire                    upm_txsdu_dval                      ;   
input   wire    [17:0]          upm_txsdu_data                      ;   
input   wire                    slink_txsdu_rdreq0                  ;   
input   wire                    slink_txsdu_rdreq1                  ; 

// declare output signal
output  wire                    txsdu_sfm_rdreq                     ;   
output  wire                    txsdu_upm_rdreq                     ;   
output  wire                    txsdu_slink_dval0                   ;   
output  wire    [17:0]          txsdu_slink_data0                   ;   
output  wire                    txsdu_slink_dval1                   ;   
output  wire    [17:0]          txsdu_slink_data1                   ;   
output  wire    [1:0]           txsdu_ram_err                       ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [1:0]               chn_sdu_empty                       ;   
wire        [1:0]               chn_sdu_dval                        ;   
wire        [1:0]               sdu_chn_rden                        ; 

// reg signal
reg         [17:0]              chn_sdu_data                        ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign  chn_sdu_empty   =   { upm_txsdu_empty , sfm_txsdu_empty } ;
assign  chn_sdu_dval    =   { upm_txsdu_dval , sfm_txsdu_dval } ;

always @( * ) begin
    case( chn_sdu_dval )
        2'b01   :   chn_sdu_data    =  sfm_txsdu_data ; 
        2'b10   :   chn_sdu_data    =  upm_txsdu_data ; 
        default :   chn_sdu_data    =  18'h00     ; 
    endcase
end

assign  txsdu_sfm_rdreq      =  sdu_chn_rden[0] ;
assign  txsdu_upm_rdreq      =  sdu_chn_rden[1] ;

//----------------------------------------------------------------------------------
// 2 - 1 schedule machine instance
//----------------------------------------------------------------------------------
    TX_SDU2S1                   U_TX_SDU2S1
    ( 
    .clk_sys                    ( clk_12_5m                 ),
    .rst_sys_n                  ( rst_12_5m_n               ),
   
    .chn_sdu_dval               ( chn_sdu_dval              ),
    .chn_sdu_data               ( chn_sdu_data              ),
    .chn_sdu_empty              ( chn_sdu_empty             ),
    .sdu_chn_rden               ( sdu_chn_rden              ),

    .fifo_rdreq0                ( slink_txsdu_rdreq0        ),
    .fifo_rd_dval0              ( txsdu_slink_dval0         ),
    .fifo_rd_data0              ( txsdu_slink_data0         ),
    .fifo_rdreq1                ( slink_txsdu_rdreq1        ),
    .fifo_rd_dval1              ( txsdu_slink_dval1         ),
    .fifo_rd_data1              ( txsdu_slink_data1         ),
    .ram_dgd_err                ( txsdu_ram_err             )
    );


endmodule
