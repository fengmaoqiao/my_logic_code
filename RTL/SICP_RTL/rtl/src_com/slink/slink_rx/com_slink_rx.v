// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SLINK_RX
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

module  COM_SLINK_RX #
(
    parameter   CARD_TYPE       =   2'b00 , // MCU : 2'b00 , COM : 2'b01 , EX : 2'b10 , IO : 2'b11  
    parameter   FIFO_TYPE       =   2'b00 , // 00: deep is 1024 ; 01: deep is 2048 ; 10 : 4096
    parameter   DELAY_ERR_ACT   =   1'b1    // 0 : no delay error , 1 : check delay error
)
    (
    // clock & reset 
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    clk_125m_0                  ,   
    clk_125m_90                 ,   
    clk_125m_180                ,   
    clk_125m_270                ,   
    rst_125m                    ,  

    destin_addr_cfg             ,     
    source_addr_cfg             ,
    destin_addr_chk             ,
    source_addr_chk             ,    

    wd_timer                    ,   
    self_cfg_err                ,   
    rx_en                       ,
    lvds_rxp_in                 ,   
    lvds_rxn_in                 ,   
    mm_slink_rdreq              ,   

    slink_mm_empty              ,   
    slink_mm_dval               ,   
    slink_mm_data               ,  

    slink_rx_eop                ,   
    slink_err                      
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
input   wire                    clk_125m_0                          ;   
input   wire                    clk_125m_90                         ;   
input   wire                    clk_125m_180                        ;   
input   wire                    clk_125m_270                        ;   
input   wire                    rst_125m                            ;  

input   wire    [17:0]          destin_addr_cfg                     ;   
input   wire    [17:0]          source_addr_cfg                     ;   
input   wire    [3:0]           destin_addr_chk                     ; //enable DA check
input   wire    [3:0]           source_addr_chk                     ; //enable SA check

input   wire    [15:0]          wd_timer                            ;   // watchdog timer , used for detecting packet delay
input   wire                    self_cfg_err                        ;   
input   wire                    rx_en                               ;
input   wire                    lvds_rxp_in                         ;   
input   wire                    lvds_rxn_in                         ;   
input   wire                    mm_slink_rdreq                      ;   

// declare output signal
output  wire                    slink_mm_empty                      ;   
output  wire                    slink_mm_dval                       ;   
output  wire    [17:0]          slink_mm_data                       ; 
output  wire                    slink_rx_eop                        ;   
output  wire                    slink_err                           ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            macrx_llcrx_dval                    ;   
wire       [7:0]                macrx_llcrx_data                    ;   
wire                            macrx_llcrx_sop                     ;   
wire                            macrx_llcrx_eop                     ;   

wire                            llcrx_rxfifo_dval                   ;   
wire       [7:0]                llcrx_rxfifo_data                   ;   
wire                            llcrx_rxfifo_sop                    ;   
wire                            llcrx_rxfifo_eop                    ;   

wire                            pcsrx_macrx_dval                    ;   
wire                            pcsrx_macrx_sop                     ;   
wire                            pcsrx_macrx_eop                     ;   
wire        [7:0]               pcsrx_macrx_data                    ;   
wire                            pmarx_pcsrx_dval                    ;   
wire        [9:0]               pmarx_pcsrx_data                    ; 
wire                            pcs_err                             ;   

wire                            slink_addr_error                    ;   
wire                            slink_err_temp                      ;   
wire        [15:0]              rxchan_run_cycle                    ;   


// reg signal

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign slink_err = slink_err_temp || slink_addr_error;


    COM_BACDCRX                     #
    (
    .FIFO_TYPE                  ( FIFO_TYPE                 )
    )
    U_BACDCRX
    (
    .clk_wr                     ( clk_125m_0                ),
    .rst_wr                     ( rst_125m                  ),
    .clk_rd                     ( clk_12_5m                 ),
    .rst_rd                     ( rst_12_5m                 ),

    .llcrx_rxfifo_dval          ( llcrx_rxfifo_dval         ),
    .llcrx_rxfifo_sop           ( llcrx_rxfifo_sop          ),
    .llcrx_rxfifo_eop           ( llcrx_rxfifo_eop          ),
    .llcrx_rxfifo_data          ( llcrx_rxfifo_data         ),

    .mm_slink_rdreq             ( mm_slink_rdreq            ),
    .slink_mm_empty             ( slink_mm_empty            ),
    .slink_mm_dval              ( slink_mm_dval             ),
    .slink_mm_data              ( slink_mm_data             )
    );

    LLCRX 
    U_LLCRX
    (
    .clk_125m                   ( clk_125m_0                ),
    .rst_125m                   ( rst_125m                  ),

    .destin_addr_cfg            ( destin_addr_cfg           ),
    .source_addr_cfg            ( source_addr_cfg           ),
    .destin_addr_chk            ( destin_addr_chk           ),
    .source_addr_chk            ( source_addr_chk           ),

    .macrx_llcrx_data           ( macrx_llcrx_data          ),
    .macrx_llcrx_dval           ( macrx_llcrx_dval          ),
    .macrx_llcrx_sop            ( macrx_llcrx_sop           ),
    .macrx_llcrx_eop            ( macrx_llcrx_eop           ),

    .llcrx_rxfifo_data          ( llcrx_rxfifo_data         ),
    .llcrx_rxfifo_dval          ( llcrx_rxfifo_dval         ),
    .llcrx_rxfifo_sop           ( llcrx_rxfifo_sop          ),
    .llcrx_rxfifo_eop           ( llcrx_rxfifo_eop          ),

    .rxchan_run_cycle           ( rxchan_run_cycle          ),
    .slink_addr_error           ( slink_addr_error          )

    );

    COM_MACRX                       #
    (
    .DELAY_ERR_ACT              ( DELAY_ERR_ACT             ),
    .CARD_TYPE                  ( CARD_TYPE                 )
    )
    U_MACRX
    (
    .clk_125m                   ( clk_125m_0                ),
    .rst_125m                   ( rst_125m                  ),

    .wd_timer                   ( wd_timer                  ),
    .self_cfg_err               ( self_cfg_err              ),
    .pcs_err                    ( pcs_err                   ),
    .pcsrx_macrx_dval           ( pcsrx_macrx_dval          ),
    .pcsrx_macrx_sop            ( pcsrx_macrx_sop           ),
    .pcsrx_macrx_eop            ( pcsrx_macrx_eop           ),
    .pcsrx_macrx_data           ( pcsrx_macrx_data          ),
    
    .macrx_llcrx_dval           ( macrx_llcrx_dval          ),
    .macrx_llcrx_sop            ( macrx_llcrx_sop           ),
    .macrx_llcrx_eop            ( macrx_llcrx_eop           ),
    .macrx_llcrx_data           ( macrx_llcrx_data          ),

    .slink_rx_eop               ( slink_rx_eop              ),
    .slink_err                  ( slink_err_temp            )
    );


    PCSRX                       U_PCSRX
    (
    .clk_125m                   ( clk_125m_0                ),
    .rst_125m                   ( rst_125m                  ),

    .pmarx_pcsrx_dval           ( pmarx_pcsrx_dval          ),
    .pmarx_pcsrx_data           ( pmarx_pcsrx_data          ),

    .pcsrx_macrx_dval           ( pcsrx_macrx_dval          ),
    .pcsrx_macrx_sop            ( pcsrx_macrx_sop           ),
    .pcsrx_macrx_eop            ( pcsrx_macrx_eop           ),
    .pcsrx_macrx_data           ( pcsrx_macrx_data          ),

    .pcs_err                    ( pcs_err                   )
    );

    PMARX                       U_PMARX
    (
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),
    .rst_125m                   ( rst_125m                  ),

    .rx_en                      ( rx_en                     ),
    .lvds_rxp_in                ( lvds_rxp_in               ),
    .lvds_rxn_in                ( lvds_rxn_in               ),
    .pmarx_pcsrx_dval           ( pmarx_pcsrx_dval          ),
    .pmarx_pcsrx_data           ( pmarx_pcsrx_data          )
    );
    
    
endmodule

