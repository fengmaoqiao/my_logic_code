// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   BPFMC01
// CREATE DATE      :   2017-08-15
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-15  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active hign
// Clock Domains    :   clk_50m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`include "DEFINES.v"

module  BPFAI01
    (
        // clock & reset
        CLK_125M_P              ,   
        CLK_125M_N              , 

        // SPI bus for ADC device  
        SPI_SCLK                ,   // SPI clock
        SPI_CS                  ,   // SPI c switch
        SPI_SDI                 ,   // SPI input data
        SPI_SDO                 ,   // SPI outout data

        WD_UART_RX              ,   
        WD_UART_TX              ,   
        WD_INT_FD               ,  // WD_INT0~9 
        WD_INT_FB               ,  // WD_INT15~24 

        // UART
        UART_RXD                ,   
        UART_TXD                ,   

        // EEPROM
        E2P_SPI_CLK             ,   
        E2P_SPI_SDI             ,   
        E2P_SPI_CS              ,   
        E2P_SPI_SDO             ,   

        // POW MINTOR
        PWR_ERR_INT             ,   
        HARD_RESET              ,   

        // LED Indicate
        LED_ERR                 ,   // the LED indicate for this board fault error 
        LED_COM                 ,   // the LED indicate for this board communication state
        LED_RUN                 ,   // the LED indicate for this board running state

        LED_CH0                 ,  // the LED indicate for this board the firest channel state 
        LED_CH1                 ,  // the LED indicate for this board the second channel state 
        LED_CH2                 ,  // the LED indicate for this board the third channel state 
        LED_CH3                 ,  // the LED indicate for this board the firest channel state 
        LED_CH4                 ,  // the LED indicate for this board the firest channel state 
        LED_CH5                 ,  // the LED indicate for this board the firest channel state 
        LED_CH6                 ,  // the LED indicate for this board the firest channel state 
        LED_CH7                 ,  // the LED indicate for this board the firest channel state 
        LED_CH8                 ,  // the LED indicate for this board the firest channel state 
        LED_CH9                 ,  // the LED indicate for this board the firest channel state 
        LED_CH10                ,  // the LED indicate for this board the firest channel state 
        LED_CH11                ,  // the LED indicate for this board the firest channel state 
        
        CH_PWN_DIAG             ,  // the Power diagnose at channel
        CH_AD_DIAG              ,  // the diagnostic and chnnel swithing signals  

        // AI moduel input signal
        MDU_SLOT                ,   // this board slot number 

        // backplane lvds 
        LVDS_RXP                ,   // connect to other board of box
        LVDS_TXP                ,      
        LVDS_RXN                ,   // connect to other board of box
        LVDS_TXN                      
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    CLK_125M_P                          ;   
input   wire                    CLK_125M_N                          ;   

input   wire    [11:0]          SPI_SDO                             ;   
input   wire    [3:0]           MDU_SLOT                            ;   
input   wire    [1:0]           LVDS_RXP                            ;   
input   wire    [1:0]           LVDS_RXN                            ;   
input   wire                    UART_RXD                            ;   
input   wire                    E2P_SPI_SDO                         ;   

input   wire                    PWR_ERR_INT                         ;   
input   wire    [11:0]          CH_PWN_DIAG                         ;   
input   wire                    HARD_RESET                          ; /* synthesis syn_preserve = 1 */  
input   wire                    WD_UART_RX                          ;
input   wire    [9:0]           WD_INT_FB                           ;
// declare output signal
output  wire    [1:0]           LVDS_TXP                            ;
output  wire    [1:0]           LVDS_TXN                            ;   
output  wire                    WD_UART_TX                          ;   
output  wire    [9:0]           WD_INT_FD                           ;
output  wire    [11:0]          SPI_SDI                             ;   
output  wire                    UART_TXD                            ;   
output  wire    [11:0]          SPI_SCLK                            ;   
output  wire    [11:0]          SPI_CS                              ;   

output  wire                    E2P_SPI_CLK                         ;   
output  wire                    E2P_SPI_SDI                         ;   
output  wire                    E2P_SPI_CS                          ;   

output  wire    [1:0]           LED_ERR                             ;   
output  wire    [1:0]           LED_COM                             ;   
output  wire    [1:0]           LED_RUN                             ;   
output  wire    [1:0]           LED_CH0                             ;   
output  wire    [1:0]           LED_CH1                             ;   
output  wire    [1:0]           LED_CH2                             ;   
output  wire    [1:0]           LED_CH3                             ;   
output  wire    [1:0]           LED_CH4                             ;   
output  wire    [1:0]           LED_CH5                             ;   
output  wire    [1:0]           LED_CH6                             ;   
output  wire    [1:0]           LED_CH7                             ;   
output  wire    [1:0]           LED_CH8                             ;   
output  wire    [1:0]           LED_CH9                             ;   
output  wire    [1:0]           LED_CH10                            ;   
output  wire    [1:0]           LED_CH11                            ;   
output  wire    [11:0]          CH_AD_DIAG                          ;   

// declare inout signal
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            clk_100m                            ;   
wire                            rst_100m                            ;   
wire                            clk_150m                            ;   
wire                            rst_150m                            ;   
wire                            clk_12_5m                           ;   
wire                            rst_12_5m_n                         ;   
wire                            rst_125m_n                          ;   
wire                            clk_125m_0                          ;   
wire                            clk_125m_90                         ;   
wire                            clk_125m_180                        ;   
wire                            clk_125m_270                        ;   
wire                            self_id_err                         ;   
wire                            hw_fault                            ;   
wire                            rxsdu_ram_err                       ;   
wire        [1:0]               slink_ram_err                       ;   
wire        [1:0]               txsdu_ram_err                       ;   
wire        [1:0]               rxsdu_slink_rdreq                   ;   
wire        [1:0]               slink_rxsdu_empty                   ;   
wire        [1:0]               slink_rxsdu_dval                    ;   
wire        [17:0]              slink_rxsdu_data        [1:0]       ; 
wire        [11:0]              cal_ch_index                        ;   

wire        [1:0]               slink_txsdu_rdreq                   ;   
wire        [1:0]               txsdu_slink_dval                    ;   
wire        [17:0]              txsdu_slink_data        [1:0]       ;   

wire        [1:0]               slink_tx_eop                        ;   
wire        [1:0]               slink_rx_eop                        ;   
wire        [1:0]               slink_err                           ;   

wire                            txsdu_sfm_rdreq                     ;   
wire                            sfm_txsdu_empty                     ;   
wire                            sfm_txsdu_dval                      ;   
wire        [17:0]              sfm_txsdu_data                      ;   

wire                            txsdu_upm_rdreq                     ;   
wire                            upm_txsdu_empty                     ;   
wire                            upm_txsdu_dval                      ;   
wire        [17:0]              upm_txsdu_data                      ;   

wire        [31:0]              up_di_stus                          ;   
wire        [31:0]              up_chn_masb                         ;   
wire                            slink_dt_dval                       ;   
wire                            slink_cfg_dval                      ; 

wire        [31:0]              dw_ctr_cmd                          ;   
wire        [31:0]              dw_chn_quan                         ;   
wire        [31:0]              dw_chn_masb                         ;   
wire        [31:0]              dw_com_stus                         ;   
wire        [31:0]              cfg_md_id                           ;   
wire        [31:0]              cfg_code_rev                        ;   
wire        [15:0]              cfg_run_tm                          ;   
wire        [7:0]               cfg_com_mode                        ;   
wire                            cfg_done                            ;
wire                            cfg_done_trig                       ;   
wire        [11:0]              cfg_chn_enable                      ;   
wire        [3:0]               slot_num_o                          ;   
wire        [1:0]               com_fault                           ;   
wire                            self_cfg_err                        ;   
wire        [1:0]               cfg_enable_slot                     ;   
wire        [1:0]               cfg_slink_chen                      ;   
wire        [11:0]              mass_bit                            ;   
wire                            cfg_err_done                        ;   
wire                            dw_com_fault                        ;   
wire        [9:0]               slink_cfg_data                      ;   
wire        [9:0]               slink_dt_data                       ;   
//  reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

    IO_CRM                         U_CRM
    (
    .clk_125m_p                 ( CLK_125M_P                ),
    .clk_125m_n                 ( CLK_125M_N                ),
    .hard_rst                   ( HARD_RESET                ),
    .soft_rst                   ( 1'b1                      ),

    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m_n                ( rst_12_5m_n               ),
    .rst_125m_n                 ( rst_125m_n                ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              )
    );

    IO_SELFM                    # (
    .BOARD_TYPE                 ( `AI_TYPE                  )
    )
    U_SELFM
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m_n                ( rst_12_5m_n               ),
    .clk_sys                    ( clk_125m_0                ),
    .rst_sys_n                  ( rst_125m_n                ),

    .slot_num                   ( MDU_SLOT                  ),

    .card_id                    ( cfg_md_id                 ),
    .code_version               ( cfg_code_rev[15:0]        ),
    .cfg_done                   ( cfg_done                  ),
    .cfg_enable_slot            ( cfg_enable_slot           ), // 12.5Mhz
    .cfg_slink_chen             ( cfg_slink_chen            ),
    .com_fault                  ( com_fault                 ),
    .slink_err                  ( slink_err                 ),
    .cfg_req_fail               ( cfg_req_fail              ),

    .txsdu_sfm_rdreq            ( txsdu_sfm_rdreq           ),
    .sfm_txsdu_empty            ( sfm_txsdu_empty           ),
    .sfm_txsdu_dval             ( sfm_txsdu_dval            ),
    .sfm_txsdu_data             ( sfm_txsdu_data            ),
    .self_cfg_err               ( self_cfg_err              ),
    .self_id_err                ( self_id_err               ),
    .cfg_err_done               ( cfg_err_done              ),
    .slot_num_o                 ( slot_num_o                ),
    .dw_com_fault               ( dw_com_fault              )
    );

//----------------------------------------------------------------------------------
// slink
//----------------------------------------------------------------------------------
  genvar i ;
  generate
  for( i = 0 ; i < 2 ; i = i+1 ) 
  begin : nMCU_SLINK

    IO_SLINK                       #                      
    (
    .CARD_TYPE                  ( 2'b11                     ),
    .FIFO_TYPE                  ( 2'b00                     )
    )
    U_MCU_SLINK
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m_n               ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),
    .rst_125m                   ( rst_125m_n                ),
                                  
    .wd_timer                   ( cfg_run_tm                ),
    .self_cfg_err               ( self_cfg_err              ),
    .rx_en                      ( 1'b1                      ),
    .lvds_rxp_in                ( LVDS_RXP[i]               ), //
    .lvds_rxn_in                ( LVDS_RXN[i]               ),
    .mm_slink_rdreq             ( rxsdu_slink_rdreq[i]      ),
    .mm_slink_data              ( txsdu_slink_data[i]       ),
    .mm_slink_dval              ( txsdu_slink_dval[i]       ),
                                   
    .lvds_txp_out               ( LVDS_TXP[i]               ),
    .lvds_txn_out               ( LVDS_TXN[i]               ),
    .slink_mm_rdreq             ( slink_txsdu_rdreq[i]      ),
    .slink_mm_empty             ( slink_rxsdu_empty[i]      ),
    .slink_mm_dval              ( slink_rxsdu_dval[i]       ),
    .slink_mm_data              ( slink_rxsdu_data[i]       ),
                                   
    .slink_tx_eop               ( slink_tx_eop[i]           ),
    .slink_rx_eop               ( slink_rx_eop[i]           ),
    .slink_err                  ( slink_err[i]              ),
    .slink_ram_err              ( slink_ram_err[i]          )
    );

  end
  endgenerate

//----------------------------------------------------------------------------------
// receive data path
//----------------------------------------------------------------------------------

    IO_RXSDU                    U_RXSDU
    (
    .clk_100m                   ( clk_125m_0                ),
    .rst_100m                   ( rst_125m_n                ),
  
    .rxsdu_slink_rdreq1         ( rxsdu_slink_rdreq[0]      ),
    .slink_rxsdu_empty1         ( slink_rxsdu_empty[0]      ),
    .slink_rxsdu_dval1          ( slink_rxsdu_dval[0]       ),
    .slink_rxsdu_data1          ( slink_rxsdu_data[0]       ),
    .rxsdu_slink_rdreq2         ( rxsdu_slink_rdreq[1]      ),
    .slink_rxsdu_empty2         ( slink_rxsdu_empty[1]      ),
    .slink_rxsdu_dval2          ( slink_rxsdu_dval[1]       ),
    .slink_rxsdu_data2          ( slink_rxsdu_data[1]       ),

    .slink_dt_dval              ( slink_dt_dval             ),
    .slink_cfg_dval             ( slink_cfg_dval            ),
    .slink_dt_data              ( slink_dt_data             ),
    .slink_cfg_data             ( slink_cfg_data            ),
    .ram_dgd_err                ( rxsdu_ram_err             )
    );

//----------------------------------------------------------------------------------
// transmit data path 
//----------------------------------------------------------------------------------

    IO_TXSDU                    U_IO_TXSDU
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m_n                ( rst_12_5m_n               ),
  
    .txsdu_sfm_rdreq            ( txsdu_sfm_rdreq           ),
    .sfm_txsdu_empty            ( sfm_txsdu_empty           ),
    .sfm_txsdu_dval             ( sfm_txsdu_dval            ),
    .sfm_txsdu_data             ( sfm_txsdu_data            ),

    .txsdu_upm_rdreq            ( txsdu_upm_rdreq           ),
    .upm_txsdu_empty            ( upm_txsdu_empty           ),
    .upm_txsdu_dval             ( upm_txsdu_dval            ),
    .upm_txsdu_data             ( upm_txsdu_data            ),

    .slink_txsdu_rdreq0         ( slink_txsdu_rdreq[0]      ),
    .slink_txsdu_rdreq1         ( slink_txsdu_rdreq[1]      ),
    .txsdu_slink_dval0          ( txsdu_slink_dval[0]       ),
    .txsdu_slink_data0          ( txsdu_slink_data[0]       ),
    .txsdu_slink_dval1          ( txsdu_slink_dval[1]       ),
    .txsdu_slink_data1          ( txsdu_slink_data[1]       ),
    .txsdu_ram_err              ( txsdu_ram_err             )
    );
//----------------------------------------------------------------------------------
// register management
//----------------------------------------------------------------------------------
    MEMDATAM    U_MEMDATAM
    (
    .clk_sys                    ( clk_125m_0                ),
    .rst_sys_n                  ( rst_125m_n                ),
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m_n                ( rst_12_5m_n               ),

        // cfginfofrm
    .slink_cfg_dval             ( slink_cfg_dval            ),
    .slink_cfg_data             ( slink_cfg_data            ),
    .cfg_md_id                  ( cfg_md_id                 ),
    .cfg_code_rev               ( cfg_code_rev              ),
    .cfg_run_tm                 ( cfg_run_tm                ),
    .cfg_com_mode               ( cfg_com_mode              ),
    .cfg_enable_slot            ( cfg_enable_slot           ),
    .cfg_slink_chen             ( cfg_slink_chen            ),

    .self_id_err                ( self_id_err               ),
    .cfg_done                   ( cfg_done                  ),
    .cfg_done_trig              ( cfg_done_trig             ),
    .cfg_chn_enable             ( cfg_chn_enable            ),
     
    // dwdatafrm
    .slink_dt_dval              ( slink_dt_dval             ),
    .slink_dt_data              ( slink_dt_data             ),
    .dw_ctr_cmd                 ( dw_ctr_cmd                ),
    .dw_com_stus                ( dw_com_stus               ),
    .com_fault                  ( com_fault                 ),
    .cfg_req_fail               ( cfg_req_fail              )

    );

    AICHCTL                     U_AICHCTL
    (
    .rst_sys_n                  ( rst_125m_n                ),
    .clk_sys                    ( clk_125m_0                ),
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m_n                ( rst_12_5m_n               ),

    .spi_clk                    ( SPI_SCLK                  ),
    .spi_cs                     ( SPI_CS                    ),
    .spi_sdi                    ( SPI_SDI                   ),
    .spi_sdo                    ( SPI_SDO                   ),

    .uart_txd                   ( UART_TXD                  ),
    .uart_rxd                   ( UART_RXD                  ),

    .slink_ram_err              ( slink_ram_err             ),
    .txsdu_ram_err              ( txsdu_ram_err             ),
    .rxsdu_ram_err              ( rxsdu_ram_err             ),
    
    .wd_int_fb                  ( WD_INT_FB                 ),
    .wd_int_fd                  ( WD_INT_FD                 ),
    .wd_uart_rx                 ( WD_UART_RX                ),
    .wd_uart_tx                 ( WD_UART_TX                ),

    .slink_tx_eop               ( slink_tx_eop              ),
    .slot_num                   ( slot_num_o                ),
    .pwr_err_int                ( PWR_ERR_INT               ),
    .e2p_spi_clk                ( E2P_SPI_CLK               ),
    .e2p_spi_sdi                ( E2P_SPI_SDI               ),
    .e2p_spi_cs                 ( E2P_SPI_CS                ),
    .e2p_spi_sdo                ( E2P_SPI_SDO               ),

    .ch_pwn_diag                ( CH_PWN_DIAG               ),
    .ch_ad_diag                 ( CH_AD_DIAG                ),

    .slink_cfg_dval             ( slink_cfg_dval            ),
    .slink_cfg_data             ( slink_cfg_data            ),

    .cfg_done                   ( cfg_err_done              ),
    .cfg_done_trig              ( cfg_done_trig             ),
    .cfg_chn_enable             ( cfg_chn_enable            ),

    .hw_fault                   ( hw_fault                  ),
    .mass_bit                   ( mass_bit                  ),
    .txsdu_upm_rdreq            ( txsdu_upm_rdreq           ),
    .upm_txsdu_empty            ( upm_txsdu_empty           ),
    .upm_txsdu_dval             ( upm_txsdu_dval            ),
    .upm_txsdu_data             ( upm_txsdu_data            ),
    .cal_ch_index               ( cal_ch_index              )
    );

    AI_LEDM                     U_LEDM
    (
    // clock & reset
    .clk_sys                    ( clk_125m_0                ),
    .rst_sys_n                  ( rst_125m_n                ),

    .hw_fault                   ( hw_fault                  ),
    .cal_ch_index               ( cal_ch_index              ),
    .dw_com_fault               ( dw_com_fault              ),
    .enable_slot                ( cfg_slink_chen            ),
    .cfg_en                     ( cfg_done                  ),
    .self_cfg_err               ( self_cfg_err              ),

    .macrx_rx_eop               ( slink_rx_eop              ),
    .lvds_pcs_err               ( slink_err                 ),
    .cfg_chn_enable             ( cfg_chn_enable            ),
    .mass_bit                   ( mass_bit                  ),
    // LED out
    .run_led                    ( LED_RUN                   ),
    .err_led                    ( LED_ERR                   ),
    .com_led                    ( LED_COM                   ),
    .ch0_led                    ( LED_CH0                   ),
    .ch1_led                    ( LED_CH1                   ),
    .ch2_led                    ( LED_CH2                   ),
    .ch3_led                    ( LED_CH3                   ),
    .ch4_led                    ( LED_CH4                   ),
    .ch5_led                    ( LED_CH5                   ),
    .ch6_led                    ( LED_CH6                   ),
    .ch7_led                    ( LED_CH7                   ),
    .ch8_led                    ( LED_CH8                   ),
    .ch9_led                    ( LED_CH9                   ),
    .ch10_led                   ( LED_CH10                  ),
    .ch11_led                   ( LED_CH11                  )

    );

endmodule

