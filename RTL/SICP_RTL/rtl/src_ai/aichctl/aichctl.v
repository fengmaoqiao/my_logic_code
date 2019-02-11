// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-07-06
// DEPARTMENT       :   R&D
// AUTHOR           :   YongjunZhang
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-07-25  YongjunZhang        Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active low
// Clock Domains    :   EMIF_CLK
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`include "DEFINES.v"

module AICHCTL 
(
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 
        clk_12_5m               ,   
        rst_12_5m_n             ,

        spi_clk                 ,   // SPI clock
        spi_cs                  ,   // SPI c switch
        spi_sdi                 ,   // SPI input data
        spi_sdo                 ,   // SPI outout data

        slink_ram_err           ,   
        txsdu_ram_err           ,   
        rxsdu_ram_err           ,   

        wd_int_fb               ,   
        wd_int_fd               ,
        wd_uart_rx              ,   
        wd_uart_tx              ,

        slink_tx_eop            ,   
        slot_num                ,   

        uart_txd                ,   
        uart_rxd                ,   
                   
        e2p_spi_clk             ,   
        e2p_spi_sdi             ,   
        e2p_spi_cs              ,   
        e2p_spi_sdo             ,   
  
        pwr_err_int             ,   
        ch_pwn_diag             ,   
        ch_ad_diag              ,   

        cfg_done                ,   
        cfg_done_trig           ,   
        cfg_chn_enable          ,
        slink_cfg_dval          ,   
        slink_cfg_data          ,
        mass_bit                ,   

        txsdu_upm_rdreq         ,   
        upm_txsdu_empty         ,   
        upm_txsdu_dval          ,   
        upm_txsdu_data          ,
        cal_ch_index            ,   
        hw_fault                   
);

/**********************************************************************************\
***************************** declare parameter ************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m_n                         ;   

input   wire    [3:0]           slot_num                            ;   
input   wire    [1:0]           slink_tx_eop                        ;   
input   wire    [1:0]           slink_ram_err                       ;   
input   wire    [1:0]           txsdu_ram_err                       ;   
input   wire                    rxsdu_ram_err                       ;

input   wire    [11:0]          spi_sdo                             ;   
input   wire                    slink_cfg_dval                      ;   
input   wire    [9:0]           slink_cfg_data                      ; 
input   wire                    cfg_done                            ;
input   wire                    cfg_done_trig                       ;   
input   wire    [11:0]          cfg_chn_enable                      ;   
input   wire                    uart_rxd                            ;   
input   wire                    e2p_spi_sdo                         ;   
input   wire    [11:0]          ch_pwn_diag                         ;   
input   wire                    pwr_err_int                         ;   
input   wire                    wd_uart_rx                          ;   
input   wire    [9:0]           wd_int_fb                           ; 
input   wire                    txsdu_upm_rdreq                     ;
// output signal
output  wire    [11:0]          spi_sdi                             ;   
output  wire    [11:0]          spi_clk                             ;   
output  wire    [11:0]          spi_cs                              ;  

output  wire                    e2p_spi_clk                         ;   
output  wire                    e2p_spi_sdi                         ;   
output  wire                    e2p_spi_cs                          ;   
output  wire    [11:0]          ch_ad_diag                          ;   
output  wire                    uart_txd                            ;   
output  wire    [11:0]          mass_bit                            ;   
output  wire                    hw_fault                            ;   
output  wire                    wd_uart_tx                          ;   
output  wire    [9:0]           wd_int_fd                           ;  
output  wire                    upm_txsdu_empty                     ;   
output  wire                    upm_txsdu_dval                      ;   
output  wire    [17:0]          upm_txsdu_data                      ;
output  wire    [11:0]          cal_ch_index                        ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [11:0]                  adacq_spi_busy                      ;   
wire    [11:0]                  adacq_rd_dval                       ;   
wire    [15:0]                  adacq_rd_data[11:0]                 ;
wire    [11:0]                  adacq_rd_en                         ;   
wire    [2:0]                   cal_adc_cnt                         ;   
wire    [11:0]                  chn_dgd_err                         ;   
wire    [11:0]                  chn_open_short                      ;   
wire    [31:0]                  mdu_stus                            ;   
wire                            up_ram_err                          ;   
wire                            wd_cfg_done                         ;   
wire    [1:0]                   prc_done_trigh                      ;   
wire    [1:0]                   prc_done_trigl                      ;   
wire                            wd_cfg_en                           ;   
wire                            rdu_fault                           ;   
wire                            pwr_ram_fault                       ;   
wire                            ch_fault                            ;   
wire    [11:0]                  param_crc_err                       ;   
wire                            wd_com_fault                        ;   

wire                            e2p_rd_en                           ;   
wire                            e2p_rd_dval                         ;   
wire    [31:0]                  e2p_rd_value                        ;   
wire    [15:0]                  e2p_rdaddr                          ;   
wire                            e2p_busy                            ;   
wire                            e2p_wr_en                           ;   
wire    [31:0]                  e2p_wr_value0                       ;   
wire    [31:0]                  e2p_wr_value1                       ;   
wire    [31:0]                  e2p_wr_value2                       ;   
wire    [31:0]                  e2p_wr_value3                       ;   
wire    [15:0]                  e2p_reg_addr                        ;   
wire                            e2p_wr_done                         ;   
wire                            e2p_rw_sel                          ;

wire    [5:0]                   acq_dgdad_enl                       ;   
wire    [5:0]                   acq_chn_sell                        ;   
wire    [2:0]                   cal_adc_cntl                        ;   
wire                            pw_on_enl                           ;   

wire    [5:0]                   acq_dgdad_enh                       ;   
wire    [5:0]                   acq_chn_selh                        ;   
wire                            pw_on_enh                           ;   

wire                            calfas_adsb_sell                    ;   
wire    [31:0]                  calfas_data_al                      ;   
wire    [31:0]                  calfas_data_bl                      ;   
wire                            calfas_start_trigl                  ;   
wire    [31:0]                  calfd_data_al                       ;   
wire    [31:0]                  calfd_data_bl                       ;   
wire                            calfd_start_trigl                   ;   
wire     [31:0]                 calfm_data_al                       ;   
wire     [31:0]                 calfm_data_bl                       ;   
wire                            calfm_start_trigl                   ;   

wire                            calfas_adsb_selh                    ;   
wire    [31:0]                  calfas_data_ah                      ;   
wire    [31:0]                  calfas_data_bh                      ;   
wire                            calfas_start_trigh                  ;   
wire    [31:0]                  calfd_data_ah                       ;   
wire    [31:0]                  calfd_data_bh                       ;   
wire                            calfd_start_trigh                   ;   
wire     [31:0]                 calfm_data_ah                       ;   
wire     [31:0]                 calfm_data_bh                       ;   
wire                            calfm_start_trigh                   ;   
wire                            fas_donel                           ;   
wire    [31:0]                  fas_resultl                         ;   
wire                            fd_donel                            ;   
wire    [31:0]                  fd_resultl                          ;   
wire                            fm_donel                            ;   
wire    [31:0]                  fm_resultl                          ;   

wire                            fm_doneh                            ;   
wire    [31:0]                  fm_resulth                          ;   
wire                            fas_doneh                           ;   
wire    [31:0]                  fas_resulth                         ;   
wire                            fd_doneh                            ;   
wire    [31:0]                  fd_resulth                          ;   
wire                            cal_donel                           ;   
wire                            cal_doneh                           ;   

wire                            param_rd_done                       ;   
wire    [15:0]                  e2p_rd_addr                         ;   
wire    [15:0]                  e2p_wr_addr                         ;   
wire                            uart_tx_wenl                        ;   
wire    [7:0]                   uart_tx_wdatal                      ;
wire                            uart_tx_wenh                        ;   
wire    [7:0]                   uart_tx_wdatah                      ;   
wire                            e2p_con_done                        ;   
wire                            cal_model_en                        ;   

wire                            temp_wr_done                        ;   
wire                            temp_chip_err                       ;   
wire                            temp_rd_en                          ;   
wire                            temp_rd_dval                        ;   
wire    [15:0]                  temp_rd_value                       ;   
wire                            temp_con_done                       ; 
wire                            param_rd_en                         ;   
wire    [11:0]                  ch_rdu_fault                        ;   
wire                            e2p_chip_err                        ;   
wire                            e2p_uartrd_en                       ;   
wire                            e2p_paramrd_en                      ;   
wire                            e2p_urd_dval                        ;
wire    [1:0]                   ch_pwr_fault                        ;   

wire    [31:0]                  up_engn_chn[11:0]                   ;
wire    [31:0]                  up_elec_chn[11:0]                   ;
wire    [31:0]                  up_masb_chn[11:0]                   ;
wire    [31:0]                  ke_coeff[11:0]                      ;
wire    [31:0]                  bq_coeff[11:0]                      ;
wire    [31:0]                  k_factor[11:0]                      ;
wire    [31:0]                  b_factor[11:0]                      ;
wire    [31:0]                  kqe_factor[11:0]                    ;
wire    [31:0]                  cfg_engn_chkdl[11:0]                ;
wire    [31:0]                  cfg_engn_chkul[11:0]                ;
wire    [31:0]                  cfg_elec_chkdl[11:0]                ;
wire    [31:0]                  cfg_elec_chkul[11:0]                ;
/**********************************************************************************\
******************************** debug code ****************************************/

/**********************************************************************************\
********************************* main code ****************************************/

    AICTL                       U_AICTL_L
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    // input signal
    .cal_done                   ( cal_donel                 ),
    .adacq_spi_busy             ( adacq_spi_busy[5:0]       ),
    .adacq_rd_dval              ( adacq_rd_dval[5:0]        ),
    .adacq_rd_data0             ( adacq_rd_data[0]          ),
    .adacq_rd_data1             ( adacq_rd_data[1]          ),
    .adacq_rd_data2             ( adacq_rd_data[2]          ),
    .adacq_rd_data3             ( adacq_rd_data[3]          ),
    .adacq_rd_data4             ( adacq_rd_data[4]          ),
    .adacq_rd_data5             ( adacq_rd_data[5]          ),

    .b_factor0                  ( b_factor[0 ]              ),
    .b_factor1                  ( b_factor[1 ]              ),
    .b_factor2                  ( b_factor[2 ]              ),
    .b_factor3                  ( b_factor[3 ]              ),
    .b_factor4                  ( b_factor[4 ]              ),
    .b_factor5                  ( b_factor[5 ]              ),
                    
    .kqe_factor0                ( kqe_factor[0 ]            ),
    .kqe_factor1                ( kqe_factor[1 ]            ),
    .kqe_factor2                ( kqe_factor[2 ]            ),
    .kqe_factor3                ( kqe_factor[3 ]            ),
    .kqe_factor4                ( kqe_factor[4 ]            ),
    .kqe_factor5                ( kqe_factor[5 ]            ),
                    
    .bq_coeff0                  ( bq_coeff[0 ]              ),
    .bq_coeff1                  ( bq_coeff[1 ]              ),
    .bq_coeff2                  ( bq_coeff[2 ]              ),
    .bq_coeff3                  ( bq_coeff[3 ]              ),
    .bq_coeff4                  ( bq_coeff[4 ]              ),
    .bq_coeff5                  ( bq_coeff[5 ]              ),
                    
    .ke_coeff0                  ( ke_coeff[0 ]              ),
    .ke_coeff1                  ( ke_coeff[1 ]              ),
    .ke_coeff2                  ( ke_coeff[2 ]              ),
    .ke_coeff3                  ( ke_coeff[3 ]              ),
    .ke_coeff4                  ( ke_coeff[4 ]              ),
    .ke_coeff5                  ( ke_coeff[5 ]              ),

    .cfg_engn_chkul0            ( cfg_engn_chkul[0 ]        ),
    .cfg_engn_chkul1            ( cfg_engn_chkul[1 ]        ),
    .cfg_engn_chkul2            ( cfg_engn_chkul[2 ]        ),
    .cfg_engn_chkul3            ( cfg_engn_chkul[3 ]        ),
    .cfg_engn_chkul4            ( cfg_engn_chkul[4 ]        ),
    .cfg_engn_chkul5            ( cfg_engn_chkul[5 ]        ),
                                   
    .cfg_engn_chkdl0            ( cfg_engn_chkdl[0 ]        ),
    .cfg_engn_chkdl1            ( cfg_engn_chkdl[1 ]        ),
    .cfg_engn_chkdl2            ( cfg_engn_chkdl[2 ]        ),
    .cfg_engn_chkdl3            ( cfg_engn_chkdl[3 ]        ),
    .cfg_engn_chkdl4            ( cfg_engn_chkdl[4 ]        ),
    .cfg_engn_chkdl5            ( cfg_engn_chkdl[5 ]        ),

    .cfg_elec_chkul0            ( cfg_elec_chkul[0 ]        ),
    .cfg_elec_chkul1            ( cfg_elec_chkul[1 ]        ),
    .cfg_elec_chkul2            ( cfg_elec_chkul[2 ]        ),
    .cfg_elec_chkul3            ( cfg_elec_chkul[3 ]        ),
    .cfg_elec_chkul4            ( cfg_elec_chkul[4 ]        ),
    .cfg_elec_chkul5            ( cfg_elec_chkul[5 ]        ),

    .cfg_elec_chkdl0            ( cfg_elec_chkdl[0 ]        ),
    .cfg_elec_chkdl1            ( cfg_elec_chkdl[1 ]        ),
    .cfg_elec_chkdl2            ( cfg_elec_chkdl[2 ]        ),
    .cfg_elec_chkdl3            ( cfg_elec_chkdl[3 ]        ),
    .cfg_elec_chkdl4            ( cfg_elec_chkdl[4 ]        ),
    .cfg_elec_chkdl5            ( cfg_elec_chkdl[5 ]        ),

    .calfas_adsb_sel            ( calfas_adsb_sell          ),
    .calfas_data_a              ( calfas_data_al            ),
    .calfas_data_b              ( calfas_data_bl            ),
    .calfas_start_trig          ( calfas_start_trigl        ),
    .calfd_data_a               ( calfd_data_al             ),
    .calfd_data_b               ( calfd_data_bl             ),
    .calfd_start_trig           ( calfd_start_trigl         ),
    .calfm_data_a               ( calfm_data_al             ),
    .calfm_data_b               ( calfm_data_bl             ),
    .calfm_start_trig           ( calfm_start_trigl         ),

    .pwr_ram_fault              ( pwr_ram_fault             ),
    .cal_model_en               ( cal_model_en              ),
    .ch_pwn_diag                ( ch_pwn_diag[5:0]          ),
    .cfg_done                   ( cfg_done                  ),
    .cfg_chn_enable             ( cfg_chn_enable[5:0]       ),
    .adacq_rd_en                ( adacq_rd_en[5:0]          ),
    .ch_rdu_fault               ( ch_rdu_fault[5:0]         ),
    .param_crc_err              ( param_crc_err[5:0]        ),

    .chn_dgd_err                ( chn_dgd_err[5:0]          ),
    .chn_open_short             ( chn_open_short[5:0]       ),
    .ch_pwr_fault               ( ch_pwr_fault[0]           ),

    .fas_done                   ( fas_donel                 ),
    .fas_result                 ( fas_resultl               ),
    .fd_done                    ( fd_donel                  ),
    .fd_result                  ( fd_resultl                ),
    .fm_done                    ( fm_donel                  ),
    .fm_result                  ( fm_resultl                ),

    .acq_dgdad_en               ( acq_dgdad_enl             ),
    .pw_on_en                   ( pw_on_enl                 ),
    .mass_bit                   ( mass_bit[5:0]             ),
    .ch_ad_diag                 ( ch_ad_diag[5:0]           ),
    .prc_done_trig              ( prc_done_trigl            ),

    .up_engn_chn0               ( up_engn_chn[0 ]           ),
    .up_engn_chn1               ( up_engn_chn[1 ]           ),
    .up_engn_chn2               ( up_engn_chn[2 ]           ),
    .up_engn_chn3               ( up_engn_chn[3 ]           ),
    .up_engn_chn4               ( up_engn_chn[4 ]           ),
    .up_engn_chn5               ( up_engn_chn[5 ]           ),
                                   
    .up_elec_chn0               ( up_elec_chn[0 ]           ),
    .up_elec_chn1               ( up_elec_chn[1 ]           ),
    .up_elec_chn2               ( up_elec_chn[2 ]           ),
    .up_elec_chn3               ( up_elec_chn[3 ]           ),
    .up_elec_chn4               ( up_elec_chn[4 ]           ),
    .up_elec_chn5               ( up_elec_chn[5 ]           ),
                                   
    .up_masb_chn0               ( up_masb_chn[0 ]           ),
    .up_masb_chn1               ( up_masb_chn[1 ]           ),
    .up_masb_chn2               ( up_masb_chn[2 ]           ),
    .up_masb_chn3               ( up_masb_chn[3 ]           ),
    .up_masb_chn4               ( up_masb_chn[4 ]           ),
    .up_masb_chn5               ( up_masb_chn[5 ]           )

    );

    AICTL                       U_AICTL_H
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    // input signal
    .cal_done                   ( cal_doneh                 ),
    .adacq_spi_busy             ( adacq_spi_busy[11:6]      ),
    .adacq_rd_dval              ( adacq_rd_dval[11:6]       ),
    .adacq_rd_data0             ( adacq_rd_data[6]          ),
    .adacq_rd_data1             ( adacq_rd_data[7]          ),
    .adacq_rd_data2             ( adacq_rd_data[8]          ),
    .adacq_rd_data3             ( adacq_rd_data[9]          ),
    .adacq_rd_data4             ( adacq_rd_data[10]         ),
    .adacq_rd_data5             ( adacq_rd_data[11]         ),

    .b_factor0                  ( b_factor[6 ]              ),
    .b_factor1                  ( b_factor[7 ]              ),
    .b_factor2                  ( b_factor[8 ]              ),
    .b_factor3                  ( b_factor[9 ]              ),
    .b_factor4                  ( b_factor[10]              ),
    .b_factor5                  ( b_factor[11]              ),
                    
    .kqe_factor0                ( kqe_factor[6 ]            ),
    .kqe_factor1                ( kqe_factor[7 ]            ),
    .kqe_factor2                ( kqe_factor[8 ]            ),
    .kqe_factor3                ( kqe_factor[9 ]            ),
    .kqe_factor4                ( kqe_factor[10]            ),
    .kqe_factor5                ( kqe_factor[11]            ),
                    
    .bq_coeff0                  ( bq_coeff[6 ]              ),
    .bq_coeff1                  ( bq_coeff[7 ]              ),
    .bq_coeff2                  ( bq_coeff[8 ]              ),
    .bq_coeff3                  ( bq_coeff[9 ]              ),
    .bq_coeff4                  ( bq_coeff[10]              ),
    .bq_coeff5                  ( bq_coeff[11]              ),
                    
    .ke_coeff0                  ( ke_coeff[6 ]              ),
    .ke_coeff1                  ( ke_coeff[7 ]              ),
    .ke_coeff2                  ( ke_coeff[8 ]              ),
    .ke_coeff3                  ( ke_coeff[9 ]              ),
    .ke_coeff4                  ( ke_coeff[10]              ),
    .ke_coeff5                  ( ke_coeff[11]              ),

    .cfg_engn_chkul0            ( cfg_engn_chkul[6 ]        ),
    .cfg_engn_chkul1            ( cfg_engn_chkul[7 ]        ),
    .cfg_engn_chkul2            ( cfg_engn_chkul[8 ]        ),
    .cfg_engn_chkul3            ( cfg_engn_chkul[9 ]        ),
    .cfg_engn_chkul4            ( cfg_engn_chkul[10]        ),
    .cfg_engn_chkul5            ( cfg_engn_chkul[11]        ),
                                   
    .cfg_engn_chkdl0            ( cfg_engn_chkdl[6 ]        ),
    .cfg_engn_chkdl1            ( cfg_engn_chkdl[7 ]        ),
    .cfg_engn_chkdl2            ( cfg_engn_chkdl[8 ]        ),
    .cfg_engn_chkdl3            ( cfg_engn_chkdl[9 ]        ),
    .cfg_engn_chkdl4            ( cfg_engn_chkdl[10]        ),
    .cfg_engn_chkdl5            ( cfg_engn_chkdl[11]        ),

    .cfg_elec_chkul0            ( cfg_elec_chkul[6 ]        ),
    .cfg_elec_chkul1            ( cfg_elec_chkul[7 ]        ),
    .cfg_elec_chkul2            ( cfg_elec_chkul[8 ]        ),
    .cfg_elec_chkul3            ( cfg_elec_chkul[9 ]        ),
    .cfg_elec_chkul4            ( cfg_elec_chkul[10]        ),
    .cfg_elec_chkul5            ( cfg_elec_chkul[11]        ),
                                                   
    .cfg_elec_chkdl0            ( cfg_elec_chkdl[6 ]        ),
    .cfg_elec_chkdl1            ( cfg_elec_chkdl[7 ]        ),
    .cfg_elec_chkdl2            ( cfg_elec_chkdl[8 ]        ),
    .cfg_elec_chkdl3            ( cfg_elec_chkdl[9 ]        ),
    .cfg_elec_chkdl4            ( cfg_elec_chkdl[10]        ),
    .cfg_elec_chkdl5            ( cfg_elec_chkdl[11]        ),

    .calfas_adsb_sel            ( calfas_adsb_selh          ),
    .calfas_data_a              ( calfas_data_ah            ),
    .calfas_data_b              ( calfas_data_bh            ),
    .calfas_start_trig          ( calfas_start_trigh        ),
    .calfd_data_a               ( calfd_data_ah             ),
    .calfd_data_b               ( calfd_data_bh             ),
    .calfd_start_trig           ( calfd_start_trigh         ),
    .calfm_data_a               ( calfm_data_ah             ),
    .calfm_data_b               ( calfm_data_bh             ),
    .calfm_start_trig           ( calfm_start_trigh         ),

    .param_crc_err              ( param_crc_err[11:6]       ),
    .pwr_ram_fault              ( pwr_ram_fault             ),
    .cal_model_en               ( cal_model_en              ),
    .ch_pwn_diag                ( ch_pwn_diag[11:6]         ),
    .cfg_done                   ( cfg_done                  ),
    .cfg_chn_enable             ( cfg_chn_enable[11:6]      ),
    .adacq_rd_en                ( adacq_rd_en[11:6]         ),
    .ch_rdu_fault               ( ch_rdu_fault[11:6]        ),

    .chn_dgd_err                ( chn_dgd_err[11:6]         ),
    .chn_open_short             ( chn_open_short[11:6]      ),
    .ch_pwr_fault               ( ch_pwr_fault[1]           ),

    .fas_done                   ( fas_doneh                 ),
    .fas_result                 ( fas_resulth               ),
    .fd_done                    ( fd_doneh                  ),
    .fd_result                  ( fd_resulth                ),
    .fm_done                    ( fm_doneh                  ),
    .fm_result                  ( fm_resulth                ),

    .ch_ad_diag                 ( ch_ad_diag[11:6]          ),
    .acq_dgdad_en               ( acq_dgdad_enh             ),
    .pw_on_en                   ( pw_on_enh                 ),
    .mass_bit                   ( mass_bit[11:6]            ),
    .prc_done_trig              ( prc_done_trigh            ),

    .up_engn_chn0               ( up_engn_chn[6 ]           ),
    .up_engn_chn1               ( up_engn_chn[7 ]           ),
    .up_engn_chn2               ( up_engn_chn[8 ]           ),
    .up_engn_chn3               ( up_engn_chn[9 ]           ),
    .up_engn_chn4               ( up_engn_chn[10]           ),
    .up_engn_chn5               ( up_engn_chn[11]           ),
                                   
    .up_elec_chn0               ( up_elec_chn[6 ]           ),
    .up_elec_chn1               ( up_elec_chn[7 ]           ),
    .up_elec_chn2               ( up_elec_chn[8 ]           ),
    .up_elec_chn3               ( up_elec_chn[9 ]           ),
    .up_elec_chn4               ( up_elec_chn[10]           ),
    .up_elec_chn5               ( up_elec_chn[11]           ),
                                   
    .up_masb_chn0               ( up_masb_chn[6 ]           ),
    .up_masb_chn1               ( up_masb_chn[7 ]           ),
    .up_masb_chn2               ( up_masb_chn[8 ]           ),
    .up_masb_chn3               ( up_masb_chn[9 ]           ),
    .up_masb_chn4               ( up_masb_chn[10]           ),
    .up_masb_chn5               ( up_masb_chn[11]           )
    );

//----------------------------------------------------------------------------------
// the module of ads8689
//----------------------------------------------------------------------------------
genvar k;
generate 
for (k=0; k<6; k = k+1)
begin : adcchl
    ADS8689CTL #(
    .CON_CNT                    ( 5'd8                      ),
    .DIV_CNT                    ( 5'd5                      )
    )
    U_ADS8689CTL
    (	
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),
    .pw_on_en                   ( pw_on_enl                 ),
    .rd_en                      ( adacq_rd_en[k]            ),
    .rd_dval                    ( adacq_rd_dval[k]          ),
    .rd_data                    ( adacq_rd_data[k]          ),
    
    // output port
    .spi_busy                   ( adacq_spi_busy[k]         ),
    .spi_cs                     ( spi_cs[k]                 ),
    .spi_clk                    ( spi_clk[k]                ),
    .spi_sdo                    ( spi_sdo[k]                ),
    .spi_rst                    (                           ),
    .spi_sdi                    ( spi_sdi[k]                ),
    .wr_done                    (                           ),
    .con_done                   (                           )
	);
end
endgenerate

genvar i;
generate 
for (i=6; i<12; i = i+1)
begin : adcchh
    ADS8689CTL #(
    .CON_CNT                    ( 5'd8                      ),
    .DIV_CNT                    ( 5'd5                      )
    )
    U_ADS8689CTL
    (	
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),
    .pw_on_en                   ( pw_on_enh                 ),
    .rd_en                      ( adacq_rd_en[i]            ),
    .rd_dval                    ( adacq_rd_dval[i]          ),
    .rd_data                    ( adacq_rd_data[i]          ),
    
    // output port
    .spi_busy                   ( adacq_spi_busy[i]         ),
    .spi_cs                     ( spi_cs[i]                 ),
    .spi_clk                    ( spi_clk[i]                ),
    .spi_sdo                    ( spi_sdo[i]                ),
    .spi_rst                    (                           ),
    .spi_sdi                    ( spi_sdi[i]                ),
    .wr_done                    (                           ),
    .con_done                   (                           )
	);
end
endgenerate

    RS232M                      U_RS232M
    (
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),

    .uart_rxd                   ( uart_rxd                  ),
    .uart_txd                   ( uart_txd                  ),
        
    .ad_rd_dval                 ( adacq_rd_dval             ),
    .ad_rd_value0               ( adacq_rd_data[0 ]         ),
    .ad_rd_value1               ( adacq_rd_data[1 ]         ),
    .ad_rd_value2               ( adacq_rd_data[2 ]         ),
    .ad_rd_value3               ( adacq_rd_data[3 ]         ),
    .ad_rd_value4               ( adacq_rd_data[4 ]         ),
    .ad_rd_value5               ( adacq_rd_data[5 ]         ),
    .ad_rd_value6               ( adacq_rd_data[6 ]         ),
    .ad_rd_value7               ( adacq_rd_data[7 ]         ),
    .ad_rd_value8               ( adacq_rd_data[8 ]         ),
    .ad_rd_value9               ( adacq_rd_data[9 ]         ),
    .ad_rd_value10              ( adacq_rd_data[10]         ),
    .ad_rd_value11              ( adacq_rd_data[11]         ),

    .uart_tx_wenl               ( uart_tx_wenl              ),
    .uart_tx_wdatal             ( uart_tx_wdatal            ),
    .uart_tx_wenh               ( uart_tx_wenh              ),
    .uart_tx_wdatah             ( uart_tx_wdatah            ),

    .e2p_urd_dval               ( e2p_urd_dval              ),
    .e2p_rd_value               ( e2p_rd_value              ),
    // output

    .cal_ch_index               ( cal_ch_index              ),
    .rd_en                      ( e2p_uartrd_en             ),
    .wr_en                      ( e2p_wr_en                 ),
    .wr_value0                  ( e2p_wr_value0             ),
    .wr_value1                  ( e2p_wr_value1             ),
    .wr_value2                  ( e2p_wr_value2             ),
    .wr_value3                  ( e2p_wr_value3             ),
    .wr_addr                    ( e2p_wr_addr               ),
    .wr_done                    ( e2p_wr_done               ),
    .e2p_rw_sel                 ( e2p_rw_sel                ),
    .e2p_busy                   ( e2p_busy                  )
    );

assign cal_model_en = e2p_rw_sel ;

    AT25CTL                     U_AT25CTL
    (        
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),
    
    .wr_en                      ( e2p_wr_en                 ),
    .wr_value0                  ( e2p_wr_value0             ),
    .wr_value1                  ( e2p_wr_value1             ),
    .wr_value2                  ( e2p_wr_value2             ),
    .wr_value3                  ( e2p_wr_value3             ),
    .reg_addr                   ( e2p_reg_addr              ),
    .rd_en                      ( e2p_rd_en                 ),
    .rd_dval                    ( e2p_rd_dval               ),
    .rd_value                   ( e2p_rd_value              ),
    .pw_on_en                   ( pw_on_enl                 ),
    // output port
    .spi_busy                   ( e2p_busy                  ),
    
    // spi_interface
    .spi_cs                     ( e2p_spi_cs                ),
    .spi_clk                    ( e2p_spi_clk               ),
    .spi_sdo                    ( e2p_spi_sdo               ),
    .spi_sdi                    ( e2p_spi_sdi               ),
    .spi_rst                    (                           ),
    .con_done                   ( e2p_con_done              ),
    .wr_done                    ( e2p_wr_done               ),
    .chip_err                   (                           )
    );

assign rdu_fault = | ch_rdu_fault ;
assign ch_fault = | ch_pwr_fault ;
assign e2p_chip_err = | param_crc_err ;

    FAULTPRC                    U_FAULTPRC
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .rst_12_5m_n                ( rst_12_5m_n               ),
    .clk_12_5m                  ( clk_12_5m                 ),

    .e2p_chip_err               ( e2p_chip_err              ),
    .pwr_err_int                ( pwr_err_int               ),
    .chn_dgd_en                 ( cfg_done                  ),
    .acq_dgdad_enl              ( acq_dgdad_enl             ),
    .acq_dgdad_enh              ( acq_dgdad_enh             ),

    .wd_cfg_en                  ( wd_cfg_en                 ),
    .wd_cfg_done                ( wd_cfg_done               ),
    .rdu_fault                  ( rdu_fault                 ),
    .ch_fault                   ( ch_fault                  ),
    .up_ram_err                 ( up_ram_err                ),
    .slink_ram_err              ( slink_ram_err             ),
    .txsdu_ram_err              ( txsdu_ram_err             ),
    .wd_clk_fault               ( wd_clk_fault              ),
    .wd_ch_fault                ( wd_ch_fault               ),
    .wd_com_fault               ( wd_com_fault              ),
    .rxsdu_ram_err              ( rxsdu_ram_err             ),

    .adacq_rd_dval              ( adacq_rd_dval             ),
    .adacq_rd_data0             ( adacq_rd_data[0]          ),
    .adacq_rd_data1             ( adacq_rd_data[1]          ),
    .adacq_rd_data2             ( adacq_rd_data[2]          ),
    .adacq_rd_data3             ( adacq_rd_data[3]          ),
    .adacq_rd_data4             ( adacq_rd_data[4]          ),
    .adacq_rd_data5             ( adacq_rd_data[5]          ),
    .adacq_rd_data6             ( adacq_rd_data[6]          ),
    .adacq_rd_data7             ( adacq_rd_data[7]          ),
    .adacq_rd_data8             ( adacq_rd_data[8]          ),
    .adacq_rd_data9             ( adacq_rd_data[9]          ),
    .adacq_rd_data10            ( adacq_rd_data[10]         ),
    .adacq_rd_data11            ( adacq_rd_data[11]         ),

    .hw_fault                   ( hw_fault                  ),
    .mdu_stus                   ( mdu_stus                  ),
    .pwr_ram_fault              ( pwr_ram_fault             ),
    .chn_dgd_err                ( chn_dgd_err               ),
    .chn_open_short             ( chn_open_short            )
    ) ;

assign e2p_reg_addr = ( param_rd_en == 1'b1 ) ? e2p_rd_addr : e2p_wr_addr ; 
assign e2p_rd_en    = ( param_rd_en == 1'b1 ) ? e2p_paramrd_en : e2p_uartrd_en ; 
assign e2p_urd_dval = ( param_rd_en == 1'b1 ) ? 1'b0 : e2p_rd_dval ;

    PARAMRD                     U_PARAMRD
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    // input signal
    .e2p_rw_sel                 ( e2p_rw_sel                ),
    .e2p_paramrd_en             ( e2p_paramrd_en            ),
    .e2p_reg_addr               ( e2p_rd_addr               ),
    .e2p_rd_dval                ( e2p_rd_dval               ),
    .e2p_rd_value               ( e2p_rd_value              ),
    .e2p_busy                   ( e2p_busy                  ),
    .e2p_con_done               ( e2p_con_done              ),
    
    .param_rd_done              ( param_rd_done             ),
    .param_crc_err              ( param_crc_err              ),
    .param_rd_en                ( param_rd_en               ),
    .b_factor0                  ( b_factor[0 ]              ),
    .b_factor1                  ( b_factor[1 ]              ),
    .b_factor2                  ( b_factor[2 ]              ),
    .b_factor3                  ( b_factor[3 ]              ),
    .b_factor4                  ( b_factor[4 ]              ),
    .b_factor5                  ( b_factor[5 ]              ),
    .b_factor6                  ( b_factor[6 ]              ),
    .b_factor7                  ( b_factor[7 ]              ),
    .b_factor8                  ( b_factor[8 ]              ),
    .b_factor9                  ( b_factor[9 ]              ),
    .b_factor10                 ( b_factor[10]              ),
    .b_factor11                 ( b_factor[11]              ),

    .k_factor0                  ( k_factor[0 ]              ),
    .k_factor1                  ( k_factor[1 ]              ),
    .k_factor2                  ( k_factor[2 ]              ),
    .k_factor3                  ( k_factor[3 ]              ),
    .k_factor4                  ( k_factor[4 ]              ),
    .k_factor5                  ( k_factor[5 ]              ),
    .k_factor6                  ( k_factor[6 ]              ),
    .k_factor7                  ( k_factor[7 ]              ),
    .k_factor8                  ( k_factor[8 ]              ),
    .k_factor9                  ( k_factor[9 ]              ),
    .k_factor10                 ( k_factor[10]              ),
    .k_factor11                 ( k_factor[11]              )
    );

    CAL_FACTOR                  U_CAL_FACTOR_L
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    .cfg_done_trig              ( cfg_done_trig             ),
    .slink_cfg_dval             ( slink_cfg_dval            ),
    .slink_cfg_data             ( slink_cfg_data            ),
    .cfg_chaddr_sel             ( 1'b0                      ),

    .fas_done                   ( fas_donel                 ),
    .fas_result                 ( fas_resultl               ),
    .fd_done                    ( fd_donel                  ),
    .fd_result                  ( fd_resultl                ),
    .fm_done                    ( fm_donel                  ),
    .fm_result                  ( fm_resultl                ),
        
    .fas_adsb_sel               ( calfas_adsb_sell          ),
    .fas_data_a                 ( calfas_data_al            ),
    .fas_data_b                 ( calfas_data_bl            ),
    .fas_start_trig             ( calfas_start_trigl        ),
    .fd_data_a                  ( calfd_data_al             ),
    .fd_data_b                  ( calfd_data_bl             ),
    .fd_start_trig              ( calfd_start_trigl         ),
    .fm_data_a                  ( calfm_data_al             ),
    .fm_data_b                  ( calfm_data_bl             ),
    .fm_start_trig              ( calfm_start_trigl         ),
    .cal_done                   ( cal_donel                 ),  

    .k_factor0                  ( k_factor[0 ]              ),
    .k_factor1                  ( k_factor[1 ]              ),
    .k_factor2                  ( k_factor[2 ]              ),
    .k_factor3                  ( k_factor[3 ]              ),
    .k_factor4                  ( k_factor[4 ]              ),
    .k_factor5                  ( k_factor[5 ]              ),

    .kqe_factor0                ( kqe_factor[0 ]            ),
    .kqe_factor1                ( kqe_factor[1 ]            ),
    .kqe_factor2                ( kqe_factor[2 ]            ),
    .kqe_factor3                ( kqe_factor[3 ]            ),
    .kqe_factor4                ( kqe_factor[4 ]            ),
    .kqe_factor5                ( kqe_factor[5 ]            ),

    .bq_coeff0                  ( bq_coeff[0 ]              ),
    .bq_coeff1                  ( bq_coeff[1 ]              ),
    .bq_coeff2                  ( bq_coeff[2 ]              ),
    .bq_coeff3                  ( bq_coeff[3 ]              ),
    .bq_coeff4                  ( bq_coeff[4 ]              ),
    .bq_coeff5                  ( bq_coeff[5 ]              ),

    .ke_coeff0                  ( ke_coeff[0 ]              ),
    .ke_coeff1                  ( ke_coeff[1 ]              ),
    .ke_coeff2                  ( ke_coeff[2 ]              ),
    .ke_coeff3                  ( ke_coeff[3 ]              ),
    .ke_coeff4                  ( ke_coeff[4 ]              ),
    .ke_coeff5                  ( ke_coeff[5 ]              ),
    .cfg_engn_chkul0            ( cfg_engn_chkul[0 ]        ),
    .cfg_engn_chkul1            ( cfg_engn_chkul[1 ]        ),
    .cfg_engn_chkul2            ( cfg_engn_chkul[2 ]        ),
    .cfg_engn_chkul3            ( cfg_engn_chkul[3 ]        ),
    .cfg_engn_chkul4            ( cfg_engn_chkul[4 ]        ),
    .cfg_engn_chkul5            ( cfg_engn_chkul[5 ]        ),
                                   
    .cfg_engn_chkdl0            ( cfg_engn_chkdl[0 ]        ),
    .cfg_engn_chkdl1            ( cfg_engn_chkdl[1 ]        ),
    .cfg_engn_chkdl2            ( cfg_engn_chkdl[2 ]        ),
    .cfg_engn_chkdl3            ( cfg_engn_chkdl[3 ]        ),
    .cfg_engn_chkdl4            ( cfg_engn_chkdl[4 ]        ),
    .cfg_engn_chkdl5            ( cfg_engn_chkdl[5 ]        ),

    .cfg_elec_chkul0            ( cfg_elec_chkul[0 ]        ),
    .cfg_elec_chkul1            ( cfg_elec_chkul[1 ]        ),
    .cfg_elec_chkul2            ( cfg_elec_chkul[2 ]        ),
    .cfg_elec_chkul3            ( cfg_elec_chkul[3 ]        ),
    .cfg_elec_chkul4            ( cfg_elec_chkul[4 ]        ),
    .cfg_elec_chkul5            ( cfg_elec_chkul[5 ]        ),

    .cfg_elec_chkdl0            ( cfg_elec_chkdl[0 ]        ),
    .cfg_elec_chkdl1            ( cfg_elec_chkdl[1 ]        ),
    .cfg_elec_chkdl2            ( cfg_elec_chkdl[2 ]        ),
    .cfg_elec_chkdl3            ( cfg_elec_chkdl[3 ]        ),
    .cfg_elec_chkdl4            ( cfg_elec_chkdl[4 ]        ),
    .cfg_elec_chkdl5            ( cfg_elec_chkdl[5 ]        )

    );

    CAL_FACTOR                  U_CAL_FACTOR_H
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    .cfg_done_trig              ( cfg_done_trig             ),
    .slink_cfg_dval             ( slink_cfg_dval            ),
    .slink_cfg_data             ( slink_cfg_data            ),
    .cfg_chaddr_sel             ( 1'b1                      ),

    .fas_done                   ( fas_doneh                 ),
    .fas_result                 ( fas_resulth               ),
    .fd_done                    ( fd_doneh                  ),
    .fd_result                  ( fd_resulth                ),
    .fm_done                    ( fm_doneh                  ),
    .fm_result                  ( fm_resulth                ),
        
    .fas_adsb_sel               ( calfas_adsb_selh          ),
    .fas_data_a                 ( calfas_data_ah            ),
    .fas_data_b                 ( calfas_data_bh            ),
    .fas_start_trig             ( calfas_start_trigh        ),
    .fd_data_a                  ( calfd_data_ah             ),
    .fd_data_b                  ( calfd_data_bh             ),
    .fd_start_trig              ( calfd_start_trigh         ),
    .fm_data_a                  ( calfm_data_ah             ),
    .fm_data_b                  ( calfm_data_bh             ),
    .fm_start_trig              ( calfm_start_trigh         ),

    .cal_done                   ( cal_doneh                 ),  
    .k_factor0                  ( k_factor[6 ]              ),
    .k_factor1                  ( k_factor[7 ]              ),
    .k_factor2                  ( k_factor[8 ]              ),
    .k_factor3                  ( k_factor[9 ]              ),
    .k_factor4                  ( k_factor[10]              ),
    .k_factor5                  ( k_factor[11]              ),

    .kqe_factor0                ( kqe_factor[6 ]            ),
    .kqe_factor1                ( kqe_factor[7 ]            ),
    .kqe_factor2                ( kqe_factor[8 ]            ),
    .kqe_factor3                ( kqe_factor[9 ]            ),
    .kqe_factor4                ( kqe_factor[10]            ),
    .kqe_factor5                ( kqe_factor[11]            ),

    .bq_coeff0                  ( bq_coeff[6 ]              ),
    .bq_coeff1                  ( bq_coeff[7 ]              ),
    .bq_coeff2                  ( bq_coeff[8 ]              ),
    .bq_coeff3                  ( bq_coeff[9 ]              ),
    .bq_coeff4                  ( bq_coeff[10]              ),
    .bq_coeff5                  ( bq_coeff[11]              ),

    .ke_coeff0                  ( ke_coeff[6 ]              ),
    .ke_coeff1                  ( ke_coeff[7 ]              ),
    .ke_coeff2                  ( ke_coeff[8 ]              ),
    .ke_coeff3                  ( ke_coeff[9 ]              ),
    .ke_coeff4                  ( ke_coeff[10]              ),
    .ke_coeff5                  ( ke_coeff[11]              ),
    .cfg_engn_chkul0            ( cfg_engn_chkul[6 ]        ),
    .cfg_engn_chkul1            ( cfg_engn_chkul[7 ]        ),
    .cfg_engn_chkul2            ( cfg_engn_chkul[8 ]        ),
    .cfg_engn_chkul3            ( cfg_engn_chkul[9 ]        ),
    .cfg_engn_chkul4            ( cfg_engn_chkul[10]        ),
    .cfg_engn_chkul5            ( cfg_engn_chkul[11]        ),
                                   
    .cfg_engn_chkdl0            ( cfg_engn_chkdl[6 ]        ),
    .cfg_engn_chkdl1            ( cfg_engn_chkdl[7 ]        ),
    .cfg_engn_chkdl2            ( cfg_engn_chkdl[8 ]        ),
    .cfg_engn_chkdl3            ( cfg_engn_chkdl[9 ]        ),
    .cfg_engn_chkdl4            ( cfg_engn_chkdl[10]        ),
    .cfg_engn_chkdl5            ( cfg_engn_chkdl[11]        ),

    .cfg_elec_chkul0            ( cfg_elec_chkul[6 ]        ),
    .cfg_elec_chkul1            ( cfg_elec_chkul[7 ]        ),
    .cfg_elec_chkul2            ( cfg_elec_chkul[8 ]        ),
    .cfg_elec_chkul3            ( cfg_elec_chkul[9 ]        ),
    .cfg_elec_chkul4            ( cfg_elec_chkul[10]        ),
    .cfg_elec_chkul5            ( cfg_elec_chkul[11]        ),
                                                   
    .cfg_elec_chkdl0            ( cfg_elec_chkdl[6 ]        ),
    .cfg_elec_chkdl1            ( cfg_elec_chkdl[7 ]        ),
    .cfg_elec_chkdl2            ( cfg_elec_chkdl[8 ]        ),
    .cfg_elec_chkdl3            ( cfg_elec_chkdl[9 ]        ),
    .cfg_elec_chkdl4            ( cfg_elec_chkdl[10]        ),
    .cfg_elec_chkdl5            ( cfg_elec_chkdl[11]        )

    );

    UPDATAFRM                   U_UPDATAFRM
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m_n                ( rst_12_5m_n               ),
        
    .cfg_done                   ( cfg_done                  ),
    .slot_num                   ( slot_num                  ),
    .mdu_stus                   ( mdu_stus                  ),

//        .cfg_done                   ( 1'b1 ),//cfg_done                  ),
//    .slot_num                   ( 4'd0 ),//slot_num                  ),
//    .mdu_stus                   ( 32'd0 ),//mdu_stus                  ),

    .up_engn_chn0               ( up_engn_chn[0]            ),
    .up_engn_chn1               ( up_engn_chn[1]            ),
    .up_engn_chn2               ( up_engn_chn[2]            ),
    .up_engn_chn3               ( up_engn_chn[3]            ),
    .up_engn_chn4               ( up_engn_chn[4]            ),
    .up_engn_chn5               ( up_engn_chn[5]            ),
    .up_engn_chn6               ( up_engn_chn[6 ]           ),
    .up_engn_chn7               ( up_engn_chn[7 ]           ),
    .up_engn_chn8               ( up_engn_chn[8 ]           ),
    .up_engn_chn9               ( up_engn_chn[9 ]           ),
    .up_engn_chn10              ( up_engn_chn[10]           ),
    .up_engn_chn11              ( up_engn_chn[11]           ),
                                   
    .up_elec_chn0               ( up_elec_chn[0]            ),
    .up_elec_chn1               ( up_elec_chn[1]            ),
    .up_elec_chn2               ( up_elec_chn[2]            ),
    .up_elec_chn3               ( up_elec_chn[3]            ),
    .up_elec_chn4               ( up_elec_chn[4]            ),
    .up_elec_chn5               ( up_elec_chn[5]            ),
    .up_elec_chn6               ( up_elec_chn[6 ]           ),
    .up_elec_chn7               ( up_elec_chn[7 ]           ),
    .up_elec_chn8               ( up_elec_chn[8 ]           ),
    .up_elec_chn9               ( up_elec_chn[9 ]           ),
    .up_elec_chn10              ( up_elec_chn[10]           ),
    .up_elec_chn11              ( up_elec_chn[11]           ),
                                   
    .up_masb_chn0               ( up_masb_chn[0]            ),
    .up_masb_chn1               ( up_masb_chn[1]            ),
    .up_masb_chn2               ( up_masb_chn[2]            ),
    .up_masb_chn3               ( up_masb_chn[3]            ),
    .up_masb_chn4               ( up_masb_chn[4]            ),
    .up_masb_chn5               ( up_masb_chn[5]            ),
    .up_masb_chn6               ( up_masb_chn[6 ]           ),
    .up_masb_chn7               ( up_masb_chn[7 ]           ),
    .up_masb_chn8               ( up_masb_chn[8 ]           ),
    .up_masb_chn9               ( up_masb_chn[9 ]           ),
    .up_masb_chn10              ( up_masb_chn[10]           ),
    .up_masb_chn11              ( up_masb_chn[11]           ),

    .ram_dgd_err                ( up_ram_err                ),
    .pfifo_crc_fault            ( pfifo_crc_fault           ),
    .txsdu_upm_rdreq            ( txsdu_upm_rdreq           ),
    .upm_txsdu_empty            ( upm_txsdu_empty           ),
    .upm_txsdu_dval             ( upm_txsdu_dval            ),
    .upm_txsdu_data             ( upm_txsdu_data            )

    );

    WDPRC                       U_WDPRC
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .rst_12_5m_n                ( rst_12_5m_n               ),
    .clk_12_5m                  ( clk_12_5m                 ),

    .cfg_slink_chen             ( cfg_slink_chen            ),
    .cfg_run_tm                 ( cfg_run_tm                ),
    .slink_tx_eop               ( slink_tx_eop              ),
    .slink_rx_eop               ( 2'b00                     ),
    .wd_ch0_trig                ( prc_done_trigl[0]         ),
    .wd_ch1_trig                ( prc_done_trigl[1]         ),
    .wd_ch2_trig                ( prc_done_trigh[0]         ),
    .wd_ch3_trig                ( prc_done_trigh[1]         ),
    .wd_ch4_trig                ( 1'b0                      ),

    .wd_int_fb                  ( wd_int_fb                 ),
    .wd_int_fd                  ( wd_int_fd                 ),
    .wd_uart_rx                 ( wd_uart_rx                ),
    .wd_uart_tx                 ( wd_uart_tx                ),

    .wd_cfg_en                  ( wd_cfg_en                 ),
    .wd_cfg_done                ( wd_cfg_done               ),
    .wd_clk_fault               ( wd_clk_fault              ),
    .wd_ch_fault                ( wd_ch_fault               ),
    .wd_com_fault               ( wd_com_fault              )
    );

endmodule
