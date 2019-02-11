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
// V100     2017-12-8  YongjunZhang        Original
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

module AICTL 
(
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 
        
        // input signal
        cal_done                ,   
        cal_model_en            ,   
        adacq_spi_busy          ,   
        adacq_rd_dval           ,   
        adacq_rd_data0          ,   
        adacq_rd_data1          ,   
        adacq_rd_data2          ,   
        adacq_rd_data3          ,   
        adacq_rd_data4          ,   
        adacq_rd_data5          ,   

        b_factor0               ,   
        b_factor1               ,   
        b_factor2               ,   
        b_factor3               ,   
        b_factor4               ,   
        b_factor5               ,   
                    
        kqe_factor0             ,   
        kqe_factor1             ,   
        kqe_factor2             ,   
        kqe_factor3             ,   
        kqe_factor4             ,   
        kqe_factor5             ,   
                    
        ke_coeff0               ,   
        ke_coeff1               ,   
        ke_coeff2               ,   
        ke_coeff3               ,   
        ke_coeff4               ,   
        ke_coeff5               ,   
                    
        bq_coeff0               ,   
        bq_coeff1               ,   
        bq_coeff2               ,   
        bq_coeff3               ,   
        bq_coeff4               ,   
        bq_coeff5               ,   

        cfg_engn_chkul0         ,   
        cfg_engn_chkul1         ,   
        cfg_engn_chkul2         ,   
        cfg_engn_chkul3         ,   
        cfg_engn_chkul4         ,   
        cfg_engn_chkul5         ,   
                                   
        cfg_engn_chkdl0         ,   
        cfg_engn_chkdl1         ,   
        cfg_engn_chkdl2         ,   
        cfg_engn_chkdl3         ,   
        cfg_engn_chkdl4         ,   
        cfg_engn_chkdl5         ,

        cfg_elec_chkul0         ,   
        cfg_elec_chkul1         ,   
        cfg_elec_chkul2         ,   
        cfg_elec_chkul3         ,   
        cfg_elec_chkul4         ,   
        cfg_elec_chkul5         ,   
                               
        cfg_elec_chkdl0         ,   
        cfg_elec_chkdl1         ,   
        cfg_elec_chkdl2         ,   
        cfg_elec_chkdl3         ,   
        cfg_elec_chkdl4         ,   
        cfg_elec_chkdl5         ,   

        calfas_adsb_sel         ,   
        calfas_data_a           ,   
        calfas_data_b           ,   
        calfas_start_trig       ,   
        calfd_data_a            ,   
        calfd_data_b            ,   
        calfd_start_trig        ,   

        calfm_data_a            ,   
        calfm_data_b            ,   
        calfm_start_trig        ,   

        param_crc_err           ,   
        pwr_ram_fault           ,   
        ch_pwn_diag             ,   

        cfg_done                ,   
        cfg_chn_enable          ,   

        chn_dgd_err             ,   
        chn_open_short          ,   
        // output signal
        fas_done                ,   
        fas_result              ,   
        fd_done                 ,   
        fd_result               ,  
        fm_done                 ,   
        fm_result               ,   

        mass_bit                ,   
        ch_ad_diag              ,   
        acq_dgdad_en            ,   
        ch_rdu_fault            ,   

        adacq_rd_en             ,   
        pw_on_en                ,   
        prc_done_trig           ,   
        ch_pwr_fault            ,   
        
        up_engn_chn0            ,   
        up_engn_chn1            ,   
        up_engn_chn2            ,   
        up_engn_chn3            ,   
        up_engn_chn4            ,   
        up_engn_chn5            ,   
                                   
        up_elec_chn0            ,   
        up_elec_chn1            ,   
        up_elec_chn2            ,   
        up_elec_chn3            ,   
        up_elec_chn4            ,   
        up_elec_chn5            ,   
                                   
        up_masb_chn0            ,   
        up_masb_chn1            ,   
        up_masb_chn2            ,   
        up_masb_chn3            ,   
        up_masb_chn4            ,   
        up_masb_chn5   
);

/**********************************************************************************\
***************************** declare parameter ************************************/
//localparam  PWN_DLY         =   32'd52    ;
localparam  PWN_DLY         =   32'd5131072    ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    cal_model_en                        ;   
input   wire                    cfg_done                            ;
input   wire    [5:0]           cfg_chn_enable                      ;   
input   wire                    cal_done                            ;  
input   wire    [5:0]           adacq_spi_busy                      ;   
input   wire    [5:0]           adacq_rd_dval                       ;   
input   wire    [15:0]          adacq_rd_data0                      ;   
input   wire    [15:0]          adacq_rd_data1                      ;   
input   wire    [15:0]          adacq_rd_data2                      ;   
input   wire    [15:0]          adacq_rd_data3                      ;   
input   wire    [15:0]          adacq_rd_data4                      ;   
input   wire    [15:0]          adacq_rd_data5                      ;   

input   wire    [31:0]          b_factor0                           ;   
input   wire    [31:0]          b_factor1                           ;   
input   wire    [31:0]          b_factor2                           ;   
input   wire    [31:0]          b_factor3                           ;   
input   wire    [31:0]          b_factor4                           ;   
input   wire    [31:0]          b_factor5                           ;     
 
input   wire    [31:0]          kqe_factor0                         ;   
input   wire    [31:0]          kqe_factor1                         ;   
input   wire    [31:0]          kqe_factor2                         ;   
input   wire    [31:0]          kqe_factor3                         ;   
input   wire    [31:0]          kqe_factor4                         ;   
input   wire    [31:0]          kqe_factor5                         ;    
 
input   wire    [31:0]          ke_coeff0                           ;   
input   wire    [31:0]          ke_coeff1                           ;   
input   wire    [31:0]          ke_coeff2                           ;   
input   wire    [31:0]          ke_coeff3                           ;   
input   wire    [31:0]          ke_coeff4                           ;   
input   wire    [31:0]          ke_coeff5                           ;   

input   wire    [31:0]          bq_coeff0                           ;   
input   wire    [31:0]          bq_coeff1                           ;   
input   wire    [31:0]          bq_coeff2                           ;   
input   wire    [31:0]          bq_coeff3                           ;   
input   wire    [31:0]          bq_coeff4                           ;   
input   wire    [31:0]          bq_coeff5                           ; 

input   wire    [31:0]          cfg_engn_chkul0                     ;   
input   wire    [31:0]          cfg_engn_chkul1                     ;   
input   wire    [31:0]          cfg_engn_chkul2                     ;   
input   wire    [31:0]          cfg_engn_chkul3                     ;   
input   wire    [31:0]          cfg_engn_chkul4                     ;   
input   wire    [31:0]          cfg_engn_chkul5                     ;   
 
input   wire    [31:0]          cfg_engn_chkdl0                     ;   
input   wire    [31:0]          cfg_engn_chkdl1                     ;   
input   wire    [31:0]          cfg_engn_chkdl2                     ;   
input   wire    [31:0]          cfg_engn_chkdl3                     ;   
input   wire    [31:0]          cfg_engn_chkdl4                     ;   
input   wire    [31:0]          cfg_engn_chkdl5                     ;  

input   wire    [31:0]          cfg_elec_chkul0                     ;   
input   wire    [31:0]          cfg_elec_chkul1                     ;   
input   wire    [31:0]          cfg_elec_chkul2                     ;   
input   wire    [31:0]          cfg_elec_chkul3                     ;   
input   wire    [31:0]          cfg_elec_chkul4                     ;   
input   wire    [31:0]          cfg_elec_chkul5                     ;   
 
input   wire    [31:0]          cfg_elec_chkdl0                     ;   
input   wire    [31:0]          cfg_elec_chkdl1                     ;   
input   wire    [31:0]          cfg_elec_chkdl2                     ;   
input   wire    [31:0]          cfg_elec_chkdl3                     ;   
input   wire    [31:0]          cfg_elec_chkdl4                     ;   
input   wire    [31:0]          cfg_elec_chkdl5                     ;

input   wire    [5:0]           param_crc_err                       ;   
input   wire                    pwr_ram_fault                       ;   
input   wire                    calfas_adsb_sel                     ;   
input   wire    [31:0]          calfas_data_a                       ;   
input   wire    [31:0]          calfas_data_b                       ;   
input   wire                    calfas_start_trig                   ;   
input   wire    [31:0]          calfd_data_a                        ;   
input   wire    [31:0]          calfd_data_b                        ;   
input   wire                    calfd_start_trig                    ;
input   wire    [31:0]          calfm_data_a                        ;   
input   wire    [31:0]          calfm_data_b                        ;   
input   wire                    calfm_start_trig                    ;

input   wire    [5:0]           ch_pwn_diag                         ;   
input   wire    [5:0]           chn_dgd_err                         ;   
input   wire    [5:0]           chn_open_short                      ;   
// output signal
output  reg                     pw_on_en                            ;
output  wire    [5:0]           acq_dgdad_en                        ;   

output  wire    [5:0]           adacq_rd_en                         ;   
output  wire    [5:0]           ch_ad_diag                          ;   

output  wire                    fas_done                            ;   
output  wire    [31:0]          fas_result                          ;   
output  wire                    fd_done                             ;   
output  wire    [31:0]          fd_result                           ;   
output  wire                    fm_done                             ;   
output  wire    [31:0]          fm_result                           ;   
output  wire    [5:0]           mass_bit                            ;   
output  wire    [5:0]           ch_rdu_fault                        ;   

output  wire    [31:0]          up_engn_chn0                        ;   
output  wire    [31:0]          up_engn_chn1                        ;   
output  wire    [31:0]          up_engn_chn2                        ;   
output  wire    [31:0]          up_engn_chn3                        ;   
output  wire    [31:0]          up_engn_chn4                        ;   
output  wire    [31:0]          up_engn_chn5                        ;   
output  wire    [31:0]          up_elec_chn0                        ;   
output  wire    [31:0]          up_elec_chn1                        ;   
output  wire    [31:0]          up_elec_chn2                        ;   
output  wire    [31:0]          up_elec_chn3                        ;   
output  wire    [31:0]          up_elec_chn4                        ;   
output  wire    [31:0]          up_elec_chn5                        ;   
output  wire    [7:0]           up_masb_chn0                        ;   
output  wire    [7:0]           up_masb_chn1                        ;   
output  wire    [7:0]           up_masb_chn2                        ;   
output  wire    [7:0]           up_masb_chn3                        ;   
output  wire    [7:0]           up_masb_chn4                        ;   
output  wire    [7:0]           up_masb_chn5                        ;   
output  wire    [1:0]           prc_done_trig                       ;   
output  wire                    ch_pwr_fault                        ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [31:0]                  up_masb_chn[5:0]                    ;
wire                            state_cal_adde                      ;   
wire                            state_cal_addq                      ;   
wire    [2:0]                   cal_chn_sel                         ;   
wire    [5:0]                   acq_dgdad_en0                       ;   
wire                            state_cal_dgdt0                     ;   
wire                            state_cal_done0                     ;   
wire    [5:0]                   adacq_rd_en0                        ;   
wire    [5:0]                   ch_ad_diag0                         ;   
wire                            state_cal_adde0                     ;   
wire                            state_cal_addq0                     ;   
wire                            prc_done_trig0                      ;   
wire    [2:0]                   cal_chn_sel0                        ;   
wire    [11:0]                  cur_state0                          ;   
wire    [5:0]                   acq_dgdad_en1                       ;   
wire    [5:0]                   adacq_rd_en1                        ;   
wire    [5:0]                   ch_ad_diag1                         ;   
wire                            state_cal_adde1                     ;   
wire                            state_cal_addq1                     ;   
wire                            state_cal_dgdt1                     ;   
wire                            state_cal_done1                     ;   
wire                            prc_done_trig1                      ;   
wire    [2:0]                   cal_chn_sel1                        ;   
wire    [11:0]                  cur_state1                          ;   
wire    [5:0]                   ch_hw_fault                         ;   
wire                                cmp_mt_test;

wire                            fd_done0                            ;   
wire    [31:0]                  fd_result0                          ;   
wire                            fas_done0                           ;   
wire    [31:0]                  fas_result0                         ;   
wire                            fm_done0                            ;   
wire    [31:0]                  fm_result0                          ;   
wire                            fd_done1                            ;   
wire    [31:0]                  fd_result1                          ;   
wire                            fas_done1                           ;   
wire    [31:0]                  fas_result1                         ;   
wire                            fm_done1                            ;   
wire    [31:0]                  fm_result1                          ;   

wire    [5:0]                   calf_dgd_mode                       ;   
wire    [5:0]                   rcy_sel                             ;   
wire                            state_cal_dgdt                      ;   
wire                            state_cal_done                      ;   
wire    [5:0]                   chn_disen_bit                       ; 
wire                            cmp_mt_en                           ;   
wire                            cmp_lt_en                           ; 
// reg signal
reg     [31:0]                  pwn_dly_cnt                         ;   
reg     [4:0]                   ad_acq_cnt                          ;
reg     [9:0]                   ad_div_ms                           ;   
reg     [5:0]                   wr_fifo_cnt                         ;   
reg     [3:0]                   wr_cnt                              ;
reg     [1:0]                   fifo_wr_sel                         ;   
reg     [6:0]                   pwn_div_us                          ;   
  
reg                             wr_fifo_en                          ;   
reg                             rcy_sel_bit                         ;  
reg                             wr_uart_en                          ;   
reg     [5:0]                   wr_uart_cnt                         ;   

reg     [5:0]                   calf_dgd_mode_mm                    ;/* synthesis syn_preserve = 1 */   
reg                             cal_done_mm                         ;/* synthesis syn_preserve = 1 */   
reg                             pw_on_en_mm                         ;/* synthesis syn_preserve = 1 */   
reg     [5:0]                   adacq_spi_busy_mm                   ;/* synthesis syn_preserve = 1 */   
reg     [5:0]                   adacq_rd_dval_mm                    ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  adacq_rd_data0_mm                   ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  adacq_rd_data1_mm                   ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  adacq_rd_data2_mm                   ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  adacq_rd_data3_mm                   ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  adacq_rd_data4_mm                   ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  adacq_rd_data5_mm                   ;/* synthesis syn_preserve = 1 */   
reg     [5:0]                   cfg_chn_enable_mm                   ;/* synthesis syn_preserve = 1 */   

reg     [5:0]                   calf_dgd_mode_ms                    ;/* synthesis syn_preserve = 1 */   
reg                             cal_done_ms                         ;/* synthesis syn_preserve = 1 */   
reg                             pw_on_en_ms                         ;/* synthesis syn_preserve = 1 */   
reg     [5:0]                   adacq_spi_busy_ms                   ;/* synthesis syn_preserve = 1 */   
reg     [5:0]                   adacq_rd_dval_ms                    ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  adacq_rd_data0_ms                   ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  adacq_rd_data1_ms                   ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  adacq_rd_data2_ms                   ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  adacq_rd_data3_ms                   ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  adacq_rd_data4_ms                   ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  adacq_rd_data5_ms                   ;/* synthesis syn_preserve = 1 */   
reg     [5:0]                   cfg_chn_enable_ms                   ;/* synthesis syn_preserve = 1 */ 

reg                             calfas_adsb_sel_mm                  ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  calfas_data_a_mm                    ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  calfas_data_b_mm                    ;/* synthesis syn_preserve = 1 */   
reg                             calfas_start_trig_mm                ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  calfd_data_a_mm                     ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  calfd_data_b_mm                     ;/* synthesis syn_preserve = 1 */   
reg                             calfd_start_trig_mm                 ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  calfm_data_a_mm                     ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  calfm_data_b_mm                     ;/* synthesis syn_preserve = 1 */   
reg                             calfm_start_trig_mm                 ;/* synthesis syn_preserve = 1 */

reg                             calfas_adsb_sel_ms                  ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  calfas_data_a_ms                    ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  calfas_data_b_ms                    ;/* synthesis syn_preserve = 1 */   
reg                             calfas_start_trig_ms                ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  calfd_data_a_ms                     ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  calfd_data_b_ms                     ;/* synthesis syn_preserve = 1 */   
reg                             calfd_start_trig_ms                 ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  calfm_data_a_ms                     ;/* synthesis syn_preserve = 1 */   
reg     [31:0]                  calfm_data_b_ms                     ;/* synthesis syn_preserve = 1 */   
reg                             calfm_start_trig_ms                 ;/* synthesis syn_preserve = 1 */

reg     [5:0]                   ch_pwn_diag_d                       ;   
reg     [5:0]                   ch_pwn_diag_d1                      ;  
reg     [5:0]                   ch_lt_err                           ;   
reg     [5:0]                   ch_mt_err                           ;   

reg                             rd_engn_d1                          ;   
reg                             rd_engn_d2                          ;   
reg                             rd_engn_d                           ;   
reg     [31:0]                  rd_engn_value                       ;   
reg     [31:0]                  rd_elec_value                       ;
reg     [31:0]                  cmp_engn_chkdl                      ;   
reg     [31:0]                  cmp_engn_chkul                      ;   
reg     [31:0]                  cmp_elec_chkdl                      ;   
reg     [31:0]                  cmp_elec_chkul                      ;     

reg     [31:0]                  up_elec_chn[5:0]                    ;
reg     [31:0]                  up_engn_chn[5:0]                    ;
/**********************************************************************************\
******************************** debug code ****************************************/

/**********************************************************************************\
********************************* main code ****************************************/
assign chn_disen_bit = ~cfg_chn_enable ;

assign state_cal_adde   =  ( rcy_sel_bit == 1'b1 ) ? state_cal_adde0    : state_cal_adde1   ;
assign state_cal_addq   =  ( rcy_sel_bit == 1'b1 ) ? state_cal_addq0    : state_cal_addq1   ;
assign acq_dgdad_en     =  ( rcy_sel_bit == 1'b1 ) ? acq_dgdad_en0      : acq_dgdad_en1     ;
assign state_cal_dgdt   =  ( rcy_sel_bit == 1'b1 ) ? state_cal_dgdt0    : state_cal_dgdt1   ;
assign state_cal_done   =  ( rcy_sel_bit == 1'b1 ) ? state_cal_done0    : state_cal_done1   ;
assign ch_ad_diag       =  ( rcy_sel_bit == 1'b1 ) ? ch_ad_diag0        : ch_ad_diag1       ;
assign adacq_rd_en      =  ( rcy_sel_bit == 1'b1 ) ? adacq_rd_en0       : adacq_rd_en1      ;
assign fas_done         =  ( rcy_sel_bit == 1'b1 ) ? fas_done0          : fas_done1         ;
assign fas_result       =  ( rcy_sel_bit == 1'b1 ) ? fas_result0        : fas_result1       ;
assign cal_chn_sel      =  ( rcy_sel_bit == 1'b1 ) ? cal_chn_sel0       : cal_chn_sel1      ;
assign cur_state        =  ( rcy_sel_bit == 1'b1 ) ? cur_state0         : cur_state1        ;
assign fd_done          =  ( rcy_sel_bit == 1'b1 ) ? fd_done0           : fd_done1          ;
assign fd_result        =  ( rcy_sel_bit == 1'b1 ) ? fd_result0         : fd_result1        ;
assign fm_done          =  ( rcy_sel_bit == 1'b1 ) ? fm_done0           : fm_done1          ;
assign fm_result        =  ( rcy_sel_bit == 1'b1 ) ? fm_result0         : fm_result1        ;

assign mass_bit[0 ] = pwr_ram_fault | ch_pwn_diag_d[0] | param_crc_err[0] | chn_open_short[0] | chn_disen_bit[0] | chn_dgd_err[0] | ch_lt_err[0] | ch_mt_err[0] |  ch_hw_fault[0] ;
assign mass_bit[1 ] = pwr_ram_fault | ch_pwn_diag_d[1] | param_crc_err[1] | chn_open_short[1] | chn_disen_bit[1] | chn_dgd_err[1] | ch_lt_err[1] | ch_mt_err[1] |  ch_hw_fault[1] ;
assign mass_bit[2 ] = pwr_ram_fault | ch_pwn_diag_d[2] | param_crc_err[2] | chn_open_short[2] | chn_disen_bit[2] | chn_dgd_err[2] | ch_lt_err[2] | ch_mt_err[2] |  ch_hw_fault[2] ;
assign mass_bit[3 ] = pwr_ram_fault | ch_pwn_diag_d[3] | param_crc_err[3] | chn_open_short[3] | chn_disen_bit[3] | chn_dgd_err[3] | ch_lt_err[3] | ch_mt_err[3] |  ch_hw_fault[3] ;
assign mass_bit[4 ] = pwr_ram_fault | ch_pwn_diag_d[4] | param_crc_err[4] | chn_open_short[4] | chn_disen_bit[4] | chn_dgd_err[4] | ch_lt_err[4] | ch_mt_err[4] |  ch_hw_fault[4] ;
assign mass_bit[5 ] = pwr_ram_fault | ch_pwn_diag_d[5] | param_crc_err[5] | chn_open_short[5] | chn_disen_bit[5] | chn_dgd_err[5] | ch_lt_err[5] | ch_mt_err[5] |  ch_hw_fault[5] ;

assign up_masb_chn[0 ]   = { 24'h000000, pwr_ram_fault , 1'b0, ch_pwn_diag_d[0], ch_lt_err[0], ch_mt_err[0], chn_open_short[0], chn_dgd_err[0], mass_bit[0 ] } ;
assign up_masb_chn[1 ]   = { 24'h000000, pwr_ram_fault , 1'b0, ch_pwn_diag_d[1], ch_lt_err[1], ch_mt_err[1], chn_open_short[1], chn_dgd_err[1], mass_bit[1 ] } ;
assign up_masb_chn[2 ]   = { 24'h000000, pwr_ram_fault , 1'b0, ch_pwn_diag_d[2], ch_lt_err[2], ch_mt_err[2], chn_open_short[2], chn_dgd_err[2], mass_bit[2 ] } ;
assign up_masb_chn[3 ]   = { 24'h000000, pwr_ram_fault , 1'b0, ch_pwn_diag_d[3], ch_lt_err[3], ch_mt_err[3], chn_open_short[3], chn_dgd_err[3], mass_bit[3 ] } ;
assign up_masb_chn[4 ]   = { 24'h000000, pwr_ram_fault , 1'b0, ch_pwn_diag_d[4], ch_lt_err[4], ch_mt_err[4], chn_open_short[4], chn_dgd_err[4], mass_bit[4 ] } ;
assign up_masb_chn[5 ]   = { 24'h000000, pwr_ram_fault , 1'b0, ch_pwn_diag_d[5], ch_lt_err[5], ch_mt_err[5], chn_open_short[5], chn_dgd_err[5], mass_bit[5 ] } ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rcy_sel_bit <=   1'b0 ;
    end
    else begin
        case ( cal_chn_sel )
            3'd0 : begin
                if ( rcy_sel[0] == 1'b1 ) begin
                    rcy_sel_bit <=   1'b1 ;
                end
                else begin
                    rcy_sel_bit <=   1'b0 ;
                end
            end
            3'd1 : begin
                if ( rcy_sel[1] == 1'b1 ) begin
                    rcy_sel_bit <=   1'b1 ;
                end
                else begin
                    rcy_sel_bit <=   1'b0 ;
                end
            end
            3'd2 : begin
                if ( rcy_sel[2] == 1'b1 ) begin
                    rcy_sel_bit <=   1'b1 ;
                end
                else begin
                    rcy_sel_bit <=   1'b0 ;
                end
            end
            3'd3 : begin
                if ( rcy_sel[3] == 1'b1 ) begin
                    rcy_sel_bit <=   1'b1 ;
                end
                else begin
                    rcy_sel_bit <=   1'b0 ;
                end
            end
            3'd4 : begin
                if ( rcy_sel[4] == 1'b1 ) begin
                    rcy_sel_bit <=   1'b1 ;
                end
                else begin
                    rcy_sel_bit <=   1'b0 ;
                end
            end
            3'd5 : begin
                if ( rcy_sel[5] == 1'b1 ) begin
                    rcy_sel_bit <=   1'b1 ;
                end
                else begin
                    rcy_sel_bit <=   1'b0 ;
                end
            end
            default : begin
            end
        endcase
    end
end
//----------------------------------------------------------------------------------
// porcess the signal of power error 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ch_pwn_diag_d1  <= 6'b000000 ;  
    end
    else begin
        if ( pwn_div_us == 7'd100 ) begin
             ch_pwn_diag_d1  <=   ~ch_pwn_diag ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// porcess the signal of power error 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ch_pwn_diag_d  <= 6'b000000 ;  
    end
    else begin
        if ( pwn_div_us == 7'd100 ) begin
             ch_pwn_diag_d  <=   ch_pwn_diag_d1 ;
        end
        else ;
    end
end

assign ch_pwr_fault = | ch_pwn_diag_d ;
//----------------------------------------------------------------------------------
// the us count 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pwn_div_us  <=  7'h00 ;
    end
    else begin
        if ( pwn_div_us == 7'd100 ) begin
            pwn_div_us  <=  7'h00 ;
        end
        else begin
            pwn_div_us  <=  pwn_div_us + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// delay for board power on
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pwn_dly_cnt  <=  32'd0;
    end
    else begin
        if ( pwn_div_us == 7'd100 ) begin
            if ( pwn_dly_cnt == PWN_DLY ) begin
                pwn_dly_cnt  <=  PWN_DLY;
            end
            else begin
                pwn_dly_cnt  <=  pwn_dly_cnt + 1'b1;
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pw_on_en    <=   1'b0 ;
    end
    else begin
        if ( pwn_dly_cnt == PWN_DLY-32'd20 ) begin
            pw_on_en    <=   1'b1 ;
        end
        else ; 
    end
end

//----------------------------------------------------------------------------------
// judgement of the scope of monitoring the value of electrical quantity
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_elec_value   <=   32'd0 ;
    end
    else begin
        if ( state_cal_adde == 1'b1 && fas_done == 1'b1 ) begin
            rd_elec_value   <=   fas_result ; 
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        up_elec_chn[0]    <=   32'h00000000 ;
        up_elec_chn[1]    <=   32'h00000000 ;
        up_elec_chn[2]    <=   32'h00000000 ;
        up_elec_chn[3]    <=   32'h00000000 ;
        up_elec_chn[4]    <=   32'h00000000 ;
        up_elec_chn[5]    <=   32'h00000000 ;
    end
    else begin
        if ( pwr_ram_fault == 1'b1 ) begin
            up_elec_chn[0]    <=   cfg_elec_chkdl0 ;
            up_elec_chn[1]    <=   cfg_elec_chkdl1 ;
            up_elec_chn[2]    <=   cfg_elec_chkdl2 ;
            up_elec_chn[3]    <=   cfg_elec_chkdl3 ;
            up_elec_chn[4]    <=   cfg_elec_chkdl4 ;
            up_elec_chn[5]    <=   cfg_elec_chkdl5 ;
        end
        else if ( rd_engn_d1 == 1'b1 && cmp_lt_en == 1'b0 && cmp_mt_en == 1'b0 ) begin 
            up_elec_chn[cal_chn_sel]    <=   rd_elec_value ;
        end
        else if ( ch_lt_err[cal_chn_sel] == 1'b1 ) begin
            case ( cal_chn_sel )
                3'd0 : begin
                    up_elec_chn[0]  <=   cfg_elec_chkdl0 ;
                end
                3'd1 : begin
                    up_elec_chn[1]  <=   cfg_elec_chkdl1 ;
                end
                3'd2 : begin
                    up_elec_chn[2]  <=   cfg_elec_chkdl2 ;
                end
                3'd3 : begin
                    up_elec_chn[3]  <=   cfg_elec_chkdl3 ;
                end
                3'd4 : begin
                    up_elec_chn[4]  <=   cfg_elec_chkdl4 ;
                end
                3'd5 : begin
                    up_elec_chn[5]  <=   cfg_elec_chkdl5 ;
                end
                default : begin
                    up_elec_chn[cal_chn_sel]  <=  up_elec_chn[cal_chn_sel] ; 
                end
            endcase
        end
        else if ( ch_mt_err[cal_chn_sel] == 1'b1 ) begin
            case ( cal_chn_sel )
                3'd0 : begin
                    up_elec_chn[0]  <=   cfg_elec_chkul0 ;
                end
                3'd1 : begin
                    up_elec_chn[1]  <=   cfg_elec_chkul1 ;
                end
                3'd2 : begin
                    up_elec_chn[2]  <=   cfg_elec_chkul2 ;
                end
                3'd3 : begin
                    up_elec_chn[3]  <=   cfg_elec_chkul3 ;
                end
                3'd4 : begin
                    up_elec_chn[4]  <=   cfg_elec_chkul4 ;
                end
                3'd5 : begin
                    up_elec_chn[5]  <=   cfg_elec_chkul5 ;
                end
                default : begin
                    up_elec_chn[cal_chn_sel]  <=  up_elec_chn[cal_chn_sel] ; 
                end
            endcase
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// judgement of the scope of monitoring the value of engineering quantity
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_engn_value   <=   32'd0 ;
    end
    else begin
        if ( state_cal_addq == 1'b1 && fas_done == 1'b1 ) begin
            rd_engn_value   <=   fas_result ; 
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_engn_d   <=   1'b0 ;
    end
    else begin
        if ( state_cal_addq == 1'b1 && fas_done == 1'b1 ) begin
            rd_engn_d   <=   1'b1 ; 
        end
        else begin
            rd_engn_d   <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_engn_d1  <=   1'b0 ;
    end
    else begin
        rd_engn_d1  <=   rd_engn_d ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_engn_d2  <=   1'b0 ;
    end
    else begin
        rd_engn_d2  <=   rd_engn_d1 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        up_engn_chn[0]    <=   32'h00000000 ;
        up_engn_chn[1]    <=   32'h00000000 ;
        up_engn_chn[2]    <=   32'h00000000 ;
        up_engn_chn[3]    <=   32'h00000000 ;
        up_engn_chn[4]    <=   32'h00000000 ;
        up_engn_chn[5]    <=   32'h00000000 ;
    end
    else begin
        if ( rd_engn_d1 == 1'b1 && cmp_lt_en == 1'b0 && cmp_mt_en == 1'b0 ) begin 
            up_engn_chn[cal_chn_sel]    <=   rd_engn_value ;
        end
        else if ( ch_lt_err[cal_chn_sel] == 1'b1 ) begin
            case ( cal_chn_sel )
                3'd0 : begin
                    up_engn_chn[0]  <=   cfg_engn_chkdl0 ;
                end
                3'd1 : begin
                    up_engn_chn[1]  <=   cfg_engn_chkdl1 ;
                end
                3'd2 : begin
                    up_engn_chn[2]  <=   cfg_engn_chkdl2 ;
                end
                3'd3 : begin
                    up_engn_chn[3]  <=   cfg_engn_chkdl3 ;
                end
                3'd4 : begin
                    up_engn_chn[4]  <=   cfg_engn_chkdl4 ;
                end
                3'd5 : begin
                    up_engn_chn[5]  <=   cfg_engn_chkdl5 ;
                end
                default : begin
                    up_engn_chn[cal_chn_sel]  <=  up_engn_chn[cal_chn_sel] ; 
                end
            endcase
        end
        else if ( ch_mt_err[cal_chn_sel] == 1'b1 ) begin
            case ( cal_chn_sel )
                3'd0 : begin
                    up_engn_chn[0]  <=   cfg_engn_chkul0 ;
                end
                3'd1 : begin
                    up_engn_chn[1]  <=   cfg_engn_chkul1 ;
                end
                3'd2 : begin
                    up_engn_chn[2]  <=   cfg_engn_chkul2 ;
                end
                3'd3 : begin
                    up_engn_chn[3]  <=   cfg_engn_chkul3 ;
                end
                3'd4 : begin
                    up_engn_chn[4]  <=   cfg_engn_chkul4 ;
                end
                3'd5 : begin
                    up_engn_chn[5]  <=   cfg_engn_chkul5 ;
                end
                default : begin
                    up_engn_chn[cal_chn_sel]  <=  up_engn_chn[cal_chn_sel] ; 
                end
            endcase
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ch_lt_err   <=   6'd0 ;
    end
    else begin
        if ( rd_engn_d1 == 1'b1 ) begin
            ch_lt_err[cal_chn_sel]  <=   cmp_lt_en ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ch_mt_err   <=   6'd0 ;
    end
    else begin
        if ( rd_engn_d1 == 1'b1 ) begin
            ch_mt_err[cal_chn_sel]  <=   cmp_mt_en ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cmp_engn_chkdl  <=   32'd0 ;
    end
    else begin
        case ( cal_chn_sel )
            3'd0 : begin
                cmp_engn_chkdl  <=   cfg_engn_chkdl0 ;
            end
            3'd1 : begin
                cmp_engn_chkdl  <=   cfg_engn_chkdl1 ;
            end
            3'd2 : begin
                cmp_engn_chkdl  <=   cfg_engn_chkdl2 ;
            end
            3'd3 : begin
                cmp_engn_chkdl  <=   cfg_engn_chkdl3 ;
            end
            3'd4 : begin
                cmp_engn_chkdl  <=   cfg_engn_chkdl4 ;
            end
            3'd5 : begin
                cmp_engn_chkdl  <=   cfg_engn_chkdl5 ;
            end
            default : begin
                cmp_engn_chkdl  <=  cmp_engn_chkdl ; 
            end
        endcase
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cmp_engn_chkul  <=   32'd0 ;
    end
    else begin
        case ( cal_chn_sel )
            3'd0 : begin
                cmp_engn_chkul  <=   cfg_engn_chkul0 ;
            end
            3'd1 : begin
                cmp_engn_chkul  <=   cfg_engn_chkul1 ;
            end
            3'd2 : begin
                cmp_engn_chkul  <=   cfg_engn_chkul2 ;
            end
            3'd3 : begin
                cmp_engn_chkul  <=   cfg_engn_chkul3 ;
            end
            3'd4 : begin
                cmp_engn_chkul  <=   cfg_engn_chkul4 ;
            end
            3'd5 : begin
                cmp_engn_chkul  <=   cfg_engn_chkul5 ;
            end
            default : begin
                cmp_engn_chkul  <=  cmp_engn_chkul ; 
            end
        endcase
    end
end

assign up_engn_chn0     = up_engn_chn[0] ;
assign up_engn_chn1     = up_engn_chn[1] ;
assign up_engn_chn2     = up_engn_chn[2] ;
assign up_engn_chn3     = up_engn_chn[3] ;
assign up_engn_chn4     = up_engn_chn[4] ;
assign up_engn_chn5     = up_engn_chn[5] ;

assign up_elec_chn0     = up_elec_chn[0] ;
assign up_elec_chn1     = up_elec_chn[1] ;
assign up_elec_chn2     = up_elec_chn[2] ;
assign up_elec_chn3     = up_elec_chn[3] ;
assign up_elec_chn4     = up_elec_chn[4] ;
assign up_elec_chn5     = up_elec_chn[5] ;

assign up_masb_chn0     = up_masb_chn[0] ;
assign up_masb_chn1     = up_masb_chn[1] ;
assign up_masb_chn2     = up_masb_chn[2] ;
assign up_masb_chn3     = up_masb_chn[3] ;
assign up_masb_chn4     = up_masb_chn[4] ;
assign up_masb_chn5     = up_masb_chn[5] ;
//----------------------------------------------------------------------------------
// 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calf_dgd_mode_mm    <=   6'd0 ;
    end
    else begin
        calf_dgd_mode_mm    <=   calf_dgd_mode ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calf_dgd_mode_ms    <=   6'd0 ;
    end
    else begin
        calf_dgd_mode_ms    <=   calf_dgd_mode ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_done_mm <=   1'b0 ;
    end
    else begin
        cal_done_mm <=   cal_done ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_done_ms <=   1'b0 ;
    end
    else begin
        cal_done_ms <=   cal_done ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pw_on_en_mm <=   1'b0 ;
    end
    else begin
        pw_on_en_mm <=   pw_on_en ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pw_on_en_ms <=   1'b0 ;
    end
    else begin
        pw_on_en_ms <=   pw_on_en ;
    end
end
       
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_spi_busy_mm <=   6'd0 ;
    end
    else begin
        adacq_spi_busy_mm <=   adacq_spi_busy ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_spi_busy_ms <=   6'd0 ;
    end
    else begin
        adacq_spi_busy_ms <=   adacq_spi_busy ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_dval_mm <=   1'b0 ;
    end
    else begin
        adacq_rd_dval_mm <=   adacq_rd_dval ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_dval_ms <=   1'b0 ;
    end
    else begin
        adacq_rd_dval_ms <=   adacq_rd_dval ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_data0_mm <=   16'h0000 ;
    end
    else begin
        adacq_rd_data0_mm <=   adacq_rd_data0 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_data0_ms <=   16'h0000 ;
    end
    else begin
        adacq_rd_data0_ms <=   adacq_rd_data0 ;
    end
end
                  
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_data1_mm <=   16'h0000 ;
    end
    else begin
        adacq_rd_data1_mm <=   adacq_rd_data1 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_data1_ms <=   16'h0000 ;
    end
    else begin
        adacq_rd_data1_ms <=   adacq_rd_data1 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_data2_mm <=   16'h0000 ;
    end
    else begin
        adacq_rd_data2_mm <=   adacq_rd_data2 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_data2_ms <=   16'h0000 ;
    end
    else begin
        adacq_rd_data2_ms <=   adacq_rd_data2 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_data3_mm <=   16'h0000 ;
    end
    else begin
        adacq_rd_data3_mm <=   adacq_rd_data3 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_data3_ms <=   16'h0000 ;
    end
    else begin
        adacq_rd_data3_ms <=   adacq_rd_data3 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_data4_mm <=   16'h0000 ;
    end
    else begin
        adacq_rd_data4_mm <=   adacq_rd_data4 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_data4_ms <=   16'h0000 ;
    end
    else begin
        adacq_rd_data4_ms <=   adacq_rd_data4 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_data5_mm <=   16'h0000 ;
    end
    else begin
        adacq_rd_data5_mm <=   adacq_rd_data5 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_data5_ms <=   16'h0000 ;
    end
    else begin
        adacq_rd_data5_ms <=   adacq_rd_data5 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfas_adsb_sel_mm <=   1'b0 ;
    end
    else begin
        calfas_adsb_sel_mm <=   calfas_adsb_sel ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfas_adsb_sel_ms <=   1'b0 ;
    end
    else begin
        calfas_adsb_sel_ms <=   calfas_adsb_sel ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfas_data_a_mm <=   32'h00000000 ;
    end
    else begin
        calfas_data_a_mm <=   calfas_data_a ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfas_data_a_ms <=   32'h00000000 ;
    end
    else begin
        calfas_data_a_ms <=   calfas_data_a ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfas_data_b_mm <=   32'h00000000 ;
    end
    else begin
        calfas_data_b_mm <=   calfas_data_b ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfas_data_b_ms <=   32'h00000000 ;
    end
    else begin
        calfas_data_b_ms <=   calfas_data_b ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfas_start_trig_mm <=   1'b0 ;
    end
    else begin
        calfas_start_trig_mm <=   calfas_start_trig ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfas_start_trig_ms <=   1'b0 ;
    end
    else begin
        calfas_start_trig_ms <=   calfas_start_trig ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfd_data_a_mm <=   32'h00000000 ;
    end
    else begin
        calfd_data_a_mm <=   calfd_data_a ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfd_data_a_ms <=   32'h00000000 ;
    end
    else begin
        calfd_data_a_ms <=   calfd_data_a ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfd_data_b_mm <=   32'h00000000 ;
    end
    else begin
        calfd_data_b_mm <=   calfd_data_b ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfd_data_b_ms <=   32'h00000000 ;
    end
    else begin
        calfd_data_b_ms <=   calfd_data_b ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfd_start_trig_mm <=   1'b0 ;
    end
    else begin
        calfd_start_trig_mm <=   calfd_start_trig ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfm_data_a_mm <=   32'h00000000 ;
    end
    else begin
        calfm_data_a_mm <=   calfm_data_a ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfm_data_a_ms <=   32'h00000000 ;
    end
    else begin
        calfm_data_a_ms <=   calfm_data_a ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfm_data_b_mm <=   32'h00000000 ;
    end
    else begin
        calfm_data_b_mm <=   calfm_data_b ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfm_data_b_ms <=   32'h00000000 ;
    end
    else begin
        calfm_data_b_ms <=   calfm_data_b ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        calfm_start_trig_mm <=   1'b0 ;
    end
    else begin
        calfm_start_trig_mm <=   calfm_start_trig ;
    end
end


always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_chn_enable_mm <=   6'b000000 ;
    end
    else begin
        cfg_chn_enable_mm <=   cfg_chn_enable ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_chn_enable_ms <=   32'h00000000 ;
    end
    else begin
        cfg_chn_enable_ms <=   cfg_chn_enable ;
    end
end

    AICHPRC                     U_AICHPRC_MM
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    // input signal
    .cal_model_en               ( cal_model_en              ),
    .calf_dgd_mode              ( calf_dgd_mode_mm          ),
    .cal_done                   ( cal_done_mm               ),
    .pw_on_en                   ( pw_on_en_mm               ),

    .adacq_spi_busy             ( adacq_spi_busy_mm         ),
    .adacq_rd_dval              ( adacq_rd_dval_mm          ),
    .adacq_rd_data0             ( adacq_rd_data0_mm         ),
    .adacq_rd_data1             ( adacq_rd_data1_mm         ),
    .adacq_rd_data2             ( adacq_rd_data2_mm         ),
    .adacq_rd_data3             ( adacq_rd_data3_mm         ),
    .adacq_rd_data4             ( adacq_rd_data4_mm         ),
    .adacq_rd_data5             ( adacq_rd_data5_mm         ),

    .calfas_adsb_sel            ( calfas_adsb_sel_mm        ),
    .calfas_data_a              ( calfas_data_a_mm          ),
    .calfas_data_b              ( calfas_data_b_mm          ),
    .calfas_start_trig          ( calfas_start_trig_mm      ),
    .calfd_data_a               ( calfd_data_a_mm           ),
    .calfd_data_b               ( calfd_data_b_mm           ),
    .calfd_start_trig           ( calfd_start_trig_mm       ),
    .calfm_data_a               ( calfm_data_a_mm           ),
    .calfm_data_b               ( calfm_data_b_mm           ),
    .calfm_start_trig           ( calfm_start_trig_mm       ),

    .b_factor0                  ( b_factor0                 ),
    .b_factor1                  ( b_factor1                 ),
    .b_factor2                  ( b_factor2                 ),
    .b_factor3                  ( b_factor3                 ),
    .b_factor4                  ( b_factor4                 ),
    .b_factor5                  ( b_factor5                 ),

    .kqe_factor0                ( kqe_factor0               ),
    .kqe_factor1                ( kqe_factor1               ),
    .kqe_factor2                ( kqe_factor2               ),
    .kqe_factor3                ( kqe_factor3               ),
    .kqe_factor4                ( kqe_factor4               ),
    .kqe_factor5                ( kqe_factor5               ),

    .ke_coeff0                  ( ke_coeff0                 ),
    .ke_coeff1                  ( ke_coeff1                 ),
    .ke_coeff2                  ( ke_coeff2                 ),
    .ke_coeff3                  ( ke_coeff3                 ),
    .ke_coeff4                  ( ke_coeff4                 ),
    .ke_coeff5                  ( ke_coeff5                 ),

    .bq_coeff0                  ( bq_coeff0                 ),
    .bq_coeff1                  ( bq_coeff1                 ),
    .bq_coeff2                  ( bq_coeff2                 ),
    .bq_coeff3                  ( bq_coeff3                 ),
    .bq_coeff4                  ( bq_coeff4                 ),
    .bq_coeff5                  ( bq_coeff5                 ),
    .cfg_chn_enable             ( cfg_chn_enable_mm         ),

     // output signal
    .ch_ad_diag                 ( ch_ad_diag0               ),
    .fas_done                   ( fas_done0                 ),
    .fas_result                 ( fas_result0               ),
    .fd_done                    ( fd_done0                  ),
    .fd_result                  ( fd_result0                ),
    .fm_done                    ( fm_done0                  ),
    .fm_result                  ( fm_result0                ),

    .state_cal_adde             ( state_cal_adde0           ),
    .state_cal_addq             ( state_cal_addq0           ),
    .acq_dgdad_en               ( acq_dgdad_en0             ),
    .state_cal_dgdt             ( state_cal_dgdt0           ),
    .state_cal_done             ( state_cal_done0           ),
    .cal_chn_sel                ( cal_chn_sel0              ),
    .adacq_rd_en                ( adacq_rd_en0              ),
    .cur_state                  ( cur_state0                ),
    .prc_done_trig              ( prc_done_trig[0]          )
             
    );

    AICHPRC                     U_AICHPRC_MS
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    // input signal
    .cal_model_en               ( cal_model_en              ),
    .calf_dgd_mode              ( calf_dgd_mode_ms          ),
    .cal_done                   ( cal_done_ms               ),
    .pw_on_en                   ( pw_on_en_ms               ),
    .adacq_spi_busy             ( adacq_spi_busy_ms         ),
    .adacq_rd_dval              ( adacq_rd_dval_ms          ),
    .adacq_rd_data0             ( adacq_rd_data0_ms         ),
    .adacq_rd_data1             ( adacq_rd_data1_ms         ),
    .adacq_rd_data2             ( adacq_rd_data2_ms         ),
    .adacq_rd_data3             ( adacq_rd_data3_ms         ),
    .adacq_rd_data4             ( adacq_rd_data4_ms         ),
    .adacq_rd_data5             ( adacq_rd_data5_ms         ),

    .calfas_adsb_sel            ( calfas_adsb_sel_ms        ),
    .calfas_data_a              ( calfas_data_a_ms          ),
    .calfas_data_b              ( calfas_data_b_ms          ),
    .calfas_start_trig          ( calfas_start_trig_ms      ),
    .calfd_data_a               ( calfd_data_a_ms           ),
    .calfd_data_b               ( calfd_data_b_ms           ),
    .calfd_start_trig           ( calfd_start_trig_ms       ),
    .calfm_data_a               ( calfm_data_a_ms           ),
    .calfm_data_b               ( calfm_data_b_ms           ),
    .calfm_start_trig           ( calfm_start_trig_ms       ),

    .b_factor0                  ( b_factor0                 ),
    .b_factor1                  ( b_factor1                 ),
    .b_factor2                  ( b_factor2                 ),
    .b_factor3                  ( b_factor3                 ),
    .b_factor4                  ( b_factor4                 ),
    .b_factor5                  ( b_factor5                 ),

    .kqe_factor0                ( kqe_factor0               ),
    .kqe_factor1                ( kqe_factor1               ),
    .kqe_factor2                ( kqe_factor2               ),
    .kqe_factor3                ( kqe_factor3               ),
    .kqe_factor4                ( kqe_factor4               ),
    .kqe_factor5                ( kqe_factor5               ),

    .ke_coeff0                  ( ke_coeff0                 ),
    .ke_coeff1                  ( ke_coeff1                 ),
    .ke_coeff2                  ( ke_coeff2                 ),
    .ke_coeff3                  ( ke_coeff3                 ),
    .ke_coeff4                  ( ke_coeff4                 ),
    .ke_coeff5                  ( ke_coeff5                 ),

    .bq_coeff0                  ( bq_coeff0                 ),
    .bq_coeff1                  ( bq_coeff1                 ),
    .bq_coeff2                  ( bq_coeff2                 ),
    .bq_coeff3                  ( bq_coeff3                 ),
    .bq_coeff4                  ( bq_coeff4                 ),
    .bq_coeff5                  ( bq_coeff5                 ),
    .cfg_chn_enable             ( cfg_chn_enable_ms         ),

     // output signal
    .ch_ad_diag                 ( ch_ad_diag1               ),
    .fas_done                   ( fas_done1                 ),
    .fas_result                 ( fas_result1               ),
    .fd_done                    ( fd_done1                  ),
    .fd_result                  ( fd_result1                ),
    .fm_done                    ( fm_done1                  ),
    .fm_result                  ( fm_result1                ),

    .state_cal_adde             ( state_cal_adde1           ),
    .state_cal_addq             ( state_cal_addq1           ),
    .acq_dgdad_en               ( acq_dgdad_en1             ),
    .state_cal_dgdt             ( state_cal_dgdt1           ),
    .state_cal_done             ( state_cal_done1           ),
    .cal_chn_sel                ( cal_chn_sel1              ),
    .adacq_rd_en                ( adacq_rd_en1              ),
    .cur_state                  ( cur_state1                ),
    .prc_done_trig              ( prc_done_trig[1]          )
             
    );

    CHREDUDIAG      U_CHREDUDIAG
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    .cal_chn_sel                ( cal_chn_sel               ),
    .fas_done0                  ( fas_done0                 ),
    .fas_result0                ( fas_result0               ), 
    .cur_state0                 ( cur_state0                ),
    .state_cal_adde0            ( state_cal_adde0           ),
    .state_cal_addq0            ( state_cal_addq0           ),
    .fas_done1                  ( fas_done1                 ),
    .fas_result1                ( fas_result1               ),
    .cur_state1                 ( cur_state1                ),
    .state_cal_adde1            ( state_cal_adde1           ),
    .state_cal_addq1            ( state_cal_addq1           ),
    .state_cal_dgdt             ( state_cal_dgdt            ),
    .state_cal_done             ( state_cal_done            ),
    .calf_dgd_mode              ( calf_dgd_mode             ),
    .ch_hw_fault                ( ch_hw_fault               ),
    .ch_rdu_fault               ( ch_rdu_fault              ),
    .rcy_sel                    ( rcy_sel                   )
    );

    FLOAT_CMPLT                 U_FLOAT_CMPLT
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .f_data_a                   ( cmp_engn_chkdl            ),
    .f_data_b                   ( rd_engn_value             ),
    .cmp_lt_en                  ( cmp_lt_en                 )
    );

    FLOAT_CMPLT                 U_FLOAT_CMPMT
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .f_data_a                   ( rd_engn_value             ),
    .f_data_b                   ( cmp_engn_chkul            ),
    .cmp_lt_en                  ( cmp_mt_en                 )
    );

    FLOAT_CMPLT                 U_FLOAT_CMPTEST
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .f_data_a                   ( up_engn_chn[5]            ),
    .f_data_b                   ( 32'h42700000              ),
    .cmp_lt_en                  ( cmp_mt_test               )
    );

endmodule
