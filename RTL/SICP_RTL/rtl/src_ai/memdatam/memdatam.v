// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-11-02
// DEPARTMENT       :   R&D
// AUTHOR           :   YongjunZhang
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-11-02  YongjunZhang        Original
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

module  MEMDATAM 
    (
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 
        clk_12_5m               ,   
        rst_12_5m_n             ,   

        // cfginfofrm
        slink_cfg_dval          ,   
        slink_cfg_data          ,   
        cfg_md_id               ,   
        cfg_code_rev            ,   
        cfg_run_tm              , 
        cfg_com_mode            ,   
        cfg_enable_slot         ,   
        cfg_slink_chen          ,   
        cfg_done                ,   
        cfg_done_trig           ,   
        cfg_chn_enable          ,   
        self_id_err             ,   
        // dwdatafrm
        slink_dt_dval           ,   
        slink_dt_data           ,   
        dw_ctr_cmd              ,   // the control command 2'd0 : ; 2'd1 : enable; 2'd3: ;
        dw_com_stus             ,   
        com_fault               ,   
        cfg_req_fail               
    );

/**********************************************************************************\
***************************** declare parameter ************************************

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input interface signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ; 
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m_n                         ;   
input   wire                    slink_dt_dval                       ;   
input   wire    [9:0]           slink_dt_data                       ; 
input   wire                    self_id_err                         ;   

input   wire                    slink_cfg_dval                      ;   
input   wire    [9:0]           slink_cfg_data                      ; 
// output interface signal
output  wire    [31:0]          dw_ctr_cmd                          ;   
output  wire    [31:0]          dw_com_stus                         ;
output  wire    [1:0]           com_fault                           ;   
output  wire    [31:0]          cfg_md_id                           ;   
output  wire    [31:0]          cfg_code_rev                        ;   
output  wire    [15:0]          cfg_run_tm                          ;   
output  wire    [7:0]           cfg_com_mode                        ;
output  wire    [1:0]           cfg_enable_slot                     ;   
output  wire                    cfg_done                            ;   
output  wire                    cfg_done_trig                       ;   
output  wire    [11:0]          cfg_chn_enable                      ;   
output  wire    [1:0]           cfg_slink_chen                      ;   
output  wire                    cfg_req_fail                        ;
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
   
/**********************************************************************************\
******************************** debug code ****************************************/

/**********************************************************************************\
********************************* main code ****************************************/
//----------------------------------------------------------------------------------
// the module of configure information frame
//----------------------------------------------------------------------------------
    CFGINFOPUB  U_CFGINFOPUB 
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m_n                ( rst_12_5m_n               ),

    .self_id_err                ( self_id_err               ),
    .slink_cfg_dval             ( slink_cfg_dval            ),
    .slink_cfg_data             ( slink_cfg_data            ),

    .cfg_req_fail               ( cfg_req_fail              ),
    .cfg_md_id                  ( cfg_md_id                 ),
    .cfg_code_rev               ( cfg_code_rev              ),
    .cfg_run_tm                 ( cfg_run_tm                ),
    .cfg_com_mode               ( cfg_com_mode              ),
    .cfg_enable_slot            ( cfg_enable_slot           ),
    .cfg_slink_chen             ( cfg_slink_chen            ),
    .cfg_done                   ( cfg_done                  ),
    .cfg_done_trig              ( cfg_done_trig             ),
    .cfg_chn_enable             ( cfg_chn_enable            )
    );

    DWDATAFRM  U_DWDATAFRM
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .slink_dt_dval              ( slink_dt_dval             ),
    .slink_dt_data              ( slink_dt_data             ),

    .cfg_done                   ( cfg_done                  ),    
    .cfg_run_tm                 ( cfg_run_tm                ),
    .dw_ctr_cmd                 ( dw_ctr_cmd                ),
    .dw_com_stus                ( dw_com_stus               ),
    .com_fault                  ( com_fault                 )
    );

endmodule
