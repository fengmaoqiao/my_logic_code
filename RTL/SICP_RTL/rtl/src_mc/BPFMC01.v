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

module  BPFMC01
    (
    // clock & reset
    FPGA_125M_P                    , // communication clock , the output of external 125M difference crystal oscillator   
    FPGA_125M_N                    ,   
    FPGA_NRST                      , // system reset , TPS3808G01DBVT's output , include poweron & button reset

    // EMIF bus
	EMIF_NCS4                      , 
    EMIF_ADDR                      , // EMIF address bus
	EMIF_DATA                      , // EMIF data bus
	EMIF_BA                        , // EMIF bank address
	EMIF_NOE                       , 
	EMIF_NWE                       , // Active-low write enable

    // backplane lvds 
	LVDS_RXP                       , // connect to other board of box
	LVDS_RXN                       , 
    LVDS_TXP                       ,   
    LVDS_TXN                       ,   

	MCU_LVDS_RXP                   , // connect to redundant MCU  
	MCU_LVDS_RXN                   ,   
	MCU_LVDS_TXP                   , 
	MCU_LVDS_TXN                   , 

    // SFF interface 
	SFF_TDIS                       ,   // connect to optical module of the tdis signal  
	SFF_SD                         ,   // connect to optical module of the sd signal 
	SFF_RXP                        ,   // connect to optical module of the recieve difference signal 
	SFF_RXN                        ,   
	SFF_TXP                        ,   // connect to optical module of the transmiss difference signal 
    SFF_TXN                        , 

	// backplane misc signals
	SLOT_NUM                       , // slot number  
	STA_NUM                        , // station number  
	BOX_NUM                        , // box number 
	ONLINE                         , // other board of box present  
    MCU_ONLINE                     ,   
	MCU_HT_LINE0                   , // heartbeat line to redundant MCU  
	MCU_HT_LINE1                   , // heartbeat line from redundant MCU  
	MCU_MST_SLV0                   , // master or slave indication to redundant MCU  
	MCU_MST_SLV1                   , // master or slave indication from redundant MCU 

    // led
    MAS_LED                        ,   
    SLA_LED                        ,   
    DEBUG_LED                      ,

    UART_RX                        ,
    UART_TX
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    FPGA_125M_P                         ;   
input   wire                    FPGA_125M_N                         ;   
input   wire                    FPGA_NRST                           ;   

input   wire	                EMIF_NCS4                           ;   
input   wire    [21:0]          EMIF_ADDR                           ;   
input   wire    [1:0]           EMIF_BA                             ;   
input   wire	                EMIF_NOE                            ;   
input   wire	                EMIF_NWE                            ;   
input   wire    [13:0]          LVDS_RXP                            ;   
input   wire    [13:0]          LVDS_RXN                            ;   
input   wire                    MCU_LVDS_RXP                        ;   
input   wire                    MCU_LVDS_RXN                        ;   
input   wire                    SFF_SD                              ;   
input   wire                    SFF_RXP                             ;   
input   wire                    SFF_RXN                             ;   

input   wire    [3:0]           SLOT_NUM                            ;/* synthesis syn_preserve = 1 */     
input   wire    [7:0]           STA_NUM                             ;/* synthesis syn_preserve = 1 */     
input   wire    [3:0]           BOX_NUM                             ;/* synthesis syn_preserve = 1 */    
input   wire    [13:0]          ONLINE                              ;/* synthesis syn_preserve = 1 */   
input   wire                    MCU_ONLINE                          ;/* synthesis syn_preserve = 1 */   
input   wire                    MCU_HT_LINE1                        ;/* synthesis syn_keep = 1 */ 
input   wire                    MCU_MST_SLV1                        ;/* synthesis syn_preserve = 1 */   

// declare output signal
output  wire    [13:0]          LVDS_TXP                            ;   
output  wire    [13:0]          LVDS_TXN                            ;   
output  wire                    MCU_LVDS_TXP                        ;   
output  wire                    MCU_LVDS_TXN                        ;   
output  wire                    SFF_TDIS                            ;   
output  wire                    SFF_TXP                             ;   
output  wire                    SFF_TXN                             ;   
output  wire                    MCU_HT_LINE0                        ;   
output  wire                    MCU_MST_SLV0                        ;   
output  wire    [1:0]           MAS_LED                             ; // [1] : green [0] : red  
output  wire    [1:0]           SLA_LED                             ;   
output  wire    [3:0]           DEBUG_LED                           ; 

// declare inout signal
inout   wire    [15:0]          EMIF_DATA                           ;

input   wire                    UART_RX                             ;
output  wire                    UART_TX                             ;

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            clk_12_5m                           ;   
wire                            rst_12_5m                           ;   
wire                            rst_125m                            ;   
wire                            clk_125m_0                          ;   
wire                            clk_125m_90                         ;   
wire                            clk_125m_180                        ;   
wire                            clk_125m_270                        ; 
wire                            soft_rst                            ;   
wire        [7:0]               dst_sta_num                         ;   

wire        [7:0]               selfm_ms_flag                       ;   
wire        [7:0]               excfg_ms_flag                       ;   
wire        [7:0]               type1_ms_flag       [3:0]           ;
wire        [7:0]               type2_ms_flag       [9:0]           ;

wire                            emif_out_ctrl                       ;   
wire        [15:0]              emif_rd_data                        ;   
wire        [15:0]              emif_wrdata                         ; 

wire                            self_cfg_wr_sel                     ;   
wire                            self_cfg_wr_en                      ;   
wire        [17:0]              self_cfg_wr_data                    ;   
wire                            self_sta_wr_sel                     ;   
wire                            self_sta_wr_en                      ;   
wire        [15:0]              self_sta_wr_data                    ;   
wire                            prm_wr_sel                          ;   
wire        [3:0]               prm_pkt_num                         ;   
wire                            prm_wr_en                           ;  
wire        [17:0]              prm_wr_data                         ;   
wire                            hrm_wr_sel                          ;  
wire        [3:0]               hrm_pkt_num                         ;   
wire                            hrm_wr_en                           ;   
wire        [17:0]              hrm_wr_data                         ;   

wire        [3:0]               type1_wr_sel                        ;   
wire        [9:0]               type2_wr_sel                        ;   
wire        [7:0]               type1_wr_port   [3:0]               ;   
wire        [2:0]               type2_wr_port   [9:0]               ;   
wire        [3:0]               type1_wr_en                         ;   
wire        [9:0]               type2_wr_en                         ;   
wire        [17:0]              type1_wr_data  [3:0]                ;   
wire        [17:0]              type2_wr_data  [9:0]                ;
wire                            ex1_cfg_wr_sel                      ;   
wire                            ex2_cfg_wr_sel                      ;   
wire                            ex3_cfg_wr_sel                      ;   
wire                            ex4_cfg_wr_sel                      ;   
wire        [3:0]               ex1_cfg_slot                        ;   
wire        [3:0]               ex2_cfg_slot                        ;   
wire        [3:0]               ex3_cfg_slot                        ;   
wire        [3:0]               ex4_cfg_slot                        ;   
wire                            ex1_cfg_wr_en                       ;   
wire                            ex2_cfg_wr_en                       ;   
wire                            ex3_cfg_wr_en                       ;   
wire                            ex4_cfg_wr_en                       ;   
wire        [17:0]              ex1_cfg_wr_data                     ;   
wire        [17:0]              ex2_cfg_wr_data                     ;   
wire        [17:0]              ex3_cfg_wr_data                     ;   
wire        [17:0]              ex4_cfg_wr_data                     ;   

wire                            selfm_rd_sel                        ;   
wire        [8:0]               selfm_rd_addr                       ;   
wire                            mpu_sta_rd_sel                      ;   
wire                            ex1_sta_rd_sel                      ;   
wire                            ex2_sta_rd_sel                      ;   
wire                            ex3_sta_rd_sel                      ;   
wire                            ex4_sta_rd_sel                      ;   
wire        [8:0]               mpu_rd_addr                         ;   
wire        [8:0]               ex1_rd_addr                         ;   
wire        [8:0]               ex2_rd_addr                         ;   
wire        [8:0]               ex3_rd_addr                         ;   
wire        [8:0]               ex4_rd_addr                         ;   
wire                            prm_rd_sel                          ;   
wire        [3:0]               prm_rd_pkt_num                      ;   
wire        [8:0]               prm_rd_addr                         ;   
wire                            hrm_rd_sel                          ;   
wire        [3:0]               hrm_rd_pkt_num                      ;   
wire        [8:0]               hrm_rd_addr                         ;   
wire        [3:0]               type1_rd_sel                        ;   
wire        [6:0]               type1_rd_port  [3:0]                ;   
wire        [8:0]               type1_rd_addr  [3:0]                ;   
wire        [9:0]               type2_rd_sel                        ;   
wire        [1:0]               type2_rd_port  [9:0]                ;   
wire        [8:0]               type2_rd_addr  [9:0]                ;   

wire        [3:0]               ex_box_data_ena     [3:0]           ;   
wire        [3:0]               ex_box_cfg_ena      [3:0]           ;   
wire        [31:0]              card_id                             ;   
wire        [15:0]              code_version                        ;   
wire        [15:0]              enable_slot                         ;   
wire        [15:0]              run_cycle                           ;   
wire        [7:0]               redundancy_mode                     ;
wire                            mpu_cfg_wr_ok                       ;  

wire        [15:0]              chn_break_err                       ;   
wire        [15:0]              chn_pkt_len_err                     ;   
wire        [15:0]              chn_pkt_tick_err                    ;   
wire        [15:0]              chn_pkt_crc_err                     ;   
wire        [15:0]              chn_pkt_delay_err                   ;   
wire        [15:0]              chn_pkt_eop                         ;   
wire        [15:0]              slink_err                           ;   

wire        [3:0]               excmm_ssdu_empty                    ;   
wire        [3:0]               excmm_ssdu_dval                     ;   
wire        [17:0]              excmm_ssdu_data0                    ;   
wire        [17:0]              excmm_ssdu_data1                    ;   
wire        [17:0]              excmm_ssdu_data2                    ;   
wire        [17:0]              excmm_ssdu_data3                    ;   
wire        [3:0]               ssdu_excmm_rdreq    [3:0]           ;   

wire        [3:0]               type1_rd_dmm_empty  [3:0]           ;
wire        [4:0]               type1_chn_type      [3:0]           ;
wire        [3:0]               type1_hot_plug_req                  ;   
wire        [3:0]               type1_rd_dval                       ;   
wire        [15:0]              type1_rd_data       [3:0]           ;
wire        [3:0]               type1_lvds_rxp_in                   ;   
wire        [3:0]               type1_lvds_rxn_in                   ;   
wire        [3:0]               type1_lvds_txp_out                  ;   
wire        [3:0]               type1_lvds_txn_out                  ;
wire        [3:0]               mpu_sta_dval                        ;   
wire        [17:0]              mpu_sta_data        [3:0]           ;
wire        [3:0]               ex1_sta_dval                        ;   
wire        [17:0]              ex1_sta_data        [3:0]           ;
wire        [3:0]               ex2_sta_dval                        ;   
wire        [17:0]              ex2_sta_data        [3:0]           ;
wire        [3:0]               ex3_sta_dval                        ;   
wire        [17:0]              ex3_sta_data        [3:0]           ;
wire        [3:0]               ex4_sta_dval                        ;   
wire        [17:0]              ex4_sta_data        [3:0]           ;
wire        [3:0]               type1_slink_err                     ;   
wire        [3:0]               type1_self_cfg_err                  ;   

wire        [3:0]               type2_rd_dmm_empty  [9:0]           ;
wire        [4:0]               type2_chn_type      [9:0]           ;
wire        [9:0]               type2_rd_dval                       ;   
wire        [15:0]              type2_rd_data       [9:0]           ;
wire        [9:0]               type2_lvds_rxp_in                   ;   
wire        [9:0]               type2_lvds_rxn_in                   ;   
wire        [9:0]               type2_lvds_txp_out                  ;   
wire        [9:0]               type2_lvds_txn_out                  ;  
wire        [9:0]               type2_sta_dval                      ;   
wire        [17:0]              type2_sta_data      [9:0]           ;
wire        [9:0]               type2_slink_err                     ;   
wire        [9:0]               type2_self_cfg_err                  ;   

wire        [15:0]              prm_rd_data                         ;  
wire                            prm_slink_err                       ;   

wire        [15:0]              hrm_rd_data                         ;
wire                            hrm_slink_err                       ;   

wire        [3:0]               rr_sel              [3:0]           ;
wire                            selfm_ra_dval                       ;   
wire        [15:0]              selfm_rd_data                       ; 
wire        [15:0]              mpu_rd_data                         ;   
wire        [15:0]              ex1_rd_data                         ;   
wire        [15:0]              ex2_rd_data                         ;   
wire        [15:0]              ex3_rd_data                         ;   
wire        [15:0]              ex4_rd_data                         ;   
wire        [15:0]              ex1_hot_plug_req                    ;   
wire        [15:0]              ex2_hot_plug_req                    ;   
wire        [15:0]              ex3_hot_plug_req                    ;   
wire        [15:0]              ex4_hot_plug_req                    ; 
wire        [3:0]               ex1_slot_sel                        ;   
wire        [3:0]               ex2_slot_sel                        ;   
wire        [3:0]               ex3_slot_sel                        ;   
wire        [3:0]               ex4_slot_sel                        ;   
wire                            emif_err                            ; 

wire                            emif_self_cfg_err                   ;   
wire                            hotr_self_cfg_err                   ;   

wire    [31:0]                  rx_frame_data                       ;   
wire                            rx_frame_data_val                   ;   
wire                            crc_check_ok                        ;   
wire                            uart_time_out                       ;   
wire                            mcu_is_master                       ;   
wire                            status_rd_sel                       ;   
wire    [9:0]                   status_rd_addr                      ;   
wire    [15:0]                  status_rd_data                      ;   

wire    [15:0]                  self_status                         ;   
wire    [15:0]                  mcu_status                          ;   
wire                            frame_send_en                       ;   
wire    [31:0]                  frame_send_data                     ;   
wire                            arm_ok                              ;   
wire                            hotra_delay                         ;   
wire                            self_send_en                        ;   
wire                            mcu_feedback_val                    ;   
wire                            mcu_state_req                       ;   
wire                            send_sta_val                        ;   
wire    [1:0]                   arm_mode                            ;   
wire                            online_shake_o                      ;   
wire    [15:0]                  current_state_o                     ;   
wire    [15:0]                  arm_cycle                           ;   
wire    [1:0]                   mcu_arm_mode                        ;
wire    [14:0]                  ex1_box_online  [3:0]               ;
wire    [14:0]                  ex2_box_online  [3:0]               ;
wire    [14:0]                  ex3_box_online  [3:0]               ;
wire    [14:0]                  ex4_box_online  [3:0]               ;
wire                            mcu_is_valid                        ;
wire                            hw_init_ok                          ;
wire                            arm_tx_finish                       ;
// reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
assign  SFF_TDIS    =  ~ rst_125m ;

assign  DEBUG_LED[0] = selfm_ms_flag == 8'hff ? 1'b0 : 1'b1  ; 
assign  DEBUG_LED[1] = 1'b1 ; 
assign  DEBUG_LED[2] = 1'b1 ; 
assign  DEBUG_LED[3] = 1'b1 ; 

assign  MAS_LED[1] = ( hw_init_ok && current_state_o != 16'd0 && redundancy_mode == 8'h20 ) ? selfm_ms_flag == 8'hff : 1'b0 ;   
assign  SLA_LED[1] = ( hw_init_ok && current_state_o != 16'd0 && redundancy_mode == 8'h20 ) ? selfm_ms_flag == 8'h00 : 1'b0 ;   
assign  MAS_LED[0] = 1'b0 ;   
assign  SLA_LED[0] = 1'b0 ;   

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

    CRM                         U_CRM
    (
    .clk_125m_p                 ( FPGA_125M_P               ),
    .clk_125m_n                 ( FPGA_125M_N               ),
    .hard_rst                   ( FPGA_NRST                 ),
    .soft_rst                   ( soft_rst                  ),

    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .rst_125m                   ( rst_125m                  ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              )
    );

//----------------------------------------------------------------------------------
// EMIF
//----------------------------------------------------------------------------------
assign  emif_wrdata =   EMIF_DATA;
assign  EMIF_DATA   =   emif_out_ctrl == 1'b1 ? emif_rd_data : 16'bzzzzzzzzzzzzzzzz ;

    EMIF                        U_EMIF
    (
    .clk_emif                   ( clk_125m_0                ),
    .rst_emif                   ( rst_125m                  ),

    .slot_num                   ( SLOT_NUM                  ),
    // EMIF interface
    .emif_cs                    ( EMIF_NCS4                 ),
    .emif_addr                  ( EMIF_ADDR                 ),
    .emif_ba                    ( EMIF_BA[1]                ),
    .emif_oe                    ( EMIF_NOE                  ),
    .emif_we                    ( EMIF_NWE                  ),
    .emif_wrdata                ( emif_wrdata               ),
    .emif_out_ctrl              ( emif_out_ctrl             ),
    .emif_rd_data               ( emif_rd_data              ),

    .self_cfg_wr_sel            ( self_cfg_wr_sel           ),
    .self_cfg_wr_en             ( self_cfg_wr_en            ),
    .self_cfg_wr_data           ( self_cfg_wr_data          ),
    .self_sta_wr_sel            ( self_sta_wr_sel           ),
    .self_sta_wr_en             ( self_sta_wr_en            ),
    .self_sta_wr_data           ( self_sta_wr_data          ),
    .prm_wr_sel                 ( prm_wr_sel                ),
    .prm_pkt_num                ( prm_pkt_num               ),
    .prm_wr_en                  ( prm_wr_en                 ),
    .prm_wr_data                ( prm_wr_data               ),
    .hrm_wr_sel                 ( hrm_wr_sel                ),
    .hrm_pkt_num                ( hrm_pkt_num               ),
    .hrm_wr_en                  ( hrm_wr_en                 ),
    .hrm_wr_data                ( hrm_wr_data               ),
    .mpu_slot2_wr_sel           ( type1_wr_sel[0]           ),
    .mpu_slot3_wr_sel           ( type1_wr_sel[1]           ),
    .mpu_slot4_wr_sel           ( type1_wr_sel[2]           ),
    .mpu_slot5_wr_sel           ( type1_wr_sel[3]           ),
    .mpu_slot6_wr_sel           ( type2_wr_sel[0]           ),
    .mpu_slot7_wr_sel           ( type2_wr_sel[1]           ),
    .mpu_slot8_wr_sel           ( type2_wr_sel[2]           ),
    .mpu_slot9_wr_sel           ( type2_wr_sel[3]           ),
    .mpu_slot10_wr_sel          ( type2_wr_sel[4]           ),
    .mpu_slot11_wr_sel          ( type2_wr_sel[5]           ),
    .mpu_slot12_wr_sel          ( type2_wr_sel[6]           ),
    .mpu_slot13_wr_sel          ( type2_wr_sel[7]           ),
    .mpu_slot14_wr_sel          ( type2_wr_sel[8]           ),
    .mpu_slot15_wr_sel          ( type2_wr_sel[9]           ),
    .mpu_slot2_port             ( type1_wr_port[0]          ),
    .mpu_slot3_port             ( type1_wr_port[1]          ),
    .mpu_slot4_port             ( type1_wr_port[2]          ),
    .mpu_slot5_port             ( type1_wr_port[3]          ),
    .mpu_slot6_port             ( type2_wr_port[0]          ),
    .mpu_slot7_port             ( type2_wr_port[1]          ),
    .mpu_slot8_port             ( type2_wr_port[2]          ),
    .mpu_slot9_port             ( type2_wr_port[3]          ),
    .mpu_slot10_port            ( type2_wr_port[4]          ),
    .mpu_slot11_port            ( type2_wr_port[5]          ),
    .mpu_slot12_port            ( type2_wr_port[6]          ),
    .mpu_slot13_port            ( type2_wr_port[7]          ),
    .mpu_slot14_port            ( type2_wr_port[8]          ),
    .mpu_slot15_port            ( type2_wr_port[9]          ),
    .mpu_slot2_wr_en            ( type1_wr_en[0]            ),
    .mpu_slot3_wr_en            ( type1_wr_en[1]            ),
    .mpu_slot4_wr_en            ( type1_wr_en[2]            ),
    .mpu_slot5_wr_en            ( type1_wr_en[3]            ),
    .mpu_slot6_wr_en            ( type2_wr_en[0]            ),
    .mpu_slot7_wr_en            ( type2_wr_en[1]            ),
    .mpu_slot8_wr_en            ( type2_wr_en[2]            ),
    .mpu_slot9_wr_en            ( type2_wr_en[3]            ),
    .mpu_slot10_wr_en           ( type2_wr_en[4]            ),
    .mpu_slot11_wr_en           ( type2_wr_en[5]            ),
    .mpu_slot12_wr_en           ( type2_wr_en[6]            ),
    .mpu_slot13_wr_en           ( type2_wr_en[7]            ),
    .mpu_slot14_wr_en           ( type2_wr_en[8]            ),
    .mpu_slot15_wr_en           ( type2_wr_en[9]            ),
    .mpu_slot2_wr_data          ( type1_wr_data[0]          ),
    .mpu_slot3_wr_data          ( type1_wr_data[1]          ),
    .mpu_slot4_wr_data          ( type1_wr_data[2]          ),
    .mpu_slot5_wr_data          ( type1_wr_data[3]          ),
    .mpu_slot6_wr_data          ( type2_wr_data[0]          ),
    .mpu_slot7_wr_data          ( type2_wr_data[1]          ),
    .mpu_slot8_wr_data          ( type2_wr_data[2]          ),
    .mpu_slot9_wr_data          ( type2_wr_data[3]          ),
    .mpu_slot10_wr_data         ( type2_wr_data[4]          ),
    .mpu_slot11_wr_data         ( type2_wr_data[5]          ),
    .mpu_slot12_wr_data         ( type2_wr_data[6]          ),
    .mpu_slot13_wr_data         ( type2_wr_data[7]          ),
    .mpu_slot14_wr_data         ( type2_wr_data[8]          ),
    .mpu_slot15_wr_data         ( type2_wr_data[9]          ),
    .ex1_cfg_wr_sel             ( ex1_cfg_wr_sel            ),
    .ex2_cfg_wr_sel             ( ex2_cfg_wr_sel            ),
    .ex3_cfg_wr_sel             ( ex3_cfg_wr_sel            ),
    .ex4_cfg_wr_sel             ( ex4_cfg_wr_sel            ),
    .ex1_cfg_slot               ( ex1_cfg_slot              ),
    .ex2_cfg_slot               ( ex2_cfg_slot              ),
    .ex3_cfg_slot               ( ex3_cfg_slot              ),
    .ex4_cfg_slot               ( ex4_cfg_slot              ),
    .ex1_cfg_wr_en              ( ex1_cfg_wr_en             ),
    .ex2_cfg_wr_en              ( ex2_cfg_wr_en             ),
    .ex3_cfg_wr_en              ( ex3_cfg_wr_en             ),
    .ex4_cfg_wr_en              ( ex4_cfg_wr_en             ),
    .ex1_cfg_wr_data            ( ex1_cfg_wr_data           ),
    .ex2_cfg_wr_data            ( ex2_cfg_wr_data           ),
    .ex3_cfg_wr_data            ( ex3_cfg_wr_data           ),
    .ex4_cfg_wr_data            ( ex4_cfg_wr_data           ),
    .self_cfg_err               ( emif_self_cfg_err         ),
    .emif_err                   ( emif_err                  ),

    .selfm_rd_data              ( selfm_rd_data             ),
    .mpu_rd_data                ( mpu_rd_data               ),
    .ex1_rd_data                ( ex1_rd_data               ),
    .ex2_rd_data                ( ex2_rd_data               ),
    .ex3_rd_data                ( ex3_rd_data               ),
    .ex4_rd_data                ( ex4_rd_data               ),
    .prm_rd_data                ( prm_rd_data               ),
    .hrm_rd_data                ( hrm_rd_data               ),
    .type1_rd_dval              ( type1_rd_dval             ),
    .slot2_rd_data              ( type1_rd_data[0]          ),
    .slot3_rd_data              ( type1_rd_data[1]          ),
    .slot4_rd_data              ( type1_rd_data[2]          ),
    .slot5_rd_data              ( type1_rd_data[3]          ),
    .slot6_rd_data              ( type2_rd_data[0]          ),
    .slot7_rd_data              ( type2_rd_data[1]          ),
    .slot8_rd_data              ( type2_rd_data[2]          ),
    .slot9_rd_data              ( type2_rd_data[3]          ),
    .slot10_rd_data             ( type2_rd_data[4]          ),
    .slot11_rd_data             ( type2_rd_data[5]          ),
    .slot12_rd_data             ( type2_rd_data[6]          ),
    .slot13_rd_data             ( type2_rd_data[7]          ),
    .slot14_rd_data             ( type2_rd_data[8]          ),
    .slot15_rd_data             ( type2_rd_data[9]          ),

    .selfm_rd_sel               ( selfm_rd_sel              ),
    .selfm_rd_addr              ( selfm_rd_addr             ),
    .mpu_sta_rd_sel             ( mpu_sta_rd_sel            ),
    .ex1_sta_rd_sel             ( ex1_sta_rd_sel            ),
    .ex2_sta_rd_sel             ( ex2_sta_rd_sel            ),
    .ex3_sta_rd_sel             ( ex3_sta_rd_sel            ),
    .ex4_sta_rd_sel             ( ex4_sta_rd_sel            ),
    .mpu_rd_addr                ( mpu_rd_addr               ),
    .ex1_rd_addr                ( ex1_rd_addr               ),
    .ex2_rd_addr                ( ex2_rd_addr               ),
    .ex3_rd_addr                ( ex3_rd_addr               ),
    .ex4_rd_addr                ( ex4_rd_addr               ),
    .prm_rd_sel                 ( prm_rd_sel                ),
    .prm_rd_pkt_num             ( prm_rd_pkt_num            ),
    .prm_rd_addr                ( prm_rd_addr               ),
    .hrm_rd_sel                 ( hrm_rd_sel                ),
    .hrm_rd_pkt_num             ( hrm_rd_pkt_num            ),
    .hrm_rd_addr                ( hrm_rd_addr               ),
    .mpu_slot2_rd_sel           ( type1_rd_sel[0]           ),
    .mpu_slot3_rd_sel           ( type1_rd_sel[1]           ),
    .mpu_slot4_rd_sel           ( type1_rd_sel[2]           ),
    .mpu_slot5_rd_sel           ( type1_rd_sel[3]           ),
    .mpu_slot6_rd_sel           ( type2_rd_sel[0]           ),
    .mpu_slot7_rd_sel           ( type2_rd_sel[1]           ),
    .mpu_slot8_rd_sel           ( type2_rd_sel[2]           ),
    .mpu_slot9_rd_sel           ( type2_rd_sel[3]           ),
    .mpu_slot10_rd_sel          ( type2_rd_sel[4]           ),
    .mpu_slot11_rd_sel          ( type2_rd_sel[5]           ),
    .mpu_slot12_rd_sel          ( type2_rd_sel[6]           ),
    .mpu_slot13_rd_sel          ( type2_rd_sel[7]           ),
    .mpu_slot14_rd_sel          ( type2_rd_sel[8]           ),
    .mpu_slot15_rd_sel          ( type2_rd_sel[9]           ),
    .mpu_slot2_rd_port          ( type1_rd_port[0]          ),
    .mpu_slot3_rd_port          ( type1_rd_port[1]          ),
    .mpu_slot4_rd_port          ( type1_rd_port[2]          ),
    .mpu_slot5_rd_port          ( type1_rd_port[3]          ),
    .mpu_slot6_rd_port          ( type2_rd_port[0]          ),
    .mpu_slot7_rd_port          ( type2_rd_port[1]          ),
    .mpu_slot8_rd_port          ( type2_rd_port[2]          ),
    .mpu_slot9_rd_port          ( type2_rd_port[3]          ),
    .mpu_slot10_rd_port         ( type2_rd_port[4]          ),
    .mpu_slot11_rd_port         ( type2_rd_port[5]          ),
    .mpu_slot12_rd_port         ( type2_rd_port[6]          ),
    .mpu_slot13_rd_port         ( type2_rd_port[7]          ),
    .mpu_slot14_rd_port         ( type2_rd_port[8]          ),
    .mpu_slot15_rd_port         ( type2_rd_port[9]          ),
    .mpu_slot2_rd_addr          ( type1_rd_addr[0]          ),
    .mpu_slot3_rd_addr          ( type1_rd_addr[1]          ),
    .mpu_slot4_rd_addr          ( type1_rd_addr[2]          ),
    .mpu_slot5_rd_addr          ( type1_rd_addr[3]          ),
    .mpu_slot6_rd_addr          ( type2_rd_addr[0]          ),
    .mpu_slot7_rd_addr          ( type2_rd_addr[1]          ),
    .mpu_slot8_rd_addr          ( type2_rd_addr[2]          ),
    .mpu_slot9_rd_addr          ( type2_rd_addr[3]          ),
    .mpu_slot10_rd_addr         ( type2_rd_addr[4]          ),
    .mpu_slot11_rd_addr         ( type2_rd_addr[5]          ),
    .mpu_slot12_rd_addr         ( type2_rd_addr[6]          ),
    .mpu_slot13_rd_addr         ( type2_rd_addr[7]          ),
    .mpu_slot14_rd_addr         ( type2_rd_addr[8]          ),
    .mpu_slot15_rd_addr         ( type2_rd_addr[9]          )
    );
//----------------------------------------------------------------------------------
// redundacncy uart
//----------------------------------------------------------------------------------


    SELF_MCU_STATUS             #
    (
    .UART_TX_PERIOD             ( 32'd375000                )    
    )
    U_SELF_MCU_STATUS
    (
    .clk_sys                    ( clk_125m_0                ),
    .rst_sys_n                  ( rst_125m                  ),

    .rx_frame_data              ( rx_frame_data             ),
    .rx_frame_data_val          ( rx_frame_data_val         ),
    .crc_check_ok               ( crc_check_ok              ),
    .uart_time_out              ( uart_err                  ),

    .mpu_sta_rd_sel             ( status_rd_sel             ),
    .mpu_sta_rd_addr            ( status_rd_addr            ),
    .mpu_sta_rd_data            ( status_rd_data            ),

    .mcu_is_master              ( mcu_is_master             ),

    .self_status                ( self_status               ),
    .mcu_status                 ( mcu_status                ),

    .slink_err                  ( slink_err                 ),
    .ms_mode                    ( selfm_ms_flag             ),
    .emif_err                   ( emif_err                  ),
    .arm_ok                     ( arm_ok                    ),

    .frame_send_en              ( frame_send_en             ),
    .frame_send_data            ( frame_send_data           ),

    .mpu_cfg_wr_ok              ( mpu_cfg_wr_ok             ),
    .send_sta_val               ( send_sta_val              ),
    .arm_mode                   ( arm_mode                  ),
    .mcu_arm_mode               ( mcu_arm_mode              ),
    .current_state_i            ( current_state_o           )
    );

    
   
    REDUNDANCY_COM              U_REDUNDANCY
    (
    .clk_sys                    ( clk_125m_0                ),
    .rst_n                      ( rst_125m                  ),

    .frame_send_en              ( frame_send_en             ),
    .frame_send_data            ( frame_send_data           ),

    .rx_frame_data              ( rx_frame_data             ),
    .rx_frame_data_val          ( rx_frame_data_val         ),
    .crc_check_ok               ( crc_check_ok              ),
    .remote_time_out            ( remote_time_out           ),

    .tx                         ( UART_TX                   ),
    .rx                         ( UART_RX                   )

    );



//----------------------------------------------------------------------------------
// Hot redundancy arbitration
//----------------------------------------------------------------------------------

    HOTRA                       U_HOTRA 
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_125m_0                ),
    .rst_emif                   ( rst_125m                  ),

    .wr_sel                     ( self_sta_wr_sel           ),
    .wr_en                      ( self_sta_wr_en            ),
    .wr_data                    ( self_sta_wr_data          ),

    .slot_num                   ( SLOT_NUM                  ),
    .sta_num                    ( STA_NUM                   ),
    .box_num                    ( BOX_NUM                   ),
    .redundancy_mode            ( redundancy_mode           ),
    .hr_online                  ( MCU_ONLINE                ),

    .self_cfg_err               ( hotr_self_cfg_err         ),
    .slink_err                  ( slink_err                 ),
    .enable_slot                ( enable_slot               ),

    .hr_ht_in                   ( MCU_HT_LINE1              ),
    .self_ht_out                ( MCU_HT_LINE0              ),
    .hr_ms_in                   ( MCU_MST_SLV1              ),
    .self_ms_out                ( MCU_MST_SLV0              ),

    .soft_rst                   ( soft_rst                  ),
    .selfm_ms_flag              ( selfm_ms_flag             ),
    .excfg_ms_flag              ( excfg_ms_flag             ),
    .slot2_ms_flag              ( type1_ms_flag[0]          ),
    .slot3_ms_flag              ( type1_ms_flag[1]          ),
    .slot4_ms_flag              ( type1_ms_flag[2]          ),
    .slot5_ms_flag              ( type1_ms_flag[3]          ),
    .slot6_ms_flag              ( type2_ms_flag[0]          ),
    .slot7_ms_flag              ( type2_ms_flag[1]          ),
    .slot8_ms_flag              ( type2_ms_flag[2]          ),
    .slot9_ms_flag              ( type2_ms_flag[3]          ),
    .slot10_ms_flag             ( type2_ms_flag[4]          ),
    .slot11_ms_flag             ( type2_ms_flag[5]          ),
    .slot12_ms_flag             ( type2_ms_flag[6]          ),
    .slot13_ms_flag             ( type2_ms_flag[7]          ),
    .slot14_ms_flag             ( type2_ms_flag[8]          ),
    .slot15_ms_flag             ( type2_ms_flag[9]          ),

    .self_status                ( self_status               ),
    .mcu_status                 ( mcu_status                ),
    .uart_err                   ( uart_err                  ),
    .arm_ok                     ( arm_ok                    ),
    .hotra_en                   ( hotra_delay               ),
    .send_sta_val               ( send_sta_val              ),
    .arm_mode                   ( arm_mode                  ),
    .current_state_o            ( current_state_o           ),
    .arm_cycle                  ( run_cycle                 ),
    .mcu_arm_mode               ( mcu_arm_mode              ),
    .uart_rd_val                ( rx_frame_data_val         ),
    .mcu_is_valid               ( mcu_is_valid              ),
    .hw_init_ok                 ( hw_init_ok                ),
    .arm_tx_finish              ( ),
    .repeat_val                 ( arm_tx_finish             )

    );

//----------------------------------------------------------------------------------
// slef management
//----------------------------------------------------------------------------------

    SELFM                       U_SELFM
    (
    .clk_150m                   ( clk_125m_0                ),
    .rst_150m                   ( rst_125m                  ),

    .selfm_rd_sel               ( selfm_rd_sel              ),
    .selfm_rd_addr              ( selfm_rd_addr             ),
    .selfm_rd_data              ( selfm_rd_data             ),

	.slot_num                   ( SLOT_NUM                  ),   
	.sta_num                    ( STA_NUM                   ),   
	.box_num                    ( BOX_NUM                   ), 
    .master_slave_flag          ( selfm_ms_flag             ),
    .mpu_cfg_wr_ok              ( mpu_cfg_wr_ok             ),

    .chn0_empty                 ( type1_rd_dmm_empty[0]     ),
    .chn1_empty                 ( type1_rd_dmm_empty[1]     ),
    .chn2_empty                 ( type1_rd_dmm_empty[2]     ),
    .chn3_empty                 ( type1_rd_dmm_empty[3]     ),
    .chn4_empty                 ( type2_rd_dmm_empty[0]     ),
    .chn5_empty                 ( type2_rd_dmm_empty[1]     ),
    .chn6_empty                 ( type2_rd_dmm_empty[2]     ),
    .chn7_empty                 ( type2_rd_dmm_empty[3]     ),
    .chn8_empty                 ( type2_rd_dmm_empty[4]     ),
    .chn9_empty                 ( type2_rd_dmm_empty[5]     ),
    .chn10_empty                ( type2_rd_dmm_empty[6]     ),
    .chn11_empty                ( type2_rd_dmm_empty[7]     ),
    .chn12_empty                ( type2_rd_dmm_empty[8]     ),
    .chn13_empty                ( type2_rd_dmm_empty[9]     ),
    //
    .mcu_is_valid               ( mcu_is_valid              ),
    .redundancy_mode			( redundancy_mode			)
    );

    MPU_CASE_STA                U_MPU_CASE_STA
    (
    .clk_150m                   ( clk_125m_0                ),
    .rst_150m                   ( rst_125m                  ),

    .mpu_sta_rd_sel             ( mpu_sta_rd_sel            ),
    .mpu_rd_addr                ( mpu_rd_addr               ),
    .mpu_rd_data                ( mpu_rd_data               ),

    .uart_sel                   ( status_rd_sel             ),
    .uart_addr                  ( status_rd_addr            ),
    .uart_data                  ( status_rd_data            ),

	.other_online               ( ONLINE                    ), 
    .card_id                    ( card_id                   ),
    .code_version               ( code_version              ),
    .enable_slot                ( enable_slot               ),
	.slot_num                   ( SLOT_NUM                  ),   
	.sta_num                    ( STA_NUM                   ),   
	.box_num                    ( BOX_NUM                   ), 
    .hmcu_oline                 ( MCU_ONLINE                ),
    .pmcu_oline                 ( SFF_SD                    ),
    .emif_self_cfg_err          ( emif_self_cfg_err         ),
    .hotr_self_cfg_err          ( hotr_self_cfg_err         ),
    .type1_self_cfg_err         ( type1_self_cfg_err        ),
    .type2_self_cfg_err         ( type2_self_cfg_err        ),
    .emif_err                   ( emif_err                  ),
    .mpu_cfg_wr_ok              ( mpu_cfg_wr_ok             ),

    .slot2_sta_dval             ( mpu_sta_dval[0]           ),
    .slot2_sta_data             ( mpu_sta_data[0]           ),
    .slot3_sta_dval             ( mpu_sta_dval[1]           ),
    .slot3_sta_data             ( mpu_sta_data[1]           ),
    .slot4_sta_dval             ( mpu_sta_dval[2]           ),
    .slot4_sta_data             ( mpu_sta_data[2]           ),
    .slot5_sta_dval             ( mpu_sta_dval[3]           ),
    .slot5_sta_data             ( mpu_sta_data[3]           ),
    .slot6_sta_dval             ( type2_sta_dval[0]         ),
    .slot6_sta_data             ( type2_sta_data[0]         ),
    .slot7_sta_dval             ( type2_sta_dval[1]         ),
    .slot7_sta_data             ( type2_sta_data[1]         ),
    .slot8_sta_dval             ( type2_sta_dval[2]         ),
    .slot8_sta_data             ( type2_sta_data[2]         ),
    .slot9_sta_dval             ( type2_sta_dval[3]         ),
    .slot9_sta_data             ( type2_sta_data[3]         ),
    .slot10_sta_dval            ( type2_sta_dval[4]         ),
    .slot10_sta_data            ( type2_sta_data[4]         ),
    .slot11_sta_dval            ( type2_sta_dval[5]         ),
    .slot11_sta_data            ( type2_sta_data[5]         ),
    .slot12_sta_dval            ( type2_sta_dval[6]         ),
    .slot12_sta_data            ( type2_sta_data[6]         ),
    .slot13_sta_dval            ( type2_sta_dval[7]         ),
    .slot13_sta_data            ( type2_sta_data[7]         ),
    .slot14_sta_dval            ( type2_sta_dval[8]         ),
    .slot14_sta_data            ( type2_sta_data[8]         ),
    .slot15_sta_dval            ( type2_sta_dval[9]         ),
    .slot15_sta_data            ( type2_sta_data[9]         ),

    .dst_sta_num                ( dst_sta_num               ),
    .prm_slink_err              ( prm_slink_err             ),
    .hrm_slink_err              ( hrm_slink_err             ),
    .type1_slink_err            ( type1_slink_err           ),
    .type2_slink_err            ( type2_slink_err           ),
    .slink_err                  ( slink_err                 )
    );

    EX_CASE_STA                 U_1_EX_CASE_STA
    (
    .clk_150m                   ( clk_125m_0                ),
    .rst_150m                   ( rst_125m                  ),

    .ex_slot_sel                ( ex1_slot_sel              ),
    .ex_sta_rd_sel              ( ex1_sta_rd_sel            ),
    .ex_rd_addr                 ( ex1_rd_addr               ),
    .ex_rd_data                 ( ex1_rd_data               ),

    .hot_plug_req               ( ex1_hot_plug_req          ),
    .slot2_sta_dval             ( ex1_sta_dval[0]           ),
    .slot2_sta_data             ( ex1_sta_data[0]           ),
    .slot3_sta_dval             ( ex1_sta_dval[1]           ),
    .slot3_sta_data             ( ex1_sta_data[1]           ),
    .slot4_sta_dval             ( ex1_sta_dval[2]           ),
    .slot4_sta_data             ( ex1_sta_data[2]           ),
    .slot5_sta_dval             ( ex1_sta_dval[3]           ),
    .slot5_sta_data             ( ex1_sta_data[3]           ),

    .ex_box_online0             ( ex1_box_online[0]         ),
    .ex_box_online1             ( ex1_box_online[1]         ),
    .ex_box_online2             ( ex1_box_online[2]         ),
    .ex_box_online3             ( ex1_box_online[3]         )

    );

    EX_CASE_STA                 U_2_EX_CASE_STA
    (
    .clk_150m                   ( clk_125m_0                ),
    .rst_150m                   ( rst_125m                  ),

    .ex_slot_sel                ( ex2_slot_sel              ),
    .ex_sta_rd_sel              ( ex2_sta_rd_sel            ),
    .ex_rd_addr                 ( ex2_rd_addr               ),
    .ex_rd_data                 ( ex2_rd_data               ),

    .hot_plug_req               ( ex2_hot_plug_req          ),
    .slot2_sta_dval             ( ex2_sta_dval[0]           ),
    .slot2_sta_data             ( ex2_sta_data[0]           ),
    .slot3_sta_dval             ( ex2_sta_dval[1]           ),
    .slot3_sta_data             ( ex2_sta_data[1]           ),
    .slot4_sta_dval             ( ex2_sta_dval[2]           ),
    .slot4_sta_data             ( ex2_sta_data[2]           ),
    .slot5_sta_dval             ( ex2_sta_dval[3]           ),
    .slot5_sta_data             ( ex2_sta_data[3]           ),

    .ex_box_online0             ( ex2_box_online[0]            ),
    .ex_box_online1             ( ex2_box_online[1]            ),
    .ex_box_online2             ( ex2_box_online[2]            ),
    .ex_box_online3             ( ex2_box_online[3]            )
    );

    EX_CASE_STA                 U_3_EX_CASE_STA
    (
    .clk_150m                   ( clk_125m_0                ),
    .rst_150m                   ( rst_125m                  ),

    .ex_slot_sel                ( ex3_slot_sel              ),
    .ex_sta_rd_sel              ( ex3_sta_rd_sel            ),
    .ex_rd_addr                 ( ex3_rd_addr               ),
    .ex_rd_data                 ( ex3_rd_data               ),

    .hot_plug_req               ( ex3_hot_plug_req          ),
    .slot2_sta_dval             ( ex3_sta_dval[0]           ),
    .slot2_sta_data             ( ex3_sta_data[0]           ),
    .slot3_sta_dval             ( ex3_sta_dval[1]           ),
    .slot3_sta_data             ( ex3_sta_data[1]           ),
    .slot4_sta_dval             ( ex3_sta_dval[2]           ),
    .slot4_sta_data             ( ex3_sta_data[2]           ),
    .slot5_sta_dval             ( ex3_sta_dval[3]           ),
    .slot5_sta_data             ( ex3_sta_data[3]           ),

    .ex_box_online0             ( ex3_box_online[0]            ),
    .ex_box_online1             ( ex3_box_online[1]            ),
    .ex_box_online2             ( ex3_box_online[2]            ),
    .ex_box_online3             ( ex3_box_online[3]            )

    );

    EX_CASE_STA                 U_4_EX_CASE_STA
    (
    .clk_150m                   ( clk_125m_0                ),
    .rst_150m                   ( rst_125m                  ),

    .ex_slot_sel                ( ex4_slot_sel              ),
    .ex_sta_rd_sel              ( ex4_sta_rd_sel            ),
    .ex_rd_addr                 ( ex4_rd_addr               ),
    .ex_rd_data                 ( ex4_rd_data               ),

    .hot_plug_req               ( ex4_hot_plug_req          ),
    .slot2_sta_dval             ( ex4_sta_dval[0]           ),
    .slot2_sta_data             ( ex4_sta_data[0]           ),
    .slot3_sta_dval             ( ex4_sta_dval[1]           ),
    .slot3_sta_data             ( ex4_sta_data[1]           ),
    .slot4_sta_dval             ( ex4_sta_dval[2]           ),
    .slot4_sta_data             ( ex4_sta_data[2]           ),
    .slot5_sta_dval             ( ex4_sta_dval[3]           ),
    .slot5_sta_data             ( ex4_sta_data[3]           ),

    .ex_box_online0             ( ex4_box_online[0]            ),
    .ex_box_online1             ( ex4_box_online[1]            ),
    .ex_box_online2             ( ex4_box_online[2]            ),
    .ex_box_online3             ( ex4_box_online[3]            )
    );

    RX_RR                       U_RX_RR
    (
    .clk_150m                   ( clk_125m_0                ),
    .rst_150m                   ( rst_125m                  ),

    .slink_err                  ( slink_err[3:0]            ),
    .ex_box_data_ena0           ( ex_box_data_ena[0]        ),
    .ex_box_data_ena1           ( ex_box_data_ena[1]        ),
    .ex_box_data_ena2           ( ex_box_data_ena[2]        ),
    .ex_box_data_ena3           ( ex_box_data_ena[3]        ),
    .ex_box_cfg_ena0            ( ex_box_cfg_ena[0]         ),
    .ex_box_cfg_ena1            ( ex_box_cfg_ena[1]         ),
    .ex_box_cfg_ena2            ( ex_box_cfg_ena[2]         ),
    .ex_box_cfg_ena3            ( ex_box_cfg_ena[3]         ),
    .ex1_slot_sel               ( ex1_slot_sel              ),
    .ex2_slot_sel               ( ex2_slot_sel              ),
    .ex3_slot_sel               ( ex3_slot_sel              ),
    .ex4_slot_sel               ( ex4_slot_sel              ),
    .rr_sel0                    ( rr_sel[0]                 ),
    .rr_sel1                    ( rr_sel[1]                 ),
    .rr_sel2                    ( rr_sel[2]                 ),
    .rr_sel3                    ( rr_sel[3]                 )
    );

//----------------------------------------------------------------------------------
// MPU board self configuration momery management instance
//----------------------------------------------------------------------------------

    SELF_CMM                    U_SELF_CMM
    (
    .clk_emif                   ( clk_125m_0                ),
    .rst_emif                   ( rst_125m                  ),

    .wr_sel                     ( self_cfg_wr_sel           ),
    .wr_en                      ( self_cfg_wr_en            ),
    .wr_data                    ( self_cfg_wr_data          ),

    .cfg_wr_ok                  ( mpu_cfg_wr_ok             ),
    .chn_type0                  ( type1_chn_type[0]         ),
    .chn_type1                  ( type1_chn_type[1]         ),
    .chn_type2                  ( type1_chn_type[2]         ),
    .chn_type3                  ( type1_chn_type[3]         ),
    .chn_type4                  ( type2_chn_type[0]         ),
    .chn_type5                  ( type2_chn_type[1]         ),
    .chn_type6                  ( type2_chn_type[2]         ),
    .chn_type7                  ( type2_chn_type[3]         ),
    .chn_type8                  ( type2_chn_type[4]         ),
    .chn_type9                  ( type2_chn_type[5]         ),
    .chn_type10                 ( type2_chn_type[6]         ),
    .chn_type11                 ( type2_chn_type[7]         ),
    .chn_type12                 ( type2_chn_type[8]         ),
    .chn_type13                 ( type2_chn_type[9]         ),
    .ex_box_data_ena0           ( ex_box_data_ena[0]        ),
    .ex_box_data_ena1           ( ex_box_data_ena[1]        ),
    .ex_box_data_ena2           ( ex_box_data_ena[2]        ),
    .ex_box_data_ena3           ( ex_box_data_ena[3]        ),
    .ex_box_cfg_ena0            ( ex_box_cfg_ena[0]         ),
    .ex_box_cfg_ena1            ( ex_box_cfg_ena[1]         ),
    .ex_box_cfg_ena2            ( ex_box_cfg_ena[2]         ),
    .ex_box_cfg_ena3            ( ex_box_cfg_ena[3]         ),
    .card_id                    ( card_id                   ),
    .code_version               ( code_version              ),
    .enable_slot                ( enable_slot               ),
    .run_cycle                  ( run_cycle                 ),
    .redundancy_mode            ( redundancy_mode           )
    );

//----------------------------------------------------------------------------------
// extention box configuration momery management instance
//----------------------------------------------------------------------------------

    EX_CMM                      U_EX_CMM
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_125m_0                ),
    .rst_emif                   ( rst_125m                  ),

    .dst_sta_num                ( dst_sta_num               ),
    .ex1_cfg_wr_sel             ( ex1_cfg_wr_sel            ),
    .ex2_cfg_wr_sel             ( ex2_cfg_wr_sel            ),
    .ex3_cfg_wr_sel             ( ex3_cfg_wr_sel            ),
    .ex4_cfg_wr_sel             ( ex4_cfg_wr_sel            ),
    .ex1_cfg_slot               ( ex1_cfg_slot              ),
    .ex2_cfg_slot               ( ex2_cfg_slot              ),
    .ex3_cfg_slot               ( ex3_cfg_slot              ),
    .ex4_cfg_slot               ( ex4_cfg_slot              ),
    .ex1_cfg_wr_en              ( ex1_cfg_wr_en             ),
    .ex2_cfg_wr_en              ( ex2_cfg_wr_en             ),
    .ex3_cfg_wr_en              ( ex3_cfg_wr_en             ),
    .ex4_cfg_wr_en              ( ex4_cfg_wr_en             ),
    .ex1_cfg_wr_data            ( ex1_cfg_wr_data           ),
    .ex2_cfg_wr_data            ( ex2_cfg_wr_data           ),
    .ex3_cfg_wr_data            ( ex3_cfg_wr_data           ),
    .ex4_cfg_wr_data            ( ex4_cfg_wr_data           ),

    .master_slave_flag          ( excfg_ms_flag             ),
    .ssdu_excmm_rdreq0          ( ssdu_excmm_rdreq[0]       ),
    .ssdu_excmm_rdreq1          ( ssdu_excmm_rdreq[1]       ),
    .ssdu_excmm_rdreq2          ( ssdu_excmm_rdreq[2]       ),
    .ssdu_excmm_rdreq3          ( ssdu_excmm_rdreq[3]       ),
    .ex1_hot_plug_req           ( ex1_hot_plug_req          ),
    .ex2_hot_plug_req           ( ex2_hot_plug_req          ),
    .ex3_hot_plug_req           ( ex3_hot_plug_req          ),
    .ex4_hot_plug_req           ( ex4_hot_plug_req          ),
    .excmm_ssdu_empty           ( excmm_ssdu_empty          ),
    .excmm_ssdu_dval            ( excmm_ssdu_dval           ),
    .excmm_ssdu_data0           ( excmm_ssdu_data0          ),
    .excmm_ssdu_data1           ( excmm_ssdu_data1          ),
    .excmm_ssdu_data2           ( excmm_ssdu_data2          ),
    .excmm_ssdu_data3           ( excmm_ssdu_data3          )
    );

//----------------------------------------------------------------------------------
// MPU box slot3-slot6 data path
//----------------------------------------------------------------------------------
assign  type1_lvds_rxp_in   =   LVDS_RXP[3:0] ;
assign  type1_lvds_rxn_in   =   LVDS_RXN[3:0] ;
assign  LVDS_TXP[3:0]       =   type1_lvds_txp_out ;  
assign  LVDS_TXN[3:0]       =   type1_lvds_txn_out ;  

  genvar i ;
  generate
  for( i = 0 ; i < 4 ; i = i+1 ) 
  begin : nTYPE1_DP

    TYPE1_DP                    #                    
    (
    .MPU_SLOT                   ( i                         )
    )
    U_TYPE1_DP
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .rst_125m                   ( rst_125m                  ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),

    .run_cycle                  ( run_cycle                 ),
    .dst_sta_num                ( dst_sta_num               ),
    .rd_dmm_empty               ( type1_rd_dmm_empty[i]     ),
    .chn_type                   ( type1_chn_type[i]         ),
    .master_slave_flag          ( type1_ms_flag[i]          ),
    .ex_box_data_ena            ( ex_box_data_ena[i]        ),
    .ex_box_cfg_ena             ( ex_box_cfg_ena[i]         ),
    .rr_sel                     ( rr_sel[i]                 ),
    .self_cfg_err               ( type1_self_cfg_err[i]     ),

    .wr_sel                     ( type1_wr_sel[i]           ),
    .wr_port                    ( type1_wr_port[i]          ),
    .wr_en                      ( type1_wr_en[i]            ),
    .wr_data                    ( type1_wr_data[i]          ),
    .rd_sel                     ( type1_rd_sel[i]           ),
    .rd_port                    ( type1_rd_port[i]          ),
    .rd_addr                    ( type1_rd_addr[i]          ),
    .rd_dval                    ( type1_rd_dval[i]          ),
    .rd_data                    ( type1_rd_data[i]          ),

    .excmm_ssdu_empty           ( excmm_ssdu_empty          ),
    .excmm_ssdu_dval            ( excmm_ssdu_dval           ),
    .excmm_ssdu_data0           ( excmm_ssdu_data0          ),
    .excmm_ssdu_data1           ( excmm_ssdu_data1          ),
    .excmm_ssdu_data2           ( excmm_ssdu_data2          ),
    .excmm_ssdu_data3           ( excmm_ssdu_data3          ),
    .ssdu_excmm_rdreq           ( ssdu_excmm_rdreq[i]       ),
    
    .lvds_rxp_in                ( type1_lvds_rxp_in[i]      ),
    .lvds_rxn_in                ( type1_lvds_rxn_in[i]      ),
    .lvds_txp_out               ( type1_lvds_txp_out[i]     ),
    .lvds_txn_out               ( type1_lvds_txn_out[i]     ),

    .mpu_sta_dval               ( mpu_sta_dval[i]           ),
    .mpu_sta_data               ( mpu_sta_data[i]           ),
    .ex1_sta_dval               ( ex1_sta_dval[i]           ),
    .ex1_sta_data               ( ex1_sta_data[i]           ),
    .ex2_sta_dval               ( ex2_sta_dval[i]           ),
    .ex2_sta_data               ( ex2_sta_data[i]           ),
    .ex3_sta_dval               ( ex3_sta_dval[i]           ),
    .ex3_sta_data               ( ex3_sta_data[i]           ),
    .ex4_sta_dval               ( ex4_sta_dval[i]           ),
    .ex4_sta_data               ( ex4_sta_data[i]           ),

    .slink_err                  ( type1_slink_err[i]        )

    );

  end
  endgenerate

//----------------------------------------------------------------------------------
// MPU box slot7-slot16 data path
//----------------------------------------------------------------------------------
assign  type2_lvds_rxp_in   =   LVDS_RXP[13:4] ;
assign  type2_lvds_rxn_in   =   LVDS_RXN[13:4] ;
assign  LVDS_TXP[13:4]      =   type2_lvds_txp_out ;  
assign  LVDS_TXN[13:4]      =   type2_lvds_txn_out ;  

  genvar j ;
  generate
  for( j = 0 ; j < 10 ; j = j+1 ) 
  begin : nTYPE2_DP

    TYPE2_DP                    U_TYPE2_DP
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .rst_125m                   ( rst_125m                  ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),

    .run_cycle                  ( run_cycle                 ),
    .dst_sta_num                ( dst_sta_num               ),
    .rd_dmm_empty               ( type2_rd_dmm_empty[j]     ),
    .chn_type                   ( type2_chn_type[j]         ),
    .master_slave_flag          ( type2_ms_flag[j]          ),
    .self_cfg_err               ( type2_self_cfg_err[j]     ),

    .wr_sel                     ( type2_wr_sel[j]           ),
    .wr_port                    ( type2_wr_port[j]          ),
    .wr_en                      ( type2_wr_en[j]            ),
    .wr_data                    ( type2_wr_data[j]          ),
    .rd_sel                     ( type2_rd_sel[j]           ),
    .rd_port                    ( type2_rd_port[j]          ),
    .rd_addr                    ( type2_rd_addr[j]          ),
    .rd_data                    ( type2_rd_data[j]          ),

    .lvds_rxp_in                ( type2_lvds_rxp_in[j]      ),
    .lvds_rxn_in                ( type2_lvds_rxn_in[j]      ),
    .lvds_txp_out               ( type2_lvds_txp_out[j]     ),
    .lvds_txn_out               ( type2_lvds_txn_out[j]     ),

    .sta_dval                   ( type2_sta_dval[j]         ),
    .sta_data                   ( type2_sta_data[j]         ),

    .slink_err                  ( type2_slink_err[j]        )
    );

  end
  endgenerate

//----------------------------------------------------------------------------------
// Parallel-Redunancy MCU Data Path
//----------------------------------------------------------------------------------
    HRM_DP                      U_PRM_DP
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .rst_125m                   ( rst_125m                  ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),

    .wd_timer                   ( run_cycle                 ),
    .wr_sel                     ( prm_wr_sel                ),
    .wr_en                      ( prm_wr_en                 ),
    .wr_pkt_num                 ( prm_pkt_num               ),
    .wr_data                    ( prm_wr_data               ),
    .rd_sel                     ( prm_rd_sel                ),
    .rd_pkt_num                 ( prm_rd_pkt_num            ),
    .rd_addr                    ( prm_rd_addr               ),
    .rd_data                    ( prm_rd_data               ),

    .rx_en                      ( SFF_SD                    ),
    .lvds_rxp_in                ( SFF_RXP                   ),
    .lvds_rxn_in                ( SFF_RXN                   ),
    .lvds_txp_out               ( SFF_TXP                   ),
    .lvds_txn_out               ( SFF_TXN                   ),

    .slink_err                  ( prm_slink_err             )
    );

//----------------------------------------------------------------------------------
// Hot-Redunancy MCU Data Path
//----------------------------------------------------------------------------------
    HRM_DP                      U_HRM_DP
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .rst_125m                   ( rst_125m                  ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),

    .wd_timer                   ( run_cycle                 ),
    .wr_sel                     ( hrm_wr_sel                ),
    .wr_en                      ( hrm_wr_en                 ),
    .wr_pkt_num                 ( hrm_pkt_num               ),
    .wr_data                    ( hrm_wr_data               ),
    .rd_sel                     ( hrm_rd_sel                ),
    .rd_pkt_num                 ( hrm_rd_pkt_num            ),
    .rd_addr                    ( hrm_rd_addr               ),
    .rd_data                    ( hrm_rd_data               ),

    .rx_en                      ( 1'b1                      ),
    .lvds_rxp_in                ( MCU_LVDS_RXP              ),
    .lvds_rxn_in                ( MCU_LVDS_RXN              ),
    .lvds_txp_out               ( MCU_LVDS_TXP              ),
    .lvds_txn_out               ( MCU_LVDS_TXN              ),

    .slink_err                  ( hrm_slink_err             )
    );


endmodule

