// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   BPFEX01
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

module  BPFEX01
    (
    // clock & reset
    FPGA_125M_P                    ,    // communication clock , the output of external 125M difference crystal oscillator   
    FPGA_125M_N                    ,       
    FPGA_NRST                      ,    // system reset , TPS3808G01DBVT's output , include poweron & button reset

    // backplane lvds 
	LVDS_RXP                       ,    // connect to other board of box
    LVDS_RXN                       ,    // connect to other board of box
    LVDS_TXP                       ,   
    LVDS_TXN                       ,   

	MCU_LVDS_RXP                   ,    // connect to redundant MCU  
	MCU_LVDS_RXN                   ,    // connect to redundant MCU  
	MCU_LVDS_TXP                   ,
    MCU_LVDS_TXN                   , 
    MCU_FPFA_IO                    ,    // connect to redundant MCU 

    // SFF interface 
	SFF_TDIS                       ,    // connect to optical module of the tdis signal  
	//SFF_SD                         ,    // connect to optical module of the sd signal // FMQ modified. @2018/8/2
    //20:01:03
	SFF_RXP                        ,    // connect to optical module of the recieve difference signal 
	SFF_RXN                        ,   
	SFF_TXP                        ,    // connect to optical module of the transmiss difference signal 
    SFF_TXN                        ,   
        
    RUN_LED                        ,    // Indicating module of work voltage status  
    ERR_LED                        ,    // Indicating module of expand failure status
    COM_LED                        ,    // Indicating module I of communication work status
    MAS_LED                        ,    // Indicating module MASTER of communication work status 
    SLA_LED                        ,    // Indicating module SLAVE of communication work status 
    SFF1_TLED                      ,    // firest optical module of the tramsmit LED   
    SFF1_RLED                      ,    // firest optical module of the receive LED
    SFF2_TLED                      ,    // second optical module of the tramsmit LED
    SFF2_RLED                      ,    // second optical module of the receive LED
    CH1_RLED                       ,    // firest channel of the tramsmit LED
    CH2_RLED                       ,    // second channel of the receive LED
    CH3_RLED                       ,    // third channel of the tramsmit LED
    CH4_RLED                       ,    // fourth channel of the receive LED
    CH5_RLED                       ,    // fifth channel of the tramsmit LED
    CH6_RLED                       ,    // sixth channel of the receive LED
    CH7_RLED                       ,    // seventh channel of the tramsmit LED
    CH8_RLED                       ,    // eighth channel of the receive LED
    CH9_RLED                       ,    // ninth channel of the tramsmit LED
    CH10_RLED                      ,    // tenth channel of the receive LED
    CH11_RLED                      ,    // eleventh channel of the tramsmit LED
    CH12_RLED                      ,    // twelfth channel of the receive LED
    CH13_RLED                      ,    // thirteenth channel of the tramsmit LED
    CH14_RLED                      ,    // fourtheenth channel of the receive LED

	// backplane misc signals
	SLOT_NUM                       ,    // slot number  
	STA_NUM                        ,    // station number  
	BOX_NUM                        ,    // box number 
	MCU_HT_LINE0                   ,    // heartbeat line to redundant MCU  
	MCU_HT_LINE1                   ,    // heartbeat line from redundant MCU 
	MCU_MST_SLV0                   ,    // master or slave indication to redundant MCU  
	MCU_MST_SLV1                   ,    // master or slave indication from redundant MCU 
    ADM_DIS                        ,
    ONLINE                              // FMQ modified. @2018/8/1 16:34:48  
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

input   wire    [13:0]          LVDS_RXP                            ;   
input   wire    [13:0]          LVDS_RXN                            ;   
input   wire    [1:0]           MCU_LVDS_RXP                        ;   
input   wire    [1:0]           MCU_LVDS_RXN                        ;   
 
//input   wire    [1:0]           SFF_SD                              ;/* synthesis syn_preserve = 1 */   // FMQ
//modified. @2018/8/2 20:01:16
input   wire    [1:0]           SFF_RXP                             ;   
input   wire    [1:0]           SFF_RXN                             ;   

input   wire    [3:0]           SLOT_NUM                            ;   
input   wire    [7:0]           STA_NUM                             ;   
input   wire    [2:0]           BOX_NUM                             ;   
input   wire                    MCU_HT_LINE1                        ;   
input   wire                    MCU_MST_SLV1                        ;   
input   wire                    MCU_FPFA_IO                         ; 
input   wire    [14:0]          ONLINE                              ;// FMQ modified. @2018/8/1 16:34:58
// declare output signal
output  wire    [13:0]          LVDS_TXP                            ;   
output  wire    [13:0]          LVDS_TXN                            ;   
output  wire    [1:0]           MCU_LVDS_TXP                        ;   
output  wire    [1:0]           MCU_LVDS_TXN                        ;   
output  wire    [1:0]           SFF_TXP                             ;   
output  wire    [1:0]           SFF_TXN                             ;   
output  wire    [1:0]           SFF_TDIS                            ;   
output  wire                    MCU_HT_LINE0                        ;   
output  wire                    MCU_MST_SLV0                        ;  
output  wire                    ADM_DIS                             ;   

output  wire                    RUN_LED                             ;   
output  wire                    ERR_LED                             ;   
output  wire    [1:0]           COM_LED                             ;   
output  wire    [1:0]           MAS_LED                             ;   
output  wire    [1:0]           SLA_LED                             ;   

output  wire    [1:0]           SFF1_TLED                           ;   
output  wire    [1:0]           SFF1_RLED                           ;   
output  wire    [1:0]           SFF2_TLED                           ;   
output  wire    [1:0]           SFF2_RLED                           ;   
output  wire    [1:0]           CH1_RLED                            ;   
output  wire    [1:0]           CH2_RLED                            ;   
output  wire    [1:0]           CH3_RLED                            ;   
output  wire    [1:0]           CH4_RLED                            ;   
output  wire    [1:0]           CH5_RLED                            ;   
output  wire    [1:0]           CH6_RLED                            ;   
output  wire    [1:0]           CH7_RLED                            ;   
output  wire    [1:0]           CH8_RLED                            ;   
output  wire    [1:0]           CH9_RLED                            ;   
output  wire    [1:0]           CH10_RLED                           ;   
output  wire    [1:0]           CH11_RLED                           ;   
output  wire    [1:0]           CH12_RLED                           ;   
output  wire    [1:0]           CH13_RLED                           ;   
output  wire    [1:0]           CH14_RLED                           ;  

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            clk_12_5m                           ;   
wire                            rst_12_5m                           ;   
wire                            clk_125m_0                          ;   
wire                            clk_125m_90                         ;   
wire                            clk_125m_180                        ;   
wire                            clk_125m_270                        ;   
wire                            rst_125m                            ;
wire                            lvds_en                             ;   

wire                            rxsdu_sfm_rdreq                     ;   
wire                            sfm_rxsdu_empty                     ;   
wire                            sfm_rxsdu_dval                      ;   
wire        [17:0]              sfm_rxsdu_data                      ;   

wire        [1:0]               lvds_slink_err      [13:0]          ;   
wire        [13:0]              lvds_tx_eop                         ;   
wire        [13:0]              lvds_rx_eop                         ;   
wire        [1:0]               ex_slink_err        [1:0]           ;   
wire        [1:0]               ex_tx_eop                           ;   
wire        [1:0]               ex_rx_eop                           ;   
wire        [1:0]               fiber_slink_err     [1:0]           ;   
wire        [1:0]               fiber_tx_eop                        ;   
wire        [1:0]               fiber_rx_eop                        ;   

wire                            wr_self_cfg_dval                    ;   
wire        [17:0]              wr_self_cfg_data                    ;
wire                            cfg_en                              ;   
wire        [31:0]              card_id                             ;   
wire        [15:0]              code_version                        ;   
wire        [31:0]              enable_slot                         ;   
wire        [15:0]              run_cycle                           ;   

wire        [1:0]               txsdu_slink_rdreq                   ;   
wire        [17:0]              rxsdu_slink_data    [1:0]           ;   
wire        [1:0]               rxsdu_slink_dval                    ;   
wire        [1:0]               slink_rxsdu_rdreq                   ;   
wire        [1:0]               slink_txsdu_empty                   ;   
wire        [1:0]               slink_txsdu_dval                    ;   
wire        [17:0]              slink_txsdu_data    [1:0]           ;  

wire        [13:0]              rxsdu_slink_rdreq                   ;   
wire        [17:0]              txsdu_slink_data    [13:0]          ;
wire        [13:0]              txsdu_slink_dval                    ;
wire        [13:0]              slink_txsdu_rdreq                   ;   
wire        [13:0]              slink_rxsdu_empty                   ;   
wire        [13:0]              slink_rxsdu_dval                    ;   
wire        [17:0]              slink_rxsdu_data    [13:0]          ;

wire        [1:0]               rxsdu_ex_rdreq                      ;   
wire        [17:0]              txsdu_ex_data       [1:0]           ;   
wire        [1:0]               txsdu_ex_dval                       ;   
wire        [1:0]               ex_txsdu_rdreq                      ;   
wire        [1:0]               ex_rxsdu_empty                      ;   
wire        [1:0]               ex_rxsdu_dval                       ;   
wire        [17:0]              ex_rxsdu_data       [1:0]           ;   

wire                            self_cfg_err                        ;   
wire        [17:0]              led_slink_err                       ;

wire        [31:0]              src_id1                             ;
wire        [31:0]              src_id2                             ;
wire        [31:0]              dst_id1                             ;
wire        [31:0]              dst_id2                             ;

wire        [7:0]               src_port1                           ;
wire        [7:0]               src_prot2                           ;
wire        [7:0]               dst_port1                           ;
wire        [7:0]               dst_port2                           ;

// reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
assign  SFF_TDIS[0]    =  ~ lvds_en ;
assign  SFF_TDIS[1]    =  ~ lvds_en ;

assign  ADM_DIS = 1'b0 ;

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// clock and reset management
//----------------------------------------------------------------------------------

    EX_CRM                      U_CRM
    (
    .clk_125m_p                 ( FPGA_125M_P               ),
    .clk_125m_n                 ( FPGA_125M_N               ),
    .hard_rst                   ( FPGA_NRST                 ),
    .soft_rst                   ( 1'b1                      ),

    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),
    .rst_125m                   ( rst_125m                  ),
    .lvds_en                    ( lvds_en                   )
    );

//----------------------------------------------------------------------------------
// self status management 
//----------------------------------------------------------------------------------

    EX_SELFM                    U_SELFM
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),

    .cfg_en                     ( cfg_en                    ),
    .slot_num                   ( SLOT_NUM                  ),
    .sta_num                    ( STA_NUM                   ),
    .box_num                    ( BOX_NUM                   ),

    .card_id                    ( card_id                   ),
    .code_version               ( code_version              ),
    .enable_slot                ( enable_slot[16:0]         ),

    .ex0_slink_err              ( ex_slink_err[0]           ),
    .ex1_slink_err              ( ex_slink_err[1]           ),
    .fiber0_slink_err           ( fiber_slink_err[0]        ),
    .fiber1_slink_err           ( fiber_slink_err[1]        ),
    .slot2_slink_err            ( lvds_slink_err[0]         ),
    .slot3_slink_err            ( lvds_slink_err[1]         ),
    .slot4_slink_err            ( lvds_slink_err[2]         ),
    .slot5_slink_err            ( lvds_slink_err[3]         ),
    .slot6_slink_err            ( lvds_slink_err[4]         ),
    .slot7_slink_err            ( lvds_slink_err[5]         ),
    .slot8_slink_err            ( lvds_slink_err[6]         ),
    .slot9_slink_err            ( lvds_slink_err[7]         ),
    .slot10_slink_err           ( lvds_slink_err[8]         ),
    .slot11_slink_err           ( lvds_slink_err[9]         ),
    .slot12_slink_err           ( lvds_slink_err[10]        ),
    .slot13_slink_err           ( lvds_slink_err[11]        ),
    .slot14_slink_err           ( lvds_slink_err[12]        ),
    .slot15_slink_err           ( lvds_slink_err[13]        ),

    .ex_txsdu_rdreq             ( ex_txsdu_rdreq[1]         ),
    .txsdu_ex_dval              ( txsdu_ex_dval[1]          ),
    .txsdu_ex_data              ( txsdu_ex_data[1]          ),

    .rxsdu_sfm_rdreq            ( rxsdu_sfm_rdreq           ),
    .sfm_rxsdu_empty            ( sfm_rxsdu_empty           ),
    .sfm_rxsdu_dval             ( sfm_rxsdu_dval            ),
    .sfm_rxsdu_data             ( sfm_rxsdu_data            ),

    .self_cfg_err               ( self_cfg_err              ),
    .led_slink_err              ( led_slink_err             ),
    .online                     ( ONLINE                    )
    );

    EX_LEDM                     U_LED
    (
    .clk_sys                    ( clk_125m_0                ),
    .rst_sys_n                  ( rst_125m                  ),
    
    .enable_slot                ( enable_slot[16:0]         ),
    .cfg_en                     ( cfg_en                    ),
    .self_cfg_err               ( self_cfg_err              ),

    .fiber_tx_eop               ( fiber_tx_eop              ),
    .fiber_rx_eop               ( fiber_rx_eop              ),
    .fiber_slink_err            ( led_slink_err[15:14]      ),
    .lvds_rx_eop                ( lvds_rx_eop               ),
    .lvds_slink_err             ( led_slink_err[13:0]       ),
    .ex_rx_eop                  ( ex_rx_eop                 ),
    .ex_slink_err               ( led_slink_err[17:16]      ),

    .run_led                    ( RUN_LED                   ),
    .err_led                    ( ERR_LED                   ),
    .com_led                    ( COM_LED                   ),
    .mas_led                    ( MAS_LED                   ),
    .sla_led                    ( SLA_LED                   ),
    .ch1_rled                   ( CH1_RLED                  ),
    .ch2_rled                   ( CH2_RLED                  ),
    .ch3_rled                   ( CH3_RLED                  ),
    .ch4_rled                   ( CH4_RLED                  ),
    .ch5_rled                   ( CH5_RLED                  ),
    .ch6_rled                   ( CH6_RLED                  ),
    .ch7_rled                   ( CH7_RLED                  ),
    .ch8_rled                   ( CH8_RLED                  ),
    .ch9_rled                   ( CH9_RLED                  ),
    .ch10_rled                  ( CH10_RLED                 ),
    .ch11_rled                  ( CH11_RLED                 ),
    .ch12_rled                  ( CH12_RLED                 ),
    .ch13_rled                  ( CH13_RLED                 ),
    .ch14_rled                  ( CH14_RLED                 ),
    .sff1_tled                  ( SFF1_TLED                 ),
    .sff1_rled                  ( SFF1_RLED                 ),
    .sff2_tled                  ( SFF2_RLED                 ),
    .sff2_rled                  ( SFF2_TLED                 )
    );

//----------------------------------------------------------------------------------
// self configuration memory management 
//----------------------------------------------------------------------------------

    EX_SELF_CMM                 U_SELF_CMM
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),

    .ex_rxsdu_empty             ( ex_rxsdu_empty[0]         ),
    .rxsdu_ex_rdreq             ( rxsdu_ex_rdreq[0]         ),
    .ex_rxsdu_dval              ( ex_rxsdu_dval[0]          ),
    .ex_rxsdu_data              ( ex_rxsdu_data[0]          ),

    .wr_self_cfg_dval           ( wr_self_cfg_dval          ),
    .wr_self_cfg_data           ( wr_self_cfg_data          ),

    .slot_num                   ( SLOT_NUM                  ),
    .cfg_en                     ( cfg_en                    ),
    .card_id                    ( card_id                   ),
    .code_version               ( code_version              ),
    .enable_slot                ( enable_slot               ),
    .run_cycle                  ( run_cycle                 ),

    .src_id1                    ( src_id1                   ),
    .src_id2                    ( src_id2                   ),
    .dst_id1                    ( dst_id1                   ),
    .dst_id2                    ( dst_id2                   ),

    .src_port1                  ( src_port1                 ),
    .src_port2                  ( src_port2                 ),
    .dst_port1                  ( dst_port1                 ),
    .dst_port2                  ( dst_port2                 )
    );

//----------------------------------------------------------------------------------
// fiber interface ( conncted to COMI , comunicated with MCU )
//----------------------------------------------------------------------------------
  genvar i ;
  generate
  for( i = 0 ; i < 2 ; i = i+1 ) 
  begin : nMCU_SLINK

    EX_SLINK                       #                      
    (
    .CARD_TYPE                  ( 2'b10                     ),
    .FIFO_TYPE                  ( 2'b01                     )
    )
    U_FIBER_SLINK
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),
    .rst_125m                   ( rst_125m                  ),
                                  
    .wd_timer                   ( run_cycle                 ),
    .self_cfg_err               ( self_cfg_err              ),
    //.rx_en                      ( SFF_SD[i]               ),        // FMQ modified. @2018/8/2 18:43:06
    .rx_en                      ( enable_slot[i+14]         ),
    .lvds_rxp_in                ( SFF_RXP[i]                ),
    .lvds_rxn_in                ( SFF_RXN[i]                ),
    .mm_slink_rdreq             ( txsdu_slink_rdreq[i]      ),
    .mm_slink_data              ( rxsdu_slink_data[i]       ),
    .mm_slink_dval              ( rxsdu_slink_dval[i]       ),
                                   
    .lvds_txp_out               ( SFF_TXP[i]                ),
    .lvds_txn_out               ( SFF_TXN[i]                ),
    .slink_mm_rdreq             ( slink_rxsdu_rdreq[i]      ),
    .slink_mm_empty             ( slink_txsdu_empty[i]      ),
    .slink_mm_dval              ( slink_txsdu_dval[i]       ),
    .slink_mm_data              ( slink_txsdu_data[i]       ),
                                   
    .slink_tx_eop               ( fiber_tx_eop[i]           ),
    .slink_rx_eop               ( fiber_rx_eop[i]           ),
    .slink_err                  ( fiber_slink_err[i]        )
    );

  end
  endgenerate

//----------------------------------------------------------------------------------
// backplane LVDS interface ( conncted to IO )
//----------------------------------------------------------------------------------
  genvar j ;
  generate
  for( j = 0 ; j < 14 ; j = j+1 ) 
  begin : nIO_SLINK

    EX_SLINK                       #                      
    (
    .CARD_TYPE                  ( 2'b10                     ),
    .FIFO_TYPE                  ( 2'b00                     )
    )
    U_LVDS_SLINK
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),
    .rst_125m                   ( rst_125m                  ),
                                  
    .wd_timer                   ( 16'd10                    ),
    .self_cfg_err               ( self_cfg_err              ),
    .rx_en                      ( enable_slot[j]            ),
    .lvds_rxp_in                ( LVDS_RXP[j]               ),
    .lvds_rxn_in                ( LVDS_RXN[j]               ),
    .mm_slink_rdreq             ( rxsdu_slink_rdreq[j]      ),
    .mm_slink_data              ( txsdu_slink_data[j]       ),
    .mm_slink_dval              ( txsdu_slink_dval[j]       ),
                                   
    .lvds_txp_out               ( LVDS_TXP[j]               ),
    .lvds_txn_out               ( LVDS_TXN[j]               ),
    .slink_mm_rdreq             ( slink_txsdu_rdreq[j]      ),
    .slink_mm_empty             ( slink_rxsdu_empty[j]      ),
    .slink_mm_dval              ( slink_rxsdu_dval[j]       ),
    .slink_mm_data              ( slink_rxsdu_data[j]       ),
                                   
    .slink_tx_eop               ( lvds_tx_eop[j]            ),
    .slink_rx_eop               ( lvds_rx_eop[j]            ),
    .slink_err                  ( lvds_slink_err[j]         )
    );

  end
  endgenerate

//----------------------------------------------------------------------------------
// anothor ex board LVDS ( 0: cfg pkt 1: status frame )
//----------------------------------------------------------------------------------
  genvar k ;
  generate
  for( k = 0 ; k < 2 ; k = k + 1 ) 
  begin : nEX_SLINK

    EX_SLINK                       #                      
    (
    .CARD_TYPE                  ( 2'b10                     ),
    .FIFO_TYPE                  ( 2'b00                     )
    )
    U_EX_SLINK
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_125m_0                 ( clk_125m_0                ),
    .clk_125m_90                ( clk_125m_90               ),
    .clk_125m_180               ( clk_125m_180              ),
    .clk_125m_270               ( clk_125m_270              ),
    .rst_125m                   ( rst_125m                  ),
                                  
    .wd_timer                   ( 16'd0                     ),
    .self_cfg_err               ( 1'b0                      ),
   //.rx_en                      ( enable_slot[16]           ),
    .rx_en                      ( 1'b0                      ),
    .lvds_rxp_in                ( MCU_LVDS_RXP[k]           ),
    .lvds_rxn_in                ( MCU_LVDS_RXN[k]           ),
    .mm_slink_rdreq             ( rxsdu_ex_rdreq[k]         ),
    .mm_slink_data              ( txsdu_ex_data[k]          ),
    .mm_slink_dval              ( txsdu_ex_dval[k]          ),
                                   
    .lvds_txp_out               ( MCU_LVDS_TXP[k]           ),
    .lvds_txn_out               ( MCU_LVDS_TXN[k]           ),
    .slink_mm_rdreq             ( ex_txsdu_rdreq[k]         ),
    .slink_mm_empty             ( ex_rxsdu_empty[k]         ),
    .slink_mm_dval              ( ex_rxsdu_dval[k]          ),
    .slink_mm_data              ( ex_rxsdu_data[k]          ),
                                   
    .slink_tx_eop               ( ex_tx_eop[k]              ),
    .slink_rx_eop               ( ex_rx_eop[k]              ),
    .slink_err                  ( ex_slink_err[k]           )
    );

  end
  endgenerate

//----------------------------------------------------------------------------------
// MCU -- IO schedule
//----------------------------------------------------------------------------------

    EX_TXSDU                    U_TXSDU
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
  
    .box_num                    ( BOX_NUM                   ),
    .slot_num                   ( SLOT_NUM                  ),

    .txsdu_slink_rdreq1         ( txsdu_slink_rdreq[0]      ),
    .slink_txsdu_empty1         ( slink_txsdu_empty[0]      ),
    .slink_txsdu_dval1          ( slink_txsdu_dval[0]       ),
    .slink_txsdu_data1          ( slink_txsdu_data[0]       ),
    .txsdu_slink_rdreq2         ( txsdu_slink_rdreq[1]      ),
    .slink_txsdu_empty2         ( slink_txsdu_empty[1]      ),
    .slink_txsdu_dval2          ( slink_txsdu_dval[1]       ),
    .slink_txsdu_data2          ( slink_txsdu_data[1]       ),

    .wr_self_cfg_dval           ( wr_self_cfg_dval          ),
    .wr_self_cfg_data           ( wr_self_cfg_data          ),

    .ex_txsdu_rdreq             ( ex_txsdu_rdreq[0]         ),
    .slink_txsdu_rdreq0         ( slink_txsdu_rdreq[0]      ),
    .slink_txsdu_rdreq1         ( slink_txsdu_rdreq[1]      ),
    .slink_txsdu_rdreq2         ( slink_txsdu_rdreq[2]      ),
    .slink_txsdu_rdreq3         ( slink_txsdu_rdreq[3]      ),
    .slink_txsdu_rdreq4         ( slink_txsdu_rdreq[4]      ),
    .slink_txsdu_rdreq5         ( slink_txsdu_rdreq[5]      ),
    .slink_txsdu_rdreq6         ( slink_txsdu_rdreq[6]      ),
    .slink_txsdu_rdreq7         ( slink_txsdu_rdreq[7]      ),
    .slink_txsdu_rdreq8         ( slink_txsdu_rdreq[8]      ),
    .slink_txsdu_rdreq9         ( slink_txsdu_rdreq[9]      ),
    .slink_txsdu_rdreq10        ( slink_txsdu_rdreq[10]     ),
    .slink_txsdu_rdreq11        ( slink_txsdu_rdreq[11]     ),
    .slink_txsdu_rdreq12        ( slink_txsdu_rdreq[12]     ),
    .slink_txsdu_rdreq13        ( slink_txsdu_rdreq[13]     ),
    
    .txsdu_ex_dval              ( txsdu_ex_dval[0]          ),
    .txsdu_slink_dval0          ( txsdu_slink_dval[0]       ),
    .txsdu_slink_dval1          ( txsdu_slink_dval[1]       ),
    .txsdu_slink_dval2          ( txsdu_slink_dval[2]       ),
    .txsdu_slink_dval3          ( txsdu_slink_dval[3]       ),
    .txsdu_slink_dval4          ( txsdu_slink_dval[4]       ),
    .txsdu_slink_dval5          ( txsdu_slink_dval[5]       ),
    .txsdu_slink_dval6          ( txsdu_slink_dval[6]       ),
    .txsdu_slink_dval7          ( txsdu_slink_dval[7]       ),
    .txsdu_slink_dval8          ( txsdu_slink_dval[8]       ),
    .txsdu_slink_dval9          ( txsdu_slink_dval[9]       ),
    .txsdu_slink_dval10         ( txsdu_slink_dval[10]      ),
    .txsdu_slink_dval11         ( txsdu_slink_dval[11]      ),
    .txsdu_slink_dval12         ( txsdu_slink_dval[12]      ),
    .txsdu_slink_dval13         ( txsdu_slink_dval[13]      ),

    .txsdu_ex_data              ( txsdu_ex_data[0]          ),
    .txsdu_slink_data0          ( txsdu_slink_data[0]       ),
    .txsdu_slink_data1          ( txsdu_slink_data[1]       ),
    .txsdu_slink_data2          ( txsdu_slink_data[2]       ),
    .txsdu_slink_data3          ( txsdu_slink_data[3]       ),
    .txsdu_slink_data4          ( txsdu_slink_data[4]       ),
    .txsdu_slink_data5          ( txsdu_slink_data[5]       ),
    .txsdu_slink_data6          ( txsdu_slink_data[6]       ),
    .txsdu_slink_data7          ( txsdu_slink_data[7]       ),
    .txsdu_slink_data8          ( txsdu_slink_data[8]       ),
    .txsdu_slink_data9          ( txsdu_slink_data[9]       ),
    .txsdu_slink_data10         ( txsdu_slink_data[10]      ),
    .txsdu_slink_data11         ( txsdu_slink_data[11]      ),
    .txsdu_slink_data12         ( txsdu_slink_data[12]      ),
    .txsdu_slink_data13         ( txsdu_slink_data[13]      ),

    .src_id1                    ( src_id1                   ),
    .src_id2                    ( src_id2                   ),
    .dst_id1                    ( dst_id1                   ),
    .dst_id2                    ( dst_id2                   ), 
    .src_port1                  ( src_port1                 ),
    .src_port2                  ( src_port2                 ),
    .dst_port1                  ( dst_port2                 ),
    .dst_port2                  ( dst_port2                 )
    );

//----------------------------------------------------------------------------------
// IO -- MCU schedule
//----------------------------------------------------------------------------------

    EX_RXSDU                    U_RXSDU
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
  
    .box_num                    ( BOX_NUM                   ),
    .card_id                    ( card_id                   ),
    .rxsdu_sfm_rdreq            ( rxsdu_sfm_rdreq           ),
    .sfm_rxsdu_empty            ( sfm_rxsdu_empty           ),
    .sfm_rxsdu_dval             ( sfm_rxsdu_dval            ),
    .sfm_rxsdu_data             ( sfm_rxsdu_data            ),

    .rxsdu_ex_rdreq             ( rxsdu_ex_rdreq[1]         ),
    .rxsdu_slink_rdreq0         ( rxsdu_slink_rdreq[0]      ),
    .rxsdu_slink_rdreq1         ( rxsdu_slink_rdreq[1]      ),
    .rxsdu_slink_rdreq2         ( rxsdu_slink_rdreq[2]      ),
    .rxsdu_slink_rdreq3         ( rxsdu_slink_rdreq[3]      ),
    .rxsdu_slink_rdreq4         ( rxsdu_slink_rdreq[4]      ),
    .rxsdu_slink_rdreq5         ( rxsdu_slink_rdreq[5]      ),
    .rxsdu_slink_rdreq6         ( rxsdu_slink_rdreq[6]      ),
    .rxsdu_slink_rdreq7         ( rxsdu_slink_rdreq[7]      ),
    .rxsdu_slink_rdreq8         ( rxsdu_slink_rdreq[8]      ),
    .rxsdu_slink_rdreq9         ( rxsdu_slink_rdreq[9]      ),
    .rxsdu_slink_rdreq10        ( rxsdu_slink_rdreq[10]     ),
    .rxsdu_slink_rdreq11        ( rxsdu_slink_rdreq[11]     ),
    .rxsdu_slink_rdreq12        ( rxsdu_slink_rdreq[12]     ),
    .rxsdu_slink_rdreq13        ( rxsdu_slink_rdreq[13]     ),
    
    .ex_rxsdu_empty             ( ex_rxsdu_empty[1]         ),
    .slink_rxsdu_empty0         ( slink_rxsdu_empty[0]      ),
    .slink_rxsdu_empty1         ( slink_rxsdu_empty[1]      ),
    .slink_rxsdu_empty2         ( slink_rxsdu_empty[2]      ),
    .slink_rxsdu_empty3         ( slink_rxsdu_empty[3]      ),
    .slink_rxsdu_empty4         ( slink_rxsdu_empty[4]      ),
    .slink_rxsdu_empty5         ( slink_rxsdu_empty[5]      ),
    .slink_rxsdu_empty6         ( slink_rxsdu_empty[6]      ),
    .slink_rxsdu_empty7         ( slink_rxsdu_empty[7]      ),
    .slink_rxsdu_empty8         ( slink_rxsdu_empty[8]      ),
    .slink_rxsdu_empty9         ( slink_rxsdu_empty[9]      ),
    .slink_rxsdu_empty10        ( slink_rxsdu_empty[10]     ),
    .slink_rxsdu_empty11        ( slink_rxsdu_empty[11]     ),
    .slink_rxsdu_empty12        ( slink_rxsdu_empty[12]     ),
    .slink_rxsdu_empty13        ( slink_rxsdu_empty[13]     ),

    .ex_rxsdu_dval              ( ex_rxsdu_dval[1]          ),
    .slink_rxsdu_dval0          ( slink_rxsdu_dval[0]       ),
    .slink_rxsdu_dval1          ( slink_rxsdu_dval[1]       ),
    .slink_rxsdu_dval2          ( slink_rxsdu_dval[2]       ),
    .slink_rxsdu_dval3          ( slink_rxsdu_dval[3]       ),
    .slink_rxsdu_dval4          ( slink_rxsdu_dval[4]       ),
    .slink_rxsdu_dval5          ( slink_rxsdu_dval[5]       ),
    .slink_rxsdu_dval6          ( slink_rxsdu_dval[6]       ),
    .slink_rxsdu_dval7          ( slink_rxsdu_dval[7]       ),
    .slink_rxsdu_dval8          ( slink_rxsdu_dval[8]       ),
    .slink_rxsdu_dval9          ( slink_rxsdu_dval[9]       ),
    .slink_rxsdu_dval10         ( slink_rxsdu_dval[10]      ),
    .slink_rxsdu_dval11         ( slink_rxsdu_dval[11]      ),
    .slink_rxsdu_dval12         ( slink_rxsdu_dval[12]      ),
    .slink_rxsdu_dval13         ( slink_rxsdu_dval[13]      ),

    .ex_rxsdu_data              ( ex_rxsdu_data[1]          ),
    .slink_rxsdu_data0          ( slink_rxsdu_data[0]       ),
    .slink_rxsdu_data1          ( slink_rxsdu_data[1]       ),
    .slink_rxsdu_data2          ( slink_rxsdu_data[2]       ),
    .slink_rxsdu_data3          ( slink_rxsdu_data[3]       ),
    .slink_rxsdu_data4          ( slink_rxsdu_data[4]       ),
    .slink_rxsdu_data5          ( slink_rxsdu_data[5]       ),
    .slink_rxsdu_data6          ( slink_rxsdu_data[6]       ),
    .slink_rxsdu_data7          ( slink_rxsdu_data[7]       ),
    .slink_rxsdu_data8          ( slink_rxsdu_data[8]       ),
    .slink_rxsdu_data9          ( slink_rxsdu_data[9]       ),
    .slink_rxsdu_data10         ( slink_rxsdu_data[10]      ),
    .slink_rxsdu_data11         ( slink_rxsdu_data[11]      ),
    .slink_rxsdu_data12         ( slink_rxsdu_data[12]      ),
    .slink_rxsdu_data13         ( slink_rxsdu_data[13]      ),

    .slink_rxsdu_rdreq0         ( slink_rxsdu_rdreq[0]      ),
    .slink_rxsdu_rdreq1         ( slink_rxsdu_rdreq[1]      ),
    .rxsdu_slink_dval0          ( rxsdu_slink_dval[0]       ),
    .rxsdu_slink_data0          ( rxsdu_slink_data[0]       ),
    .rxsdu_slink_dval1          ( rxsdu_slink_dval[1]       ),
    .rxsdu_slink_data1          ( rxsdu_slink_data[1]       ),

    .src_id1                    ( src_id1                   ),
    .src_id2                    ( src_id2                   ),
    .dst_id1                    ( dst_id1                   ),
    .dst_id2                    ( dst_id2                   ), 
    .src_port1                  ( src_port1                 ),
    .src_port2                  ( src_port2                 ),
    .dst_port1                  ( dst_port2                 ),
    .dst_port2                  ( dst_port2                 )
    
    );

endmodule

