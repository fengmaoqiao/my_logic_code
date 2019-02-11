// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SCIPBPFCM
// CREATE DATE      :   2017-10-16
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-10-16  TingtingGan     Original
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

module  SCIPBPFCM
    (
    // clock & reset
    FPGA_125M_P                 ,   // communication clock , the output of external 125M difference crystal oscillator   
    FPGA_125M_N                 ,   
    FPGA_NRST                   ,   // system reset , TPS3808G01DBVT's output , include poweron & button reset

    // backplane lvds 
    LVDS_RXP                    ,   // connect to other board of box
    LVDS_RXN                    ,   // connect to other board of box
    LVDS_TXP                    ,   
    LVDS_TXN                    ,   

    // SFF interface 
    SFF_TDIS                    ,   // connect to optical module of the tdis signal  
    SFF_SD                      ,   // connect to optical module of the sd signal 
    SFF_RXP                     ,   // connect to optical module of the recieve difference signal 
    SFF_RXN                     ,   
    SFF_TXP                     ,   // connect to optical module of the transmiss difference signal 
    SFF_TXN                     ,   
    
    // communication LED : [0] green [1] red  , active high
    SFF1_TLED                   ,   // firest optical module of the tramsmit LED   
    SFF1_RLED                   ,   // firest optical module of the receive LED
    SFF2_TLED                   ,   // second optical module of the tramsmit LED
    SFF2_RLED                   ,   // second optical module of the receive LED
    SFF3_TLED                   ,   // third channel of the tramsmit LED
    SFF3_RLED                   ,   // third channel of the receive LED
    SFF4_TLED                   ,   // fourth channel of the tramsmit LED
    SFF4_RLED                   ,   // fourth channel of the receive LED

    MC1_LED                     ,   
    MC2_LED                     ,   
    RUN_LED                     ,   
    ERR_LED                     ,   
    COM_LED                     ,   

	// backplane misc signals
	SLOT_NUM                    ,       // slot number  

    WD_UART_RX                  ,
    WD_UART_TX                  ,
    CHANNEL_FEEDDOG             ,
    //DEBUG       
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

input   wire    [1:0]           LVDS_RXP                            ;   
input   wire    [1:0]           LVDS_RXN                            ;   
 
input   wire    [3:0]           SFF_SD                              ;   
input   wire    [3:0]           SFF_RXP                             ;   
input   wire    [3:0]           SFF_RXN                             ;   

input   wire    [3:0]           SLOT_NUM                            ;   

// declare output signal
output  wire    [1:0]           LVDS_TXP                            ;   
output  wire    [1:0]           LVDS_TXN                            ;   
output  wire    [3:0]           SFF_TXP                             ;   
output  wire    [3:0]           SFF_TXN                             ;   
output  wire    [3:0]           SFF_TDIS                            ;   

output  wire    [1:0]           SFF1_TLED                           ;   
output  wire    [1:0]           SFF1_RLED                           ;   
output  wire    [1:0]           SFF2_TLED                           ;   
output  wire    [1:0]           SFF2_RLED                           ; 
output  wire    [1:0]           SFF3_TLED                           ;   
output  wire    [1:0]           SFF3_RLED                           ;  
output  wire    [1:0]           SFF4_TLED                           ;   
output  wire    [1:0]           SFF4_RLED                           ; 

output  wire    [1:0]           MC1_LED                             ;   
output  wire    [1:0]           MC2_LED                             ;   
output  wire                    RUN_LED                             ;   
output  wire                    ERR_LED                             ;   
output  wire    [1:0]           COM_LED                             ;   

input   wire                    WD_UART_RX                          ;
output  wire                    WD_UART_TX                          ;
output  wire    [5:0]           CHANNEL_FEEDDOG                     ;

//output  wire                    DEBUG                               ;

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

wire                            rxsdu_sfm_rdreq                     ;   
wire                            sfm_rxsdu_empty                     ;   
wire                            sfm_rxsdu_dval                      ;   
wire        [17:0]              sfm_rxsdu_data                      ;   

wire                            wr_self_cfg_dval                    ;   
wire        [17:0]              wr_self_cfg_data                    ;  
wire                            cfg_en                              ;   
wire        [31:0]              card_id                             ;   
wire        [15:0]              code_version                        ;   
wire        [15:0]              enable_slot                         ;   
wire        [15:0]              run_cycle                           ;   
wire        [4:0]               card_type                           ; 
wire                            self_cfg_err                        ;   

wire        [1:0]               lvds_slink_err                      ;   
wire        [3:0]               fiber_slink_err                     ;   
wire        [3:0]               fiber_tx_eop                        ;   
wire        [3:0]               fiber_rx_eop                        ;   
wire        [1:0]               lvds_tx_eop                         ;   
wire        [1:0]               lvds_rx_eop                         ;   

wire        [1:0]               txsdu_slink_rdreq                   ;   
wire        [17:0]              rxsdu_slink_data    [1:0]           ;   
wire        [1:0]               rxsdu_slink_dval                    ;   
wire        [1:0]               slink_rxsdu_rdreq                   ;   
wire        [1:0]               slink_txsdu_empty                   ;   
wire        [1:0]               slink_txsdu_dval                    ;   


wire        [3:0]               rxsdu_slink_rdreq                   ;   
wire        [3:0]               txsdu_slink_dval                    ;
wire        [3:0]               slink_txsdu_rdreq                   ;   
wire        [3:0]               slink_rxsdu_empty                   ;   
wire        [3:0]               slink_rxsdu_dval                    ;  

wire        [2:0]               port1_dst_box                       ;   
wire        [2:0]               port2_dst_box                       ;   
wire        [2:0]               port3_dst_box                       ;   
wire        [2:0]               port4_dst_box                       ;   

// wire array signal
wire        [17:0]              slink_txsdu_data        [1:0]       ;  
wire        [17:0]              txsdu_slink_data        [3:0]       ;
wire        [17:0]              slink_rxsdu_data        [3:0]       ;
wire                            board_type_ok                       ;   

wire        [5:0]               channel_enable                      ;   
wire                            cfg_finish_flag                     ;   

wire        [5:0]               slink_rx_eop                        ;
// reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
assign  SFF_TDIS[0]    =  ~ rst_125m ;
assign  SFF_TDIS[1]    =  ~ rst_125m ;
assign  SFF_TDIS[2]    =  ~ rst_125m ;
assign  SFF_TDIS[3]    =  ~ rst_125m ;


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
    .rst_125m                   ( rst_125m                  )
    );

//----------------------------------------------------------------------------------
// self status management 
//----------------------------------------------------------------------------------

    COM_SELFM                   U_COM_SELFM
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),

    .slot_num                   ( SLOT_NUM                  ),

    .cfg_en                     ( cfg_en                    ),
    .board_type_ok              ( board_type_ok             ),
    .card_id                    ( card_id                   ),
    .code_version               ( code_version              ),
    .enable_slot                ( enable_slot               ),
    .card_type                  ( card_type                 ),
    .self_cfg_err               ( self_cfg_err              ),
    .sff_sd                     ( SFF_SD                    ),

    .lvds_slink_err             ( lvds_slink_err            ),
    .fiber_slink_err            ( fiber_slink_err           ),

    .rxsdu_sfm_rdreq            ( rxsdu_sfm_rdreq           ),
    .sfm_rxsdu_empty            ( sfm_rxsdu_empty           ),
    .sfm_rxsdu_dval             ( sfm_rxsdu_dval            ),
    .sfm_rxsdu_data             ( sfm_rxsdu_data            ),

    .debug_bus                  (                           )
    );

//----------------------------------------------------------------------------------
// self configuration memory management 
//----------------------------------------------------------------------------------

    COM_SELF_CMM                U_COM_SELF_CMM
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),

    .wr_self_cfg_dval           ( wr_self_cfg_dval          ),
    .wr_self_cfg_data           ( wr_self_cfg_data          ),

    .cfg_en                     ( cfg_en                    ),
    .card_id                    ( card_id                   ),
    .code_version               ( code_version              ),
    .enable_slot                ( enable_slot               ),
    .run_cycle                  ( run_cycle                 ),
    .port1_dst_box              ( port1_dst_box             ),
    .port2_dst_box              ( port2_dst_box             ),
    .port3_dst_box              ( port3_dst_box             ),
    .port4_dst_box              ( port4_dst_box             )
    );

//----------------------------------------------------------------------------------
// backplane interface ( comunicate with MCU )
//----------------------------------------------------------------------------------
  genvar i ;
  generate
  for( i = 0 ; i < 2 ; i = i+1 ) 
  begin : nLVDS_SLINK

    SLINK                       #                      
    (
    .DELAY_ERR_ACT              ( 1'b1                      ),
    .CARD_TYPE                  ( 2'b01                     ),
    .FIFO_TYPE                  ( 2'b10                     )
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
    
    .card_type                  ( card_type                 ),
    .wd_timer                   ( run_cycle                 ),
    .self_cfg_err               ( self_cfg_err              ),
    .rx_en                      ( 1'b1                      ),
    .lvds_rxp_in                ( LVDS_RXP[i]               ),
    .lvds_rxn_in                ( LVDS_RXN[i]               ),
    .mm_slink_rdreq             ( txsdu_slink_rdreq[i]      ),
    .mm_slink_data              ( rxsdu_slink_data[i]       ),
    .mm_slink_dval              ( rxsdu_slink_dval[i]       ),
                                   
    .lvds_txp_out               ( LVDS_TXP[i]               ),
    .lvds_txn_out               ( LVDS_TXN[i]               ),
    .slink_mm_rdreq             ( slink_rxsdu_rdreq[i]      ),
    .slink_mm_empty             ( slink_txsdu_empty[i]      ),
    .slink_mm_dval              ( slink_txsdu_dval[i]       ),
    .slink_mm_data              ( slink_txsdu_data[i]       ),
                                   
    .slink_tx_eop               ( lvds_tx_eop[i]            ),
    .slink_rx_eop               ( lvds_rx_eop[i]            ),
    .slink_err                  ( lvds_slink_err[i]         )
    );

  end
  endgenerate

//----------------------------------------------------------------------------------
// FIBER interface ( conncted to IO )
//----------------------------------------------------------------------------------
  genvar j ;
  generate
  for( j = 0 ; j < 4 ; j = j+1 ) 
  begin : nFIBER_SLINK

    SLINK                       #                      
    (
    .DELAY_ERR_ACT              ( 1'b1                      ),
    .CARD_TYPE                  ( 2'b01                     ),
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
                                  
    .card_type                  ( card_type                 ),
    .wd_timer                   ( run_cycle                 ),
    .self_cfg_err               ( self_cfg_err              ),
    .rx_en                      ( SFF_SD[j]                 ),
    .lvds_rxp_in                ( SFF_RXP[j]                ),
    .lvds_rxn_in                ( SFF_RXN[j]                ),
    .mm_slink_rdreq             ( rxsdu_slink_rdreq[j]      ),
    .mm_slink_data              ( txsdu_slink_data[j]       ),
    .mm_slink_dval              ( txsdu_slink_dval[j]       ),
                                   
    .lvds_txp_out               ( SFF_TXP[j]                ),
    .lvds_txn_out               ( SFF_TXN[j]                ),
    .slink_mm_rdreq             ( slink_txsdu_rdreq[j]      ),
    .slink_mm_empty             ( slink_rxsdu_empty[j]      ),
    .slink_mm_dval              ( slink_rxsdu_dval[j]       ),
    .slink_mm_data              ( slink_rxsdu_data[j]       ),
    
    .slink_tx_eop               ( fiber_tx_eop[j]           ),
    .slink_rx_eop               ( fiber_rx_eop[j]           ),
    .slink_err                  ( fiber_slink_err[j]        )
    );

  end
  endgenerate

//----------------------------------------------------------------------------------
// MCU -- COM schedule
//----------------------------------------------------------------------------------

    TXSDU                       U_TXSDU
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
  
`ifdef SIM
    .port1_dst_box              ( 4'd1                      ),
    .port2_dst_box              ( 4'd2                      ),
    .port3_dst_box              ( 4'd3                      ),
    .port4_dst_box              ( 4'd4                      ),
`else
    .port1_dst_box              ( port1_dst_box             ),
    .port2_dst_box              ( port2_dst_box             ),
    .port3_dst_box              ( port3_dst_box             ),
    .port4_dst_box              ( port4_dst_box             ),
`endif
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

    .slink_txsdu_rdreq0         ( slink_txsdu_rdreq[0]      ),
    .slink_txsdu_rdreq1         ( slink_txsdu_rdreq[1]      ),
    .slink_txsdu_rdreq2         ( slink_txsdu_rdreq[2]      ),
    .slink_txsdu_rdreq3         ( slink_txsdu_rdreq[3]      ),
    
    .txsdu_slink_dval0          ( txsdu_slink_dval[0]       ),
    .txsdu_slink_dval1          ( txsdu_slink_dval[1]       ),
    .txsdu_slink_dval2          ( txsdu_slink_dval[2]       ),
    .txsdu_slink_dval3          ( txsdu_slink_dval[3]       ),

    .txsdu_slink_data0          ( txsdu_slink_data[0]       ),
    .txsdu_slink_data1          ( txsdu_slink_data[1]       ),
    .txsdu_slink_data2          ( txsdu_slink_data[2]       ),
    .txsdu_slink_data3          ( txsdu_slink_data[3]       )
    );

//----------------------------------------------------------------------------------
// COM -- MCU schedule
//----------------------------------------------------------------------------------

    RXSDU                       U_RXSDU
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
  
    .rxsdu_sfm_rdreq            ( rxsdu_sfm_rdreq           ),
    .sfm_rxsdu_empty            ( sfm_rxsdu_empty           ),
    .sfm_rxsdu_dval             ( sfm_rxsdu_dval            ),
    .sfm_rxsdu_data             ( sfm_rxsdu_data            ),

    .rxsdu_slink_rdreq0         ( rxsdu_slink_rdreq[0]      ),
    .rxsdu_slink_rdreq1         ( rxsdu_slink_rdreq[1]      ),
    .rxsdu_slink_rdreq2         ( rxsdu_slink_rdreq[2]      ),
    .rxsdu_slink_rdreq3         ( rxsdu_slink_rdreq[3]      ),
    
    .slink_rxsdu_empty0         ( slink_rxsdu_empty[0]      ),
    .slink_rxsdu_empty1         ( slink_rxsdu_empty[1]      ),
    .slink_rxsdu_empty2         ( slink_rxsdu_empty[2]      ),
    .slink_rxsdu_empty3         ( slink_rxsdu_empty[3]      ),

    .slink_rxsdu_dval0          ( slink_rxsdu_dval[0]       ),
    .slink_rxsdu_dval1          ( slink_rxsdu_dval[1]       ),
    .slink_rxsdu_dval2          ( slink_rxsdu_dval[2]       ),
    .slink_rxsdu_dval3          ( slink_rxsdu_dval[3]       ),

    .slink_rxsdu_data0          ( slink_rxsdu_data[0]       ),
    .slink_rxsdu_data1          ( slink_rxsdu_data[1]       ),
    .slink_rxsdu_data2          ( slink_rxsdu_data[2]       ),
    .slink_rxsdu_data3          ( slink_rxsdu_data[3]       ),

    .slink_rxsdu_rdreq0         ( slink_rxsdu_rdreq[0]      ),
    .slink_rxsdu_rdreq1         ( slink_rxsdu_rdreq[1]      ),
    .rxsdu_slink_dval0          ( rxsdu_slink_dval[0]       ),
    .rxsdu_slink_data0          ( rxsdu_slink_data[0]       ),
    .rxsdu_slink_dval1          ( rxsdu_slink_dval[1]       ),
    .rxsdu_slink_data1          ( rxsdu_slink_data[1]       )
    );


//----------------------------------------------------------------------------------
// LED control
//----------------------------------------------------------------------------------
    LEDM                        U_LEDM 
    (
    .clk_sys                    ( clk_125m_0                ),
    .rst_sys_n                  ( rst_125m                  ),
    
    .card_type                  ( card_type                 ),
    .sff_enable                 ( SFF_SD                    ),
    .enable_slot                ( enable_slot               ),
    .cfg_en                     ( cfg_en                    ),
    .board_type_ok              ( board_type_ok             ),
    .self_cfg_err               ( self_cfg_err              ),

    .fiber_tx_eop               ( fiber_tx_eop              ),
    .fiber_rx_eop               ( fiber_rx_eop              ),
    .fiber_slink_err            ( fiber_slink_err           ),
    .lvds_rx_eop                ( lvds_rx_eop               ),
    .lvds_slink_err             ( lvds_slink_err            ),

    .run_led                    ( RUN_LED                   ),
    .err_led                    ( ERR_LED                   ),
    .mc1_led                    ( MC1_LED                   ),
    .mc2_led                    ( MC2_LED                   ),
    .com_led                    ( COM_LED                   ),
    .sff0_tled                  ( SFF1_TLED                 ),
    .sff1_tled                  ( SFF2_TLED                 ),
    .sff2_tled                  ( SFF3_TLED                 ),
    .sff3_tled                  ( SFF4_TLED                 ),
    .sff0_rled                  ( SFF1_RLED                 ),
    .sff1_rled                  ( SFF2_RLED                 ),
    .sff2_rled                  ( SFF3_RLED                 ),
    .sff3_rled                  ( SFF4_RLED                 )
    );


watchdog_top #(
    .U_DLY                      (0                          )
)
u_watchdog_top
(
    .clk_sys                    ( clk_125m_0                ),
    .rst_n                      ( rst_125m                  ),
    
    .run_cycle                  ( run_cycle                 ),
    .enable_slot                ( enable_slot               ),
    .cfg_finish_flag            ( cfg_finish_flag           ),
    
    .wd_uart_rx                 ( WD_UART_RX                ),
    .wd_uart_tx                 ( WD_UART_TX                ),
    //watchdog feed symbol
    .slink_rx_eop               ( slink_rx_eop              ),
    .channel_feeddog            ( CHANNEL_FEEDDOG           )
);

assign slink_rx_eop = {fiber_rx_eop,lvds_rx_eop};

endmodule
