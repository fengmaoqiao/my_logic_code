`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08/21/2017 11:20:06 AM
// Design Name: 
// Module Name: phy_top
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

(* DONT_TOUCH = "yes" *)
module phy_top(
//   -- ------------------------------------------------------------------------
//   -- incoming reset
//   -- ------------------------------------------------------------------------ 
    input	 wire external_resetn,
    input	 wire crstn,
//   -- -------------------------------------------------------------------------
//   -- incoming clock
//   -- ------------------------------------------------------------------------
    input	 wire source_clk,
    input	 wire mpifClk,
    input    wire plf_clk,
    
    input    wire AD9361_clk,
    
//  -- -------------------------------------------------------------------------
//  -- Clocks & Reset               
//  -- -------------------------------------------------------------------------
    output	 wire bus_clk_resetn_o,
    output	 wire bus_clk_reset_o,
    output	 wire cclk_resetn_o,
    output	 wire bus_clk_o,

    output	 wire cclk_o,
    output	 wire cclk_n_o,
    
    output	 wire dac_gclk,
    output	 wire adc_gclk,
    output	 wire enable_7mhz,
    output	 wire a7s_gclk,
    output	 wire mem_rst_n_o,

//    -- Clock controls
    output	 wire clkcntl_out_0,
    output	 wire clkcntl_updata_o,
    output	 wire osc32ken_o,
    //input	 wire reg_en_hisslp,

//	--clock selection
    //input	 wire reg_44_80_cntl,

  // --  Reset controls
    input	 wire swreset,
    input	 wire pmreset,
  // -- Signals for reset status
    output	 wire wdreset_stat,
    output	 wire swreset_stat,
    output	 wire pmreset_stat,
    output	 wire extreset_stat,
  // -- Watchdog Timer --
    input 	 wire wd_enable,
    input 	 wire [6:0] wd_div,
    input 	 wire wd_stroke,
//	-- -------------------------------------------------------
//	-- misc
//	-- -------------------------------------------------------
    output	 wire refclk_req,
    output	 wire clk32_select_out,

  
  /***********************************************************
  * AD9361 INTERFACE 
  ***********************************************************/
    output   wire [15:0] modem_tx_a_i_rf,    //out to rf
    output   wire [15:0] modem_tx_a_q_rf,    //out to rf
    input    wire [15:0] modem_rx_a_i_rf,    //in from rf
    input    wire [15:0] modem_rx_a_q_rf,    //in from rf

    output                  dac_dovf,
    output                  dac_dunf,
    output                  adc_dovf,
    output                  adc_dunf,  
    input                   rf_rst,
    input                   adc_enable_i0,
    input                   adc_valid_i0, 
    input                   adc_enable_q0,
    input                   adc_valid_q0,    
    input                   dac_enable_i0,
    input                   dac_valid_i0, 
    input                   dac_enable_q0,
    input                   dac_valid_q0,   
    output                  txfifo_empty,
    output                  rxfifo_full,  

    
  /***********************************************************
  * AHB_TO_APB BUS convert signal 
  ***********************************************************/
    input	    wire [15:0] s_apb_paddr,
    input	    wire        s_apb_penable,
    input	    wire [2:0]  s_apb_pprot,
    input	    wire [31:0] s_apb_pwdata, 
    
    input 	  wire   	    psel_modema, 
    input     wire        psel_modemg,
    input     wire        psel_radio,
    input     wire        psel_frontend,
    input     wire        psel_macphy_if,
    input     wire        psel_macphy_rf,

    input	    wire [3:0]  s_apb_pstrb,
    input	    wire        s_apb_pwrite,
    /* output */
    output	  wire [31:0] s_apb_prdata_if,
    output    wire [31:0] s_apb_prdata_rf,
    output	  wire [31:0] s_apb_prdata_modema,
    output	  wire [31:0] s_apb_prdata_modemg,
    output	  wire [31:0] s_apb_prdata_radio,
    output	  wire [31:0] s_apb_prdata_frontend,    
    output	  wire 		    s_apb_pready_if,
    output	  wire 		    s_apb_pready_modema,
    output	  wire [1:0]  s_apb_pslverr,	
    output                txv_immstop,
//--------------------- phy interface ------------------
    input    wire         testmode        ,
    input 	 wire 		    keepRFOn        ,
    output	 wire 		    phy_cca_ind_medium ,                    
    output	 wire 		    phyRdy          ,
    output   wire 		    CCAPrimary20    ,          //edit by fengmaoqiao input 2 output
//------------------ tx ----------------
    input 	 wire 		    txReq           ,
    input 	 wire [7:0]   txData          ,
    input 	 wire 		    macDataValid    ,
    input	   wire 		    mpIfTxFifoEmtpy ,
    output	 wire 		    txEnd_p         ,
//-----------------  rx  --------------
    input 	 wire 		    rxReq           ,
    input         [11:0]  tx_data_out,
    input         [11:0]  rx_data_in,

    output	 wire [7:0]   rxData          ,
    output	 wire 		    rxEndForTiming_p,
    output	 wire 		    rxEnd_p         ,
    output   wire [11:0]  rxv_length      ,
    
    output                agc_fall

    );
 
    
  /***********************************************************
  * Signal Declaration 
  ***********************************************************/
    wire                    modem_rx_a_tog;
    wire    [10:0]          modem_rx_a_i_phy     ;
    wire    [10:0]          modem_rx_a_q_phy     ;
    
    
    wire                    modem_tx_a_tog;
    wire    [9:0]           modem_tx_a_i_phy     ;
    wire    [9:0]           modem_tx_a_q_phy     ;
        
    wire                    phy_data_ind                      ;
    wire     [7:0]          bup_rxdata                        ;
    //----------------------------------------------------------
    wire                    phy_data_conf                     ;
    wire     [7:0]          fifo_dout                         ;
    //----------------------------------------------------------
    wire                    clk_60m               ;
    wire                    clk_80m               ; 
    wire                    clk_20m            ;
    reg                     rst_n                 ;
    
    wire                    phy_txstartend_conf   ;
    wire                    phy_data_req          ;
    wire           [7:0]    bup_txdata            ;
    wire                    phy_txstartend_req    ; 
    wire                    phy_ccarst_req        ;
    wire                    rxv_macaddr_match     ;       
    wire           [3:0]    txv_datarate          ;  
    wire           [11:0]   txv_length            ;
    wire           [6:0]    txpwr_level           ;
    wire           [15:0]   txv_service           ;
    wire                    cp2_detected    ;
    
    wire                    bus_gclk_o            ;   
    
    wire      [11:0]         rxv_length           ;
    wire      [15:0]         rxv_service          ;
    wire                     rxv_service_ind      ;
    wire      [3:0]          rxv_datarate         ;  
     
    wire      [3:0]          sourcedata_ch; 
    wire                     cap_data_en ;
    
    wire                     rxfifo_almost_empty;
    wire                     txfifo_almost_full;
    
    wire                     rx_start;
    wire                     en_20m_i;
    
    reg        [3:0]         reset_n_cnt = 4'd0;
   parameter                 RESET_TIME = 4'd15;

 always@(posedge clk_80m) begin
    if(reset_n_cnt < RESET_TIME)begin
        rst_n       <= 1'b0;
        reset_n_cnt <= reset_n_cnt + 1'b1;
    end
    else begin
        rst_n <= 1'b1;
        reset_n_cnt <= reset_n_cnt;
    end
 end
 
 
 clk_wiz_1 u_clk_wiz_1(
    .clk_in1          ( AD9361_clk            ),
    .resetn           ( external_resetn       ),
    
    .clk_out1         ( clk_60m               ), 
    .clk_out2         ( clk_80m               ), 
    .clk_out3         ( en_20m_i              )
 );   

   
    
    
  /***********************************************************
  * PHY INSTANCE
  ***********************************************************/
    rw_wlanbb_11g_maxim
     #(
      .num_queues_g           (4 ),
      .num_abstimer_g         (8 ),
      .radar_g                (1 ),
      .fpga_g                 (1 ), 
      .wdt_div_g              (11),
      .gate_arm_in_fpga       (0 ),
      .gate_ofdm_in_fpga      (1 ),
      .use_clkskip_in_fpga    (0 ),
      .rf_cnt_size_g          (8 )
    )
    rw_wlanbb_11g_maxim_inst
    (
    
    
    .external_resetn        (external_resetn),           //-- 1.8V external reset pin
    .crstn                  (external_resetn      ),           //-- reset from CardBus for PCI bridge
//    -- -------------------------------------------------------------------------
//    -- incoming clk from external
//    -- ------------------------------------------------------------------------
    .plf_clk                ( plf_clk              ),
    .clk_60m                ( clk_60m              ),
    .clk_80m                ( clk_80m              ),
    .en_20m_i               ( en_20m_i             ),
//    -- -------------------------------------------------------------------------
//    -- Clocks & Reset -- outgoing to platform      
//    -- ------------------------------------------------------------------------
    .rst_n                  ( rst_n               ),
  
    .psel_modema           (psel_modema   ),             //--in
    .psel_modemb           (   ),                     //--in
    .psel_modemg           (psel_modemg   ),                     //--in
    .psel_radio            (psel_radio   ),                     //--in
    .psel_streamproc       (   ),                     //--in
    .psel_frontend         (psel_frontend   ),                     //--in
    .paddr                 (s_apb_paddr[11:0]  ),             //--in  apb addr in
    .pwrite                (s_apb_pwrite ),             //--in    apb pw enable in
    .penable               (s_apb_penable),                //--in  apb bus enable in
    .pwdata                (s_apb_pwdata ),             //--in  apb pw data in
    
    .prdata_modema         (s_apb_prdata_modema    ),
    .prdata_modemb         (),
    .prdata_modemg         (s_apb_prdata_modemg    ),
    .prdata_bup            (),
    .prdata_radio          (s_apb_prdata_radio     ),
    .prdata_streamproc     (),
    .prdata_frontend       (s_apb_prdata_frontend  ), 

    .anaif_rxi             (anaif_rxi  ),
    .anaif_rxq             (anaif_rxq  ),
    .anaif_txi             (anaif_txi  ),         
    .anaif_txq             (anaif_txq  ),  
        
	//--------------- debug ---------------------------------------
    .modem_rx_a_tog             (modem_rx_a_tog       ),
    .modem_rx_a_i_phy           (modem_rx_a_i_phy     ),
    .modem_rx_a_q_phy           (modem_rx_a_q_phy     ),
    
    .modem_tx_a_tog             (modem_tx_a_tog       ),
    .modem_tx_a_i_phy           (modem_tx_a_i_phy     ),
    .modem_tx_a_q_phy           (modem_tx_a_q_phy     ),
    
    .agc_lock                   (1'b1  ),
    .agc_rise                   (  ),
    .agc_fall_o                 (  ),    
        
    .phy_data_conf_o            (phy_data_conf         ),
        
    .phy_data_ind_o             (phy_data_ind          ),
    .bup_rxdata_o               (bup_rxdata            ),
    
    .rxv_length_o               ( rxv_length           ),
    .rxv_service_o              ( rxv_service          ),
    .rxv_service_ind_o          ( rxv_service_ind      ),
    .rxv_datarate_o             ( rxv_datarate         ),

    .phy_txstartend_conf        ( phy_txstartend_conf  ),
    .phy_cca_ind_medium         ( phy_cca_ind_medium   ), 

    .phy_data_req               ( phy_data_req         ),
    .bup_txdata                 ( bup_txdata           ),
    .phy_txstartend_req         ( phy_txstartend_req   ), 
    .phy_ccarst_req             ( phy_ccarst_req       ),
    .rxv_macaddr_match          ( rxv_macaddr_match    ),       
    .txv_datarate               ( txv_datarate         ),    
    .txv_length                 ( txv_length           ),
    .txpwr_level                ( txpwr_level          ), 
    .txv_service                ( txv_service          ),
    .txv_immstop                ( txv_immstop          ),
    .cp2_detected               ( cp2_detected         )  //out 

  ); 


  /***********************************************************
  * tx_rx_fifo between the PHY and AD9361
  ***********************************************************/
    tx_rx_fifo u_tx_rx_fifo(
    
    .clk_80m                     ( clk_80m                    ),
    .source_clk                  ( source_clk                 ),
    .AD9361_clk                  ( AD9361_clk                 ),
    .txv_immstop                 ( txv_immstop                ),
    .rst_n                       ( rst_n                      ),
    
    .sourcedata_ch               ( sourcedata_ch              ),
    .cap_data_en                 ( cap_data_en                ),
    
    /* phy if from phy*/
    .modem_tx_a_tog              ( modem_tx_a_tog             ),
    .modem_tx_a_i_phy            ( modem_tx_a_i_phy           ),   //in from phy
    .modem_tx_a_q_phy            ( modem_tx_a_q_phy           ),   //in from phy
    /* analog if */
    .modem_tx_a_i_rf_o           ( modem_tx_a_i_rf            ),   //out to RF
    .modem_tx_a_q_rf_o           ( modem_tx_a_q_rf            ),   //out to RF
     
    /* analog if*/ 
    .modem_rx_a_i_rf_in          ( modem_rx_a_i_rf            ),     // in from rf
    .modem_rx_a_q_rf_in          ( modem_rx_a_q_rf            ),     // in from rf          

    /* phy if to phy*/ 
    .modem_rx_a_tog              ( modem_rx_a_tog             ),
    .modem_rx_a_i_phy            ( modem_rx_a_i_phy           ),     // out to phy
    .modem_rx_a_q_phy            ( modem_rx_a_q_phy           ),     // out to phy
   

    /* the CTL INTERFACE between phy and AD9361 */

    .dac_dovf                    (dac_dovf                    ),
    .dac_dunf                    (dac_dunf                    ),
    .adc_dovf                    (adc_dovf                    ),
    .adc_dunf                    (adc_dunf                    ),

    .rf_rst                      (rf_rst                      ),
    .adc_enable_i0               (adc_enable_i0               ),
    .adc_valid_i0                (adc_valid_i0                ),
    .adc_enable_q0               (adc_enable_q0               ),
    .adc_valid_q0                (adc_valid_q0                ),
    .dac_enable_i0               (dac_enable_i0               ),
    .dac_valid_i0                (dac_valid_i0                ),
    .dac_enable_q0               (dac_enable_q0               ),
    .dac_valid_q0                (dac_valid_q0                ),
    .txfifo_empty                (txfifo_empty                ),  
    .rxfifo_full                 (rxfifo_full                 ),
    .rxfifo_almost_empty         (rxfifo_almost_empty         ),
    .txfifo_almost_full          (txfifo_almost_full          ),
    .rx_start                    (rx_start                    )
    );
  
  /***********************************************************
  * MACPHY_IF include rx_mod and tx_mod and regbank
  ***********************************************************/
  macphy_if u_macphy_if(
    
        .clk_80m              ( clk_80m                    ), 
        .bus_clk_resetn       ( external_resetn            ),
        .sourcedata_ch        ( sourcedata_ch              ),
        .cap_data_en          ( cap_data_en                ),
  // ------------ APB ---------------------------------     
        .psel                 ( psel_macphy_if             ),
        .paddr                ( s_apb_paddr[11:0]          ),     
        .pwrite               ( s_apb_pwrite               ),    
        .penable              ( s_apb_penable              ),   
        .pwdata               ( s_apb_pwdata               ),   
     
        .prdata               ( s_apb_prdata_if            ),
        .prdata_valid         ( s_apb_pready_if            ),
  //----------------- mac signal tx  ------------------------
        .mpifClk              ( mpifClk                    ),
        .phyRdy               ( phyRdy                     ),        
        .testmode             (testmode                    ), 
                
        .txReq                ( txReq                      ),
        .txData               ( txData                     ),
        .macDataValid         ( macDataValid               ),
        .txEnd_p              ( txEnd_p                    ),
        .mpIfTxFifoEmtpy      ( mpIfTxFifoEmtpy            ),
  //----------------- mac signal rx  ------------------------
        .rxReq                ( rxReq                      ),
        .rxData               ( rxData                     ),
        .rxEndForTiming_p     ( rxEndForTiming_p           ),
        .rxEnd_p              ( rxEnd_p                    ), 
        
        .CCAPrimary20         ( CCAPrimary20               ),  
  //------------------ tx data   --------------------------
        .phy_txstartend_conf  ( phy_txstartend_conf        ),
        .phy_data_conf        ( phy_data_conf              ),
    
        .phy_data_req         ( phy_data_req               ),
        .bup_txdata           ( bup_txdata                 ),
        .phy_txstartend_req   ( phy_txstartend_req         ), 
        .phy_ccarst_req       ( phy_ccarst_req             ),
        .rxv_macaddr_match    ( rxv_macaddr_match          ),       
        .txv_datarate_reg     ( txv_datarate               ),    
        .txv_length_reg       ( txv_length                 ),
        .txpwr_level_reg      ( txpwr_level                ), 
        .txv_service_reg      ( txv_service                ),
        
  //--------------------- rx data --------------------------
        .phy_data_ind         ( phy_data_ind               ),
        .bup_rxdata           ( bup_rxdata                 ),
        .rxv_length           ( rxv_length                 ),
        .rxv_datarate         ( rxv_datarate               ),
        .rxv_signal_ind       ( rxv_service_ind            ),
        .EndForRx             ( EndForRx                   ),
        .txv_immstop          ( txv_immstop                ),
        
   //---------------------- debug ------------------------------
   
        .modem_tx_a_i_phy      ( modem_tx_a_i_phy          ),
        .modem_tx_a_i_rf       ( modem_tx_a_i_rf           ),
        .modem_rx_a_i_phy      ( modem_rx_a_i_phy          ),
        .modem_rx_a_i_rf       ( modem_rx_a_i_rf           ),
        .tx_data_out           ( tx_data_out               ),
        .rx_data_in            ( rx_data_in                ),
        .cp2_detected          ( cp2_detected              )  //in         
    );
    
    cca_detect  cca_detect_1
    (
        /* input */
        .clk                    ( clk_80m                           ),
        .reset_n                ( external_resetn                   ),
        .en_20m_i               ( AD9361_clk                        ),
        .agc_inbd_pow_en        ( 1'b1                              ),    

        `ifdef FMQ_SIMULATE 
        .modem_rx_a_i_rf        ( {4'b0,modem_rx_a_i_phy,1'b0}      ),
        .modem_rx_a_q_rf        ( {4'b0,modem_rx_a_q_phy,1'b0}      ),
        `elsif
        .modem_rx_a_i_rf        ( modem_rx_a_i_rf                   ),
        .modem_rx_a_q_rf        ( modem_rx_a_q_rf                   ),
        `endif
        .reg_top_limit          ( reg_top_limit                     ),
        .reg_lower_limit        ( reg_lower_limit                   ),
        /* output */
        .cca_detect_o           ( agc_fall                          )
    );
   
    
endmodule
