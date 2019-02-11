// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   TYPE2_MMTX
// CREATE DATE      :   2017-08-25
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-25  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   memory management of TYPE2 transmit data path
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

module  TYPE2_MMTX
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    clk_emif                    ,   
    rst_emif                    ,   

    // mpu box configuration 
    run_cycle                   ,   
    chn_type                    , 
    dst_sta_num                 ,   
    master_slave_flag           ,
    hot_plug_req                ,

    // connect to EMIF module
    wr_sel                      ,   
    wr_port                     ,   
    wr_en                       ,   
    wr_data                     ,   

    // connect to slink protocol stack
    slink_mmtx_rdreq            ,   
    mmtx_slink_dval             ,
    mmtx_slink_data             
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
input   wire                    clk_emif                            ;   
input   wire                    rst_emif                            ;  

input   wire        [15:0]      run_cycle                           ;
input   wire        [7:0]       dst_sta_num                         ;   
input   wire        [4:0]       chn_type                            ;   
input   wire        [7:0]       master_slave_flag                   ;   
input   wire                    hot_plug_req                        ;   
input   wire                    wr_sel                              ;   
input   wire        [2:0]       wr_port                             ;   
input   wire                    wr_en                               ;   
input   wire        [17:0]      wr_data                             ; 
input   wire                    slink_mmtx_rdreq                    ;   

// declare output signal
output  wire                    mmtx_slink_dval                     ;   
output  wire        [17:0]      mmtx_slink_data                     ;  

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [1:0]               data_sel                            ;   
wire                            cfg_sel                             ;   
wire        [3:0]               dmm_empty                           ;   
wire        [4:0]               sdu_chn_rden                        ;   
wire        [3:0]               tpram_sdu_dval                      ;   
wire        [17:0]              tpram_sdu_data  [1:0]               ;   
wire                            mpu_cfg_empty                       ;   
wire        [17:0]              mpu_cfg_data                        ;   
wire        [4:0]               chn_sdu_empty                       ;   
wire        [4:0]               chn_sdu_dval_tmp                    ;   
wire                            mpu_cfg_dval                        ;   

// reg signal
reg         [4:0]               chn_sdu_dval                        ;   
reg         [17:0]              chn_sdu_data                        ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign  data_sel[0] =  ( wr_sel == 1'b1 && wr_port[2] == 1'b0 && wr_port[0] == 1'b1 ) ? 1'b1 : 1'b0 ;  
assign  data_sel[1] =  ( wr_sel == 1'b1 && wr_port[2] == 1'b1 && wr_port[0] == 1'b1 ) ? 1'b1 : 1'b0 ;  
assign  cfg_sel     =  ( wr_sel == 1'b1 && wr_port[2:0] == 3'b000 ) ? 1'b1 : 1'b0 ;  

//----------------------------------------------------------------------------------
// port 0-1 DMMTX instance
//----------------------------------------------------------------------------------
    TYPE2_DMMTX                 U1_TYPE2_DMMTX
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .run_cycle                  ( run_cycle                 ),
    .dst_sta_num                ( dst_sta_num               ),
    .dst_port0                  ( 3'd0                      ),
    .dst_port1                  ( 3'd1                      ),
    .pkt_num0                   ( 4'd0                      ),
    .pkt_num1                   ( 4'd0                      ),

    .wr_sel                     ( data_sel[0]               ),
    .port_sel                   ( wr_port[1]                ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),

    .chn_type                   ( chn_type                  ),
    .master_slave_flag          ( master_slave_flag         ),
    .dmm_empty                  ( dmm_empty[1:0]            ),
    .rd_en                      ( sdu_chn_rden[1:0]         ),
    .tpram_sdu_dval             ( tpram_sdu_dval[1:0]       ),
    .tpram_sdu_data             ( tpram_sdu_data[0]         )
    );

//----------------------------------------------------------------------------------
// port 2-3 DMMTX instance
//----------------------------------------------------------------------------------
    TYPE2_DMMTX                 U2_TYPE2_DMMTX
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .run_cycle                  ( run_cycle                 ),
    .dst_sta_num                ( dst_sta_num               ),
    .dst_port0                  ( 3'd2                      ),
    .dst_port1                  ( 3'd3                      ),
    .pkt_num0                   ( 4'd0                      ),
    .pkt_num1                   ( 4'd0                      ),

    .wr_sel                     ( data_sel[1]               ),
    .port_sel                   ( wr_port[1]                ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),

    .chn_type                   ( chn_type                  ),
    .master_slave_flag          ( master_slave_flag         ),
    .dmm_empty                  ( dmm_empty[3:2]            ),
    .rd_en                      ( sdu_chn_rden[3:2]         ),
    .tpram_sdu_dval             ( tpram_sdu_dval[3:2]       ),
    .tpram_sdu_data             ( tpram_sdu_data[1]         )
    );

//----------------------------------------------------------------------------------
// MPU box slot[n] board configuration momery management instance
//----------------------------------------------------------------------------------

    MPU_CMM                     U_MPU_CMM
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .run_cycle                  ( run_cycle                 ),
    .dst_sta_num                ( dst_sta_num               ),
    .tpram_sel                  ( cfg_sel                   ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),

    .master_slave_flag          ( master_slave_flag         ),
    .hot_plug_req               ( hot_plug_req              ),
    .cfg_empty                  ( mpu_cfg_empty             ),
    .rd_en                      ( sdu_chn_rden[4]           ),
    .tpram_sdu_dval             ( mpu_cfg_dval              ),
    .tpram_sdu_data             ( mpu_cfg_data              )
    );

//----------------------------------------------------------------------------------
// 5 - 1 schedule machine instance
//----------------------------------------------------------------------------------
assign  chn_sdu_empty       =   { mpu_cfg_empty , dmm_empty } ; 
assign  chn_sdu_dval_tmp    =   { mpu_cfg_dval , tpram_sdu_dval } ;

always @ ( posedge clk_12_5m ) begin
    chn_sdu_dval   <=   chn_sdu_dval_tmp ;
end

always @ ( posedge clk_12_5m ) begin
    case( chn_sdu_dval_tmp )
        5'b00001   :   chn_sdu_data    <=  tpram_sdu_data[0] ; 
        5'b00010   :   chn_sdu_data    <=  tpram_sdu_data[0] ; 
        5'b00100   :   chn_sdu_data    <=  tpram_sdu_data[1] ; 
        5'b01000   :   chn_sdu_data    <=  tpram_sdu_data[1] ; 
        5'b10000   :   chn_sdu_data    <=  mpu_cfg_data ; 
        default    :   chn_sdu_data    <=  18'h00 ; 
    endcase
end

    SDU5S1                      U_SDU5S1
    (
    .clk_sys                    ( clk_12_5m                 ),
    .rst_sys                    ( rst_12_5m                 ),
   
    .chn_sdu_dval               ( chn_sdu_dval              ),
    .chn_sdu_data               ( chn_sdu_data              ),
    .chn_sdu_empty              ( chn_sdu_empty             ),
    .sdu_chn_rden               ( sdu_chn_rden              ),

    .fifo_rdreq                 ( slink_mmtx_rdreq          ),
    .fifo_empty                 (                           ),
    .fifo_rd_dval               ( mmtx_slink_dval           ),
    .fifo_rd_data               ( mmtx_slink_data           )
    );


endmodule

