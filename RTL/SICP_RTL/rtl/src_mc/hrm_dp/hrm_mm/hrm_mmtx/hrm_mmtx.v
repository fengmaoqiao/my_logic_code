// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   HRM_MMTX
// CREATE DATE      :   2017-09-21
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-21  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   memory management of Hot-Redunancy MCU transmit data path
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

module  HRM_MMTX
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    clk_emif                    ,   
    rst_emif                    ,   

    // connect to EMIF module
    chn_sel                     ,  
    hrm_pkt_num                 ,   
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

input   wire                    chn_sel                             ; 
input   wire        [3:0]       hrm_pkt_num                         ;   
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
wire        [3:0]               dmm_empty                           ;   
wire        [4:0]               sdu_chn_rden                        ;   
wire        [3:0]               tpram_sdu_dval                      ;   
wire        [17:0]              tpram_sdu_data  [4:0]               ;   
wire        [4:0]               chn_sdu_empty                       ;   

// reg signal
reg         [17:0]              chn_sdu_data                        ;   
reg         [4:0]               chn_sdu_dval                        ;  

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign  data_sel[0] =  ( chn_sel == 1'b1 && hrm_pkt_num[3:1] == 3'b000 ) ? 1'b1 : 1'b0 ;  
assign  data_sel[1] =  ( chn_sel == 1'b1 && hrm_pkt_num[3:1] == 3'b001 ) ? 1'b1 : 1'b0 ;  
//assign  data_sel[2] =  ( chn_sel == 1'b1 && hrm_pkt_num[3:1] == 3'b010 ) ? 1'b1 : 1'b0 ;  
//assign  data_sel[3] =  ( chn_sel == 1'b1 && hrm_pkt_num[3:1] == 3'b011 ) ? 1'b1 : 1'b0 ;  
//assign  data_sel[4] =  ( chn_sel == 1'b1 && hrm_pkt_num[3:1] == 3'b100 ) ? 1'b1 : 1'b0 ;  

//----------------------------------------------------------------------------------
// hrm packet muber 0-1 DMMTX instance
//----------------------------------------------------------------------------------
    TYPE2_DMMTX                 U1_TYPE2_DMMTX
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .dst_port0                  ( 3'd0                      ),
    .dst_port1                  ( 3'd0                      ),
    .pkt_num0                   ( 4'd0                      ),
    .pkt_num1                   ( 4'd1                      ),

    .wr_sel                     ( data_sel[0]               ),
    .port_sel                   ( hrm_pkt_num[0]            ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),

    .chn_type                   ( `MPU_TYPE                 ),
    .master_slave_flag          ( 8'hff                     ),
    .dmm_empty                  ( dmm_empty[1:0]            ),
    .rd_en                      ( sdu_chn_rden[1:0]         ),
    .tpram_sdu_dval             ( tpram_sdu_dval[1:0]       ),
    .tpram_sdu_data             ( tpram_sdu_data[0]         )
    );

//----------------------------------------------------------------------------------
// hrm packet muber 2-3 DMMTX instance
//----------------------------------------------------------------------------------
    TYPE2_DMMTX                 U2_TYPE2_DMMTX
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .dst_port0                  ( 3'd0                      ),
    .dst_port1                  ( 3'd0                      ),
    .pkt_num0                   ( 4'd2                      ),
    .pkt_num1                   ( 4'd3                      ),

    .wr_sel                     ( data_sel[1]               ),
    .port_sel                   ( hrm_pkt_num[0]            ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),

    .chn_type                   ( `MPU_TYPE                 ),
    .master_slave_flag          ( 8'hff                     ),
    .dmm_empty                  ( dmm_empty[3:2]            ),
    .rd_en                      ( sdu_chn_rden[3:2]         ),
    .tpram_sdu_dval             ( tpram_sdu_dval[3:2]       ),
    .tpram_sdu_data             ( tpram_sdu_data[1]         )
    );

////----------------------------------------------------------------------------------
//// hrm packet muber 4-5 DMMTX instance
////----------------------------------------------------------------------------------
//    TYPE2_DMMTX                 U3_TYPE2_DMMTX
//    (
//    .clk_12_5m                  ( clk_12_5m                 ),
//    .rst_12_5m                  ( rst_12_5m                 ),
//    .clk_emif                   ( clk_emif                  ),
//    .rst_emif                   ( rst_emif                  ),
//
//    .dst_port0                  ( 3'd0                      ),
//    .dst_port1                  ( 3'd0                      ),
//    .pkt_num0                   ( 4'd4                      ),
//    .pkt_num1                   ( 4'd5                      ),
//
//    .wr_sel                     ( data_sel[2]               ),
//    .port_sel                   ( hrm_pkt_num[0]            ),
//    .wr_en                      ( wr_en                     ),
//    .wr_data                    ( wr_data                   ),
//
//    .chn_type                   ( `MPU_TYPE                 ),
//    .master_slave_flag          ( 8'hff                     ),
//    .dmm_empty                  ( dmm_empty[5:4]            ),
//    .rd_en                      ( sdu_chn_rden[5:4]         ),
//    .tpram_sdu_dval             ( tpram_sdu_dval[5:4]       ),
//    .tpram_sdu_data             ( tpram_sdu_data[2]         )
//    );
//
////----------------------------------------------------------------------------------
//// hrm packet muber 6-7 DMMTX instance
////----------------------------------------------------------------------------------
//    TYPE2_DMMTX                 U4_TYPE2_DMMTX
//    (
//    .clk_12_5m                  ( clk_12_5m                 ),
//    .rst_12_5m                  ( rst_12_5m                 ),
//    .clk_emif                   ( clk_emif                  ),
//    .rst_emif                   ( rst_emif                  ),
//
//    .dst_port0                  ( 3'd0                      ),
//    .dst_port1                  ( 3'd0                      ),
//    .pkt_num0                   ( 4'd6                      ),
//    .pkt_num1                   ( 4'd7                      ),
//
//    .wr_sel                     ( data_sel[3]               ),
//    .port_sel                   ( hrm_pkt_num[0]            ),
//    .wr_en                      ( wr_en                     ),
//    .wr_data                    ( wr_data                   ),
//
//    .chn_type                   ( `MPU_TYPE                 ),
//    .master_slave_flag          ( 8'hff                     ),
//    .dmm_empty                  ( dmm_empty[7:6]            ),
//    .rd_en                      ( sdu_chn_rden[7:6]         ),
//    .tpram_sdu_dval             ( tpram_sdu_dval[7:6]       ),
//    .tpram_sdu_data             ( tpram_sdu_data[3]         )
//    );
//
////----------------------------------------------------------------------------------
//// hrm packet muber 8-9 DMMTX instance
////----------------------------------------------------------------------------------
//    TYPE2_DMMTX                 U5_TYPE2_DMMTX
//    (
//    .clk_12_5m                  ( clk_12_5m                 ),
//    .rst_12_5m                  ( rst_12_5m                 ),
//    .clk_emif                   ( clk_emif                  ),
//    .rst_emif                   ( rst_emif                  ),
//
//    .dst_port0                  ( 3'd0                      ),
//    .dst_port1                  ( 3'd0                      ),
//    .pkt_num0                   ( 4'd8                      ),
//    .pkt_num1                   ( 4'd9                      ),
//
//    .wr_sel                     ( data_sel[4]               ),
//    .port_sel                   ( hrm_pkt_num[0]            ),
//    .wr_en                      ( wr_en                     ),
//    .wr_data                    ( wr_data                   ),
//
//    .chn_type                   ( `MPU_TYPE                 ),
//    .master_slave_flag          ( 8'hff                     ),
//    .dmm_empty                  ( dmm_empty[9:8]            ),
//    .rd_en                      ( sdu_chn_rden[9:8]         ),
//    .tpram_sdu_dval             ( tpram_sdu_dval[9:8]       ),
//    .tpram_sdu_data             ( tpram_sdu_data[4]         )
//    );
//
//----------------------------------------------------------------------------------
// 10 - 1 schedule machine instance
//----------------------------------------------------------------------------------
assign  chn_sdu_empty       =   { 1'b1 , dmm_empty } ; 

always @ ( posedge clk_12_5m ) begin
    chn_sdu_dval   <=   { 1'b0 , tpram_sdu_dval } ;
end

always @ ( posedge clk_12_5m ) begin
    case( tpram_sdu_dval )
        4'b0001   :   chn_sdu_data    <=  tpram_sdu_data[0] ; 
        4'b0010   :   chn_sdu_data    <=  tpram_sdu_data[0] ; 
        4'b0100   :   chn_sdu_data    <=  tpram_sdu_data[1] ; 
        4'b1000   :   chn_sdu_data    <=  tpram_sdu_data[1] ; 
        default   :   chn_sdu_data    <=  18'h00 ; 
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

