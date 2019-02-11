// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SEX_CMM
// CREATE DATE      :   2017-09-07
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-07  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   The configuration Memory Management of Single Extetion box   
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

module  SEX_CMM
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    clk_emif                    ,   
    rst_emif                    ,   

    // mpu box configuration 
    master_slave_flag           ,
    hot_plug_req                ,
    dst_sta_num                 ,   

    // write port 
    ex_box_sel                  ,   
    chn_sel                     ,   
    wr_en                       ,   
    wr_data                     ,   

    // read port
    ssdu_excmm_rdreq            , 
    excmm_ssdu_empty            ,   
    excmm_ssdu_dval             ,   
    excmm_ssdu_data               
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   DST_BOX_NUM     =   3'd0 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   
input   wire                    clk_emif                            ;   
input   wire                    rst_emif                            ;   

input   wire        [7:0]       dst_sta_num                         ;   
input   wire        [7:0]       master_slave_flag                   ;   
input   wire        [15:0]      hot_plug_req                        ;  
input   wire                    ex_box_sel                          ;   
input   wire        [3:0]       chn_sel                             ;   
input   wire                    wr_en                               ;   
input   wire        [17:0]      wr_data                             ;
input   wire                    ssdu_excmm_rdreq                    ;   

// declare output signal
output  wire                    excmm_ssdu_empty                    ;   
output  wire                    excmm_ssdu_dval                     ;   
output  wire        [17:0]      excmm_ssdu_data                     ;  

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [15:0]              cm_empty                            ;   
wire        [15:0]              rd_en                               ;   
wire        [15:0]              tpram_sdu_dval                      ;   
wire        [17:0]              tpram1_sdu_data                     ;   
wire        [17:0]              tpram2_sdu_data                     ;   
wire        [17:0]              tpram3_sdu_data                     ;   
wire        [17:0]              tpram4_sdu_data                     ;  
wire        [3:0]               cfg_sel                             ;   

// reg signal
reg         [17:0]              chn_sdu_data                        ;   
reg         [15:0]              chn_sdu_dval                        ;   
reg                             ex_box_sel_d1                       ;   
reg         [3:0]               chn_sel_d1                          ;   
reg                             wr_en_d1                            ;   
reg         [17:0]              wr_data_d1                          ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
always @ ( posedge clk_emif ) begin
    ex_box_sel_d1  <=  ex_box_sel  ;                   
    chn_sel_d1     <=  chn_sel     ;                   
    wr_en_d1       <=  wr_en       ;                   
    wr_data_d1     <=  wr_data     ;                
end

assign  cfg_sel[0] =  ( ex_box_sel_d1 == 1'b1 && ( chn_sel_d1[3:2] == 2'b00 ) ) ? 1'b1 : 1'b0 ;  
assign  cfg_sel[1] =  ( ex_box_sel_d1 == 1'b1 && ( chn_sel_d1[3:2] == 2'b01 ) ) ? 1'b1 : 1'b0 ;  
assign  cfg_sel[2] =  ( ex_box_sel_d1 == 1'b1 && ( chn_sel_d1[3:2] == 2'b10 ) ) ? 1'b1 : 1'b0 ;  
assign  cfg_sel[3] =  ( ex_box_sel_d1 == 1'b1 && ( chn_sel_d1[3:2] == 2'b11 ) ) ? 1'b1 : 1'b0 ; 

//----------------------------------------------------------------------------------
// slot4-slot1 configuration LSRAM instance
//----------------------------------------------------------------------------------
    EX_CMCELL                   #
    (
    .DST_BOX_NUM                ( DST_BOX_NUM               ),
    .DST_SLOT_NUM1              ( 4'd0                      ),
    .DST_SLOT_NUM2              ( 4'd1                      ),
    .DST_SLOT_NUM3              ( 4'd2                      ),
    .DST_SLOT_NUM4              ( 4'd3                      )
    )
    U1_EX_CMCELL
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .dst_sta_num                ( dst_sta_num               ),
    .master_slave_flag          ( master_slave_flag         ),
    .hot_plug_req               ( hot_plug_req[3:0]         ),

    .cfg_sel                    ( cfg_sel[0]                ),
    .exchn_sel                  ( chn_sel_d1[1:0]           ),
    .wr_en                      ( wr_en_d1                  ),
    .wr_data                    ( wr_data_d1                ),

    .cm_empty                   ( cm_empty[3:0]             ),
    .rd_en                      ( rd_en[3:0]                ),
    .tpram_sdu_dval             ( tpram_sdu_dval[3:0]       ),
    .tpram_sdu_data             ( tpram1_sdu_data           )
    );

//----------------------------------------------------------------------------------
// slot8-slot5 configuration LSRAM instance
//----------------------------------------------------------------------------------
    EX_CMCELL                   #
    (
    .DST_BOX_NUM                ( DST_BOX_NUM               ),
    .DST_SLOT_NUM1              ( 4'd4                      ),
    .DST_SLOT_NUM2              ( 4'd5                      ),
    .DST_SLOT_NUM3              ( 4'd6                      ),
    .DST_SLOT_NUM4              ( 4'd7                      )
    )
    U2_EX_CMCELL
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .dst_sta_num                ( dst_sta_num               ),
    .master_slave_flag          ( master_slave_flag         ),
    .hot_plug_req               ( hot_plug_req[7:4]         ),

    .cfg_sel                    ( cfg_sel[1]                ),
    .exchn_sel                  ( chn_sel_d1[1:0]           ),
    .wr_en                      ( wr_en_d1                  ),
    .wr_data                    ( wr_data_d1                ),

    .cm_empty                   ( cm_empty[7:4]             ),
    .rd_en                      ( rd_en[7:4]                ),
    .tpram_sdu_dval             ( tpram_sdu_dval[7:4]       ),
    .tpram_sdu_data             ( tpram2_sdu_data           )
    );

//----------------------------------------------------------------------------------
// slot12-slot9 configuration LSRAM instance
//----------------------------------------------------------------------------------
    EX_CMCELL                   #
    (
    .DST_BOX_NUM                ( DST_BOX_NUM               ),
    .DST_SLOT_NUM1              ( 4'd8                      ),
    .DST_SLOT_NUM2              ( 4'd9                      ),
    .DST_SLOT_NUM3              ( 4'd10                     ),
    .DST_SLOT_NUM4              ( 4'd11                     )
    )
    U3_EX_CMCELL
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .dst_sta_num                ( dst_sta_num               ),
    .master_slave_flag          ( master_slave_flag         ),
    .hot_plug_req               ( hot_plug_req[11:8]        ),

    .cfg_sel                    ( cfg_sel[2]                ),
    .exchn_sel                  ( chn_sel_d1[1:0]           ),
    .wr_en                      ( wr_en_d1                  ),
    .wr_data                    ( wr_data_d1                ),

    .cm_empty                   ( cm_empty[11:8]            ),
    .rd_en                      ( rd_en[11:8]               ),
    .tpram_sdu_dval             ( tpram_sdu_dval[11:8]      ),
    .tpram_sdu_data             ( tpram3_sdu_data           )
    );

//----------------------------------------------------------------------------------
// slot16-slot13 configuration LSRAM instance
//----------------------------------------------------------------------------------
    EX_CMCELL                   #
    (
    .DST_BOX_NUM                ( DST_BOX_NUM               ),
    .DST_SLOT_NUM1              ( 4'd12                     ),
    .DST_SLOT_NUM2              ( 4'd13                     ),
    .DST_SLOT_NUM3              ( 4'd14                     ),
    .DST_SLOT_NUM4              ( 4'd15                     )
    )
    U4_EX_CMCELL
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .dst_sta_num                ( dst_sta_num               ),
    .master_slave_flag          ( master_slave_flag         ),
    .hot_plug_req               ( hot_plug_req[15:12]       ),

    .cfg_sel                    ( cfg_sel[3]                ),
    .exchn_sel                  ( chn_sel_d1[1:0]           ),
    .wr_en                      ( wr_en_d1                  ),
    .wr_data                    ( wr_data_d1                ),

    .cm_empty                   ( cm_empty[15:12]           ),
    .rd_en                      ( rd_en[15:12]              ),
    .tpram_sdu_dval             ( tpram_sdu_dval[15:12]     ),
    .tpram_sdu_data             ( tpram4_sdu_data           )
    );

//----------------------------------------------------------------------------------
// 16 - 1 schedule machine instance
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m ) begin
    chn_sdu_dval   <=   tpram_sdu_dval ;
end

always @ ( posedge clk_12_5m ) begin
    case( tpram_sdu_dval )
        16'b0000000000000001   :   chn_sdu_data    <=  tpram1_sdu_data ; 
        16'b0000000000000010   :   chn_sdu_data    <=  tpram1_sdu_data ; 
        16'b0000000000000100   :   chn_sdu_data    <=  tpram1_sdu_data ; 
        16'b0000000000001000   :   chn_sdu_data    <=  tpram1_sdu_data ; 
        16'b0000000000010000   :   chn_sdu_data    <=  tpram2_sdu_data ; 
        16'b0000000000100000   :   chn_sdu_data    <=  tpram2_sdu_data ; 
        16'b0000000001000000   :   chn_sdu_data    <=  tpram2_sdu_data ; 
        16'b0000000010000000   :   chn_sdu_data    <=  tpram2_sdu_data ;  
        16'b0000000100000000   :   chn_sdu_data    <=  tpram3_sdu_data ;  
        16'b0000001000000000   :   chn_sdu_data    <=  tpram3_sdu_data ;  
        16'b0000010000000000   :   chn_sdu_data    <=  tpram3_sdu_data ;  
        16'b0000100000000000   :   chn_sdu_data    <=  tpram3_sdu_data ;  
        16'b0001000000000000   :   chn_sdu_data    <=  tpram4_sdu_data ;  
        16'b0010000000000000   :   chn_sdu_data    <=  tpram4_sdu_data ;  
        16'b0100000000000000   :   chn_sdu_data    <=  tpram4_sdu_data ; 
        16'b1000000000000000   :   chn_sdu_data    <=  tpram4_sdu_data ; 
        default                :   chn_sdu_data    <=  18'h00 ; 
    endcase
end

    SDU16S1                     U_SDU16S1
    (
    .clk_sys                    ( clk_12_5m                 ),
    .rst_sys                    ( rst_12_5m                 ),
   
    .chn_sdu_dval               ( chn_sdu_dval              ),
    .chn_sdu_data               ( chn_sdu_data              ),
    .chn_sdu_empty              ( cm_empty                  ),
    .sdu_chn_rden               ( rd_en                     ),

    .fifo_rdreq                 ( ssdu_excmm_rdreq          ),
    .fifo_empty                 ( excmm_ssdu_empty          ),
    .fifo_rd_dval               ( excmm_ssdu_dval           ),
    .fifo_rd_data               ( excmm_ssdu_data           )
    );

endmodule

