// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   TYPE1_MMTX
// CREATE DATE      :   2017-08-21
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-21  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   memory management of TYPE1 transmit data path
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

module  TYPE1_MMTX
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    clk_emif                    ,   
    rst_emif                    ,   

    // mpu box configuration 
    run_cycle                   ,   
    dst_sta_num                 ,   
    chn_type                    , 
    master_slave_flag           ,
    hot_plug_req                ,
    ex_box_data_ena             , // if chn_type is COM1 , this signal indicate COM1 connct to which EX box
    ex_box_cfg_ena              , // if chn_type is COM1 , this signal decide which EX box's configuration shoud send from this COM1

    // write port
    wr_sel                      ,   
    wr_port                     ,   
    wr_en                       ,   
    wr_data                     ,   

    // extention box configuration data interface
    excmm_ssdu_empty            ,   
    excmm_ssdu_dval             ,
    excmm_ssdu_data0            ,   
    excmm_ssdu_data1            ,   
    excmm_ssdu_data2            ,   
    excmm_ssdu_data3            ,   
    ssdu_excmm_rdreq            ,

    // slink interface
    slink_mmtx_rdreq            ,   
    mmtx_slink_dval             ,
    mmtx_slink_data             

    //             
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   MPU_SLOT = 4'd0 ;

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
input   wire        [3:0]       ex_box_data_ena                     ;   
input   wire        [3:0]       ex_box_cfg_ena                      ;  

input   wire                    wr_sel                              ;   
input   wire        [7:0]       wr_port                             ;   
input   wire                    wr_en                               ;   
input   wire        [17:0]      wr_data                             ; 

input   wire                    slink_mmtx_rdreq                    ;   
input   wire        [3:0]       excmm_ssdu_empty                    ;   
input   wire        [3:0]       excmm_ssdu_dval                     ;   
input   wire        [17:0]      excmm_ssdu_data0                    ;   
input   wire        [17:0]      excmm_ssdu_data1                    ;   
input   wire        [17:0]      excmm_ssdu_data2                    ;   
input   wire        [17:0]      excmm_ssdu_data3                    ;   

// declare output signal
output  wire                    mmtx_slink_dval                     ;   
output  wire        [17:0]      mmtx_slink_data                     ; 
output  wire        [3:0]       ssdu_excmm_rdreq                    ;

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [3:0]               ex_data_slot    [3:0]               ;
wire        [3:0]               ex_wr_en                            ;  
wire        [17:0]              ex_wr_data      [3:0]               ;
wire                            cfg_tpram_sel                       ; 
wire        [3:0]               mpu_data_sel                        ;  
wire        [3:0]               ex_data_sel                         ;   
wire        [3:0]               port_empty                          ;   
wire        [3:0]               ex_cfg_empty                        ;   
wire        [3:0]               ex_cfg_dval                         ;   
wire        [3:0]               port_dval                           ;   
wire        [15:0]              dmm_empty      [3:0]                ;   
wire        [15:0]              rd_en          [3:0]                ;   
wire        [15:0]              tpram_sdu_dval [3:0]                ;   
wire        [17:0]              tpram_sdu_data [3:0]                ;  
wire        [17:0]              port_data      [3:0]                ;  
wire        [3:0]               ssdu_dmm_rdreq                      ;  
wire        [8:0]               chn_sdu_empty                       ;   
wire                            mpu_cfg_empty                       ;   
wire                            mpu_cfg_dval                        ;   
wire        [17:0]              mpu_cfg_data                        ;  
wire        [8:0]               sdu_chn_rden                        ;
wire        [8:0]               chn_sdu_dval_tmp                    ;   

// reg signal
reg         [8:0]               chn_sdu_dval                        ;  
reg         [17:0]              chn_sdu_data                        ;
reg         [3:0]               ex_box_data_ena_d1                  ;   
reg         [3:0]               ex_box_cfg_ena_d1                   ; 
reg         [3:0]               ex_box_cfg_ena_d2                   ; 
reg                             wr_sel_d1                           ;   
reg         [7:0]               wr_port_d1                          ;   
reg         [3:0]               data_tpram_sel                      ;  
reg         [3:0]               chn_sel                             ; 
reg         [4:0]               chn_type_d1                         ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

always @ ( posedge clk_emif ) begin
    wr_sel_d1           <=   wr_sel ;
    wr_port_d1          <=   wr_port ;
    ex_box_data_ena_d1  <=   ex_box_data_ena ;
end

always @ ( posedge clk_12_5m ) begin
    ex_box_cfg_ena_d1   <=   ex_box_cfg_ena ;
    ex_box_cfg_ena_d2   <=   ex_box_cfg_ena_d1 ;
end

assign  cfg_tpram_sel   =  ( wr_sel_d1 == 1'b1 && wr_port_d1[7:5] == 3'b000 && 
                             wr_port_d1[4:1] == MPU_SLOT + 2'd2 && wr_port_d1[0] == 1'b0 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_12_5m ) begin
    chn_type_d1   <=   chn_type ;
end

always @ ( posedge clk_emif ) begin
    if ( chn_type_d1 == `COM1_TYPE ) begin
        chn_sel   <=   wr_port_d1[4:1] ;
    end
    else begin
        chn_sel   <=   4'd0 ;
    end
end

//----------------------------------------------------------------------------------
// MPU box slot[n] board data momery management instance
//----------------------------------------------------------------------------------
  genvar i;
  generate
  for( i = 0 ; i < 4 ; i = i+1 ) 
  begin : nLSRAM

assign  mpu_data_sel[i] =  ( wr_sel_d1 == 1'b1 && wr_port_d1[7] == 1'b0 && wr_port_d1[6:5] == i && 
                             wr_port_d1[4:1] == MPU_SLOT + 2'd2 && wr_port_d1[0] == 1'b1 ) ? 1'b1 : 1'b0 ;

assign  ex_data_sel[i] =  ( wr_sel_d1 == 1'b1 && wr_port_d1[7] == 1'b1 && wr_port_d1[6:5] == i && 
                               wr_port_d1[0] == 1'b1 && ex_box_data_ena_d1[i] == 1'b1 ) ? 1'b1 : 1'b0 ; 

always @ ( posedge clk_emif ) begin
    if ( mpu_data_sel[i] == 1'b1 || ex_data_sel[i] == 1'b1 ) begin
        data_tpram_sel[i]   <=   1'b1 ;
    end
    else begin
        data_tpram_sel[i]   <=   1'b0 ;
    end
end

assign  ex_cfg_empty[i] =   ex_box_cfg_ena_d2[i] == 1'b1 ?  excmm_ssdu_empty[i] : 1'b1 ;      
assign  ex_cfg_dval[i]  =   ex_box_cfg_ena_d2[i] == 1'b1 ?  excmm_ssdu_dval[i] : 1'b0 ;      

    TYPE1_DMMTX                 U_TYPE1_DMMTX
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .run_cycle                  ( run_cycle                 ),
    .dst_sta_num                ( dst_sta_num               ),
    .chn_type                   ( chn_type_d1               ),
    .master_slave_flag          ( master_slave_flag         ),
    .dst_box_num                ( i                         ),

    .wr_sel                     ( data_tpram_sel[i]         ),
    .chn_sel                    ( chn_sel                   ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),

    .dmm_empty                  ( dmm_empty[i]              ),
    .rd_en                      ( rd_en[i]                  ),
    .tpram_sdu_dval             ( tpram_sdu_dval[i]         ),
    .tpram_sdu_data             ( tpram_sdu_data[i]         )
    );

    SDU16S1                     U_SDU16S1
    (
    .clk_sys                    ( clk_12_5m                 ),
    .rst_sys                    ( rst_12_5m                 ),
   
    .chn_sdu_dval               ( tpram_sdu_dval[i]         ),
    .chn_sdu_data               ( tpram_sdu_data[i]         ),
    .chn_sdu_empty              ( dmm_empty[i]              ),
    .sdu_chn_rden               ( rd_en[i]                  ),

    .fifo_rdreq                 ( ssdu_dmm_rdreq[i]         ),
    .fifo_empty                 ( port_empty[i]             ),
    .fifo_rd_dval               ( port_dval[i]              ),
    .fifo_rd_data               ( port_data[i]              )
    );

  end
  endgenerate

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
    .tpram_sel                  ( cfg_tpram_sel             ),
    .wr_en                      ( wr_en                     ),
    .wr_data                    ( wr_data                   ),

    .master_slave_flag          ( master_slave_flag         ),
    .hot_plug_req               ( hot_plug_req              ),
    .cfg_empty                  ( mpu_cfg_empty             ),
    .rd_en                      ( sdu_chn_rden[8]           ),
    .tpram_sdu_dval             ( mpu_cfg_dval              ),
    .tpram_sdu_data             ( mpu_cfg_data              )
    );

//----------------------------------------------------------------------------------
// 9 - 1 schedule machine instance
//----------------------------------------------------------------------------------
assign  ssdu_dmm_rdreq      =   sdu_chn_rden[3:0] ; 
assign  ssdu_excmm_rdreq    =   sdu_chn_rden[7:4] ; 
assign  chn_sdu_empty       =   { mpu_cfg_empty , ex_cfg_empty , port_empty } ; 
assign  chn_sdu_dval_tmp    =   { mpu_cfg_dval , ex_cfg_dval , port_dval } ;

always @ ( posedge clk_12_5m ) begin
    chn_sdu_dval   <=   chn_sdu_dval_tmp ;
end

always @ ( posedge clk_12_5m ) begin
    case( chn_sdu_dval_tmp )
        9'b000000001   :   chn_sdu_data    <=  port_data[0] ; 
        9'b000000010   :   chn_sdu_data    <=  port_data[1] ; 
        9'b000000100   :   chn_sdu_data    <=  port_data[2] ; 
        9'b000001000   :   chn_sdu_data    <=  port_data[3] ; 
        9'b000010000   :   chn_sdu_data    <=  excmm_ssdu_data0 ; 
        9'b000100000   :   chn_sdu_data    <=  excmm_ssdu_data1 ; 
        9'b001000000   :   chn_sdu_data    <=  excmm_ssdu_data2 ; 
        9'b010000000   :   chn_sdu_data    <=  excmm_ssdu_data3 ;  
        9'b100000000   :   chn_sdu_data    <=  mpu_cfg_data ;  
        default        :   chn_sdu_data    <=  18'h00 ; 
    endcase
end

    SDU9S1                      U_SDU9S1
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

