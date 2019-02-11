// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   EX_CMM
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
// PURPOSE          :   The configuration Memory Management of Extetion box   
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

module  EX_CMM
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    clk_emif                    ,   
    rst_emif                    ,   

    // mpu box configuration 
    dst_sta_num                 ,   
    master_slave_flag           ,
    ex1_hot_plug_req            ,   
    ex2_hot_plug_req            ,   
    ex3_hot_plug_req            ,   
    ex4_hot_plug_req            ,   

    // write port 
    ex1_cfg_wr_sel              ,   
    ex2_cfg_wr_sel              ,   
    ex3_cfg_wr_sel              ,   
    ex4_cfg_wr_sel              ,   
    ex1_cfg_slot                ,   
    ex2_cfg_slot                ,   
    ex3_cfg_slot                ,   
    ex4_cfg_slot                ,   
    ex1_cfg_wr_en               ,   
    ex2_cfg_wr_en               ,   
    ex3_cfg_wr_en               ,   
    ex4_cfg_wr_en               ,   
    ex1_cfg_wr_data             ,   
    ex2_cfg_wr_data             ,   
    ex3_cfg_wr_data             ,   
    ex4_cfg_wr_data             ,   

    // read port
    ssdu_excmm_rdreq0           ,   
    ssdu_excmm_rdreq1           ,   
    ssdu_excmm_rdreq2           ,   
    ssdu_excmm_rdreq3           ,   
    excmm_ssdu_empty            ,   
    excmm_ssdu_dval             ,   
    excmm_ssdu_data0            ,   
    excmm_ssdu_data1            ,   
    excmm_ssdu_data2            ,   
    excmm_ssdu_data3               
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

input   wire        [7:0]       dst_sta_num                         ;   
input   wire        [7:0]       master_slave_flag                   ;   
input   wire        [15:0]      ex1_hot_plug_req                    ;   
input   wire        [15:0]      ex2_hot_plug_req                    ;   
input   wire        [15:0]      ex3_hot_plug_req                    ;   
input   wire        [15:0]      ex4_hot_plug_req                    ;   
input   wire                    ex1_cfg_wr_sel                      ;   
input   wire                    ex2_cfg_wr_sel                      ;   
input   wire                    ex3_cfg_wr_sel                      ;   
input   wire                    ex4_cfg_wr_sel                      ;   
input   wire        [3:0]       ex1_cfg_slot                        ;   
input   wire        [3:0]       ex2_cfg_slot                        ;   
input   wire        [3:0]       ex3_cfg_slot                        ;   
input   wire        [3:0]       ex4_cfg_slot                        ;   
input   wire                    ex1_cfg_wr_en                       ;   
input   wire                    ex2_cfg_wr_en                       ;   
input   wire                    ex3_cfg_wr_en                       ;   
input   wire                    ex4_cfg_wr_en                       ;   
input   wire        [17:0]      ex1_cfg_wr_data                     ;   
input   wire        [17:0]      ex2_cfg_wr_data                     ;   
input   wire        [17:0]      ex3_cfg_wr_data                     ;   
input   wire        [17:0]      ex4_cfg_wr_data                     ;   
input   wire        [3:0]       ssdu_excmm_rdreq0                   ;   
input   wire        [3:0]       ssdu_excmm_rdreq1                   ;   
input   wire        [3:0]       ssdu_excmm_rdreq2                   ;   
input   wire        [3:0]       ssdu_excmm_rdreq3                   ;   

// declare output signal
output  wire        [3:0]       excmm_ssdu_empty                    ;   
output  wire        [3:0]       excmm_ssdu_dval                     ;   
output  wire        [17:0]      excmm_ssdu_data0                    ;   
output  wire        [17:0]      excmm_ssdu_data1                    ;   
output  wire        [17:0]      excmm_ssdu_data2                    ;   
output  wire        [17:0]      excmm_ssdu_data3                    ;  

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [3:0]               exbox_sel                           ;
wire        [3:0]               chn_sel             [3:0]           ;
wire        [17:0]              excmm_ssdu_data     [3:0]           ;
wire        [3:0]               ssdu_excmm_rdreq                    ; 
wire        [15:0]              ex_hot_plug_req     [3:0]           ;
wire        [3:0]               wr_en                               ;  
wire        [17:0]              wr_data             [3:0]           ;

// reg signal

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign  exbox_sel[0]  =  ex1_cfg_wr_sel ;
assign  exbox_sel[1]  =  ex2_cfg_wr_sel ;
assign  exbox_sel[2]  =  ex3_cfg_wr_sel ;
assign  exbox_sel[3]  =  ex4_cfg_wr_sel ;

assign  chn_sel[0]    =   ex1_cfg_slot ;    
assign  chn_sel[1]    =   ex2_cfg_slot ;    
assign  chn_sel[2]    =   ex3_cfg_slot ;    
assign  chn_sel[3]    =   ex4_cfg_slot ;  

assign  wr_en[0]      =   ex1_cfg_wr_en ;    
assign  wr_en[1]      =   ex2_cfg_wr_en ;    
assign  wr_en[2]      =   ex3_cfg_wr_en ;    
assign  wr_en[3]      =   ex4_cfg_wr_en ;    

assign  wr_data[0]    =   ex1_cfg_wr_data ;   
assign  wr_data[1]    =   ex2_cfg_wr_data ;   
assign  wr_data[2]    =   ex3_cfg_wr_data ;   
assign  wr_data[3]    =   ex4_cfg_wr_data ;   

assign  ssdu_excmm_rdreq[0] = ( ssdu_excmm_rdreq3[0] == 1'b1 || ssdu_excmm_rdreq2[0] == 1'b1 || 
                                ssdu_excmm_rdreq1[0] == 1'b1 || ssdu_excmm_rdreq0[0] == 1'b1 ) ? 1'b1 : 1'b0 ; 
assign  ssdu_excmm_rdreq[1] = ( ssdu_excmm_rdreq3[1] == 1'b1 || ssdu_excmm_rdreq2[1] == 1'b1 || 
                                ssdu_excmm_rdreq1[1] == 1'b1 || ssdu_excmm_rdreq0[1] == 1'b1 ) ? 1'b1 : 1'b0 ; 
assign  ssdu_excmm_rdreq[2] = ( ssdu_excmm_rdreq3[2] == 1'b1 || ssdu_excmm_rdreq2[2] == 1'b1 || 
                                ssdu_excmm_rdreq1[2] == 1'b1 || ssdu_excmm_rdreq0[2] == 1'b1 ) ? 1'b1 : 1'b0 ; 
assign  ssdu_excmm_rdreq[3] = ( ssdu_excmm_rdreq3[3] == 1'b1 || ssdu_excmm_rdreq2[3] == 1'b1 || 
                                ssdu_excmm_rdreq1[3] == 1'b1 || ssdu_excmm_rdreq0[3] == 1'b1 ) ? 1'b1 : 1'b0 ; 

//----------------------------------------------------------------------------------
//  Extetion box EX_CMM instance
//----------------------------------------------------------------------------------
  genvar i;
  generate
  for( i = 0 ; i < 4 ; i = i+1 ) 
  begin : nexbox

    SEX_CMM                     #
    (
    .DST_BOX_NUM                ( i                         )
    )
    U_SEX_CMM
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),
    .clk_emif                   ( clk_emif                  ),
    .rst_emif                   ( rst_emif                  ),

    .dst_sta_num                ( dst_sta_num               ),
    .ex_box_sel                 ( exbox_sel[i]              ),
    .chn_sel                    ( chn_sel[i]                ),
    .wr_en                      ( wr_en[i]                  ),
    .wr_data                    ( wr_data[i]                ),

    .master_slave_flag          ( master_slave_flag         ),
    .ssdu_excmm_rdreq           ( ssdu_excmm_rdreq[i]       ),
    .hot_plug_req               ( ex_hot_plug_req[i]        ),
    .excmm_ssdu_empty           ( excmm_ssdu_empty[i]       ),
    .excmm_ssdu_dval            ( excmm_ssdu_dval[i]        ),
    .excmm_ssdu_data            ( excmm_ssdu_data[i]        )
    );

  end
  endgenerate

assign  ex_hot_plug_req[0]  =   ex1_hot_plug_req ;
assign  ex_hot_plug_req[1]  =   ex2_hot_plug_req ;
assign  ex_hot_plug_req[2]  =   ex3_hot_plug_req ;
assign  ex_hot_plug_req[3]  =   ex4_hot_plug_req ;

assign  excmm_ssdu_data0    =   excmm_ssdu_data[0] ; 
assign  excmm_ssdu_data1    =   excmm_ssdu_data[1] ; 
assign  excmm_ssdu_data2    =   excmm_ssdu_data[2] ; 
assign  excmm_ssdu_data3    =   excmm_ssdu_data[3] ; 

endmodule

