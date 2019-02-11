// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   RXSDU
// CREATE DATE      :   2017-09-26
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-26  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   receive path schedule machine
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

module RXSDU
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    
    // status feedback frame interface
    rxsdu_sfm_rdreq             ,   
    sfm_rxsdu_empty             ,   
    sfm_rxsdu_dval              ,   
    sfm_rxsdu_data              ,  

    // SLINK connected to IO
    rxsdu_slink_rdreq0          ,   
    rxsdu_slink_rdreq1          ,   
    rxsdu_slink_rdreq2          ,   
    rxsdu_slink_rdreq3          ,   
    
    slink_rxsdu_empty0          ,   
    slink_rxsdu_empty1          ,   
    slink_rxsdu_empty2          ,   
    slink_rxsdu_empty3          ,   

    slink_rxsdu_dval0           ,   
    slink_rxsdu_dval1           ,   
    slink_rxsdu_dval2           ,   
    slink_rxsdu_dval3           ,   
 
    slink_rxsdu_data0           ,   
    slink_rxsdu_data1           ,   
    slink_rxsdu_data2           ,   
    slink_rxsdu_data3           ,   

    // slink connected to COMI   
    slink_rxsdu_rdreq0          ,   
    slink_rxsdu_rdreq1          ,   
    rxsdu_slink_dval0           ,   
    rxsdu_slink_data0           ,   
    rxsdu_slink_dval1           ,   
    rxsdu_slink_data1              
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

input   wire                    sfm_rxsdu_empty                     ;   
input   wire                    sfm_rxsdu_dval                      ;   
input   wire    [17:0]          sfm_rxsdu_data                      ;   

input   wire                    slink_rxsdu_empty0                  ;   
input   wire                    slink_rxsdu_empty1                  ;   
input   wire                    slink_rxsdu_empty2                  ;   
input   wire                    slink_rxsdu_empty3                  ;   

input   wire                    slink_rxsdu_dval0                   ;   
input   wire                    slink_rxsdu_dval1                   ;   
input   wire                    slink_rxsdu_dval2                   ;   
input   wire                    slink_rxsdu_dval3                   ;   
 
input   wire    [17:0]          slink_rxsdu_data0                   ;   
input   wire    [17:0]          slink_rxsdu_data1                   ;   
input   wire    [17:0]          slink_rxsdu_data2                   ;   
input   wire    [17:0]          slink_rxsdu_data3                   ;   

input   wire                    slink_rxsdu_rdreq0                  ;   
input   wire                    slink_rxsdu_rdreq1                  ;   

// declare output signal
output  wire                    rxsdu_sfm_rdreq                     ;   

output  wire                    rxsdu_slink_rdreq0                  ;   
output  wire                    rxsdu_slink_rdreq1                  ;   
output  wire                    rxsdu_slink_rdreq2                  ;   
output  wire                    rxsdu_slink_rdreq3                  ;   

output  wire                    rxsdu_slink_dval0                   ;   
output  wire    [17:0]          rxsdu_slink_data0                   ;   
output  wire                    rxsdu_slink_dval1                   ;   
output  wire    [17:0]          rxsdu_slink_data1                   ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [4:0]               chn_sdu_empty                       ;   
wire        [4:0]               chn_sdu_dval_tmp                    ;   
wire        [4:0]               sdu_chn_rden                        ;   
wire        [3:0]               slink_rxsdu_sop                     ;   
wire        [17:0]              slink_rxsdu_data0_tmp               ;   
wire        [17:0]              slink_rxsdu_data1_tmp               ;   
wire        [17:0]              slink_rxsdu_data2_tmp               ;   
wire        [17:0]              slink_rxsdu_data3_tmp               ;   

// reg signal
reg         [4:0]               chn_sdu_dval                        ;   
reg         [17:0]              chn_sdu_data                        ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign  chn_sdu_empty   =    { sfm_rxsdu_empty       ,
                               slink_rxsdu_empty0    ,   
                               slink_rxsdu_empty1    ,   
                               slink_rxsdu_empty2    ,   
                               slink_rxsdu_empty3    } ;

assign  chn_sdu_dval_tmp =   { sfm_rxsdu_dval        ,
                               slink_rxsdu_dval0     ,   
                               slink_rxsdu_dval1     ,   
                               slink_rxsdu_dval2     ,   
                               slink_rxsdu_dval3     } ;

always @( clk_12_5m ) begin
    chn_sdu_dval <= chn_sdu_dval_tmp ;
end

always @( clk_12_5m ) begin
    case( chn_sdu_dval_tmp )
        16'b0000000000000001   :   chn_sdu_data    =  slink_rxsdu_data3_tmp  ;  
        16'b0000000000000010   :   chn_sdu_data    =  slink_rxsdu_data2_tmp  ;  
        16'b0000000000000100   :   chn_sdu_data    =  slink_rxsdu_data1_tmp  ;  
        16'b0000000000001000   :   chn_sdu_data    =  slink_rxsdu_data0_tmp  ;  
        16'b0000000000010000   :   chn_sdu_data    =  sfm_rxsdu_data     ;  
        default                :   chn_sdu_data    =  18'h00 ; 
    endcase
end

assign  slink_rxsdu_data0_tmp   =  slink_rxsdu_data0 ;
assign  slink_rxsdu_data1_tmp   =  slink_rxsdu_data1 ;
assign  slink_rxsdu_data2_tmp   =  slink_rxsdu_data2 ;
assign  slink_rxsdu_data3_tmp   =  slink_rxsdu_data3 ;

//assign  slink_rxsdu_data0_tmp   = ( card_type != `COM1_TYPE && slink_rxsdu_sop[0] == 1'b1 ) ? 18'h200ff : slink_rxsdu_data0 ;
//assign  slink_rxsdu_data1_tmp   = ( card_type != `COM1_TYPE && slink_rxsdu_sop[1] == 1'b1 ) ? 18'h210ff : slink_rxsdu_data1 ;
//assign  slink_rxsdu_data2_tmp   = ( card_type != `COM1_TYPE && slink_rxsdu_sop[2] == 1'b1 ) ? 18'h220ff : slink_rxsdu_data2 ;
//assign  slink_rxsdu_data3_tmp   = ( card_type != `COM1_TYPE && slink_rxsdu_sop[3] == 1'b1 ) ? 18'h230ff : slink_rxsdu_data3 ;

assign  slink_rxsdu_sop[0]  =  slink_rxsdu_data0[17] == 1'b1 && slink_rxsdu_dval0 == 1'b1 ;
assign  slink_rxsdu_sop[1]  =  slink_rxsdu_data1[17] == 1'b1 && slink_rxsdu_dval1 == 1'b1 ;
assign  slink_rxsdu_sop[2]  =  slink_rxsdu_data2[17] == 1'b1 && slink_rxsdu_dval2 == 1'b1 ;
assign  slink_rxsdu_sop[3]  =  slink_rxsdu_data3[17] == 1'b1 && slink_rxsdu_dval3 == 1'b1 ;

assign  rxsdu_sfm_rdreq     =  sdu_chn_rden[4]  ; 
assign  rxsdu_slink_rdreq0  =  sdu_chn_rden[3]  ; 
assign  rxsdu_slink_rdreq1  =  sdu_chn_rden[2]  ; 
assign  rxsdu_slink_rdreq2  =  sdu_chn_rden[1]  ; 
assign  rxsdu_slink_rdreq3  =  sdu_chn_rden[0]  ; 

//----------------------------------------------------------------------------------
// 5 - 1 schedule machine instance
//----------------------------------------------------------------------------------
    COM_SDU5S1                  U_SDU5S1
    (
    .clk_sys                    ( clk_12_5m                 ),
    .rst_sys                    ( rst_12_5m                 ),
   
    .chn_sdu_dval               ( chn_sdu_dval              ),
    .chn_sdu_data               ( chn_sdu_data              ),
    .chn_sdu_empty              ( chn_sdu_empty             ),
    .sdu_chn_rden               ( sdu_chn_rden              ),

    .fifo_rdreq0                ( slink_rxsdu_rdreq0        ),
    .fifo_rd_dval0              ( rxsdu_slink_dval0         ),
    .fifo_rd_data0              ( rxsdu_slink_data0         ),
    .fifo_rdreq1                ( slink_rxsdu_rdreq1        ),
    .fifo_rd_dval1              ( rxsdu_slink_dval1         ),
    .fifo_rd_data1              ( rxsdu_slink_data1         )
    );

endmodule
