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

module EX_RXSDU
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,  

    box_num                     ,
    card_id                     ,

    // status feedback frame interface
    rxsdu_sfm_rdreq             ,   
    sfm_rxsdu_empty             ,   
    sfm_rxsdu_dval              ,   
    sfm_rxsdu_data              ,  

    // SLINK connected to IO
    rxsdu_ex_rdreq              ,   
    rxsdu_slink_rdreq0          ,   
    rxsdu_slink_rdreq1          ,   
    rxsdu_slink_rdreq2          ,   
    rxsdu_slink_rdreq3          ,   
    rxsdu_slink_rdreq4          ,   
    rxsdu_slink_rdreq5          ,   
    rxsdu_slink_rdreq6          ,   
    rxsdu_slink_rdreq7          ,   
    rxsdu_slink_rdreq8          ,   
    rxsdu_slink_rdreq9          ,   
    rxsdu_slink_rdreq10         ,   
    rxsdu_slink_rdreq11         ,   
    rxsdu_slink_rdreq12         ,   
    rxsdu_slink_rdreq13         ,   
    
    ex_rxsdu_empty              ,   
    slink_rxsdu_empty0          ,   
    slink_rxsdu_empty1          ,   
    slink_rxsdu_empty2          ,   
    slink_rxsdu_empty3          ,   
    slink_rxsdu_empty4          ,   
    slink_rxsdu_empty5          ,   
    slink_rxsdu_empty6          ,   
    slink_rxsdu_empty7          ,   
    slink_rxsdu_empty8          ,   
    slink_rxsdu_empty9          ,   
    slink_rxsdu_empty10         ,   
    slink_rxsdu_empty11         ,   
    slink_rxsdu_empty12         ,   
    slink_rxsdu_empty13         ,   

    ex_rxsdu_dval               ,   
    slink_rxsdu_dval0           ,   
    slink_rxsdu_dval1           ,   
    slink_rxsdu_dval2           ,   
    slink_rxsdu_dval3           ,   
    slink_rxsdu_dval4           ,   
    slink_rxsdu_dval5           ,   
    slink_rxsdu_dval6           ,   
    slink_rxsdu_dval7           ,   
    slink_rxsdu_dval8           ,   
    slink_rxsdu_dval9           ,   
    slink_rxsdu_dval10          ,   
    slink_rxsdu_dval11          ,   
    slink_rxsdu_dval12          ,   
    slink_rxsdu_dval13          ,   

    ex_rxsdu_data               ,   
    slink_rxsdu_data0           ,   
    slink_rxsdu_data1           ,   
    slink_rxsdu_data2           ,   
    slink_rxsdu_data3           ,   
    slink_rxsdu_data4           ,   
    slink_rxsdu_data5           ,   
    slink_rxsdu_data6           ,   
    slink_rxsdu_data7           ,   
    slink_rxsdu_data8           ,   
    slink_rxsdu_data9           ,   
    slink_rxsdu_data10          ,   
    slink_rxsdu_data11          ,   
    slink_rxsdu_data12          ,   
    slink_rxsdu_data13          ,   

    // slink connected to COMI   
    slink_rxsdu_rdreq0          ,   
    slink_rxsdu_rdreq1          ,   
    rxsdu_slink_dval0           ,   
    rxsdu_slink_data0           ,   
    rxsdu_slink_dval1           ,   
    rxsdu_slink_data1           ,

    src_id1                     ,
    src_id2                     ,
    dst_id1                     ,
    dst_id2                     ,

    src_port1                   ,
    src_port2                   ,
    dst_port1                   ,
    dst_port2                   ,
    cfg_en         
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

input   wire    [2:0]           box_num                             ;   
input   wire                    sfm_rxsdu_empty                     ;   
input   wire                    sfm_rxsdu_dval                      ;   
input   wire    [17:0]          sfm_rxsdu_data                      ;   
input   wire                    ex_rxsdu_empty                      ;   
input   wire                    slink_rxsdu_empty0                  ;   
input   wire                    slink_rxsdu_empty1                  ;   
input   wire                    slink_rxsdu_empty2                  ;   
input   wire                    slink_rxsdu_empty3                  ;   
input   wire                    slink_rxsdu_empty4                  ;   
input   wire                    slink_rxsdu_empty5                  ;   
input   wire                    slink_rxsdu_empty6                  ;   
input   wire                    slink_rxsdu_empty7                  ;   
input   wire                    slink_rxsdu_empty8                  ;   
input   wire                    slink_rxsdu_empty9                  ;   
input   wire                    slink_rxsdu_empty10                 ;   
input   wire                    slink_rxsdu_empty11                 ;   
input   wire                    slink_rxsdu_empty12                 ;   
input   wire                    slink_rxsdu_empty13                 ;   
input   wire                    ex_rxsdu_dval                       ;   
input   wire                    slink_rxsdu_dval0                   ;   
input   wire                    slink_rxsdu_dval1                   ;   
input   wire                    slink_rxsdu_dval2                   ;   
input   wire                    slink_rxsdu_dval3                   ;   
input   wire                    slink_rxsdu_dval4                   ;   
input   wire                    slink_rxsdu_dval5                   ;   
input   wire                    slink_rxsdu_dval6                   ;   
input   wire                    slink_rxsdu_dval7                   ;   
input   wire                    slink_rxsdu_dval8                   ;   
input   wire                    slink_rxsdu_dval9                   ;   
input   wire                    slink_rxsdu_dval10                  ;   
input   wire                    slink_rxsdu_dval11                  ;   
input   wire                    slink_rxsdu_dval12                  ;   
input   wire                    slink_rxsdu_dval13                  ;   
input   wire    [17:0]          ex_rxsdu_data                       ;   
input   wire    [17:0]          slink_rxsdu_data0                   ;   
input   wire    [17:0]          slink_rxsdu_data1                   ;   
input   wire    [17:0]          slink_rxsdu_data2                   ;   
input   wire    [17:0]          slink_rxsdu_data3                   ;   
input   wire    [17:0]          slink_rxsdu_data4                   ;   
input   wire    [17:0]          slink_rxsdu_data5                   ;   
input   wire    [17:0]          slink_rxsdu_data6                   ;   
input   wire    [17:0]          slink_rxsdu_data7                   ;   
input   wire    [17:0]          slink_rxsdu_data8                   ;   
input   wire    [17:0]          slink_rxsdu_data9                   ;   
input   wire    [17:0]          slink_rxsdu_data10                  ;   
input   wire    [17:0]          slink_rxsdu_data11                  ;   
input   wire    [17:0]          slink_rxsdu_data12                  ;   
input   wire    [17:0]          slink_rxsdu_data13                  ;   

input   wire                    slink_rxsdu_rdreq0                  ;   
input   wire                    slink_rxsdu_rdreq1                  ;   

// declare output signal
output  wire                    rxsdu_sfm_rdreq                     ;   

output  wire                    rxsdu_ex_rdreq                      ;   
output  wire                    rxsdu_slink_rdreq0                  ;   
output  wire                    rxsdu_slink_rdreq1                  ;   
output  wire                    rxsdu_slink_rdreq2                  ;   
output  wire                    rxsdu_slink_rdreq3                  ;   
output  wire                    rxsdu_slink_rdreq4                  ;   
output  wire                    rxsdu_slink_rdreq5                  ;   
output  wire                    rxsdu_slink_rdreq6                  ;   
output  wire                    rxsdu_slink_rdreq7                  ;   
output  wire                    rxsdu_slink_rdreq8                  ;   
output  wire                    rxsdu_slink_rdreq9                  ;   
output  wire                    rxsdu_slink_rdreq10                 ;   
output  wire                    rxsdu_slink_rdreq11                 ;   
output  wire                    rxsdu_slink_rdreq12                 ;   
output  wire                    rxsdu_slink_rdreq13                 ; 

output  wire                    rxsdu_slink_dval0                   ;   
output  wire    [17:0]          rxsdu_slink_data0                   ;   
output  wire                    rxsdu_slink_dval1                   ;   
output  wire    [17:0]          rxsdu_slink_data1                   ; 
input   wire    [31:0]          card_id                               ; 

input   wire    [31:0]          src_id1                             ;
input   wire    [31:0]          src_id2                             ;
input   wire    [31:0]          dst_id1                             ;
input   wire    [31:0]          dst_id2                             ;

input   wire    [7:0]           src_port1                           ;
input   wire    [7:0]           src_port2                           ;
input   wire    [7:0]           dst_port1                           ;
input   wire    [7:0]           dst_port2                           ;

input   wire                    cfg_en                              ;

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [15:0]              chn_sdu_empty                       ;   
wire        [15:0]              sdu_chn_rden                        ;  
wire                            rxsdu_slink_data_sop0               ;   
wire        [17:0]              rxsdu_slink_data_tmp0               ;   
wire                            rxsdu_slink_data_sop1               ;   
wire        [17:0]              rxsdu_slink_data_tmp1               ;   
wire        [15:0]              chn_sdu_dval_tmp                    ;  
wire        [13:0]              slink_rxsdu_sop                     ;  
wire        [17:0]              slink_data0_tmp                     ;   
wire        [17:0]              slink_data1_tmp                     ;   
wire        [17:0]              slink_data2_tmp                     ;   
wire        [17:0]              slink_data3_tmp                     ;   
wire        [17:0]              slink_data4_tmp                     ;   
wire        [17:0]              slink_data5_tmp                     ;   
wire        [17:0]              slink_data6_tmp                     ;   
wire        [17:0]              slink_data7_tmp                     ;   
wire        [17:0]              slink_data8_tmp                     ;   
wire        [17:0]              slink_data9_tmp                     ;   
wire        [17:0]              slink_data10_tmp                    ;   
wire        [17:0]              slink_data11_tmp                    ;   
wire        [17:0]              slink_data12_tmp                    ;   
wire        [17:0]              slink_data13_tmp                    ;   

// reg signal
reg         [15:0]              chn_sdu_dval                        ;  
reg         [17:0]              chn_sdu_data                        ;  

wire        [2:0]               box_num_cfg                         ;
reg         [2:0]               box_num_up                          ;

assign      box_num_cfg =   card_id[7:5]                            ;

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
always @(posedge clk_12_5m or negedge rst_12_5m) begin
  if( ~rst_12_5m ) begin
      box_num_up <= box_num ;
  end else begin
    if( cfg_en )
      box_num_up <= box_num_cfg ;
    else
      box_num_up <= box_num;
  end
end
/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//assign  rxsdu_slink_data0     =   rxsdu_slink_data_sop0 == 1'b1 ? { 2'b10 , rxsdu_slink_data_tmp0[15] , box_num  ,
assign  rxsdu_slink_data0     =   rxsdu_slink_data_sop0 == 1'b1 ? { 2'b10 , rxsdu_slink_data_tmp0[15] , box_num_up  ,
                                  rxsdu_slink_data_tmp0[11:1] , 1'b0 } : rxsdu_slink_data_tmp0 ;
assign  rxsdu_slink_data_sop0 =   ( rxsdu_slink_dval0 == 1'b1 && rxsdu_slink_data_tmp0[17] == 1'b1 ) ? 1'b1 : 1'b0 ;

//assign  rxsdu_slink_data1     =   rxsdu_slink_data_sop1 == 1'b1 ? { 2'b10 , rxsdu_slink_data_tmp1[15] , box_num  , 
assign  rxsdu_slink_data1     =   rxsdu_slink_data_sop1 == 1'b1 ? { 2'b10 , rxsdu_slink_data_tmp1[15] , box_num_up  , 
                                  rxsdu_slink_data_tmp1[11:1] , 1'b1 } : rxsdu_slink_data_tmp1 ;
assign  rxsdu_slink_data_sop1 =   ( rxsdu_slink_dval1 == 1'b1 && rxsdu_slink_data_tmp1[17] == 1'b1 ) ? 1'b1 : 1'b0 ;

assign  chn_sdu_empty   =   { sfm_rxsdu_empty        ,
                              ex_rxsdu_empty         ,
                              slink_rxsdu_empty0     ,   
                              slink_rxsdu_empty1     ,   
                              slink_rxsdu_empty2     ,   
                              slink_rxsdu_empty3     ,   
                              slink_rxsdu_empty4     ,   
                              slink_rxsdu_empty5     ,   
                              slink_rxsdu_empty6     ,   
                              slink_rxsdu_empty7     ,   
                              slink_rxsdu_empty8     ,   
                              slink_rxsdu_empty9     ,   
                              slink_rxsdu_empty10    ,   
                              slink_rxsdu_empty11    ,   
                              slink_rxsdu_empty12    ,   
                              slink_rxsdu_empty13    } ;

assign  chn_sdu_dval_tmp =  { sfm_rxsdu_dval        ,
                              ex_rxsdu_dval         ,
                              slink_rxsdu_dval0     ,   
                              slink_rxsdu_dval1     ,   
                              slink_rxsdu_dval2     ,   
                              slink_rxsdu_dval3     ,   
                              slink_rxsdu_dval4     ,   
                              slink_rxsdu_dval5     ,   
                              slink_rxsdu_dval6     ,   
                              slink_rxsdu_dval7     ,   
                              slink_rxsdu_dval8     ,   
                              slink_rxsdu_dval9     ,   
                              slink_rxsdu_dval10    ,   
                              slink_rxsdu_dval11    ,   
                              slink_rxsdu_dval12    ,   
                              slink_rxsdu_dval13    } ;

assign  slink_rxsdu_sop[0]   =  slink_rxsdu_data0[17]  == 1'b1 && slink_rxsdu_dval0  == 1'b1 ;
assign  slink_rxsdu_sop[1]   =  slink_rxsdu_data1[17]  == 1'b1 && slink_rxsdu_dval1  == 1'b1 ;
assign  slink_rxsdu_sop[2]   =  slink_rxsdu_data2[17]  == 1'b1 && slink_rxsdu_dval2  == 1'b1 ;
assign  slink_rxsdu_sop[3]   =  slink_rxsdu_data3[17]  == 1'b1 && slink_rxsdu_dval3  == 1'b1 ;
assign  slink_rxsdu_sop[4]   =  slink_rxsdu_data4[17]  == 1'b1 && slink_rxsdu_dval4  == 1'b1 ;
assign  slink_rxsdu_sop[5]   =  slink_rxsdu_data5[17]  == 1'b1 && slink_rxsdu_dval5  == 1'b1 ;
assign  slink_rxsdu_sop[6]   =  slink_rxsdu_data6[17]  == 1'b1 && slink_rxsdu_dval6  == 1'b1 ;
assign  slink_rxsdu_sop[7]   =  slink_rxsdu_data7[17]  == 1'b1 && slink_rxsdu_dval7  == 1'b1 ;
assign  slink_rxsdu_sop[8]   =  slink_rxsdu_data8[17]  == 1'b1 && slink_rxsdu_dval8  == 1'b1 ;
assign  slink_rxsdu_sop[9]   =  slink_rxsdu_data9[17]  == 1'b1 && slink_rxsdu_dval9  == 1'b1 ;
assign  slink_rxsdu_sop[10]  =  slink_rxsdu_data10[17] == 1'b1 && slink_rxsdu_dval10 == 1'b1 ;
assign  slink_rxsdu_sop[11]  =  slink_rxsdu_data11[17] == 1'b1 && slink_rxsdu_dval11 == 1'b1 ;
assign  slink_rxsdu_sop[12]  =  slink_rxsdu_data12[17] == 1'b1 && slink_rxsdu_dval12 == 1'b1 ;
assign  slink_rxsdu_sop[13]  =  slink_rxsdu_data13[17] == 1'b1 && slink_rxsdu_dval13 == 1'b1 ;

assign  slink_data0_tmp  = slink_rxsdu_sop[0]  == 1'b1 ? { 2'b10 , slink_rxsdu_data0[15]  , 3'd0 , 4'h2 , 8'hff } : slink_rxsdu_data0  ;
assign  slink_data1_tmp  = slink_rxsdu_sop[1]  == 1'b1 ? { 2'b10 , slink_rxsdu_data1[15]  , 3'd0 , 4'h3 , 8'hff } : slink_rxsdu_data1  ;
assign  slink_data2_tmp  = slink_rxsdu_sop[2]  == 1'b1 ? { 2'b10 , slink_rxsdu_data2[15]  , 3'd0 , 4'h4 , 8'hff } : slink_rxsdu_data2  ;
assign  slink_data3_tmp  = slink_rxsdu_sop[3]  == 1'b1 ? { 2'b10 , slink_rxsdu_data3[15]  , 3'd0 , 4'h5 , 8'hff } : slink_rxsdu_data3  ;
assign  slink_data4_tmp  = slink_rxsdu_sop[4]  == 1'b1 ? { 2'b10 , slink_rxsdu_data4[15]  , 3'd0 , 4'h6 , 8'hff } : slink_rxsdu_data4  ;
assign  slink_data5_tmp  = slink_rxsdu_sop[5]  == 1'b1 ? { 2'b10 , slink_rxsdu_data5[15]  , 3'd0 , 4'h7 , 8'hff } : slink_rxsdu_data5  ;
assign  slink_data6_tmp  = slink_rxsdu_sop[6]  == 1'b1 ? { 2'b10 , slink_rxsdu_data6[15]  , 3'd0 , 4'h8 , 8'hff } : slink_rxsdu_data6  ;
assign  slink_data7_tmp  = slink_rxsdu_sop[7]  == 1'b1 ? { 2'b10 , slink_rxsdu_data7[15]  , 3'd0 , 4'h9 , 8'hff } : slink_rxsdu_data7  ;
assign  slink_data8_tmp  = slink_rxsdu_sop[8]  == 1'b1 ? { 2'b10 , slink_rxsdu_data8[15]  , 3'd0 , 4'ha , 8'hff } : slink_rxsdu_data8  ;
assign  slink_data9_tmp  = slink_rxsdu_sop[9]  == 1'b1 ? { 2'b10 , slink_rxsdu_data9[15]  , 3'd0 , 4'hb , 8'hff } : slink_rxsdu_data9  ;
assign  slink_data10_tmp = slink_rxsdu_sop[10] == 1'b1 ? { 2'b10 , slink_rxsdu_data10[15] , 3'd0 , 4'hc , 8'hff } : slink_rxsdu_data10 ;
assign  slink_data11_tmp = slink_rxsdu_sop[11] == 1'b1 ? { 2'b10 , slink_rxsdu_data11[15] , 3'd0 , 4'hd , 8'hff } : slink_rxsdu_data11 ;
assign  slink_data12_tmp = slink_rxsdu_sop[12] == 1'b1 ? { 2'b10 , slink_rxsdu_data12[15] , 3'd0 , 4'he , 8'hff } : slink_rxsdu_data12 ;
assign  slink_data13_tmp = slink_rxsdu_sop[13] == 1'b1 ? { 2'b10 , slink_rxsdu_data13[15] , 3'd0 , 4'hf , 8'hff } : slink_rxsdu_data13 ;

always @ ( posedge clk_12_5m ) begin
    chn_sdu_dval   <=   chn_sdu_dval_tmp ;
end

always @ ( posedge clk_12_5m ) begin
    case( chn_sdu_dval_tmp )
        16'b0000000000000001   :   chn_sdu_data    <=  slink_data13_tmp ; 
        16'b0000000000000010   :   chn_sdu_data    <=  slink_data12_tmp ; 
        16'b0000000000000100   :   chn_sdu_data    <=  slink_data11_tmp ; 
        16'b0000000000001000   :   chn_sdu_data    <=  slink_data10_tmp ; 
        16'b0000000000010000   :   chn_sdu_data    <=  slink_data9_tmp  ; 
        16'b0000000000100000   :   chn_sdu_data    <=  slink_data8_tmp  ; 
        16'b0000000001000000   :   chn_sdu_data    <=  slink_data7_tmp  ; 
        16'b0000000010000000   :   chn_sdu_data    <=  slink_data6_tmp  ;  
        16'b0000000100000000   :   chn_sdu_data    <=  slink_data5_tmp  ;  
        16'b0000001000000000   :   chn_sdu_data    <=  slink_data4_tmp  ;  
        16'b0000010000000000   :   chn_sdu_data    <=  slink_data3_tmp  ;  
        16'b0000100000000000   :   chn_sdu_data    <=  slink_data2_tmp  ;  
        16'b0001000000000000   :   chn_sdu_data    <=  slink_data1_tmp  ;  
        16'b0010000000000000   :   chn_sdu_data    <=  slink_data0_tmp  ;  
        16'b0100000000000000   :   chn_sdu_data    <=  ex_rxsdu_data    ;  
        16'b1000000000000000   :   chn_sdu_data    <=  sfm_rxsdu_data   ;  
        default                :   chn_sdu_data    <=  18'h00     ; 
    endcase
end

assign  rxsdu_sfm_rdreq      =  sdu_chn_rden[15] ; 
assign  rxsdu_ex_rdreq       =  sdu_chn_rden[14] ; 
assign  rxsdu_slink_rdreq0   =  sdu_chn_rden[13] ; 
assign  rxsdu_slink_rdreq1   =  sdu_chn_rden[12] ; 
assign  rxsdu_slink_rdreq2   =  sdu_chn_rden[11] ; 
assign  rxsdu_slink_rdreq3   =  sdu_chn_rden[10] ; 
assign  rxsdu_slink_rdreq4   =  sdu_chn_rden[9]  ; 
assign  rxsdu_slink_rdreq5   =  sdu_chn_rden[8]  ; 
assign  rxsdu_slink_rdreq6   =  sdu_chn_rden[7]  ; 
assign  rxsdu_slink_rdreq7   =  sdu_chn_rden[6]  ; 
assign  rxsdu_slink_rdreq8   =  sdu_chn_rden[5]  ; 
assign  rxsdu_slink_rdreq9   =  sdu_chn_rden[4]  ; 
assign  rxsdu_slink_rdreq10  =  sdu_chn_rden[3]  ; 
assign  rxsdu_slink_rdreq11  =  sdu_chn_rden[2]  ; 
assign  rxsdu_slink_rdreq12  =  sdu_chn_rden[1]  ; 
assign  rxsdu_slink_rdreq13  =  sdu_chn_rden[0]  ; 

//----------------------------------------------------------------------------------
// 16 - 1 schedule machine instance
//----------------------------------------------------------------------------------
    EX_SDU16S1                  U_SDU16S1
    (
    .clk_sys                    ( clk_12_5m                 ),
    .rst_sys                    ( rst_12_5m                 ),
   
    .chn_sdu_dval               ( chn_sdu_dval              ),
    .chn_sdu_data               ( chn_sdu_data              ),
    .chn_sdu_empty              ( chn_sdu_empty             ),
    .sdu_chn_rden               ( sdu_chn_rden              ),

    .fifo_rdreq0                ( slink_rxsdu_rdreq0        ),
    .fifo_rd_dval0              ( rxsdu_slink_dval0         ),
    .fifo_rd_data0              ( rxsdu_slink_data_tmp0     ),
    .fifo_rdreq1                ( slink_rxsdu_rdreq1        ),
    .fifo_rd_dval1              ( rxsdu_slink_dval1         ),
    .fifo_rd_data1              ( rxsdu_slink_data_tmp1     )
    );

endmodule
