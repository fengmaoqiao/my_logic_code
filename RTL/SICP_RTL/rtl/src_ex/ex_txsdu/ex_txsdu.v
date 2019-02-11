// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   TXSDU
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
// PURPOSE          :   transmit path schedule machine
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

module EX_TXSDU
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
  
    // control signals
    box_num                     ,   
    slot_num                    , 

    // SLINK connected to COM1
    txsdu_slink_rdreq1          ,   
    slink_txsdu_empty1          ,   
    slink_txsdu_dval1           ,   
    slink_txsdu_data1           ,   
    
    txsdu_slink_rdreq2          ,   
    slink_txsdu_empty2          ,   
    slink_txsdu_dval2           ,   
    slink_txsdu_data2           ,   

    // self configuration 
    wr_self_cfg_dval            ,   
    wr_self_cfg_data            ,   

    // SLINK connected to IO
    ex_txsdu_rdreq              ,   
    slink_txsdu_rdreq0          ,   
    slink_txsdu_rdreq1          ,   
    slink_txsdu_rdreq2          ,   
    slink_txsdu_rdreq3          ,   
    slink_txsdu_rdreq4          ,   
    slink_txsdu_rdreq5          ,   
    slink_txsdu_rdreq6          ,   
    slink_txsdu_rdreq7          ,   
    slink_txsdu_rdreq8          ,   
    slink_txsdu_rdreq9          ,   
    slink_txsdu_rdreq10         ,   
    slink_txsdu_rdreq11         ,   
    slink_txsdu_rdreq12         ,   
    slink_txsdu_rdreq13         ,   
    
    txsdu_ex_dval               ,   
    txsdu_slink_dval0           ,   
    txsdu_slink_dval1           ,   
    txsdu_slink_dval2           ,   
    txsdu_slink_dval3           ,   
    txsdu_slink_dval4           ,   
    txsdu_slink_dval5           ,   
    txsdu_slink_dval6           ,   
    txsdu_slink_dval7           ,   
    txsdu_slink_dval8           ,   
    txsdu_slink_dval9           ,   
    txsdu_slink_dval10          ,   
    txsdu_slink_dval11          ,   
    txsdu_slink_dval12          ,   
    txsdu_slink_dval13          ,   

    txsdu_ex_data               ,   
    txsdu_slink_data0           ,   
    txsdu_slink_data1           ,   
    txsdu_slink_data2           ,   
    txsdu_slink_data3           ,   
    txsdu_slink_data4           ,   
    txsdu_slink_data5           ,   
    txsdu_slink_data6           ,   
    txsdu_slink_data7           ,   
    txsdu_slink_data8           ,   
    txsdu_slink_data9           ,   
    txsdu_slink_data10          ,   
    txsdu_slink_data11          ,   
    txsdu_slink_data12          ,   
    txsdu_slink_data13          ,

    src_id1                     ,
    src_id2                     ,
    dst_id1                     ,
    dst_id2                     ,
    src_port1                   ,
    src_port2                   ,
    dst_port1                   ,
    dst_port2                     
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
input   wire    [3:0]           slot_num                            ;   

input   wire                    slink_txsdu_empty1                  ;   
input   wire                    slink_txsdu_dval1                   ;   
input   wire    [17:0]          slink_txsdu_data1                   ;   
input   wire                    slink_txsdu_empty2                  ;   
input   wire                    slink_txsdu_dval2                   ;   
input   wire    [17:0]          slink_txsdu_data2                   ;

input   wire                    ex_txsdu_rdreq                      ;   
input   wire                    slink_txsdu_rdreq0                  ;   
input   wire                    slink_txsdu_rdreq1                  ;   
input   wire                    slink_txsdu_rdreq2                  ;   
input   wire                    slink_txsdu_rdreq3                  ;   
input   wire                    slink_txsdu_rdreq4                  ;   
input   wire                    slink_txsdu_rdreq5                  ;   
input   wire                    slink_txsdu_rdreq6                  ;   
input   wire                    slink_txsdu_rdreq7                  ;   
input   wire                    slink_txsdu_rdreq8                  ;   
input   wire                    slink_txsdu_rdreq9                  ;   
input   wire                    slink_txsdu_rdreq10                 ;   
input   wire                    slink_txsdu_rdreq11                 ;   
input   wire                    slink_txsdu_rdreq12                 ;   
input   wire                    slink_txsdu_rdreq13                 ; 

// declare output signal
output  wire                    txsdu_slink_rdreq1                  ;   
output  wire                    txsdu_slink_rdreq2                  ;   

output  reg                     wr_self_cfg_dval                    ;   
output  wire    [17:0]          wr_self_cfg_data                    ;   

output  wire                    txsdu_ex_dval                       ;   
output  wire                    txsdu_slink_dval0                   ;   
output  wire                    txsdu_slink_dval1                   ;   
output  wire                    txsdu_slink_dval2                   ;   
output  wire                    txsdu_slink_dval3                   ;   
output  wire                    txsdu_slink_dval4                   ;   
output  wire                    txsdu_slink_dval5                   ;   
output  wire                    txsdu_slink_dval6                   ;   
output  wire                    txsdu_slink_dval7                   ;   
output  wire                    txsdu_slink_dval8                   ;   
output  wire                    txsdu_slink_dval9                   ;   
output  wire                    txsdu_slink_dval10                  ;   
output  wire                    txsdu_slink_dval11                  ;   
output  wire                    txsdu_slink_dval12                  ;   
output  wire                    txsdu_slink_dval13                  ;   
output  wire    [17:0]          txsdu_ex_data                       ;   
output  wire    [17:0]          txsdu_slink_data0                   ;   
output  wire    [17:0]          txsdu_slink_data1                   ;   
output  wire    [17:0]          txsdu_slink_data2                   ;   
output  wire    [17:0]          txsdu_slink_data3                   ;   
output  wire    [17:0]          txsdu_slink_data4                   ;   
output  wire    [17:0]          txsdu_slink_data5                   ;   
output  wire    [17:0]          txsdu_slink_data6                   ;   
output  wire    [17:0]          txsdu_slink_data7                   ;   
output  wire    [17:0]          txsdu_slink_data8                   ;   
output  wire    [17:0]          txsdu_slink_data9                   ;   
output  wire    [17:0]          txsdu_slink_data10                  ;   
output  wire    [17:0]          txsdu_slink_data11                  ;   
output  wire    [17:0]          txsdu_slink_data12                  ;   
output  wire    [17:0]          txsdu_slink_data13                  ;   

input   wire    [31:0]          src_id1                             ;
input   wire    [31:0]          src_id2                             ;
input   wire    [31:0]          dst_id1                             ;
input   wire    [31:0]          dst_id2                             ;

input   wire    [7:0]           src_port1                           ;
input   wire    [7:0]           src_port2                           ;
input   wire    [7:0]           dst_port1                           ;
input   wire    [7:0]           dst_port2                           ;
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            chip_cs                             ;   
wire        [1:0]               chn_sdu_empty                       ;   
wire        [1:0]               chn_sdu_dval                        ;   
wire        [1:0]               sdu_chn_rden                        ;   
wire        [17:0]              chn_sdu_data                        ;   
wire                            ex_tx_dval                          ;   
wire        [17:0]              ex_tx_data                          ;   
wire        [14:0]              wr_sel                              ;   
wire        [14:0]              rd_req                              ;   
wire        [14:0]              rd_dval                             ;   
wire        [17:0]              rd_data     [14:0]                  ;  
wire                            wr_self_cfg_master                  ;   

// reg signal
reg                             tx_dval                             ;   
reg                             tx_dval_d1                          ;   
reg                             tx_dval_d2                          ;   
reg                             data_sop                            ;   
reg                             data_sop_d1                         ;   
reg                             data_sop_d2                         ;   
reg                             data_eop                            ;   
reg                             data_eop_d1                         ;   
reg                             data_eop_d2                         ;   
reg         [17:0]              tx_data                             ;   
reg         [17:0]              tx_data_d1                          ;   
reg         [17:0]              tx_data_d2                          ;   
reg         [7:0]               dest_addr                           ;   
reg         [7:0]               sour_addr                           ;   
reg         [15:0]              pkt_type                            ;   
reg         [15:0]              wr_data     [14:0]  /* synthesis syn_preseve = 1 */ ;   
reg         [14:0]              wr_sop              /* synthesis syn_preseve = 1 */ ;   
reg         [14:0]              wr_eop              /* synthesis syn_preseve = 1 */ ;   
reg         [14:0]              wr_dval             /* synthesis syn_preseve = 1 */ ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
reg         [1:0]               port1_src_addr                      ;
reg         [1:0]               port2_src_addr                      ;

always @( posedge clk_12_5m or negedge rst_12_5m ) begin 
    if( ~rst_12_5m ) begin
         port1_src_addr <= 2'b00;
    end else begin
        if( slink_txsdu_dval1== 1'b1 && slink_txsdu_data1[17] == 1'b1)
         port1_src_addr <= slink_txsdu_data1[1:0];
    end
end

always @( posedge clk_12_5m or negedge rst_12_5m ) begin 
    if( ~rst_12_5m ) begin
         port2_src_addr <= 2'b00;
    end else begin
        if( slink_txsdu_dval2== 1'b1 && slink_txsdu_data2[17] == 1'b1)
         port2_src_addr <= slink_txsdu_data2[1:0];
    end
end

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// 2 - 1 schedule machine
//----------------------------------------------------------------------------------

assign  chip_cs = 1'b1 ;  

assign  chn_sdu_empty   =   { slink_txsdu_empty1 , slink_txsdu_empty2 } ;
assign  chn_sdu_dval    =   { slink_txsdu_dval1 , slink_txsdu_dval2 } ;
assign  chn_sdu_data    =   slink_txsdu_dval1 == 1'b1 ? slink_txsdu_data1 : 
                            slink_txsdu_dval2 ? slink_txsdu_data2 : 18'h00 ;

assign  txsdu_slink_rdreq1  =  sdu_chn_rden[1]  ; 
assign  txsdu_slink_rdreq2  =  sdu_chn_rden[0]  ; 

    SDU2S1                      U_SDU2S1
    (
    .clk_sys                    ( clk_12_5m                 ),
    .rst_sys                    ( rst_12_5m                 ),
   
    .chip_cs                    ( chip_cs                   ),
    .chn_sdu_dval               ( chn_sdu_dval              ),
    .chn_sdu_data               ( chn_sdu_data              ),
    .chn_sdu_empty              ( chn_sdu_empty             ),
    .sdu_chn_rden               ( sdu_chn_rden              ),

    .debug_bus                  (                           )
    );

assign  ex_tx_dval     =   | chn_sdu_dval ;
assign  ex_tx_data     =   chn_sdu_data ;

//----------------------------------------------------------------------------------
// data delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m ) begin
    if( ex_tx_dval == 1'b1 )begin
        tx_dval   <=   1'b1 ;
    end
    else begin
        tx_dval   <=   1'b0 ;
    end
end

always @ ( posedge clk_12_5m ) begin
    tx_dval_d1   <=   tx_dval ;
    tx_dval_d2   <=   tx_dval_d1 ;
end

always @ ( posedge clk_12_5m ) begin
    if( ex_tx_dval == 1'b1 && ex_tx_data[17] == 1'b1 )begin
        data_sop   <=   1'b1 ;
    end
    else begin
        data_sop   <=   1'b0 ;
    end
end

always @ ( posedge clk_12_5m ) begin
    data_sop_d1   <=   data_sop ;
    data_sop_d2   <=   data_sop_d1 ;
end

always @ ( posedge clk_12_5m ) begin
    if( ex_tx_dval == 1'b1 && ex_tx_data[16] == 1'b1 )begin
        data_eop   <=   1'b1 ;
    end
    else begin
        data_eop   <=   1'b0 ;
    end
end

always @ ( posedge clk_12_5m ) begin
    data_eop_d1   <=   data_eop ;
    data_eop_d2   <=   data_eop_d1 ;
end


always @ ( posedge clk_12_5m ) begin
    if( ex_tx_dval == 1'b1 )begin
        tx_data   <=   ex_tx_data ;
    end
    else begin
        tx_data   <=   10'h00 ;
    end
end

always @ ( posedge clk_12_5m ) begin
    tx_data_d1   <=   tx_data ;
    tx_data_d2   <=   tx_data_d1 ;
end

//----------------------------------------------------------------------------------
// DA & SA & TYPE parse
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        dest_addr   <=   8'h00 ;
    end
    else if( ex_tx_dval == 1'b1 && ex_tx_data[17] == 1'b1 )begin
        dest_addr   <=   ex_tx_data[15:8] ;
    end
    else ;
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sour_addr   <=   8'h00 ;
    end
    else if( ex_tx_dval == 1'b1 && ex_tx_data[17] == 1'b1 )begin
        sour_addr   <=   ex_tx_data[7:0] ;
    end
    else ;
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_type   <=   16'h00 ;
    end
    else if( data_sop == 1'b1 ) begin
        pkt_type   <=   ex_tx_data[15:0] ;
    end
    else if( data_eop == 1'b1 ) begin
        pkt_type   <=   16'h00 ;
    end
end

//----------------------------------------------------------------------------------
// self configuration 
//----------------------------------------------------------------------------------
assign  wr_self_cfg_master  = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == slot_num && sour_addr[7] == 1'b1 && pkt_type == `CFG_TYPE ;  

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        wr_self_cfg_dval   <=   1'b0 ;
    end
    else begin
        if( ex_tx_dval == 1'b1 && ex_tx_data[16] == 1'b1 )begin
            wr_self_cfg_dval   <=   1'b0 ;
        end
        else if( data_sop_d2 == 1'b1 && wr_self_cfg_master == 1'b1 )begin
            wr_self_cfg_dval   <=   1'b1 ;
        end
    end
end

assign  wr_self_cfg_data    =   ex_tx_data ;

//----------------------------------------------------------------------------------
// IO data and configuran memory management
//----------------------------------------------------------------------------------
assign  wr_sel[0]  = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:1] == 3'd0 && dest_addr[0] == ~ slot_num[0]
                     && sour_addr[7] == 1'b1 && pkt_type == `CFG_TYPE  ; 

assign  wr_sel[1]  = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd2  && sour_addr[7] == 1'b1  ; 
assign  wr_sel[2]  = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd3  && sour_addr[7] == 1'b1  ; 
assign  wr_sel[3]  = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd4  && sour_addr[7] == 1'b1  ; 
assign  wr_sel[4]  = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd5  && sour_addr[7] == 1'b1  ; 
assign  wr_sel[5]  = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd6  && sour_addr[7] == 1'b1  ; 
assign  wr_sel[6]  = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd7  && sour_addr[7] == 1'b1  ; 
assign  wr_sel[7]  = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd8  && sour_addr[7] == 1'b1  ; 
assign  wr_sel[8]  = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd9  && sour_addr[7] == 1'b1  ; 
assign  wr_sel[9]  = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd10 && sour_addr[7] == 1'b1  ; 
assign  wr_sel[10] = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd11 && sour_addr[7] == 1'b1  ; 
assign  wr_sel[11] = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd12 && sour_addr[7] == 1'b1  ; 
assign  wr_sel[12] = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd13 && sour_addr[7] == 1'b1  ; 
assign  wr_sel[13] = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd14 && sour_addr[7] == 1'b1  ; 
assign  wr_sel[14] = ( dest_addr[6:4] == box_num - 1 ) && dest_addr[3:0] == 4'd15 && sour_addr[7] == 1'b1  ; 

  genvar i ;
  generate
  for( i = 0 ; i < 15 ; i = i+1 ) 
  begin : nIO_CHN

always @ ( posedge clk_12_5m ) begin
    wr_sop[i]   <=   data_sop_d2 ;
    wr_eop[i]   <=   data_eop_d2 ;
    wr_dval[i]  <=   tx_dval_d2 ;
    wr_data[i]  <=   tx_data_d2[15:0] ;
end

    IO_MMTX                     U_IO_MMTX
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),

    .wr_sel                     ( wr_sel[i]                 ),
    .wr_dval                    ( wr_dval[i]                ),
    .wr_sop                     ( wr_sop[i]                 ),
    .wr_eop                     ( wr_eop[i]                 ),
    .wr_data                    ( wr_data[i]                ),

    .rd_req                     ( rd_req[i]                 ),
    .rd_dval                    ( rd_dval[i]                ),
    .rd_data                    ( rd_data[i]                )
    );

  end
  endgenerate

//----------------------------------------------------------------------------------
// IO SLINK interface 
//----------------------------------------------------------------------------------
assign  rd_req[0]   =   ex_txsdu_rdreq  ;                   
assign  rd_req[1]   =   slink_txsdu_rdreq0  ;                   
assign  rd_req[2]   =   slink_txsdu_rdreq1  ;                   
assign  rd_req[3]   =   slink_txsdu_rdreq2  ;                   
assign  rd_req[4]   =   slink_txsdu_rdreq3  ;                   
assign  rd_req[5]   =   slink_txsdu_rdreq4  ;                   
assign  rd_req[6]   =   slink_txsdu_rdreq5  ;                   
assign  rd_req[7]   =   slink_txsdu_rdreq6  ;                   
assign  rd_req[8]   =   slink_txsdu_rdreq7  ;                   
assign  rd_req[9]   =   slink_txsdu_rdreq8  ;                   
assign  rd_req[10]  =   slink_txsdu_rdreq9  ;                   
assign  rd_req[11]  =   slink_txsdu_rdreq10 ;                   
assign  rd_req[12]  =   slink_txsdu_rdreq11 ;                   
assign  rd_req[13]  =   slink_txsdu_rdreq12 ;                   
assign  rd_req[14]  =   slink_txsdu_rdreq13 ;                 

assign  txsdu_ex_dval       =   rd_dval[0]  ;                       
assign  txsdu_slink_dval0   =   rd_dval[1]  ;                       
assign  txsdu_slink_dval1   =   rd_dval[2]  ;                    
assign  txsdu_slink_dval2   =   rd_dval[3]  ;                    
assign  txsdu_slink_dval3   =   rd_dval[4]  ;                    
assign  txsdu_slink_dval4   =   rd_dval[5]  ;                    
assign  txsdu_slink_dval5   =   rd_dval[6]  ;                    
assign  txsdu_slink_dval6   =   rd_dval[7]  ;                    
assign  txsdu_slink_dval7   =   rd_dval[8]  ;                    
assign  txsdu_slink_dval8   =   rd_dval[9]  ;                    
assign  txsdu_slink_dval9   =   rd_dval[10] ;                    
assign  txsdu_slink_dval10  =   rd_dval[11] ;                    
assign  txsdu_slink_dval11  =   rd_dval[12] ;                    
assign  txsdu_slink_dval12  =   rd_dval[13] ;                    
assign  txsdu_slink_dval13  =   rd_dval[14] ;                  
  
assign  txsdu_ex_data       =   rd_data[0]  ;                    
assign  txsdu_slink_data0   =   rd_data[1]  ;                    
assign  txsdu_slink_data1   =   rd_data[2]  ;                    
assign  txsdu_slink_data2   =   rd_data[3]  ;                    
assign  txsdu_slink_data3   =   rd_data[4]  ;                    
assign  txsdu_slink_data4   =   rd_data[5]  ;                    
assign  txsdu_slink_data5   =   rd_data[6]  ;                    
assign  txsdu_slink_data6   =   rd_data[7]  ;                    
assign  txsdu_slink_data7   =   rd_data[8]  ;                    
assign  txsdu_slink_data8   =   rd_data[9]  ;                    
assign  txsdu_slink_data9   =   rd_data[10] ;                    
assign  txsdu_slink_data10  =   rd_data[11] ;                    
assign  txsdu_slink_data11  =   rd_data[12] ;                    
assign  txsdu_slink_data12  =   rd_data[13] ;                    
assign  txsdu_slink_data13  =   rd_data[14] ;                    


endmodule
