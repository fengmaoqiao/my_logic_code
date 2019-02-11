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

module TXSDU
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
  
    // address signals
    port1_dst_addr              ,   
    port2_dst_addr              ,   
    port3_dst_addr              ,   
    port4_dst_addr              ,   
    self_slot_num               ,
    self_box_num                ,


    // SLINK connected to IO
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
    slink_txsdu_rdreq0          ,   
    slink_txsdu_rdreq1          ,   
    slink_txsdu_rdreq2          ,   
    slink_txsdu_rdreq3          ,   
    
    txsdu_slink_dval0           ,   
    txsdu_slink_dval1           ,   
    txsdu_slink_dval2           ,   
    txsdu_slink_dval3           ,   

    txsdu_slink_data0           ,   
    txsdu_slink_data1           ,   
    txsdu_slink_data2           ,   
    txsdu_slink_data3             
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

input   wire    [17:0]          port1_dst_addr                      ;   
input   wire    [17:0]          port2_dst_addr                      ;   
input   wire    [17:0]          port3_dst_addr                      ;   
input   wire    [17:0]          port4_dst_addr                      ;   
input   wire    [4:0]           self_slot_num                       ;   
input   wire    [2:0]           self_box_num                        ;

input   wire                    slink_txsdu_empty1                  ;   
input   wire                    slink_txsdu_dval1                   ;   
input   wire    [17:0]          slink_txsdu_data1                   ;   
input   wire                    slink_txsdu_empty2                  ;   
input   wire                    slink_txsdu_dval2                   ;   
input   wire    [17:0]          slink_txsdu_data2                   ;   

input   wire                    slink_txsdu_rdreq0                  ;   
input   wire                    slink_txsdu_rdreq1                  ;   
input   wire                    slink_txsdu_rdreq2                  ;   
input   wire                    slink_txsdu_rdreq3                  ;   

// declare output signal
output  wire                    txsdu_slink_rdreq1                  ;   
output  wire                    txsdu_slink_rdreq2                  ;   

output  reg                     wr_self_cfg_dval                    ;   
output  wire    [17:0]          wr_self_cfg_data                    ;   

output  wire                    txsdu_slink_dval0                   ;   
output  wire                    txsdu_slink_dval1                   ;   
output  wire                    txsdu_slink_dval2                   ;   
output  wire                    txsdu_slink_dval3                   ;   
  
output  wire    [17:0]          txsdu_slink_data0                   ;   
output  wire    [17:0]          txsdu_slink_data1                   ;   
output  wire    [17:0]          txsdu_slink_data2                   ;   
output  wire    [17:0]          txsdu_slink_data3                   ;   

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
wire        [3:0]               wr_sel_tmp                          ;   
wire        [3:0]               rd_req                              ;   
wire        [3:0]               rd_dval                             ;   
wire        [17:0]              rd_data     [3:0]                   ;  
wire        [17:0]              destin_port [3:0]                   ;
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
reg         [23:0]              dest_addr                           ;   
reg         [7:0]               sour_addr                           ;   
reg         [15:0]              pkt_type                            ;   
reg         [15:0]              wr_data     [3:0]   /* synthesis syn_preserve = 1 */ ;   
reg         [3:0]               wr_sop              /* synthesis syn_preserve = 1 */ ;   
reg         [3:0]               wr_eop              /* synthesis syn_preserve = 1 */ ;   
reg         [3:0]               wr_dval             /* synthesis syn_preserve = 1 */ ;   
reg         [3:0]               wr_sel                              ;  
reg         [3:0]               wr_sel_tmp1                         ;   

reg                             sop_flag                            ;   
reg                             sop_flag_d1                         ;
reg   [10:0]                    pkt_cnt                             ;   
reg   [15:0]                    run_cycle_source                    ;   
wire                            self_addr_ok                        ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

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
    if( ex_tx_dval == 1'b1 ) begin
        tx_dval   <=   1'b1 ;
    end
    else begin
        tx_dval   <=   1'b0 ;
    end
end

always @ ( posedge clk_12_5m ) begin
    tx_dval_d1   <=   tx_dval ;
    tx_dval_d2   <=   tx_dval_d1 ;
    sop_flag_d1  <=   sop_flag ;
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
        tx_data   <=   18'h00 ;
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
        sop_flag   <=   1'b0 ;
    end
    else if( ex_tx_dval == 1'b1 && ex_tx_data[17] == 1'b1 ) begin
        sop_flag   <=   1'b1 ;
    end
    else if( ex_tx_dval == 1'b1 && ex_tx_data[16] == 1'b1 ) begin
        sop_flag   <=   1'b0 ;
    end
    else ;
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_cnt   <=   11'h0 ;
    end
    else if( ex_tx_dval == 1'b1 && sop_flag == 1'b1 ) begin
        pkt_cnt   <=   pkt_cnt + 1'b1;
    end
    else if( sop_flag == 1'b0 ) begin
        pkt_cnt   <=   11'h0 ;
    end
    else ;
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        dest_addr[23:8]   <=   16'h00 ;
    end
    else if( ex_tx_dval == 1'b1 && ex_tx_data[17] == 1'b1 )begin
        dest_addr[23:8]   <=   ex_tx_data[15:0] ;
    end
    else ;
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        dest_addr[7:0]   <=   8'h00 ;
    end
    else if( ex_tx_dval == 1'b1 && data_sop == 1'b1 )begin
        dest_addr[7:0]   <=   ex_tx_data[15:8] ;
    end
    else ;
end

//sa addr 23~16 bit
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sour_addr   <=   8'h00 ;
    end
    else if( ex_tx_dval == 1'b1 && data_sop == 1'b1 )begin
        sour_addr   <=   ex_tx_data[7:0] ;
    end
    else ;
end

//the run cycle of source
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_type   <=   16'h00 ;
    end
    else if( pkt_cnt == 11'd3 && ex_tx_dval == 1'b1)begin
        pkt_type   <=   ex_tx_data[15:0] ;
    end
    else ;
end

assign destin_port[0] = port1_dst_addr;
assign destin_port[1] = port2_dst_addr;
assign destin_port[2] = port3_dst_addr;
assign destin_port[3] = port4_dst_addr;


//----------------------------------------------------------------------------------
// self configuration 
//----------------------------------------------------------------------------------
assign self_addr_ok = (sop_flag_d1 == 1'b1)&& ({self_box_num,self_slot_num} == dest_addr[9:2]);
assign wr_self_cfg_master  = self_addr_ok && sour_addr[2] == 1'b1 && pkt_type == `CFG_TYPE ;//if for com && master && cfg data

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
//send master and slave data to external board
assign  wr_sel_tmp[0]  = (dest_addr[9:7] == port1_dst_addr[9:7]); //&& sour_addr[2] == 1'b1
assign  wr_sel_tmp[1]  = (dest_addr[9:7] == port2_dst_addr[9:7]); //&& sour_addr[2] == 1'b1
assign  wr_sel_tmp[2]  = (dest_addr[9:7] == port3_dst_addr[9:7]); //&& sour_addr[2] == 1'b1
assign  wr_sel_tmp[3]  = (dest_addr[9:7] == port4_dst_addr[9:7]); //&& sour_addr[2] == 1'b1

//assign  wr_sel[0]  = ( card_type == `COM3_TYPE ) ? dest_addr[7] == 1'b0 : wr_sel_tmp[0] ; 
//assign  wr_sel[1]  = ( card_type == `COM3_TYPE ) ? dest_addr[7] == 1'b0 : wr_sel_tmp[1] ; 
//assign  wr_sel[2]  = ( card_type == `COM3_TYPE ) ? dest_addr[7] == 1'b0 : wr_sel_tmp[2] ; 
//assign  wr_sel[3]  = ( card_type == `COM3_TYPE ) ? dest_addr[7] == 1'b0 : wr_sel_tmp[3] ; 

  genvar i ;
  generate
  for( i = 0 ; i < 4 ; i = i+1 ) 
  begin : nIO_CHN

always @ ( posedge clk_12_5m ) begin
//    if ( card_type == `COM3_TYPE ) begin
//        wr_sel_tmp1[i]   <=   ~ dest_addr[7] ;
//    end
//    else if ( card_type == `COM2_TYPE && dest_addr[5:4] == i ) begin
//        wr_sel_tmp1[i]   <=   1'b1 ;
//    end
//    else begin
        wr_sel_tmp1[i]   <=   wr_sel_tmp[i] ;
//    end
end

always @ ( posedge clk_12_5m ) begin
    wr_sel[i]   <=   wr_sel_tmp1[i] ;
end

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

    .destin_port                ( destin_port[i]            ),
    .self_slot_num              ( self_slot_num             ),
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
// data 
//----------------------------------------------------------------------------------
assign  rd_req[0]   =   slink_txsdu_rdreq0  ;                   
assign  rd_req[1]   =   slink_txsdu_rdreq1  ;                   
assign  rd_req[2]   =   slink_txsdu_rdreq2  ;                   
assign  rd_req[3]   =   slink_txsdu_rdreq3  ;                   

assign  txsdu_slink_dval0   =   rd_dval[0] ;        
assign  txsdu_slink_dval1   =   rd_dval[1] ;                    
assign  txsdu_slink_dval2   =   rd_dval[2] ;                    
assign  txsdu_slink_dval3   =   rd_dval[3] ;                    
 
assign  txsdu_slink_data0   =   rd_data[0] ;                    
assign  txsdu_slink_data1   =   rd_data[1] ;                    
assign  txsdu_slink_data2   =   rd_data[2] ;                    
assign  txsdu_slink_data3   =   rd_data[3] ;  

endmodule
