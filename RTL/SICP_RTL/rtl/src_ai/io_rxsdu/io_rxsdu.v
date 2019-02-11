// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   IO_RXSDU
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

module IO_RXSDU
    (
    // clock & reset
    clk_100m                    ,   
    rst_100m                    ,   
  
    // SLINK connected to COM1
    rxsdu_slink_rdreq1          ,   
    slink_rxsdu_empty1          ,   
    slink_rxsdu_dval1           ,   
    slink_rxsdu_data1           ,   
    
    rxsdu_slink_rdreq2          ,   
    slink_rxsdu_empty2          ,   
    slink_rxsdu_dval2           ,   
    slink_rxsdu_data2           ,   

    slink_dt_dval               ,   
    slink_cfg_dval              , 
    slink_cfg_data              ,   
    slink_dt_data               ,
    ram_dgd_err
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/


/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_100m                            ;   
input   wire                    rst_100m                            ;   

input   wire                    slink_rxsdu_empty1                  ;   
input   wire                    slink_rxsdu_dval1                   ;   
input   wire    [17:0]          slink_rxsdu_data1                   ;   
input   wire                    slink_rxsdu_empty2                  ;   
input   wire                    slink_rxsdu_dval2                   ;   
input   wire    [17:0]          slink_rxsdu_data2                   ;

// declare output signal
output  wire                    rxsdu_slink_rdreq1                  ;   
output  wire                    rxsdu_slink_rdreq2                  ;   
output  reg                     slink_dt_dval                       ;   
output  reg                     slink_cfg_dval                      ;   
output  wire    [9:0]           slink_dt_data                       ;   
output  wire    [9:0]           slink_cfg_data                      ;   
output  wire                    ram_dgd_err                         ;   
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
wire                            io_tx_dval                          ;   
wire        [17:0]              io_tx_data                          ;   
wire        [17:0]              ram_wr_data                         ;  
wire        [17:0]              ram_rd_data                         ;   
wire                            ram_din_val                         ;   
wire                            ram_dout_val                        ;   
wire        [7:0]               ram_din_data                        ;   
wire        [7:0]               ram_dout_data                       ;   
wire                            din_sop                             ;   
wire                            din_eop                             ;   
wire                            dout_sop                            ;   
wire                            dout_eop                            ;   


// reg signal
reg                             data_sop                            ;  
reg         [13:0]              data_sop_dly                        ;   
reg         [7:0]               dest_addr                           ;   
reg         [7:0]               sour_addr                           ;   
reg         [15:0]              pkt_type                            ;   
reg                             ram_wr_en                           ;   
reg         [9:0]               ram_wr_addr                         ;   
reg         [7:0]               com_sta_hign                        ;   
reg                             ram_empty                           ;   
reg         [9:0]               ram_rd_addr                         ;   


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

assign  chn_sdu_empty   =   { slink_rxsdu_empty1 , slink_rxsdu_empty2 } ;
assign  chn_sdu_dval    =   { slink_rxsdu_dval1 , slink_rxsdu_dval2 } ;
assign  chn_sdu_data    =   slink_rxsdu_dval1 == 1'b1 ? slink_rxsdu_data1 : slink_rxsdu_data2 ;

assign  rxsdu_slink_rdreq1  =  sdu_chn_rden[1]  ; 
assign  rxsdu_slink_rdreq2  =  sdu_chn_rden[0]  ; 

    RX_SDU2S1                   U_RX_SDU2S1
    (
    .clk_sys                    ( clk_100m                  ),
    .rst_sys                    ( rst_100m                  ),
   
    .chip_cs                    ( chip_cs                   ),
    .chn_sdu_dval               ( chn_sdu_dval              ),
    .chn_sdu_data               ( chn_sdu_data              ),
    .chn_sdu_empty              ( chn_sdu_empty             ),
    .sdu_chn_rden               ( sdu_chn_rden              )
    );

assign  io_tx_dval     =   | chn_sdu_dval ;
assign  io_tx_data     =   chn_sdu_data ;

//----------------------------------------------------------------------------------
// data delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        data_sop   <=   1'b0 ;
    end
    else if( io_tx_dval == 1'b1 && io_tx_data[17] == 1'b1 )begin
        data_sop   <=   1'b1 ;
    end
    else begin
        data_sop   <=   1'b0 ;
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        data_sop_dly   <=   14'd0 ;
    end
    else begin
        data_sop_dly   <=   { data_sop_dly[12:0] , data_sop } ;
    end
end

//----------------------------------------------------------------------------------
// DA & SA & TYPE parse
//----------------------------------------------------------------------------------
//always @ ( posedge clk_100m or negedge rst_100m ) begin
//    if( rst_100m == 1'b0 ) begin
//        dest_addr   <=   8'h00 ;
//    end
//    else if( io_tx_dval == 1'b1 && io_tx_data[17] == 1'b1 )begin
//        dest_addr   <=   io_tx_data[7:0] ;
//    end
//end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        sour_addr   <=   8'h00 ;
    end
    else if( data_sop_dly[1] == 1'b1  )begin
        sour_addr   <=   io_tx_data[7:0] ;
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        pkt_type   <=   16'h00 ;
    end
    else begin
        if( data_sop_dly[6] == 1'b1 )begin
            pkt_type[15:8]   <=   io_tx_data[7:0] ;
        end
        else if ( data_sop_dly[7] == 1'b1 ) begin
            pkt_type[7:0]   <=   io_tx_data[7:0] ;
        end
    end
end

//----------------------------------------------------------------------------------
// IO data and cfg data
//----------------------------------------------------------------------------------

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        slink_cfg_dval   <=   1'b0 ;
    end
    else begin
        if ( io_tx_dval == 1'b1 && io_tx_data[16] == 1'b1 ) begin
            slink_cfg_dval   <=   1'b0 ;
        end
        else if ( data_sop_dly[11] == 1'b1 && sour_addr[2] == 1'b1 && pkt_type == `CFG_TYPE ) begin
            slink_cfg_dval   <=   1'b1 ;
        end
    end
end

assign  slink_cfg_data = { data_sop_dly[12] , io_tx_data[16] , io_tx_data[7:0] } ;

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        slink_dt_dval   <=   1'b0 ;
    end
    else begin
        if ( ram_empty == 1'b0 && ram_rd_data[8] == 1'b1 ) begin
            slink_dt_dval   <=   1'b0 ;
        end
        else if ( ram_empty == 1'b0 ) begin
            slink_dt_dval   <=   1'b1 ;
        end
    end
end

assign  slink_dt_data = ram_rd_data[9:0] ;

//----------------------------------------------------------------------------------
// RAM read and write control
//----------------------------------------------------------------------------------
always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        ram_wr_en   <=   1'b0 ;
    end
    else begin
        if ( io_tx_dval == 1'b1 && io_tx_data[16] == 1'b1 ) begin
            ram_wr_en   <=   1'b0 ;
        end
        else if ( data_sop_dly[11] == 1'b1 && sour_addr[2] == 1'b1 && pkt_type == `DATA_TYPE ) begin
            ram_wr_en   <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        ram_wr_addr   <=   10'h00 ;
    end
    else begin
        if ( data_sop_dly[11] == 1'b1 && sour_addr[2] == 1'b1 && pkt_type == `DATA_TYPE ) begin
            ram_wr_addr   <=   10'h00 ;
        end
        else if ( io_tx_dval == 1'b1 ) begin
            ram_wr_addr   <=   ram_wr_addr + 1'b1 ;
        end
    end
end

assign  ram_wr_data = { 8'h00 , data_sop_dly[12] , io_tx_data[16] , io_tx_data[7:0] } ;

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        com_sta_hign   <=   8'h00 ;
    end
    else begin
        if ( ram_wr_addr == 10'd118 ) begin
            com_sta_hign   <=   ram_wr_data[7:0] ;
        end
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        ram_empty   <=   1'b1 ;
    end
    else begin
        if ( ram_empty == 1'b0 && ram_rd_data[8] == 1'b1 ) begin
            ram_empty   <=   1'b1 ;
        end
        else if ( ram_wr_en == 1'b1 && ram_wr_addr == 10'd119 && ram_wr_data[7:0] == 8'h00 && com_sta_hign == 8'h00 ) begin
            ram_empty   <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        ram_rd_addr   <=   10'h00 ;
    end
    else begin
        if ( ram_empty == 1'b1 ) begin
            ram_rd_addr   <=   10'h00 ;
        end
        else begin
            ram_rd_addr   <=   ram_rd_addr + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// LSRAM instance
//----------------------------------------------------------------------------------

    RAM1K18                     U_LSRAM_W10D1024 
    (
    .A_DOUT                     ( ram_rd_data               ), 
    .B_DOUT                     (                           ), 
    .BUSY                       (                           ), 
    .A_CLK                      ( clk_100m                  ), 
    .A_DOUT_CLK                 ( 1'b1                      ), 
    .A_ARST_N                   ( 1'b1                      ), 
    .A_DOUT_EN                  ( 1'b1                      ), // 0 : register holds previous data ; 1 : normal register operation 
    .A_BLK                      ( 3'b111                    ), // 111 : perform read or write operation on port A 
    .A_DOUT_ARST_N              ( 1'b1                      ), 
    .A_DOUT_SRST_N              ( 1'b1                      ), 
    .A_DIN                      ( 18'h00                    ),  
    .A_ADDR                     ( { ram_rd_addr, 4'h0 }     ), // used bits [13:4] , [3:0] to be grounded 
    .A_WEN                      ( 2'b00                     ), // 00 : read operation
    .B_CLK                      ( clk_100m                  ), 
    .B_DOUT_CLK                 ( 1'b1                      ), 
    .B_ARST_N                   ( 1'b1                      ), 
    .B_DOUT_EN                  ( 1'b1                      ), // 0 : register holds previous data ; 1 : normal register operation
    .B_BLK                      ( { ram_wr_en , 2'b11 }     ), // 011 : no operation ; 111 : read or write operation 
    .B_DOUT_ARST_N              ( 1'b0                      ), 
    .B_DOUT_SRST_N              ( 1'b1                      ), 
    .B_DIN                      ( ram_wr_data               ), 
    .B_ADDR                     ( { ram_wr_addr , 4'h0 }    ), // used bits [13:4] , [3:0] to be grounded  
    .B_WEN                      ( 2'b11                     ), // 11 : write[15:0]
    .A_EN                       ( 1'b1                      ), // power down , active low
    .A_DOUT_LAT                 ( 1'b1                      ), // 0 : register operation ; 1 : latch operation 
    .A_WIDTH                    ( 3'b100                    ), // 100: 1k*18 / 1k*16
    .A_WMODE                    ( 1'b1                      ), // 0 : output data port holds the previous value ; 1 : feed-through 
    .B_EN                       ( 1'b1                      ), // power down , active low
    .B_DOUT_LAT                 ( 1'b1                      ), // 0 : register operation ; 1 : latch operation
    .B_WIDTH                    ( 3'b100                    ), // 100: 1k*18 / 1k*16 
    .B_WMODE                    ( 1'b1                      ), // 0 : output data port holds the previous value ; 1 : feed-through 
    .SII_LOCK                   ( 1'b0                      )
    );

assign din_sop   = ram_wr_data[9] && ram_wr_en;
assign din_eop   = ram_wr_data[8] && ram_wr_en;
assign dout_sop  = slink_dt_data[9] && slink_dt_dval;
assign dout_eop  = slink_dt_data[8] && slink_dt_dval;

assign  ram_din_val    = ram_wr_en ;
assign  ram_dout_val   = slink_dt_dval ;
assign  ram_din_data   = ram_wr_data[7:0] ;
assign  ram_dout_data  = slink_dt_data[7:0] ;

    RAMDGDM #(
    .CRC_LEN_L                  ( 10'd0                     ),
    .CRC_LEN_H                  ( 10'd116                   ),
    .FUN_SEL                    ( 1'b0                      ),
    .BIT_WIDTH                  ( 8                         ),
    .RAM_DGD_TYPE               ( 1'b0                      )
    )
    U_RXSDURAM(
    .clk_wr                     ( clk_100m                  ),
    .rst_wr_n                   ( rst_100m                  ),
    .clk_rd                     ( clk_100m                  ),
    .rst_rd_n                   ( rst_100m                  ),

    .slink_prd_err              ( 1'b0                      ),
    .din_sop                    ( din_sop                   ),
    .din_eop                    ( din_eop                   ),
    .dout_sop                   ( dout_sop                  ),
    .dout_eop                   ( dout_eop                  ),
    .ram_din_val                ( ram_din_val               ),
    .ram_dout_val               ( ram_dout_val              ),
    .ram_din_data               ( ram_din_data              ),
    .ram_dout_data              ( ram_dout_data             ),
 
    .ram_dgd_err                ( ram_dgd_err               )
    
    );

endmodule
