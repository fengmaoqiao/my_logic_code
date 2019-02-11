// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   TYPE2_MMRX
// CREATE DATE      :   2017-08-28
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-28  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   memory management of TYPE2 recive data path
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

module  TYPE2_MMRX
    (
    clk_100m                    ,   
    rst_100m                    , 

    // connect to selfm module
    rd_dmm_empty                ,

    // connect to EMIF module
    rd_sel                      ,   
    rd_port                     ,   
    rd_addr                     ,   
    rd_data                     ,   

    // these signals from slink protocol stack
    slink_mm_empty              ,
    slink_mmrx_dval             ,   
    slink_mmrx_data             ,
    mmrx_slink_rdreq            ,

    // state frame 
    sta_dval                    ,   
    sta_data                    ,   
   
    hot_plug_req                ,   
    mm_delay_err             
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   BASE0_ADDR  =   10'd000 ;  
parameter   BASE1_ADDR  =   10'd512 ;  

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_100m                            ;   
input   wire                    rst_100m                            ; 

input   wire                    rd_sel                              ;   
input   wire        [1:0]       rd_port                             ;   
input   wire        [8:0]       rd_addr                             ;   
input   wire                    slink_mm_empty                      ;   
input   wire                    slink_mmrx_dval                     ;   
input   wire        [17:0]      slink_mmrx_data                     ;   

// declare output signal
output  reg         [17:0]      rd_data                             ;   
output  reg                     sta_dval                            ;   
output  reg         [17:0]      sta_data                            ;   
output  wire                    mmrx_slink_rdreq                    ;  
output  reg         [3:0]       rd_dmm_empty                        ;
output  wire                    mm_delay_err                        ;  
output  reg                     hot_plug_req                        ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [17:0]              wr_data                             ;
wire        [17:0]              tpram_rd_data   [1:0]               ;   
wire                            wr_en                               ;   
wire        [1:0]               tpram_wr_en                         ; 
wire        [3:0]               wr_finish                           ;   
wire                            pfifo_sop                           ;   
wire                            pfifo_eop                           ;   
wire        [15:0]              pfifo_wrdata                        ;   
wire                            sta_dval_tmp                        ;   
wire        [17:0]              sta_data_tmp                        ;   
wire                            new_sop_d2                          ;   

// reg signal
reg         [7:0]               dest_addr                           ;   
reg         [15:0]              pkt_type                            ;  
reg                             new_sop                             ;   
reg         [1:0]               new_sop_d1                          ;   
reg                             new_sop_d3                          ;   
reg                             wr_en_flag                          ;   
reg         [9:0]               wr_addr                             ;   
reg                             mmrx_slink_rdreq_tmp                ;  
reg                             pfifo_wren                          ; 
reg         [3:0]               rd_port_sel                         ;   
reg         [3:0]               rd_port_sel_d1                      ;   
reg         [9:0]               tpram_rd_addr   [1:0]               ;   
reg                             data_sop                            ;   
reg         [15:0]              sour_addr                           ;   
reg         [13:0]              data_sop_dly                        ;
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
assign  mm_delay_err = 1'b0 ;

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// read request
//----------------------------------------------------------------------------------
assign mmrx_slink_rdreq = ( slink_mm_empty == 1'b0 && mmrx_slink_rdreq_tmp == 1'b1 ) ? 1'b1 : 1'b0 ; 

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        mmrx_slink_rdreq_tmp   <=   1'b1 ;
    end
    else begin
        if( rd_sel == 1'b0 ) begin
            mmrx_slink_rdreq_tmp   <=   1'b1 ;
        end
        else if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[17] == 1'b1 && slink_mmrx_data[15] == 1'b0 )begin
            if( rd_sel == 1'b1 && rd_port == slink_mmrx_data[13:12] ) begin
                mmrx_slink_rdreq_tmp   <=   1'b0 ;
            end
            else begin
                mmrx_slink_rdreq_tmp   <=   1'b1 ;
            end
        end
    end
end

//----------------------------------------------------------------------------------
// DA & SA & TYPE parse
//----------------------------------------------------------------------------------
//----------------------------------------------------------------------------------
// data delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        data_sop   <=   1'b0 ;
    end
    else if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[17] == 1'b1 )begin
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

//
//always @ ( posedge clk_100m or negedge rst_100m ) begin
//    if( rst_100m == 1'b0 ) begin
//        sour_addr   <=   16'd0 ;
//    end
//    else if( data_sop_dly[2] == 1'b1  )begin
//        sour_addr   <=   slink_mmrx_data ;
//    end
//end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        dest_addr   <=   8'h00 ;
    end
    else begin
        if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[17] == 1'b1 )begin
            dest_addr   <=   slink_mmrx_data[15:8] ;
        end
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        pkt_type   <=   16'h00 ;
    end
    else begin
        if( data_sop_dly[4] == 1'b1 )begin
            pkt_type   <=   slink_mmrx_data[15:0] ;
        end
    end
end

//----------------------------------------------------------------------------------
// state frame pfifo control
//----------------------------------------------------------------------------------
assign  pfifo_sop   =   new_sop_d2 ;
assign  pfifo_eop   =   ( slink_mmrx_dval == 1'b1 && slink_mmrx_data[16] == 1'b1 ) ? 1'b1 : 1'b0 ; 
assign  pfifo_wrdata =  new_sop_d2 == 1'b1 ? { 8'h00 , dest_addr } : slink_mmrx_data ;

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        pfifo_wren   <=   1'b0 ;
    end
    else begin
        if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[16] == 1'b1 ) begin
            pfifo_wren   <=   1'b0 ;
        end
        else if ( new_sop_d1 == 2'b01 && pkt_type == `STA_TYPE ) begin
            pfifo_wren   <=   1'b1 ;
        end
    end
end

assign  sta_dval_tmp = pfifo_wren ;
assign  sta_data_tmp = { pfifo_sop , pfifo_eop , pfifo_wrdata } ;

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        hot_plug_req  <=   1'b0 ;
    end
    else begin
        if ( sta_dval == 1'b0 ) begin
            hot_plug_req  <=   1'b0 ;
        end
        else if ( new_sop_d3 == 1'b1 && slink_mmrx_data[15] == 1'b1 ) begin
            hot_plug_req  <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_100m ) begin
    sta_dval   <=   sta_dval_tmp ;
    sta_data   <=   sta_data_tmp ;
end

//----------------------------------------------------------------------------------
// write control
//----------------------------------------------------------------------------------
always @ ( posedge clk_100m ) begin
    if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[17] == 1'b1 )begin
        new_sop   <=   1'b1 ;
    end
    else begin
        new_sop   <=   1'b0 ;
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        new_sop_d1   <=   2'b00 ;
    end
    else begin
        if( slink_mmrx_dval == 1'b1 ) begin
            if ( slink_mmrx_data[17] == 1'b1 )begin
                new_sop_d1   <=   2'b00 ;
            end
            else if ( new_sop_d1 == 2'b11 ) begin
                new_sop_d1   <=   new_sop_d1 ;
            end
            else begin
                new_sop_d1   <=   new_sop_d1 + 1'b1 ;
            end
        end
    end
end

assign  new_sop_d2  =   ( new_sop_d1 == 2'b10 ) ? 1'b1 : 1'b0 ; 

always @ ( posedge clk_100m ) begin
    new_sop_d3   <=   new_sop_d2 ;
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        wr_en_flag   <=   1'b0 ;
    end
    else begin
        if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[16] == 1'b1 )begin
            wr_en_flag   <=   1'b0 ;
        end
        else if( new_sop_d2 == 1'b1 && pkt_type == `DATA_TYPE ) begin
            wr_en_flag   <=   1'b1 ;
        end
    end
end

assign  wr_en = ( wr_en_flag == 1'b1 && slink_mmrx_dval == 1'b1 ) ? 1'b1 : 1'b0  ;

assign  tpram_wr_en[0] = ( wr_en == 1'b1 && dest_addr[5] == 1'b0 ) ? 1'b1 : 1'b0 ;
assign  tpram_wr_en[1] = ( wr_en == 1'b1 && dest_addr[5] == 1'b1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        wr_addr   <=   10'h00 ;
    end
    else begin
        if( new_sop_d2 == 1'b1 && pkt_type == `DATA_TYPE ) begin
            if( dest_addr[4] == 1'b0 ) begin
                wr_addr <=   BASE0_ADDR ;
            end
            else begin
                wr_addr <=   BASE1_ADDR ;
            end
        end
        else if( wr_en == 1'b1 ) begin
            wr_addr   <=   wr_addr + 1'b1 ;
        end
    end
end

assign  wr_data   =   slink_mmrx_data ;

//----------------------------------------------------------------------------------
// empty generator
//----------------------------------------------------------------------------------
genvar j ;
generate
for( j = 0 ; j < 4 ; j = j+1 ) 
begin : nIOCHN

assign  wr_finish[j] =   ( wr_en == 1'b1 && wr_data[16] == 1'b1 && dest_addr[5:4] == j ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_100m ) begin
    if( rd_sel == 1'b1 && rd_port == j ) begin
        rd_port_sel[j]  <=   1'b1 ;
    end
    else begin
        rd_port_sel[j]  <=   1'b0 ;
    end
end

always @ ( posedge clk_100m ) begin
    rd_port_sel_d1[j]  <=   rd_port_sel[j] ;
end

end
endgenerate

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        rd_dmm_empty[0] <= 1'b1 ;
    end
    else begin
        if( rd_port_sel[0] == 1'b1 && tpram_rd_data[0][16] == 1'b1 ) begin          
            rd_dmm_empty[0] <= 1'b1 ;
        end
        else if( wr_finish[0] == 1'b1 ) begin
            rd_dmm_empty[0] <= 1'b0 ;
        end
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        rd_dmm_empty[1] <= 1'b1 ;
    end
    else begin
        if( rd_port_sel[1] == 1'b1 && tpram_rd_data[0][16] == 1'b1 ) begin          
            rd_dmm_empty[1] <= 1'b1 ;
        end
        else if( wr_finish[1] == 1'b1 ) begin
            rd_dmm_empty[1] <= 1'b0 ;
        end
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        rd_dmm_empty[2] <= 1'b1 ;
    end
    else begin
        if( rd_port_sel[2] == 1'b1 && tpram_rd_data[1][16] == 1'b1 ) begin          
            rd_dmm_empty[2] <= 1'b1 ;
        end
        else if( wr_finish[2] == 1'b1 ) begin
            rd_dmm_empty[2] <= 1'b0 ;
        end
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        rd_dmm_empty[3] <= 1'b1 ;
    end
    else begin
        if( rd_port_sel[3] == 1'b1 && tpram_rd_data[1][16] == 1'b1 ) begin          
            rd_dmm_empty[3] <= 1'b1 ;
        end
        else if( wr_finish[3] == 1'b1 ) begin
            rd_dmm_empty[3] <= 1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// read control
//----------------------------------------------------------------------------------

always @ ( posedge clk_100m ) begin
    if( rd_port_sel[0] == 1'b1 ) begin
        tpram_rd_addr[0]  <=   { 1'b0 , rd_addr } ;
    end
    else if ( rd_port_sel[1] == 1'b1 ) begin
        tpram_rd_addr[0]  <=   rd_addr + BASE1_ADDR ;
    end
    else begin
        tpram_rd_addr[0]  <=   10'h00 ;
    end
end

always @ ( posedge clk_100m ) begin
    if( rd_port_sel[2] == 1'b1 ) begin
        tpram_rd_addr[1]  <=   { 1'b0 , rd_addr } ;
    end
    else if ( rd_port_sel[3] == 1'b1 ) begin
        tpram_rd_addr[1]  <=   rd_addr + BASE1_ADDR ;
    end
    else begin
        tpram_rd_addr[1]  <=   10'h00 ;
    end
end

always @ ( posedge clk_100m ) begin
    if( | rd_port_sel_d1[1:0] == 1'b1 ) begin
        rd_data  <=   tpram_rd_data[0] ;
    end
    else begin
        rd_data  <=   tpram_rd_data[1] ;
    end
end

//----------------------------------------------------------------------------------
// LSRAM instance  
//----------------------------------------------------------------------------------

  genvar i ;
  generate
  for( i = 0 ; i < 2 ; i = i+1 ) 
  begin : nLSRAM

    RAM1K18                     U1_LSRAM_W18D1024 
    (
    .A_DOUT                     ( tpram_rd_data[i]          ), 
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
    .A_ADDR                     ( { tpram_rd_addr[i], 4'h0 }), // used bits [13:4] , [3:0] to be grounded 
    .A_WEN                      ( 2'b00                     ), // 00 : read operation
    .B_CLK                      ( clk_100m                  ), 
    .B_DOUT_CLK                 ( 1'b1                      ), 
    .B_ARST_N                   ( 1'b1                      ), 
    .B_DOUT_EN                  ( 1'b1                      ), // 0 : register holds previous data ; 1 : normal register operation
    .B_BLK                      ( { tpram_wr_en[i] , 2'b11 }), // 011 : no operation ; 111 : read or write operation 
    .B_DOUT_ARST_N              ( 1'b0                      ), 
    .B_DOUT_SRST_N              ( 1'b1                      ), 
    .B_DIN                      ( wr_data                   ), 
    .B_ADDR                     ( { wr_addr[9:0], 4'h0 }    ), // used bits [13:4] , [3:0] to be grounded  
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

  end
  endgenerate


endmodule

