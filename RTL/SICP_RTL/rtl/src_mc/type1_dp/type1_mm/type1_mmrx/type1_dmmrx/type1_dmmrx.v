// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   TYPE1_DMMRX
// CREATE DATE      :   2017-09-09
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-09  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   Data memory management of TYPE1 recive data path
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

module  TYPE1_DMMRX
    (
    clk_100m                    ,   
    rst_100m                    , 

    // write port
    ex_box_num                  ,
    wr_en                       ,   
    wr_addr                     ,   
    wr_data                     , 

    // read port
    rr_sel                      ,   
    rd_sel                      ,   
    rd_port                     ,   
    rd_addr                     ,   
    rd_port_sel                 ,   
    rd_data_tmp                 
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   MPU_SLOT = 4'd0 ; 
parameter   EX_NUM   = 3'b000 ;

parameter   BASE0_ADDR  =   10'd000 ;  
parameter   BASE1_ADDR  =   10'd064 ;  
parameter   BASE2_ADDR  =   10'd128 ;  
parameter   BASE3_ADDR  =   10'd192 ;  
parameter   BASE4_ADDR  =   10'd256 ;  
parameter   BASE5_ADDR  =   10'd320 ;  
parameter   BASE6_ADDR  =   10'd384 ;  
parameter   BASE7_ADDR  =   10'd448 ;  
parameter   BASE8_ADDR  =   10'd512 ;  
parameter   BASE9_ADDR  =   10'd576 ;  
parameter   BASEA_ADDR  =   10'd640 ;  
parameter   BASEB_ADDR  =   10'd704 ;  
parameter   BASEC_ADDR  =   10'd768 ;  
parameter   BASED_ADDR  =   10'd832 ;  
parameter   BASEE_ADDR  =   10'd896 ;  
parameter   BASEF_ADDR  =   10'd960 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_100m                            ;   
input   wire                    rst_100m                            ; 

input   wire    [1:0]           ex_box_num                          ;   
input   wire                    wr_en                               ;   
input   wire    [9:0]           wr_addr                             ;   
input   wire    [17:0]          wr_data                             ;   
input   wire                    rr_sel                              ;   
input   wire                    rd_sel                              ;   
input   wire    [6:0]           rd_port                             ;   
input   wire    [8:0]           rd_addr                             ;   

// declare output signal
output  reg                     rd_port_sel                         ;   
output  wire    [17:0]          rd_data_tmp                         ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            mpu_rd_sel                          ;   
wire                            ex_rd_sel                           ;   
wire                            wr_tpram_en                         ;   
wire        [9:0]               tpram_rd_addr                       ;   

// reg signal
reg         [3:0]               tpram_chn_sel                       ;   
reg                             rd_port_sel_tmp                     ;  
reg         [9:0]               base_addr                           ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

// write enable generator
assign  wr_tpram_en = ( wr_en == 1'b1 && ex_box_num == EX_NUM ) ? 1'b1 : 1'b0 ;

// read selection generator
assign  mpu_rd_sel  = ( rd_sel == 1'b1 && rd_port[6] == 1'b0 && rd_port[5:4] == EX_NUM && rd_port[3:0] == MPU_SLOT + 2'd2 ) ? 1'b1 : 1'b0 ; 
assign  ex_rd_sel   = ( rd_sel == 1'b1 && rd_port[6] == 1'b1 && rd_port[5:4] == EX_NUM && rr_sel == 1'b1 ) ? 1'b1 : 1'b0 ; 

always @ ( posedge clk_100m ) begin
    if( mpu_rd_sel == 1'b1 || ex_rd_sel == 1'b1 ) begin
        rd_port_sel_tmp  <=   1'b1 ;
    end
    else begin
        rd_port_sel_tmp  <=   1'b0 ;
    end
end

always @ ( posedge clk_100m ) begin
    rd_port_sel  <=   rd_port_sel_tmp ;
end

always @ ( posedge clk_100m ) begin
    if( ex_rd_sel == 1'b1 ) begin
        tpram_chn_sel  <=   rd_port[3:0] ;
    end
    else begin
        tpram_chn_sel  <=   4'd0 ;
    end
end

always @ ( posedge clk_100m ) begin
    case( tpram_chn_sel )
        4'h0    :   base_addr    <=  BASE0_ADDR ; 
        4'h1    :   base_addr    <=  BASE1_ADDR ; 
        4'h2    :   base_addr    <=  BASE2_ADDR ; 
        4'h3    :   base_addr    <=  BASE3_ADDR ; 
        4'h4    :   base_addr    <=  BASE4_ADDR ; 
        4'h5    :   base_addr    <=  BASE5_ADDR ; 
        4'h6    :   base_addr    <=  BASE6_ADDR ; 
        4'h7    :   base_addr    <=  BASE7_ADDR ; 
        4'h8    :   base_addr    <=  BASE8_ADDR ; 
        4'h9    :   base_addr    <=  BASE9_ADDR ; 
        4'ha    :   base_addr    <=  BASEA_ADDR ; 
        4'hb    :   base_addr    <=  BASEB_ADDR ; 
        4'hc    :   base_addr    <=  BASEC_ADDR ; 
        4'hd    :   base_addr    <=  BASED_ADDR ; 
        4'he    :   base_addr    <=  BASEE_ADDR ; 
        4'hf    :   base_addr    <=  BASEF_ADDR ; 
        default :   base_addr    <=  BASE0_ADDR ;
    endcase
end

assign  tpram_rd_addr   =   ( rd_port_sel_tmp == 1'b1 ) ? ( base_addr + rd_addr ) : 10'h00 ;    

//----------------------------------------------------------------------------------
// TYPE1_DMMRX instance
//----------------------------------------------------------------------------------
    RAM1K18                     U1_LSRAM_W18D1024 
    (
    .A_DOUT                     ( rd_data_tmp               ), 
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
    .A_ADDR                     ( { tpram_rd_addr, 4'h0 }   ), // used bits [13:4] , [3:0] to be grounded 
    .A_WEN                      ( 2'b00                     ), // 00 : read operation
    .B_CLK                      ( clk_100m                  ), 
    .B_DOUT_CLK                 ( 1'b1                      ), 
    .B_ARST_N                   ( 1'b1                      ), 
    .B_DOUT_EN                  ( 1'b1                      ), // 0 : register holds previous data ; 1 : normal register operation
    .B_BLK                      ( { wr_tpram_en , 2'b11 }   ), // 011 : no operation ; 111 : read or write operation 
    .B_DOUT_ARST_N              ( 1'b0                      ), 
    .B_DOUT_SRST_N              ( 1'b1                      ), 
    .B_DIN                      ( wr_data                   ), 
    .B_ADDR                     ( { wr_addr , 4'h0 }        ), // used bits [13:4] , [3:0] to be grounded  
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


endmodule

