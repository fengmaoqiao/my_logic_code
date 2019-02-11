// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   HRM_MMRX
// CREATE DATE      :   2017-09-22
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-22  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   memory management of Hot-Redunancy MCU
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

module  HRM_MMRX_S
    (
    clk_100m                    ,   
    rst_100m                    , 

    // read port
    rd_sel                      ,   
    chn_sel                     ,   
    hrm_pkt_num                 ,   
    rd_addr                     ,   
    rd_data                     ,   

    // write port
    wr_sel                      ,   
    wr_en                       ,   
    wr_addr                     ,   
    wr_data                       
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
input   wire                    chn_sel                             ;
input   wire        [3:0]       hrm_pkt_num                         ;
input   wire        [8:0]       rd_addr                             ;
input   wire                    wr_sel                              ;   
input   wire        [1:0]       wr_en                               ;   
input   wire        [9:0]       wr_addr                             ;   
input   wire        [17:0]      wr_data                             ;   

// declare output signal
output  reg         [17:0]      rd_data                             ; 

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [1:0]               tpram_wr_en                         ;   
wire        [17:0]              tpram_rd_data   [1:0]               ;  

// reg signal
reg         [1:0]               wr_en_d1                            ;   
reg         [9:0]               wr_addr_d1                          ;   
reg         [17:0]              wr_data_d1                          ;   
reg         [9:0]               tpram_rd_addr                       ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// write control
//----------------------------------------------------------------------------------
always @ ( posedge clk_100m ) begin
    wr_en_d1    <=   wr_en ;
    wr_addr_d1  <=   wr_addr ;
    wr_data_d1  <=   wr_data ;
end

assign  tpram_wr_en[0]  =   ( wr_sel == 1'b1 && wr_en_d1[0] == 1'b1 ) ? 1'b1 : 1'b0 ;    
assign  tpram_wr_en[1]  =   ( wr_sel == 1'b1 && wr_en_d1[1] == 1'b1 ) ? 1'b1 : 1'b0 ;    

//----------------------------------------------------------------------------------
// read control
//----------------------------------------------------------------------------------

always @ ( posedge clk_100m ) begin
    if ( rd_sel == 1'b1 && chn_sel == 1'b1 ) begin
        if ( hrm_pkt_num[0] == 1'b0 ) begin
            tpram_rd_addr   <= { 1'b0 , rd_addr } ;
        end
        else begin
            tpram_rd_addr   <= rd_addr + BASE1_ADDR ;
        end
    end
    else begin
        tpram_rd_addr   <=  10'h00 ;
    end
end

always @ ( posedge clk_100m ) begin
    case( hrm_pkt_num[3:1] )
        3'b000   :   rd_data    <=  tpram_rd_data[0] ; 
        3'b001   :   rd_data    <=  tpram_rd_data[1] ; 
        default  :   rd_data    <=  18'h00 ; 
    endcase
end

//----------------------------------------------------------------------------------
// LSRAM instance  
//----------------------------------------------------------------------------------
  genvar j;
  generate
  for( j = 0 ; j < 2 ; j = j+1 ) 
  begin : nLSRAM

    RAM1K18                     U1_LSRAM_W18D1024 
    (
    .A_DOUT                     ( tpram_rd_data[j]          ), 
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
    .B_BLK                      ( { tpram_wr_en[j] , 2'b11 }), // 011 : no operation ; 111 : read or write operation 
    .B_DOUT_ARST_N              ( 1'b0                      ), 
    .B_DOUT_SRST_N              ( 1'b1                      ), 
    .B_DIN                      ( wr_data_d1                ), 
    .B_ADDR                     ( { wr_addr_d1[9:0], 4'h0 } ), // used bits [13:4] , [3:0] to be grounded  
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

