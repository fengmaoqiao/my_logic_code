// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   pfifo_w16d1024
// CREATE DATE      :   2017-06-10
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-06-10  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
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

module PFIFO_W18D4096
    (
    // Clocks and Reset
    wclock                      ,   // write Clock
    rclock                      ,   // Read Clock
    wreset                      ,   // write Reset , active low
    rreset                      ,   // read Reset , active low

    // Input Data Bus and Control ports
    wdata                       ,   // Input Write data
    wsop                        ,   // eop of input write data
    weop                        ,   // eop of input write data
    we                          ,   // Write Enable
    re                          ,   // Read Enable

    // Output Data bus
    rdata                       ,   // Output Read data

    // Status Flags
    full                        ,   // Full flag
    empty                           // Empty flag
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   RD_DEPTH         = 16 ;
parameter   WR_DEPTH         = 16 ;

parameter   FULL_WR_DEPTH    = 4096 ; // write depth
parameter   FULL_RD_DEPTH    = 4096 ; // read depth

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    wclock                              ;   
input   wire                    rclock                              ;   
input   wire                    wreset                              ;   
input   wire                    rreset                              ;  

input   wire    [15:0]          wdata                               ; 
input   wire                    wsop                                ;   
input   wire                    weop                                ;   
input   wire                    we                                  ;   
input   wire                    re                                  ;   

// declare output singal
output  reg     [17:0]          rdata                               ;   
output  reg                     full                                ;   
output  reg                     empty                               ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [WR_DEPTH-1 : 0]    wdiff_bus                           ;   
wire        [RD_DEPTH-1 : 0]    rptr_bin_sync                       ;   
wire        [17:0]              rddata                              ;   
wire                            eop_sync                            ;   
wire                            empty_tmp                           ;   
wire                            we0                                 ;   
wire                            we1                                 ;   
wire                            we2                                 ;   
wire                            we3                                 ;   
wire        [9:0]               memraddr0                           ;   
wire        [9:0]               memraddr1                           ;   
wire        [9:0]               memraddr2                           ;   
wire        [9:0]               memraddr3                           ;   
wire        [17:0]              rddata0                             ;   
wire        [17:0]              rddata1                             ;   
wire        [17:0]              rddata2                             ;   
wire        [17:0]              rddata3                             ;   

// reg signal
reg         [9 : 0]             memwaddr                            ;   
reg         [9 : 0]             memraddr                            ;   
reg         [WR_DEPTH-1 : 0]    wptr                                ;   
reg         [RD_DEPTH-1 : 0]    rptr                                ;   
reg         [RD_DEPTH-1 : 0]    rptr_bin_sync2                      ;   
reg         [RD_DEPTH-1 : 0]    rptr_gray                           ;   
reg         [RD_DEPTH-1 : 0]    rptr_gray_d1                        ;   
reg         [RD_DEPTH-1 : 0]    rptr_gray_sync                      ;   
reg                             eop_extend                          ;   
reg         [3:0]               eop_extend_cnt                      ;   
reg                             eop_sync_tmp1                       ;   
reg                             eop_sync_tmp2                       ;   
reg                             eop_sync_tmp3                       ;   
reg         [4:0]               pkt_cnt                             ;  
reg                             re_d1                               ;  
reg         [1:0]               wr_lsram_cs                         ;   
reg         [1:0]               rd_lsram_cs                         ;   
reg         [1:0]               rd_lsram_cs_d1                      ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// output generator
//----------------------------------------------------------------------------------
always @( posedge rclock or negedge rreset ) begin
    if( rreset == 1'b0 ) begin
        re_d1 <= 1'b0 ;
    end
    else begin          
        re_d1 <= re ;
    end
end

always @( posedge rclock ) begin
    rd_lsram_cs_d1 <= rd_lsram_cs ;
end

always @( * ) begin
    case( rd_lsram_cs_d1 )
        2'b00   : rdata    <=   rddata0 ;
        2'b01   : rdata    <=   rddata1 ;
        2'b10   : rdata    <=   rddata2 ;
        2'b11   : rdata    <=   rddata3 ;
        default : rdata    <=   18'h00 ;
    endcase
end

//----------------------------------------------------------------------------------
// pfifo empty generator
//----------------------------------------------------------------------------------
always @( posedge wclock or negedge wreset ) begin
    if( wreset == 1'b0 ) begin
        eop_extend <= 1'b0 ;
    end
    else begin
        if( eop_extend_cnt == 4'hf ) begin
            eop_extend <= 1'b0 ;
        end
        else if( weop == 1'b1 && we == 1'b1 ) begin
            eop_extend <= 1'b1 ;
        end
    end
end

always @( posedge wclock or negedge wreset ) begin
    if( wreset == 1'b0 ) begin
        eop_extend_cnt <= 4'h0 ;
    end
    else begin
        if( eop_extend == 1'b1 ) begin
            eop_extend_cnt <= eop_extend_cnt + 1'b1 ;
        end
        else begin
            eop_extend_cnt <= 4'h0 ;
        end
    end
end

always @( posedge rclock or negedge rreset ) begin
    if( rreset == 1'b0 ) begin
        eop_sync_tmp1  <= 1'b0 ;
        eop_sync_tmp2  <= 1'b0 ;
        eop_sync_tmp3  <= 1'b0 ;
    end
    else begin         
        eop_sync_tmp1 <= eop_extend ;
        eop_sync_tmp2 <= eop_sync_tmp1 ;
        eop_sync_tmp3 <= eop_sync_tmp2 ;
    end
end

assign  eop_sync = ( eop_sync_tmp2 == 1'b1 && eop_sync_tmp3 == 1'b0 ) ? 1'b1 : 1'b0 ;

always @( posedge rclock or negedge rreset ) begin
    if( rreset == 1'b0 ) begin
        pkt_cnt <= 5'h00 ;
    end
    else begin
        if( re == 1'b1 && rdata[16] == 1'b1 && eop_sync == 1'b1 ) begin          
            pkt_cnt <= pkt_cnt ;
        end
        else if( eop_sync == 1'b1 ) begin
            pkt_cnt <= pkt_cnt + 1'b1 ;
        end
        else if( re == 1'b1 && rdata[16] == 1'b1 ) begin          
            pkt_cnt <= pkt_cnt - 1'b1 ;
        end
        else ;
    end
end

assign  empty_tmp = ( pkt_cnt == 5'h00 || ( re == 1'b1 && re_d1 == 1'b1 && rdata[16] == 1'b1 ) ) ? 1'b1 : 1'b0 ;

always @( posedge rclock or negedge rreset ) begin
    if( rreset == 1'b0 ) begin
        empty <= 1'b1 ;
    end
    else begin          
        empty <= empty_tmp ;
    end
end

//----------------------------------------------------------------------------------
// full generator
//----------------------------------------------------------------------------------
always @( posedge wclock or negedge wreset ) begin
    if( wreset == 1'b0 ) begin
        wptr <= {WR_DEPTH{1'b0}} ;
    end
    else begin
        if( we == 1'b1 ) begin
            wptr <= wptr + 1'b1 ;
        end
        else ;
    end
end

always @( posedge rclock or negedge rreset ) begin
    if( rreset == 1'b0 ) begin
        rptr <= {RD_DEPTH{1'b0}} ;
    end
    else begin
        if( re == 1'b1 ) begin
            if( empty_tmp == 1'b1 && re_d1 == 1'b1 ) begin
                rptr <= rptr ;
            end
            else begin
                rptr <= rptr + 1'b1 ;
            end
        end
        else ;
    end
end

always @( posedge rclock or negedge rreset ) begin
    if( rreset == 1'b0 ) begin
        rptr_gray <= {RD_DEPTH{1'b0}} ;
    end
    else begin 
	    rptr_gray <= ( rptr >> 1 ) ^ rptr ;
    end
end

always @( posedge wclock or negedge wreset ) begin
    if( wreset == 1'b0 ) begin
      rptr_gray_d1   <= {RD_DEPTH{1'b0}} ;
      rptr_gray_sync <= {RD_DEPTH{1'b0}} ;
   end
   else begin
      rptr_gray_d1   <= rptr_gray ;
      rptr_gray_sync <= rptr_gray_d1 ;
   end
end

    gtbc                        #
    (
    .ADDRWIDTH                  ( RD_DEPTH                  )
    )
    u1_gtbc
    (
    .gray_in                    ( rptr_gray_sync            ),
    .bin_out                    ( rptr_bin_sync             )
    );

always @( posedge wclock or negedge wreset ) begin
    if( wreset == 1'b0 ) begin
        rptr_bin_sync2  <= {RD_DEPTH{1'b0}} ;
    end
    else begin
  	    rptr_bin_sync2 <= rptr_bin_sync ;
    end
end

assign  wdiff_bus = ( wptr - rptr_bin_sync2 ) ; 

always @( posedge wclock or negedge wreset ) begin
    if( wreset == 1'b0 ) begin
        full   <= 1'b0 ;
    end
    else begin
        if( wdiff_bus >= ( FULL_WR_DEPTH - 1'b1 ) ) begin
            full   <= 1'b1 ;    
        end
        else begin
            full   <= 1'b0 ;
        end
    end
end 

//----------------------------------------------------------------------------------
// read & write address generator
//----------------------------------------------------------------------------------
always @( posedge wclock or negedge wreset ) begin
    if( wreset == 1'b0 ) begin
        memwaddr <= 10'h00 ;
    end
    else begin
        if( we == 1'b1 ) begin
            if( memwaddr == 1023 ) begin 
                memwaddr <= 10'h00 ;
            end
            else begin
                memwaddr <= memwaddr + 1'b1 ;
            end
        end
    end
end

always @( posedge wclock or negedge wreset ) begin
    if( wreset == 1'b0 ) begin
        wr_lsram_cs <= 2'b00 ;
    end
    else begin
        if( we == 1'b1 && memwaddr == 1023 ) begin 
            wr_lsram_cs <= wr_lsram_cs + 1'b1 ;
        end
        else ;
    end
end

assign  we0 = ( we == 1'b1 && wr_lsram_cs == 2'd0 ) ? 1'b1 : 1'b0 ;
assign  we1 = ( we == 1'b1 && wr_lsram_cs == 2'd1 ) ? 1'b1 : 1'b0 ;
assign  we2 = ( we == 1'b1 && wr_lsram_cs == 2'd2 ) ? 1'b1 : 1'b0 ;
assign  we3 = ( we == 1'b1 && wr_lsram_cs == 2'd3 ) ? 1'b1 : 1'b0 ;

always @( posedge rclock or negedge rreset ) begin
    if( rreset == 1'b0 ) begin
        memraddr <= 10'h0 ;
    end
    else begin
        if( re == 1'b1 ) begin
            if( memraddr == 1023 ) begin 
                memraddr <= 10'h0 ;
            end
            else if( empty_tmp == 1'b1 && re_d1 == 1'b1 ) begin
                memraddr <= memraddr ;
            end
            else begin
                memraddr <= memraddr + 1'b1 ;
            end
        end
    end
end

always @( posedge rclock or negedge rreset ) begin
    if( rreset == 1'b0 ) begin
        rd_lsram_cs <= 2'b00 ;
    end
    else begin
        if( re == 1'b1 && memraddr == 1023 ) begin 
            rd_lsram_cs <= rd_lsram_cs + 1'b1 ;
        end
        else ;
    end
end

assign  memraddr0 = rd_lsram_cs == 2'd0 ? memraddr : 10'h00 ;
assign  memraddr1 = rd_lsram_cs == 2'd1 ? memraddr : 10'h00 ;
assign  memraddr2 = rd_lsram_cs == 2'd2 ? memraddr : 10'h00 ;
assign  memraddr3 = rd_lsram_cs == 2'd3 ? memraddr : 10'h00 ;

//----------------------------------------------------------------------------------
// LSRAM instance
//----------------------------------------------------------------------------------

    RAM1K18                     U_0_LSRAM_W10D1024 
    (
    .A_DOUT                     ( rddata0                           ), 
    .B_DOUT                     (                                   ), 
    .BUSY                       (                                   ), 
    .A_CLK                      ( rclock                            ), 
    .A_DOUT_CLK                 ( 1'b1                              ), 
    .A_ARST_N                   ( 1'b1                              ), 
    .A_DOUT_EN                  ( 1'b1                              ), // 0 : register holds previous data ; 1 : normal register operation 
    .A_BLK                      ( 3'b111                            ), // 111 : perform read or write operation on port A 
    .A_DOUT_ARST_N              ( 1'b1                              ), 
    .A_DOUT_SRST_N              ( 1'b1                              ), 
    .A_DIN                      ( 18'h00                            ),  
    .A_ADDR                     ( { memraddr0, 4'h0 }               ), // used bits [13:4] , [3:0] to be grounded 
    .A_WEN                      ( 2'b00                             ), // 00 : read operation
    .B_CLK                      ( wclock                            ), 
    .B_DOUT_CLK                 ( 1'b1                              ), 
    .B_ARST_N                   ( 1'b1                              ), 
    .B_DOUT_EN                  ( 1'b1                              ), // 0 : register holds previous data ; 1 : normal register operation
    .B_BLK                      ( { we0 , 2'b11 }                   ), // 011 : no operation ; 111 : read or write operation 
    .B_DOUT_ARST_N              ( 1'b0                              ), 
    .B_DOUT_SRST_N              ( 1'b1                              ), 
    .B_DIN                      ( { wsop , weop , wdata }           ), 
    .B_ADDR                     ( { memwaddr[9:0], 4'h0 }           ), // used bits [13:4] , [3:0] to be grounded  
    .B_WEN                      ( 2'b11                             ), // 11 : write[15:0]
    .A_EN                       ( 1'b1                              ), // power down , active low
    .A_DOUT_LAT                 ( 1'b1                              ), // 0 : register operation ; 1 : latch operation 
    .A_WIDTH                    ( 3'b100                            ), // 100: 1k*18 / 1k*16
    .A_WMODE                    ( 1'b1                              ), // 0 : output data port holds the previous value ; 1 : feed-through 
    .B_EN                       ( 1'b1                              ), // power down , active low
    .B_DOUT_LAT                 ( 1'b1                              ), // 0 : register operation ; 1 : latch operation
    .B_WIDTH                    ( 3'b100                            ), // 100: 1k*18 / 1k*16 
    .B_WMODE                    ( 1'b1                              ), // 0 : output data port holds the previous value ; 1 : feed-through 
    .SII_LOCK                   ( 1'b0                              )
    );

    RAM1K18                     U_1_LSRAM_W10D1024 
    (
    .A_DOUT                     ( rddata1                           ), 
    .B_DOUT                     (                                   ), 
    .BUSY                       (                                   ), 
    .A_CLK                      ( rclock                            ), 
    .A_DOUT_CLK                 ( 1'b1                              ), 
    .A_ARST_N                   ( 1'b1                              ), 
    .A_DOUT_EN                  ( 1'b1                              ), // 0 : register holds previous data ; 1 : normal register operation 
    .A_BLK                      ( 3'b111                            ), // 111 : perform read or write operation on port A 
    .A_DOUT_ARST_N              ( 1'b1                              ), 
    .A_DOUT_SRST_N              ( 1'b1                              ), 
    .A_DIN                      ( 18'h00                            ),  
    .A_ADDR                     ( { memraddr1, 4'h0 }               ), // used bits [13:4] , [3:0] to be grounded 
    .A_WEN                      ( 2'b00                             ), // 00 : read operation
    .B_CLK                      ( wclock                            ), 
    .B_DOUT_CLK                 ( 1'b1                              ), 
    .B_ARST_N                   ( 1'b1                              ), 
    .B_DOUT_EN                  ( 1'b1                              ), // 0 : register holds previous data ; 1 : normal register operation
    .B_BLK                      ( { we1 , 2'b11 }                   ), // 011 : no operation ; 111 : read or write operation 
    .B_DOUT_ARST_N              ( 1'b0                              ), 
    .B_DOUT_SRST_N              ( 1'b1                              ), 
    .B_DIN                      ( { wsop , weop , wdata }           ), 
    .B_ADDR                     ( { memwaddr[9:0], 4'h0 }           ), // used bits [13:4] , [3:0] to be grounded  
    .B_WEN                      ( 2'b11                             ), // 11 : write[15:0]
    .A_EN                       ( 1'b1                              ), // power down , active low
    .A_DOUT_LAT                 ( 1'b1                              ), // 0 : register operation ; 1 : latch operation 
    .A_WIDTH                    ( 3'b100                            ), // 100: 1k*18 / 1k*16
    .A_WMODE                    ( 1'b1                              ), // 0 : output data port holds the previous value ; 1 : feed-through 
    .B_EN                       ( 1'b1                              ), // power down , active low
    .B_DOUT_LAT                 ( 1'b1                              ), // 0 : register operation ; 1 : latch operation
    .B_WIDTH                    ( 3'b100                            ), // 100: 1k*18 / 1k*16 
    .B_WMODE                    ( 1'b1                              ), // 0 : output data port holds the previous value ; 1 : feed-through 
    .SII_LOCK                   ( 1'b0                              )
    );

    RAM1K18                     U_2_LSRAM_W10D1024 
    (
    .A_DOUT                     ( rddata2                           ), 
    .B_DOUT                     (                                   ), 
    .BUSY                       (                                   ), 
    .A_CLK                      ( rclock                            ), 
    .A_DOUT_CLK                 ( 1'b1                              ), 
    .A_ARST_N                   ( 1'b1                              ), 
    .A_DOUT_EN                  ( 1'b1                              ), // 0 : register holds previous data ; 1 : normal register operation 
    .A_BLK                      ( 3'b111                            ), // 111 : perform read or write operation on port A 
    .A_DOUT_ARST_N              ( 1'b1                              ), 
    .A_DOUT_SRST_N              ( 1'b1                              ), 
    .A_DIN                      ( 18'h00                            ),  
    .A_ADDR                     ( { memraddr2, 4'h0 }               ), // used bits [13:4] , [3:0] to be grounded 
    .A_WEN                      ( 2'b00                             ), // 00 : read operation
    .B_CLK                      ( wclock                            ), 
    .B_DOUT_CLK                 ( 1'b1                              ), 
    .B_ARST_N                   ( 1'b1                              ), 
    .B_DOUT_EN                  ( 1'b1                              ), // 0 : register holds previous data ; 1 : normal register operation
    .B_BLK                      ( { we2 , 2'b11 }                   ), // 011 : no operation ; 111 : read or write operation 
    .B_DOUT_ARST_N              ( 1'b0                              ), 
    .B_DOUT_SRST_N              ( 1'b1                              ), 
    .B_DIN                      ( { wsop , weop , wdata }           ), 
    .B_ADDR                     ( { memwaddr[9:0], 4'h0 }           ), // used bits [13:4] , [3:0] to be grounded  
    .B_WEN                      ( 2'b11                             ), // 11 : write[15:0]
    .A_EN                       ( 1'b1                              ), // power down , active low
    .A_DOUT_LAT                 ( 1'b1                              ), // 0 : register operation ; 1 : latch operation 
    .A_WIDTH                    ( 3'b100                            ), // 100: 1k*18 / 1k*16
    .A_WMODE                    ( 1'b1                              ), // 0 : output data port holds the previous value ; 1 : feed-through 
    .B_EN                       ( 1'b1                              ), // power down , active low
    .B_DOUT_LAT                 ( 1'b1                              ), // 0 : register operation ; 1 : latch operation
    .B_WIDTH                    ( 3'b100                            ), // 100: 1k*18 / 1k*16 
    .B_WMODE                    ( 1'b1                              ), // 0 : output data port holds the previous value ; 1 : feed-through 
    .SII_LOCK                   ( 1'b0                              )
    );
    RAM1K18                     U_3_LSRAM_W10D1024 
    (
    .A_DOUT                     ( rddata3                           ), 
    .B_DOUT                     (                                   ), 
    .BUSY                       (                                   ), 
    .A_CLK                      ( rclock                            ), 
    .A_DOUT_CLK                 ( 1'b1                              ), 
    .A_ARST_N                   ( 1'b1                              ), 
    .A_DOUT_EN                  ( 1'b1                              ), // 0 : register holds previous data ; 1 : normal register operation 
    .A_BLK                      ( 3'b111                            ), // 111 : perform read or write operation on port A 
    .A_DOUT_ARST_N              ( 1'b1                              ), 
    .A_DOUT_SRST_N              ( 1'b1                              ), 
    .A_DIN                      ( 18'h00                            ),  
    .A_ADDR                     ( { memraddr3, 4'h0 }               ), // used bits [13:4] , [3:0] to be grounded 
    .A_WEN                      ( 2'b00                             ), // 00 : read operation
    .B_CLK                      ( wclock                            ), 
    .B_DOUT_CLK                 ( 1'b1                              ), 
    .B_ARST_N                   ( 1'b1                              ), 
    .B_DOUT_EN                  ( 1'b1                              ), // 0 : register holds previous data ; 1 : normal register operation
    .B_BLK                      ( { we3 , 2'b11 }                   ), // 011 : no operation ; 111 : read or write operation 
    .B_DOUT_ARST_N              ( 1'b0                              ), 
    .B_DOUT_SRST_N              ( 1'b1                              ), 
    .B_DIN                      ( { wsop , weop , wdata }           ), 
    .B_ADDR                     ( { memwaddr[9:0], 4'h0 }           ), // used bits [13:4] , [3:0] to be grounded  
    .B_WEN                      ( 2'b11                             ), // 11 : write[15:0]
    .A_EN                       ( 1'b1                              ), // power down , active low
    .A_DOUT_LAT                 ( 1'b1                              ), // 0 : register operation ; 1 : latch operation 
    .A_WIDTH                    ( 3'b100                            ), // 100: 1k*18 / 1k*16
    .A_WMODE                    ( 1'b1                              ), // 0 : output data port holds the previous value ; 1 : feed-through 
    .B_EN                       ( 1'b1                              ), // power down , active low
    .B_DOUT_LAT                 ( 1'b1                              ), // 0 : register operation ; 1 : latch operation
    .B_WIDTH                    ( 3'b100                            ), // 100: 1k*18 / 1k*16 
    .B_WMODE                    ( 1'b1                              ), // 0 : output data port holds the previous value ; 1 : feed-through 
    .SII_LOCK                   ( 1'b0                              )
    );

endmodule 

