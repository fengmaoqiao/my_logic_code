// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
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
`timescale 1 ns / 1 ns
`include "DEFINES.v"

module bfifo_w3d64
    (
    // Clocks and Reset
    WCLOCK                      ,   // write Clock
    RCLOCK                      ,   // Read Clock
    RESET                       ,   // Reset active low
    // Input Data Bus and Control ports
    WDATA                       ,   // Input Write data
    WE                          ,   // Write Enable
    RE                          ,   // Read Enable
    // Output Data bus
    RDATA                       ,   // Output Read data
    // Status Flags
    FULL                        ,   // Full flag
    EMPTY                           // Empty flag
    // For external memory
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   RWIDTH              = 3 ;  // Read  port Data Width
parameter   WWIDTH              = 3 ;  // Write port Data Width

parameter   READ_DEPTH          = 6 ;
parameter   WRITE_DEPTH         = 6 ;

parameter   FULL_WRITE_DEPTH    = 64 ; // write depth
parameter   FULL_READ_DEPTH     = 64 ; // read depth

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input                           WCLOCK                              ;   
input                           RCLOCK                              ;   
input                           RESET                               ;   
input       [WWIDTH - 1 : 0]    WDATA                               ;   
input                           WE                                  ;   
input                           RE                                  ;  

// declare output singal
output      [RWIDTH - 1 : 0]    RDATA                               ;   
output                          FULL                                ;   
output                          EMPTY                               ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            RCLOCK                              ;   
wire                            WCLOCK                              ;   
wire        [READ_DEPTH : 0]    rdiff_bus                           ;   
wire        [WRITE_DEPTH : 0]   wdiff_bus                           ;   
wire        [READ_DEPTH : 0]    rptr_bin_sync                       ;   
wire        [WRITE_DEPTH : 0]   wptr_bin_sync                       ;   
wire                            emptyi                              ;   
wire        [17:0]              rddata                              ;
wire        [RWIDTH - 1 : 0]    RDATA                               ;   

// reg signal
reg                             FULL                                ;   
reg                             EMPTY                               ;   
reg                             empty_tmp                           ;   
reg         [WRITE_DEPTH-1 : 0] memwaddr                            ;   
reg         [READ_DEPTH-1 : 0]  memraddr                            ;   
reg         [WRITE_DEPTH : 0]   wptr                                ;   
reg         [READ_DEPTH  : 0]   rptr                                ;   
reg         [WRITE_DEPTH : 0]   wptr_bin_sync2                      ;   
reg         [READ_DEPTH : 0]    rptr_bin_sync2                      ;   
reg         [WRITE_DEPTH : 0]   wptr_gray                           ;   
reg         [READ_DEPTH  : 0]   rptr_gray                           ;   
reg         [WRITE_DEPTH : 0]   wptr_gray_d1                        ;   
reg         [WRITE_DEPTH : 0]   wptr_gray_sync                      ;   
reg         [READ_DEPTH  : 0]   rptr_gray_d1                        ;   
reg         [READ_DEPTH  : 0]   rptr_gray_sync                      ;   
reg                             re_d1                               ;   
reg                             start_flag                          ;   
reg                             start_flag_d1                       ;   
reg         [RWIDTH - 1 : 0]    rdata_tmp                           ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// output generator
//----------------------------------------------------------------------------------
always @( posedge RCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        re_d1 <= 1'b0 ;
    end
    else begin          
        re_d1 <= RE ;
    end
end

always @( posedge RCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        rdata_tmp <= 'h0 ;
    end
    else if( RE == 1'b0 && re_d1 == 1'b1 ) begin          
        rdata_tmp <= rddata[RWIDTH - 1:0] ;
    end
end

assign RDATA = ( RE == 1'b1 && re_d1 == 1'b0 && start_flag_d1 == 1'b1 ) ? rdata_tmp : rddata[RWIDTH - 1:0] ; 

//----------------------------------------------------------------------------------
// empty generator
//----------------------------------------------------------------------------------
always @( posedge WCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        wptr <= 'h0 ;
    end
    else if( WE == 1'b1 ) begin
        wptr <= wptr + 1'b1 ;
    end
    else ;
end

always @( posedge RCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        rptr <= 'h0 ;
    end
    else if( RE == 1'b1 ) begin          
        rptr <= rptr + 1'b1 ;
    end
    else ;
end

always @( posedge WCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        wptr_gray <= 'h0 ;
    end
    else begin    
		wptr_gray <= ( wptr >> 1 ) ^ wptr ;
    end
end
   
always @( posedge RCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
      wptr_gray_d1 <= 'h0 ;
      wptr_gray_sync <= 'h0 ;
   end
   else begin
      wptr_gray_d1 <= wptr_gray ;
      wptr_gray_sync <= wptr_gray_d1 ;
   end
end

    gtbc #(
    .ADDRWIDTH                  (WRITE_DEPTH                )
    )
    u0_gtbc
    (
    .gray_in                    (wptr_gray_sync             ),
    .bin_out                    (wptr_bin_sync              )
    );

always @( posedge RCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
       wptr_bin_sync2  <= 'h0;
     end
     else begin	     
       wptr_bin_sync2 <= wptr_bin_sync;
     end
  end

assign rdiff_bus = ( wptr_bin_sync2 - rptr ) ;

assign emptyi = ( rdiff_bus <= 3 ) ? 1'b1 : 1'b0 ;   

always @( posedge RCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        empty_tmp   <= 1'b1 ;
    end
    else begin
        if( rdiff_bus == 3 ) begin  
            if( RE == 1'b1 ) begin
                empty_tmp   <= 1'b1 ;          
            end
            else begin
                empty_tmp   <= 1'b0 ; 
            end
        end
        else begin
             empty_tmp   <= emptyi ;          
        end
    end
end

always @( posedge RCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        EMPTY <= 1'b1 ;
    end
    else begin          
        EMPTY <= empty_tmp ;
    end
end

always @( posedge RCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        start_flag <= 1'b0 ;
    end
    else if( empty_tmp == 1'b0 && EMPTY == 1'b1 ) begin
        start_flag <= 1'b1 ;
    end
    else ;
end

always @( posedge RCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        start_flag_d1 <= 1'b0 ;
    end
    else begin
        start_flag_d1 <= start_flag ;
    end
end

//----------------------------------------------------------------------------------
// full generator
//----------------------------------------------------------------------------------
always @( posedge RCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        rptr_gray <= 'h0 ;
    end
    else begin 
	    rptr_gray <= ( rptr >> 1 ) ^ rptr ;
    end
end

always @( posedge WCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
      rptr_gray_d1 <= 'h0 ;
      rptr_gray_sync <= 'h0 ;
   end
   else begin
      rptr_gray_d1 <= rptr_gray ;
      rptr_gray_sync <= rptr_gray_d1 ;
   end
end

    gtbc #(
    .ADDRWIDTH                  (READ_DEPTH                 )
    )
    u1_gtbc
    (
    .gray_in                    (rptr_gray_sync             ),
    .bin_out                    (rptr_bin_sync              )
    );

always @( posedge WCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        rptr_bin_sync2  <= 'h0 ;
    end
    else begin
  	    rptr_bin_sync2 <= rptr_bin_sync ;
    end
end

assign  wdiff_bus = ( wptr - rptr_bin_sync2 ) ; 

always @( posedge WCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        FULL   <= 1'b0 ;
    end
    else if( wdiff_bus >= ( FULL_WRITE_DEPTH - 1'b1 ) )begin
        FULL   <= 1'b1 ;    
    end
    else begin
        FULL   <= 1'b0 ;
    end
end 

//----------------------------------------------------------------------------------
// read & write address generator
//----------------------------------------------------------------------------------
always @( posedge WCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        memwaddr <= 'h0 ;
    end
    else begin
        if( WE == 1'b1 ) begin
            if( memwaddr == ( FULL_WRITE_DEPTH - 1 ) ) begin 
                memwaddr <= 'h0 ;
            end
            else begin
                memwaddr <= memwaddr + 1'b1 ;
            end
        end
    end
end

always @( posedge RCLOCK or negedge RESET ) begin
    if( RESET == 1'b0 ) begin
        memraddr <= 'h0 ;
    end
    else begin
        if( RE == 1'b1 ) begin
            if( memraddr == ( FULL_READ_DEPTH - 1 ) ) begin 
                memraddr <= 'h0 ;
            end
            else begin
                memraddr <= memraddr + 1'b1 ;
            end
        end
        else if( empty_tmp == 1'b0 && EMPTY == 1'b1 && start_flag == 1'b0 ) begin
            memraddr <= memraddr + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// uSRAM instance
//----------------------------------------------------------------------------------

    RAM64x18                    u_bfifo_w3d64 
    (
    .A_DOUT                     ( rddata                    ), 
    .B_DOUT                     (                           ), 
    .BUSY                       (                           ), 
    .A_ADDR_CLK                 ( RCLOCK                    ), 
    .A_DOUT_CLK                 ( 1'b1                      ), 
    .A_ADDR_SRST_N              ( 1'b1                      ), 
    .A_DOUT_SRST_N              ( 1'b1                      ), 
    .A_ADDR_ARST_N              ( 1'b1                      ), 
    .A_DOUT_ARST_N              ( 1'b1                      ), 
    .A_ADDR_EN                  ( 1'b1                      ), 
    .A_DOUT_EN                  ( 1'b1                      ), 
    .A_BLK                      ( 2'b11                     ), 
    .A_ADDR                     ( {2'b00, memraddr[5:0], 2'b00}), 
    .B_ADDR_CLK                 ( RCLOCK                    ), 
    .B_DOUT_CLK                 ( 1'b1                      ), 
    .B_ADDR_SRST_N              ( 1'b1                      ), 
    .B_DOUT_SRST_N              ( 1'b1                      ), 
    .B_ADDR_ARST_N              ( 1'b1                      ), 
    .B_DOUT_ARST_N              ( 1'b1                      ), 
    .B_ADDR_EN                  ( 1'b1                      ), 
    .B_DOUT_EN                  ( 1'b1                      ), 
    .B_BLK                      ( 2'b11                     ), 
    .B_ADDR                     ( 10'h00                    ), 
    .C_CLK                      ( WCLOCK                    ), 
    .C_ADDR                     ( {2'b00, memwaddr[5:0], 2'b00}), 
    .C_DIN                      ( {15'h00, WDATA[2:0]}      ), 
    .C_WEN                      ( WE                        ), 
    .C_BLK                      ( {WE, 1'b1}                ), 
    .A_EN                       ( 1'b1                      ), 
    .A_ADDR_LAT                 ( 1'b0                      ), 
    .A_DOUT_LAT                 ( 1'b1                      ), 
    .A_WIDTH                    ( 3'b010                    ), 
    .B_EN                       ( 1'b1                      ), 
    .B_ADDR_LAT                 ( 1'b0                      ), 
    .B_DOUT_LAT                 ( 1'b1                      ), 
    .B_WIDTH                    ( 3'b010                    ), 
    .C_EN                       ( 1'b1                      ), 
    .C_WIDTH                    ( 3'b010                    ), 
    .SII_LOCK                   ( 1'b0                      )
    );
    
endmodule 

