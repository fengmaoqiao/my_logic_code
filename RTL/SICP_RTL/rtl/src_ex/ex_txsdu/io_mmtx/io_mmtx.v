// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   IO_MMTX
// CREATE DATE      :   2017-09-27
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-27  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   Memory Management of IO channel transmit data path
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

module  IO_MMTX
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   

    // mpu box configuration 

    // write port 
    wr_sel                      ,   
    wr_dval                     ,   
    wr_sop                      ,   
    wr_eop                      ,   
    wr_data                     ,   

    // read port
    rd_req                      ,   
    rd_dval                     ,   
    rd_data                        
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

input   wire                    wr_sel                              ;   
input   wire                    wr_dval                             ;   
input   wire                    wr_sop                              ;   
input   wire                    wr_eop                              ;   
input   wire    [15:0]          wr_data                             ;   
input   wire                    rd_req                              ;   

// declare output signal
output  wire                    rd_dval                             ;   
output  wire    [17:0]          rd_data                             ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            pfifo_rden                          ;   
wire                            pfifo_empty                         ;   
wire        [17:0]              pfifo_rddata                        ;   

// reg signal
reg                             pfifo_rden_d1                       ; 
reg                             pfifo_eop                           ;  
reg         [15:0]              pfifo_wrdata                        ;   
reg                             pfifo_wren                          ; 
reg                             pfifo_sop                           ;   
reg                             pfifo_sop_d1                        ;   
reg         [15:0]              pkt_tick                            ;  


/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// pfifo write control
//----------------------------------------------------------------------------------
always @( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin	
        pkt_tick <=   16'h00 ;           
    end
    else begin
        if( wr_sel == 1'b1 && wr_sop == 1'b1 ) begin
            pkt_tick <=   pkt_tick + 1'b1 ;
        end
        else ;
    end
end

always @( posedge clk_12_5m ) begin
    if ( wr_sel == 1'b1 ) begin
        pfifo_wren  <=  wr_dval ;
    end
    else begin
        pfifo_wren  <=  1'b0 ;
    end
end

always @( posedge clk_12_5m ) begin
    if ( wr_sel == 1'b1 ) begin
        if ( pfifo_sop_d1 == 1'b1 ) begin
            pfifo_wrdata  <=  pkt_tick ;
        end
        else begin
            pfifo_wrdata  <=  wr_data ;
        end
    end
    else begin
        pfifo_wrdata  <=  16'h00 ;
    end
end

always @( posedge clk_12_5m ) begin
    if ( wr_sel == 1'b1 ) begin
        pfifo_sop  <=  wr_sop ;
    end
    else begin
        pfifo_sop  <=  1'b0 ;
    end
end

always @( posedge clk_12_5m ) begin
    pfifo_sop_d1  <=  pfifo_sop ;
end

always @( posedge clk_12_5m ) begin
    if ( wr_sel == 1'b1 ) begin
        pfifo_eop  <=  wr_eop ;
    end
    else begin
        pfifo_eop  <=  1'b0 ;
    end
end


//----------------------------------------------------------------------------------
// pfifo read control
//----------------------------------------------------------------------------------
assign  slink_mm_empty  =   pfifo_empty ;   
assign  pfifo_rden = ( pfifo_empty == 1'b0 && rd_req == 1'b1 ) ? 1'b1 : 1'b0 ;

always @( posedge clk_12_5m ) begin
	pfifo_rden_d1 <=  	pfifo_rden ;
end

assign  rd_dval = ( pfifo_rden_d1 == 1'b1 && pfifo_empty == 1'b0 ) ? 1'b1 : 1'b0 ;
assign  rd_data = pfifo_rddata ;

    PFIFO_W18D1024              U_PFIFO_W18D1024
    (
    // Inputs
    .wclock                     ( clk_12_5m                 ),
    .rclock                     ( clk_12_5m                 ),
    .wreset                     ( rst_12_5m                 ),
    .rreset                     ( rst_12_5m                 ),
    .wdata                      ( pfifo_wrdata              ),
    .wsop                       ( pfifo_sop                 ),
    .weop                       ( pfifo_eop                 ),
    .we                         ( pfifo_wren                ),
    .re                         ( pfifo_rden                ),
    // Outputs
    .empty                      ( pfifo_empty               ),
    .full                       (                           ),
    .rdata                      ( pfifo_rddata              )
    );

endmodule

