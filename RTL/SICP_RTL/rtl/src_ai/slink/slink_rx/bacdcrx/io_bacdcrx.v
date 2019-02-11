// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   BACDCRX
// CREATE DATE      :   2017-08-22
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-22  TingtingGan     Original
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

module IO_BACDCRX
    (
    clk_wr                      ,   
    rst_wr                      ,   
    clk_rd                      ,   
    rst_rd                      ,   

    slink_err                   ,   
    macrx_rxfifo_dval           ,   
    macrx_rxfifo_sop            ,   
    macrx_rxfifo_eop            ,   
    macrx_rxfifo_data           ,  

    mm_slink_rdreq              ,   
    slink_mm_empty              ,   
    slink_mm_dval               ,   
    slink_mm_data               ,
    ram_dgd_err

    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_wr                              ;   
input   wire                    rst_wr                              ;   
input   wire                    clk_rd                              ;   
input   wire                    rst_rd                              ;   
input   wire                    macrx_rxfifo_dval                   ;   
input   wire                    macrx_rxfifo_sop                    ;   
input   wire                    macrx_rxfifo_eop                    ;   
input   wire    [7:0]           macrx_rxfifo_data                   ;   
input   wire                    mm_slink_rdreq                      ;   
input   wire                    slink_err                           ;   
// declare output signal
output  wire                    slink_mm_empty                      ;   
output  wire                    slink_mm_dval                       ;   
output  wire    [17:0]          slink_mm_data                       ;   
output  wire                    ram_dgd_err                         ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            pfifo_rden                          ;   
wire                            pfifo_empty                         ;   
wire        [17:0]              pfifo_rddata                        ;   
wire                            pfifo_eop                           ;  
wire        [15:0]              pfifo_wrdata                        ;   
wire                            pfifo_wren                          ; 
wire                            pfifo_sop                           ;   
wire                            ram_din_val                         ;   
wire                            ram_dout_val                        ;   
wire        [7:0]               ram_din_data                        ;   
wire        [7:0]               ram_dout_data                       ;   
wire                            din_sop                             ;   
wire                            din_eop                             ;   
wire                            dout_sop                            ;   
wire                            dout_eop                            ;   

// reg signal
reg                             pfifo_rden_d1                       ; 

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

assign  pfifo_wrdata =  { 8'h00 , macrx_rxfifo_data } ;
assign  pfifo_wren   =  macrx_rxfifo_dval ;
assign  pfifo_sop    =  macrx_rxfifo_sop ;
assign  pfifo_eop    =  macrx_rxfifo_eop ;

//----------------------------------------------------------------------------------
// pfifo control
//----------------------------------------------------------------------------------
assign  slink_mm_empty  =   pfifo_empty ;   
assign  pfifo_rden = ( pfifo_empty == 1'b0 && mm_slink_rdreq == 1'b1 ) ? 1'b1 : 1'b0 ;

always @( posedge clk_rd or negedge rst_rd ) begin
    if( rst_rd == 1'b0 ) begin	
		pfifo_rden_d1 <=  	1'b0 ;
	end
    else begin
		pfifo_rden_d1 <=  	pfifo_rden ;
	end
end

assign  slink_mm_dval = ( pfifo_rden_d1 == 1'b1 && pfifo_empty == 1'b0 ) ? 1'b1 : 1'b0 ;
assign  slink_mm_data = pfifo_rddata ;

    PFIFO_W18D1024              U_pfifo_w16d1024
    (
    // Inputs
    .wclock                     ( clk_wr                    ),
    .rclock                     ( clk_rd                    ),
    .wreset                     ( rst_wr                    ),
    .rreset                     ( rst_rd                    ),
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

//----------------------------------------------------------------------------------
// diagnosing this ram thouth the down data fream of crc
//----------------------------------------------------------------------------------
assign  ram_din_val    = pfifo_wren ;
assign  ram_dout_val   = pfifo_rden ;
assign  ram_din_data   = pfifo_wrdata[7:0] ;
assign  ram_dout_data  = pfifo_rddata[7:0] ;

assign din_sop   = pfifo_sop;
assign din_eop   = pfifo_eop;
assign dout_sop  = slink_mm_data[17] && slink_mm_dval;
assign dout_eop  = slink_mm_data[16] && slink_mm_dval;

    RAMDGDM #(
    .CRC_LEN_L                  ( 10'd4                     ),
    .CRC_LEN_H                  ( 10'd120                   ),
    .FUN_SEL                    ( 1'b1                      ),
    .BIT_WIDTH                  ( 8                         ),
    .RAM_DGD_TYPE               ( 1'b0                      )
    )
    U_RXRAMDGDM(
    .clk_wr                     ( clk_wr                    ),
    .rst_wr_n                   ( rst_wr                    ),
    .clk_rd                     ( clk_rd                    ),
    .rst_rd_n                   ( rst_rd                    ),

    .slink_prd_err              ( slink_err                 ),
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

