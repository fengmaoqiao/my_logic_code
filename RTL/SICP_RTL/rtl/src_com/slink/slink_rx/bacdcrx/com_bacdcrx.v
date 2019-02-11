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

module COM_BACDCRX
    (
    clk_wr                      ,   
    rst_wr                      ,   
    clk_rd                      ,   
    rst_rd                      ,   

    llcrx_rxfifo_dval           ,   
    llcrx_rxfifo_sop            ,   
    llcrx_rxfifo_eop            ,   
    llcrx_rxfifo_data           ,  

    mm_slink_rdreq              ,   
    slink_mm_empty              ,   
    slink_mm_dval               ,   
    slink_mm_data                
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   FIFO_TYPE   =   2'b00 ; // 00: deep is 1024 ; 01: deep is 2048 ; 10 : 4096

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_wr                              ;   
input   wire                    rst_wr                              ;   
input   wire                    clk_rd                              ;   
input   wire                    rst_rd                              ;   
input   wire                    llcrx_rxfifo_dval                   ;   
input   wire                    llcrx_rxfifo_sop                    ;   
input   wire                    llcrx_rxfifo_eop                    ;   
input   wire    [7:0]           llcrx_rxfifo_data                   ;   
input   wire                    mm_slink_rdreq                      ;   

// declare output signal
output  wire                    slink_mm_empty                      ;   
output  wire                    slink_mm_dval                       ;   
output  wire    [17:0]          slink_mm_data                       ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            pfifo_rden                          ;   
wire                            pfifo_empty                         ;   
wire        [17:0]              pfifo_rddata                        ;   
wire                            pfifo_eop                           ;  

// reg signal
reg         [7:0]               data_d1                             ;   
reg                             extract_flag                        ;   
reg         [15:0]              pfifo_wrdata                        ;   
reg                             pfifo_wren                          ; 
reg                             new_sop_flag                        ;   
reg                             pfifo_sop                           ;   
reg                             pfifo_rden_d1                       ; 
reg                             rd_sop                              ;   
reg         [17:0]              rd_byte1                            ;   
reg                             even_byte_eop                       ;   
reg                             odd_byte_eop                        ;  

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

// eight to sixteen byte conversion
always @( posedge clk_wr ) begin
    if ( llcrx_rxfifo_dval == 1'b1 ) begin
	data_d1 <=  	llcrx_rxfifo_data ;
    end
end

always @( posedge clk_wr or negedge rst_wr ) begin
    if( rst_wr == 1'b0 ) begin	
		extract_flag <=   1'b0 ;
	end
    else begin
        if( llcrx_rxfifo_eop == 1'b1 ) begin
    		extract_flag <=   1'b0 ;
    	end
        else if( llcrx_rxfifo_dval == 1'b1 ) begin
    		extract_flag <=   ~ extract_flag ;
    	end
    end
end

always @( posedge clk_wr or negedge rst_wr ) begin
    if( rst_wr == 1'b0 ) begin	
		pfifo_wrdata <=      16'h00 ;
	end
    else begin
        if( ( extract_flag == 1'b1 && llcrx_rxfifo_dval == 1'b1 ) || ( llcrx_rxfifo_eop == 1'b1 && extract_flag == 1'b0 ) ) begin
		    pfifo_wrdata <=  	{ data_d1 , llcrx_rxfifo_data } ;
	    end
        else ;
    end
end

always @( posedge clk_wr ) begin
     if( ( extract_flag == 1'b1 && llcrx_rxfifo_dval == 1'b1 ) || ( llcrx_rxfifo_eop == 1'b1 && extract_flag == 1'b0 ) ) begin
	     pfifo_wren <=  	1'b1 ;
	 end
     else begin
	 	pfifo_wren <=  	1'b0 ;
	 end
end

always @( posedge clk_wr or negedge rst_wr ) begin
    if( rst_wr == 1'b0 ) begin	
		new_sop_flag <=  	1'b0 ;
	end
    else begin
        if ( llcrx_rxfifo_sop == 1'b1 ) begin
    		new_sop_flag <=  	1'b1 ;
    	end
        else if( llcrx_rxfifo_dval == 1'b1 ) begin
    		new_sop_flag <=  	1'b0 ;
    	end
    end
end

always @( posedge clk_wr ) begin
    if ( new_sop_flag == 1'b1 && llcrx_rxfifo_dval == 1'b1 ) begin
    	pfifo_sop <=  	1'b1 ;
    end
    else begin
    	pfifo_sop <=  	1'b0 ;
    end
end

always @( posedge clk_wr ) begin
    if ( llcrx_rxfifo_eop == 1'b1 && extract_flag == 1'b1 ) begin
    	even_byte_eop <=  	llcrx_rxfifo_eop ;
    end
    else begin
    	even_byte_eop <=  	1'b0 ;
    end
end

always @( posedge clk_wr ) begin
    if( llcrx_rxfifo_eop == 1'b1 && extract_flag == 1'b0 ) begin
    	odd_byte_eop <=  	llcrx_rxfifo_eop ;
    end
    else begin
    	odd_byte_eop <=  	1'b0 ;
    end
end

assign  pfifo_eop = ( odd_byte_eop == 1'b1 || even_byte_eop == 1'b1 ) ? 1'b1 : 1'b0 ;

//----------------------------------------------------------------------------------
// pfifo control
//----------------------------------------------------------------------------------
assign  slink_mm_empty  =   pfifo_empty ;   
assign  pfifo_rden = ( pfifo_empty == 1'b0 && mm_slink_rdreq == 1'b1 ) ? 1'b1 : 1'b0 ;

always @( posedge clk_rd ) begin
	pfifo_rden_d1 <=  	pfifo_rden ;
end

//always @( posedge clk_rd ) begin
//    if ( pfifo_rden_d1 == 1'b1 && pfifo_empty == 1'b0 ) begin
//	    slink_mm_dval   <=    1'b1 ;
//    end
//    else begin
//	    slink_mm_dval   <=    1'b0 ;
//    end
//end
//
assign  slink_mm_dval = ( pfifo_rden_d1 == 1'b1 && pfifo_empty == 1'b0 ) ? 1'b1 : 1'b0 ;  
assign  slink_mm_data = pfifo_rddata ;

generate
if( FIFO_TYPE == 2'b00 ) begin

    PFIFO_W18D1024              U_PFIFO_W18D2048
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

end
endgenerate

generate
if( FIFO_TYPE == 2'b01 ) begin

    PFIFO_W18D2048              U_PFIFO_W18D2048
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

end
endgenerate

generate
if( FIFO_TYPE == 2'b10 ) begin

    PFIFO_W18D4096              U_PFIFO_W18D4096
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

end
endgenerate


endmodule

