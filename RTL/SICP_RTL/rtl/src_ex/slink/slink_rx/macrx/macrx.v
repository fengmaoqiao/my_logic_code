// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-06-27
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-06-27  TingtingGan     Original
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

module EX_MACRX
    (
    clk_125m                    ,   
    rst_125m                    ,   

    wd_timer                    ,   
    self_cfg_err                ,
    pcs_err                     ,   

    pcsrx_macrx_dval            ,   
    pcsrx_macrx_sop             ,   
    pcsrx_macrx_eop             ,   
    pcsrx_macrx_data            ,   
    
    macrx_rxfifo_dval           ,   
    macrx_rxfifo_sop            ,   
    macrx_rxfifo_eop            ,   
    macrx_rxfifo_data           , 

    slink_rx_eop                ,   
    slink_err               
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   CARD_TYPE   =   2'b00 ; // MCU : 2'b00 , COM : 2'b01 , EX : 2'b10 , IO : 2'b11    

parameter   CNT_1MS =   32'd125000 ; // 125000 * 8 = 1ms

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_125m                            ;   
input   wire                    rst_125m                            ;   

input   wire    [15:0]          wd_timer                            ;   // watchdog timer , used for detecting packet delay
input   wire                    self_cfg_err                        ;  
input   wire                    pcs_err                             ;   

input   wire                    pcsrx_macrx_dval                    ;   
input   wire                    pcsrx_macrx_sop                     ;   
input   wire                    pcsrx_macrx_eop                     ;   
input   wire    [7:0]           pcsrx_macrx_data                    ;   

// declare output signal
output  reg                     macrx_rxfifo_dval                   ;   
output  reg                     macrx_rxfifo_sop                    ;   
output  wire                    macrx_rxfifo_eop                    ;   
output  reg     [7:0]           macrx_rxfifo_data                   ;   

output  reg                     slink_rx_eop                        ;   
output  wire                    slink_err                           ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [7:0]               chksum_data                         ; 
wire        [31:0]              chksum_dout                         ;
wire                            chksum_sop                          ;   
wire                            chksum_eop                          ;   
wire                            payload_flag                        ;  
wire                            macrx_eop                           ;   

// reg signal
reg         [7:0]               macrx_data_d1                       ; 
reg         [7:0]               macrx_data_d2                       ; 
reg                             macrx_dval_d1                       ;   
reg                             macrx_sop_d1                        ;   
reg                             macrx_eop_d1                        ;   
reg         [2:0]               cnt_55                              ;
reg         [15:0]              pkt_len_cnt                         ;   
reg         [15:0]              pkt_len                             ;  
reg         [15:0]              pkt_tick                            ;   
reg         [15:0]              pkt_tick_d1                         ;  
reg                             pkt_len_err                         ;   
reg                             tick_err                            ; 
reg                             chksum_dval                         ;   
reg         [2:0]               crc_cnt                             ;  
reg         [31:0]              fcs_field                           ;   
reg                             cnt_55_flag                         ;   
reg                             app_data_flag                       ;   
reg                             pkt_len_flag                        ;   
reg                             fcs_field_falg                      ;   
reg                             crc_err                             ;  
reg                             pcsrx_macrx_eop_d1                  ;   
reg                             pcsrx_macrx_eop_d2                  ;  
reg                             pcsrx_macrx_eop_d3                  ;  
reg         [15:0]              com_sta                             ; 
reg                             lost_eop_detect                     ;  
reg                             com_sta_high                        ;   
reg                             com_sta_low                         ;  
reg                             self_cfg_err_d1                     ;   
reg                             self_cfg_err_d2                     ;  
reg                             pkt_extra_flag                      ;  
reg         [3:0]               extra_cnt                           ;   
reg         [31:0]              clk_1ms_cnt                         ;
reg                             clk_1ms_flag                        ;   
reg         [15:0]              delay_cnt                           ; 
reg                             delay_err                           ; 
reg         [15:0]              wd_timer_d1                         ;   
reg         [15:0]              wd_timer_d2                         ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

always @( posedge clk_125m ) begin
	slink_rx_eop	<=  pcsrx_macrx_eop_d3 ;
end

//----------------------------------------------------------------------------------
// delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m ) begin
    macrx_dval_d1   <=  pcsrx_macrx_dval ;  
	macrx_sop_d1    <=  pcsrx_macrx_sop ;
	macrx_eop_d1    <=  pcsrx_macrx_eop ;
end

always @ ( posedge clk_125m ) begin
	macrx_data_d1 <=  	pcsrx_macrx_data ;
    macrx_data_d2   <=  macrx_data_d1 ; 
end

//----------------------------------------------------------------------------------
//  preamble check
//----------------------------------------------------------------------------------
always @( posedge clk_125m ) begin
    if( cnt_55_flag == 1'b1 ) begin
        if( macrx_dval_d1 == 1'b1 && macrx_data_d1 == 8'h55 ) begin
            cnt_55	<=  cnt_55 + 1'b1 ;
        end
    end
    else begin
    	cnt_55	<=  3'b000 ;
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		cnt_55_flag	<=  1'b0 ;
	end
    else begin
        if( macrx_dval_d1 == 1'b1 && macrx_data_d1 != 8'h55 ) begin
            cnt_55_flag	<=  1'b0 ;
        end
        else if( macrx_sop_d1 == 1'b1 && macrx_data_d1 == 8'h55 ) begin
	    	cnt_55_flag	<=  1'b1 ;
	    end
    end
end

//----------------------------------------------------------------------------------
// packet length check
//----------------------------------------------------------------------------------
always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		app_data_flag	<=  	1'b0 ;
	end
    else begin
        if( extra_cnt == 4'd8 || macrx_eop == 1'b1 ) begin
            app_data_flag	<=  	1'b0 ;
        end
        else if( chksum_sop == 1'b1 ) begin
	    	app_data_flag	<=  	1'b1 ;
	    end
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		pkt_len_flag	<=  	1'b0 ;
	end
    else begin
        if( macrx_eop == 1'b1 ) begin
            pkt_len_flag	<=  	1'b0 ;
        end
        else if( chksum_sop == 1'b1 ) begin
	    	pkt_len_flag	<=  	1'b1 ;
	    end
    end
end

always @( posedge clk_125m ) begin
    if( pkt_len_flag == 1'b1 ) begin
        if( macrx_dval_d1 == 1'b1 ) begin
            pkt_len_cnt	<=   pkt_len_cnt + 1'b1 ;
        end
    end
    else begin
    	pkt_len_cnt	<=  16'h00 ;
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		pkt_len <=  16'h0078 ;
	end
    else begin
        if( app_data_flag == 1'b1 && macrx_dval_d1 == 1'b1 ) begin
            if( pkt_len_cnt == 16'd6 ) begin
                pkt_len[15:8]   <=  macrx_data_d1 ;
            end
            else if( pkt_len_cnt == 16'd7 ) begin
                pkt_len[7:0]    <=  macrx_data_d1 ;
            end
        end
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		pkt_extra_flag <=    1'b0 ;
	end
    else begin
        if( macrx_eop == 1'b1 ) begin
	    	pkt_extra_flag <=    1'b0 ;
	    end
        else if ( pkt_len_flag == 1'b1 && pkt_len_cnt == pkt_len ) begin
            pkt_extra_flag <=    1'b1 ;
        end
    end
end

always @( posedge clk_125m ) begin
    if( pkt_extra_flag == 1'b1 ) begin
        if( macrx_dval_d1 == 1'b1 ) begin
            extra_cnt	<=   extra_cnt + 1'b1 ;
        end
    end
    else begin
    	extra_cnt	<=  4'h0 ;
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		pkt_len_err <=    1'b0 ;
	end
    else begin
        if( pcsrx_macrx_eop_d3 == 1'b1 ) begin
	    	pkt_len_err <=    1'b0 ;
	    end
        else if ( macrx_eop_d1 == 1'b1 && extra_cnt != 4'd13 )begin
            pkt_len_err <=    1'b1 ;
        end
        else if ( macrx_dval_d1 == 1'b1 && extra_cnt == 4'd12 && macrx_data_d1 != 8'hfd ) begin
            pkt_len_err <=    1'b1 ;
        end
    end
end

always @( posedge clk_125m ) begin
    if ( macrx_dval_d1 == 1'b1 && extra_cnt == 4'd13 )begin
        lost_eop_detect <=    1'b1 ;
    end
    else begin
        lost_eop_detect <=    1'b0 ;
    end
end

assign  macrx_eop = ( ( macrx_eop_d1 == 1'b1 && pkt_len_flag == 1'b1 ) || lost_eop_detect == 1'b1 ) ? 1'b1 : 1'b0 ;

//----------------------------------------------------------------------------------
// packet serial number check
//----------------------------------------------------------------------------------
always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		pkt_tick <=  	16'h00 ;
	end
    else begin
        if( app_data_flag == 1'b1 && macrx_dval_d1 == 1'b1 ) begin
            if( pkt_len_cnt == 16'd4 ) begin
                pkt_tick[15:8]   <=  	macrx_data_d1 ;
            end
            else if( pkt_len_cnt == 16'd5 ) begin
                pkt_tick[7:0]    <=      macrx_data_d1 ;
            end
        end
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		pkt_tick_d1 <=  	16'h00 ;
	end
    else begin
        if ( pkt_len_cnt == 10'd8 && macrx_rxfifo_dval == 1'b1 )begin
            pkt_tick_d1 <=  	pkt_tick ;
        end
	end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		tick_err <=    1'b0 ;
	end
    else begin
        if( pcsrx_macrx_eop_d3 == 1'b1 ) begin
	    	tick_err <=    1'b0 ;
	    end
        else if ( pkt_len_cnt == 10'd7 && macrx_rxfifo_dval == 1'b1 )begin
            if( pkt_tick != pkt_tick_d1 + 1'b1 ) begin
                tick_err <=    1'b1 ;
            end
            else begin
                tick_err <=    1'b0 ;
            end
        end
    end
end

//----------------------------------------------------------------------------------
// CRC32 generator
//----------------------------------------------------------------------------------
always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        chksum_dval <=   1'b0 ;
    end
    else begin
        if( app_data_flag == 1'b1 && macrx_dval_d1 == 1'b1 ) begin
            chksum_dval <=   1'b1 ;   
        end
        else begin
            chksum_dval <=   1'b0 ;     
        end
    end
end

assign  chksum_sop  = ( macrx_dval_d1 == 1'b1 && macrx_data_d1 == 8'hd5 && cnt_55 == 3'b110 ) ? 1'b1 : 1'b0 ;
assign  chksum_eop  = ( chksum_dval == 1'b1 && extra_cnt == 4'd8 ) ? 1'b1 : 1'b0 ;

assign  chksum_data =  macrx_data_d2 ;
					 
    FCS32                       U_FCS32 
    (
    //input port
    .clk_sys                    ( clk_125m                  ),
    .rst_sys                    ( ~rst_125m                 ),
    .crc_din                    ( chksum_data               ),
    .crc_cap                    ( chksum_eop                ),
    .crc_sop                    ( chksum_sop                ),
    .crc_din_vld                ( chksum_dval               ),
    //output port
    .crc_dout                   ( chksum_dout               )
    );

//----------------------------------------------------------------------------------
// crc32 check
//----------------------------------------------------------------------------------
always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		fcs_field_falg	<=  	1'b0 ;
	end
    else begin
        if( crc_cnt[2] == 1'b1 ) begin
            fcs_field_falg	<=  	1'b0 ;
        end
	    else if( extra_cnt == 4'd8 ) begin
	    	fcs_field_falg	<=  	1'b1 ;
	    end
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		crc_cnt <=  	3'b00 ;
	end
    else begin
        if( fcs_field_falg == 1'b1 ) begin
            if ( macrx_dval_d1 == 1'b1 ) begin
                crc_cnt <=   crc_cnt + 1'b1 ;
            end
            else ;
        end
        else begin
	    	crc_cnt <=  	3'b00 ;
	    end
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		fcs_field <=     32'h00 ;
	end
    else begin
        if( fcs_field_falg == 1'b1 ) begin
            if ( macrx_dval_d1 == 1'b1 ) begin
                fcs_field   <=   { fcs_field[23:0] , macrx_data_d1 } ;
            end
        end
        else begin
	    	fcs_field <=     32'h00 ;
	    end
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		crc_err <=    1'b0 ;
	end
    else begin
        if( pcsrx_macrx_eop_d3 == 1'b1 ) begin
	    	crc_err <=    1'b0 ;
	    end
        else if ( crc_cnt == 3'd4 )begin
            if( fcs_field != chksum_dout ) begin
                crc_err <=    1'b1 ;
            end
            else begin
                crc_err <=    1'b0 ;
            end
        end
    end
end

//----------------------------------------------------------------------------------
// delay check 
//----------------------------------------------------------------------------------
always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
        clk_1ms_cnt   <=   32'h00 ;
    end
    else begin
        if( clk_1ms_cnt == CNT_1MS ) begin
            clk_1ms_cnt   <=   32'h00 ;
        end
        else begin
            clk_1ms_cnt   <=   clk_1ms_cnt + 1'b1 ;
        end
    end
end

always @( posedge clk_125m ) begin
    if( clk_1ms_cnt == CNT_1MS ) begin
        clk_1ms_flag   <=   1'b1 ;
    end
    else begin
        clk_1ms_flag   <=   1'b0 ;
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
        delay_cnt   <=   16'h00 ;
    end
    else begin
        if( macrx_eop == 1'b1 ) begin
            delay_cnt   <=   16'h00 ;
        end
        else if ( clk_1ms_flag == 1'b1 ) begin
            delay_cnt   <=   delay_cnt + 1'b1 ;
        end
    end
end

always @( posedge clk_125m ) begin
	wd_timer_d1	<=  wd_timer ;
	wd_timer_d2	<=  wd_timer_d1 ;
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
        delay_err   <=   1'b0 ;
    end
    else begin
        if( wd_timer_d2 == 16'h0000 ) begin
            delay_err   <=   1'b0 ;
        end
        else if( delay_cnt >= wd_timer_d2 + 3'd5 ) begin
            delay_err   <=   1'b1 ;
        end
        else begin
            delay_err   <=   1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// communication status process
//----------------------------------------------------------------------------------
always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		pcsrx_macrx_eop_d1	<=  	1'b0 ;
		pcsrx_macrx_eop_d2	<=  	1'b0 ;
		pcsrx_macrx_eop_d3	<=  	1'b0 ;
	end
    else begin
		pcsrx_macrx_eop_d1	<=  	macrx_eop ;
		pcsrx_macrx_eop_d2	<=  	pcsrx_macrx_eop_d1 ;
		pcsrx_macrx_eop_d3	<=  	pcsrx_macrx_eop_d2 ;
	end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		com_sta_high <= 1'b0 ;
	end
    else begin
        if( extra_cnt == 4'd6 ) begin
            com_sta_high    <=  1'b1 ;
        end
        else begin
            com_sta_high    <=  1'b0 ;
        end
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		com_sta_low <= 1'b0 ;
	end
    else begin
        if( extra_cnt == 4'd7 ) begin
            com_sta_low    <=  1'b1 ;
        end
        else begin
            com_sta_low    <=  1'b0 ;
        end
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		com_sta <=  	16'h00 ;
	end
    else begin
        if( macrx_dval_d1 == 1'b1 ) begin
            if( com_sta_high == 1'b1 ) begin
                com_sta[15:8]   <=  macrx_data_d1 ;
            end
            else if( com_sta_low == 1'b1 ) begin
                com_sta[7:0]    <=  macrx_data_d1 ;
            end
        end
    end
end

//----------------------------------------------------------------------------------
// new data generator
//----------------------------------------------------------------------------------
assign  payload_flag = ( app_data_flag == 1'b1 && extra_cnt != 4'd6 && extra_cnt != 4'd7 ) ? 1'b1 : 1'b0 ;

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        macrx_rxfifo_dval <=   1'b0 ;
    end
    else begin
        if( ( payload_flag == 1'b1 && macrx_dval_d1 == 1'b1 ) || pcsrx_macrx_eop_d1 == 1'b1 || pcsrx_macrx_eop_d2 == 1'b1 ) begin
            macrx_rxfifo_dval <=   1'b1 ;   
        end
        else begin
            macrx_rxfifo_dval <=   1'b0 ;     
        end
    end
end

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        macrx_rxfifo_sop <=   1'b0 ;
    end
    else begin
        if( app_data_flag == 1'b1 && macrx_dval_d1 == 1'b1 && pkt_len_cnt == 16'd0 ) begin
            macrx_rxfifo_sop <=   1'b1 ;   
        end
        else begin
            macrx_rxfifo_sop <=   1'b0 ;     
        end
    end
end

assign  macrx_rxfifo_eop    =   pcsrx_macrx_eop_d3 ; 

//----------------------------------------------------------------------------------
// data generator
//----------------------------------------------------------------------------------
always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin	
		self_cfg_err_d1	<=  	1'b0 ;
		self_cfg_err_d2	<=  	1'b0 ;
	end
    else begin
		self_cfg_err_d1	<=  	self_cfg_err ;
		self_cfg_err_d2	<=  	self_cfg_err_d1 ;
	end
end

// communication card
generate
if( CARD_TYPE == 2'b01 ) begin

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        macrx_rxfifo_data <=   8'h00 ;
    end
    else begin
        if( pcsrx_macrx_eop_d1 == 1'b1 ) begin
            macrx_rxfifo_data <=    { self_cfg_err_d2 , pkt_len_err , tick_err , crc_err , com_sta[11:8] } ;     
        end
        else if( pcsrx_macrx_eop_d2 == 1'b1 ) begin
            macrx_rxfifo_data <=    com_sta[7:0] ;     
        end
        else begin
            macrx_rxfifo_data <=    macrx_data_d1 ;     
        end
    end
end

end
endgenerate

// extention card
generate
if( CARD_TYPE == 2'b10 ) begin

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        macrx_rxfifo_data <=   8'h00 ;
    end
    else begin
        if( pcsrx_macrx_eop_d1 == 1'b1 ) begin
            macrx_rxfifo_data <=    com_sta[15:8] ;     
        end
        else if( pcsrx_macrx_eop_d2 == 1'b1 ) begin
            macrx_rxfifo_data <=    { com_sta[7:4] , self_cfg_err_d2 , pkt_len_err , tick_err , crc_err } ;     
        end
        else begin
            macrx_rxfifo_data <=    macrx_data_d1 ;     
        end
    end
end

end
endgenerate

// 00 : mcu , 11 : IO
generate
if( CARD_TYPE == 2'b00 || CARD_TYPE == 2'b11  ) begin

always @( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        macrx_rxfifo_data <=   8'h00 ;
    end
    else begin
        if( pcsrx_macrx_eop_d1 == 1'b1 ) begin
            macrx_rxfifo_data <=    com_sta[15:8] ;     
        end
        else if( pcsrx_macrx_eop_d2 == 1'b1 ) begin
            macrx_rxfifo_data <=    { self_cfg_err_d2 , pkt_len_err , tick_err , crc_err , com_sta[3:0] } ;     
        end
        else begin
            macrx_rxfifo_data <=    macrx_data_d1 ;     
        end
    end
end

end
endgenerate

//----------------------------------------------------------------------------------
// slink diagnose
//----------------------------------------------------------------------------------
    EX_SLINK_DIAG                  U_SLINK_DIAG
    (
    .clk_125m                   ( clk_125m                  ),
    .rst_125m                   ( rst_125m                  ),

    .chn_break_err              ( pcs_err                   ),
    .chn_pkt_len_err            ( pkt_len_err               ),
    .chn_pkt_tick_err           ( tick_err                  ),
    .chn_pkt_crc_err            ( crc_err                   ),
    .chn_pkt_delay_err          ( delay_err                 ),
    .chn_pkt_eop                ( macrx_rxfifo_eop          ),
   
    .slink_err                  ( slink_err                 )
    );

endmodule


