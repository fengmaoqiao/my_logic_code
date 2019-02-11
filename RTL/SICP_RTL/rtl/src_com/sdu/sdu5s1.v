// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SDU5S1
// CREATE DATE      :   2017-08-23
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-23  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   9 select 1 schedule machine
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

module COM_SDU5S1
    (
    clk_sys                     ,   
    rst_sys                     ,   
   
    chn_sdu_dval                ,    
    chn_sdu_data                ,    
    chn_sdu_empty               ,  
    sdu_chn_rden                ,

    fifo_rdreq0                 ,   
    fifo_rd_dval0               ,   
    fifo_rd_data0               ,   
    fifo_rdreq1                 ,   
    fifo_rd_dval1               ,   
    fifo_rd_data1                 
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   CHN_NUM         =   5  ; // 5 - 1 schedule
parameter   CHN_NUM_WIDTH   =   4  ;
parameter   DATA_WIDTH      =   18 ; // [17] : sop [16] : eop [15:0] : data  

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys                             ;   
input   wire    [CHN_NUM-1:0]   chn_sdu_dval  	                    ;   
input   wire    [DATA_WIDTH-1:0]chn_sdu_data    	                ;   
input   wire    [CHN_NUM-1:0]   chn_sdu_empty  	                    ;   
input   wire                    fifo_rdreq0                         ;   
input   wire                    fifo_rdreq1                         ;  

// declare output signal
output  wire    [CHN_NUM-1:0]   sdu_chn_rden   	                    ; 
output  wire                    fifo_rd_dval0                       ;   
output  wire    [DATA_WIDTH-1:0]fifo_rd_data0    	                ;   
output  wire                    fifo_rd_dval1                       ;   
output  wire    [DATA_WIDTH-1:0]fifo_rd_data1    	                ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [CHN_NUM-1:0]       chn_eop_flag                        ;   
wire                            eop_flag                            ;   
wire                            rden_act                            ;   
wire                            rd_req                              ;   
wire        [CHN_NUM-1:0]       chn_rden   	                        ;   
wire        [CHN_NUM-1:0]       sdu_turn_empty  	                ;   
wire        [17:0]              rd_data     [1:0]                   ;  
wire        [1:0]               rd_en                               ; 
wire                            wr_en_tmp                           ;   
wire        [17:0]              wr_data_tmp                         ;  
wire                            wr_sop                              ;   
wire                            wr_eop                              ;  
wire                            back_pressure                       ;   

// reg signal
reg         [CHN_NUM_WIDTH-1:0] sdu_num                             ;   
reg                             eop_all_empty                       ;   
reg                             all_empty                           ;   
reg         [CHN_NUM-1:0]       sdu_empty                           ;   
reg         [1:0]               fifo_empty                          ;   
reg         [1:0]               rd_en_d1                            ;   
reg         [9:0]               memwaddr                            ;   
reg         [9:0]               memraddr        [1:0]               ;  
reg                             wr_en                               ;   
reg         [17:0]              wr_data                             ;  
reg         [15:0]              pkt_tick                            ;  
reg                             wr_sop_d1                           ;   
reg                             wr_sop_d2                           ;  
reg         [3:0]               pkt_cnt         [1:0]               ;

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

assign  sdu_turn_empty =   { chn_sdu_empty[0] , chn_sdu_empty[1] , chn_sdu_empty[2] , chn_sdu_empty[3] , chn_sdu_empty[4] };

genvar i;
generate
for( i = 0 ; i < CHN_NUM ; i = i+1 ) 
begin : nCHN

assign  chn_eop_flag[i] = ( chn_sdu_dval[i] == 1'b1 && chn_sdu_data[DATA_WIDTH-2] == 1'b1 ) ? 1'b1 : 1'b0 ;
assign  sdu_chn_rden[i] = ( chn_sdu_empty[i] == 1'b0 && sdu_num == i && rd_req == 1'b1 ) ? 1'b1 : 1'b0 ;
assign  chn_rden[i] = ( chn_sdu_empty[i] == 1'b0 && sdu_num == i ) ? 1'b1 : 1'b0 ;

end
endgenerate

always @( posedge clk_sys or negedge rst_sys ) begin
    if( rst_sys == 1'b0 ) begin
        sdu_num <=   4'b0000 ;
    end
    else if( sdu_num >= 4'd5 ) begin
        sdu_num    <=   sdu_num - 4'd5 ;
    end
    else if( all_empty == 1'b1 ) begin
        if( chn_sdu_empty[0] == 1'b0 ) begin
            sdu_num <=   4'b0000 ;    
        end
        else if( chn_sdu_empty[1] == 1'b0 ) begin
            sdu_num <=   4'b0001 ;
        end
        else if( chn_sdu_empty[2] == 1'b0 ) begin
            sdu_num <=   4'b0010 ;
        end
        else if( chn_sdu_empty[3] == 1'b0 ) begin
            sdu_num <=   4'b0011 ;
        end
        else if( chn_sdu_empty[4] == 1'b0 ) begin
            sdu_num <=   4'b0100 ;
        end
    end
    else if( eop_flag == 1'b1 ||( eop_all_empty == 1'b1 && rden_act == 1'b0 ) ) begin
        if( sdu_empty[4] == 1'b0 ) begin
            sdu_num <=   sdu_num + 4'b0001 ;
        end
        else if( sdu_empty[3] == 1'b0 ) begin
            sdu_num <=   sdu_num + 4'b0010 ;
        end
        else if( sdu_empty[2] == 1'b0 ) begin
            sdu_num <=   sdu_num + 4'b0011 ;
        end
        else if( sdu_empty[1] == 1'b0 ) begin
            sdu_num <=   sdu_num + 4'b0100 ;
        end
        else begin
            sdu_num <=   sdu_num ;
        end
    end 
end

always @( * ) begin
    case( sdu_num )
        3'b000   :   sdu_empty    =  { sdu_turn_empty[3:0], sdu_turn_empty[4] } ;
        3'b001   :   sdu_empty    =  { sdu_turn_empty[2:0], sdu_turn_empty[4:3] } ;
        3'b010   :   sdu_empty    =  { sdu_turn_empty[1:0], sdu_turn_empty[4:2] } ;
        3'b011   :   sdu_empty    =  { sdu_turn_empty[0],   sdu_turn_empty[4:1] } ;
        3'b100   :   sdu_empty    =  sdu_turn_empty ;
        default  :   sdu_empty    =  sdu_turn_empty ;
    endcase
end

assign  eop_flag = | chn_eop_flag ;
assign  rden_act = | chn_rden ;

//assign  rd_req   = ( back_pressure == 1'b0 && all_empty == 1'b0 ) ? 1'b1 : 1'b0 ;
assign  rd_req   = ( & fifo_empty == 1'b1 && all_empty == 1'b0 ) ? 1'b1 : 1'b0 ;

always @( posedge clk_sys ) begin
    if( & chn_sdu_empty == 1'b1 ) begin
        all_empty   <=   1'b1 ;   
    end
    else begin
        all_empty   <=   1'b0 ;
    end
end

always @( posedge clk_sys or negedge rst_sys ) begin
    if( rst_sys == 1'b0 ) begin
        eop_all_empty   <=   1'b0 ;   
    end
    else begin
        if( eop_all_empty == 1'b1 && all_empty == 1'b0 ) begin
            eop_all_empty   <=   1'b0 ;
        end
        else if( eop_flag == 1'b1 && ( & sdu_empty[CHN_NUM-1:1] == 1'b1 ) ) begin
            eop_all_empty   <=   1'b1 ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// fifo
//----------------------------------------------------------------------------------

assign  wr_en_tmp   =   | chn_sdu_dval ;
assign  wr_data_tmp =   chn_sdu_data ;
assign  wr_sop      =   ( wr_en_tmp == 1'b1 && wr_data_tmp[17] == 1'b1 ) ? 1'b1 : 1'b0 ;
assign  wr_eop      =   ( wr_en_tmp == 1'b1 && wr_data_tmp[16] == 1'b1 ) ? 1'b1 : 1'b0 ;

always @( posedge clk_sys ) begin
    wr_en  <=   wr_en_tmp ;
end

always @( posedge clk_sys ) begin
    wr_sop_d1  <=   wr_sop ;
    wr_sop_d2  <=   wr_sop_d1 ;
end

always @( posedge clk_sys or negedge rst_sys ) begin
    if( rst_sys == 1'b0 ) begin
        pkt_tick <=   16'h00 ;           
    end
    else begin
        if( wr_sop == 1'b1 ) begin
            pkt_tick <=   pkt_tick + 1'b1 ;
        end
        else ;
    end
end

always @( posedge clk_sys ) begin
    if ( wr_sop_d2 == 1'b1 ) begin
        wr_data  <=   { 2'b00 , pkt_tick } ;
    end
    else begin
        wr_data  <=   wr_data_tmp ;
    end
end

assign  rd_en[0] = ( fifo_empty[0] == 1'b0 && fifo_rdreq0 == 1'b1 ) ? 1'b1 : 1'b0 ;
assign  rd_en[1] = ( fifo_empty[1] == 1'b0 && fifo_rdreq1 == 1'b1 ) ? 1'b1 : 1'b0 ;

assign  fifo_rd_dval0 = rd_en_d1[0] ;
assign  fifo_rd_dval1 = rd_en_d1[1] ;

assign  fifo_rd_data0 = rd_data[0] ;
assign  fifo_rd_data1 = rd_data[1] ;

//----------------------------------------------------------------------------------
// write address generator
//----------------------------------------------------------------------------------
always @( posedge clk_sys or negedge rst_sys ) begin
    if( rst_sys == 1'b0 ) begin
        memwaddr <= 10'h00 ;
    end
    else begin
        if( wr_en == 1'b1 ) begin
            if( memwaddr == 1023 ) begin 
                memwaddr <= 10'h00 ;
            end
            else begin
                memwaddr <= memwaddr + 1'b1 ;
            end
        end
    end
end

//----------------------------------------------------------------------------------
// LSRAM control
//----------------------------------------------------------------------------------
  genvar j ;
  generate
  for( j = 0 ; j < 2 ; j = j+1 ) 
  begin : nLSRAM

always @( posedge clk_sys ) begin
    rd_en_d1[j]   <=   rd_en[j] ;
end

always @( posedge clk_sys or negedge rst_sys ) begin
    if( rst_sys == 1'b0 ) begin
        fifo_empty[j]   <=   1'b1 ;
    end
    else begin
        if( rd_en[j] == 1'b1 && rd_data[j][16] == 1'b1 ) begin
            fifo_empty[j]   <=   1'b1 ;  
        end
        else if( wr_en_tmp == 1'b1 && wr_data_tmp[16] == 1'b1 ) begin
            fifo_empty[j]   <=   1'b0 ;  
        end
    end
end

always @( posedge clk_sys or negedge rst_sys ) begin
    if( rst_sys == 1'b0 ) begin
        memraddr[j] <= 10'h00 ;
    end
    else begin
        if( rd_en[j] == 1'b1 ) begin
            if( memraddr[j] == 1023 ) begin 
                memraddr[j] <= 10'h00 ;
            end
            else if( fifo_empty[j] == 1'b1 && rd_en_d1[j] == 1'b1 ) begin
                memraddr[j] <= memraddr[j] ;
            end
            else begin
                memraddr[j] <= memraddr[j] + 1'b1 ;
            end
        end
    end
end

//always @( posedge clk_sys or negedge rst_sys ) begin
//    if( rst_sys == 1'b0 ) begin
//        pkt_cnt[j] <= 4'h0 ;
//    end
//    else begin
//        if( rd_en[j] == 1'b1 && rd_data[j][16] == 1'b1 && wr_eop == 1'b1 ) begin          
//            pkt_cnt[j] <= pkt_cnt[j] ;
//        end
//        else if( wr_eop == 1'b1 ) begin
//            pkt_cnt[j] <= pkt_cnt[j] + 1'b1 ;
//        end
//        else if( rd_en[j] == 1'b1 && rd_data[j][16] == 1'b1 ) begin          
//            pkt_cnt[j] <= pkt_cnt[j] - 1'b1 ;
//        end
//        else ;
//    end
//end
//
//assign  back_pressure   =   ( pkt_cnt[0][3] == 1'b1 || pkt_cnt[1][3] == 1'b1 ) ? 1'b1 : 1'b0 ;

    RAM1K18                     U_0_LSRAM_W10D1024 
    (
    .A_DOUT                     ( rd_data[j]                        ), 
    .B_DOUT                     (                                   ), 
    .BUSY                       (                                   ), 
    .A_CLK                      ( clk_sys                           ), 
    .A_DOUT_CLK                 ( 1'b1                              ), 
    .A_ARST_N                   ( 1'b1                              ), 
    .A_DOUT_EN                  ( 1'b1                              ), // 0 : register holds previous data ; 1 : normal register operation 
    .A_BLK                      ( 3'b111                            ), // 111 : perform read or write operation on port A 
    .A_DOUT_ARST_N              ( 1'b1                              ), 
    .A_DOUT_SRST_N              ( 1'b1                              ), 
    .A_DIN                      ( 18'h00                            ),  
    .A_ADDR                     ( { memraddr[j] , 4'h0 }            ), // used bits [13:4] , [3:0] to be grounded 
    .A_WEN                      ( 2'b00                             ), // 00 : read operation
    .B_CLK                      ( clk_sys                           ), 
    .B_DOUT_CLK                 ( 1'b1                              ), 
    .B_ARST_N                   ( 1'b1                              ), 
    .B_DOUT_EN                  ( 1'b1                              ), // 0 : register holds previous data ; 1 : normal register operation
    .B_BLK                      ( { wr_en , 2'b11 }                 ), // 011 : no operation ; 111 : read or write operation 
    .B_DOUT_ARST_N              ( 1'b0                              ), 
    .B_DOUT_SRST_N              ( 1'b1                              ), 
    .B_DIN                      ( wr_data                           ), 
    .B_ADDR                     ( { memwaddr , 4'h0 }               ), // used bits [13:4] , [3:0] to be grounded  
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

  end
  endgenerate

endmodule
