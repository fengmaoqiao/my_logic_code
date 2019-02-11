// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   TYPE1_DMMTX
// CREATE DATE      :   2017-08-21
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-21  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   Data Memory Management of TYPE1 transmit data path
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

module  TYPE1_DMMTX
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    clk_emif                    ,   
    rst_emif                    ,   

    // mpu box configuration 
    run_cycle                   ,   
    dst_sta_num                 ,   
    chn_type                    , 
    master_slave_flag           ,
    dst_box_num                 ,   

    // write port 
    wr_sel                      ,   
    chn_sel                     ,   
    wr_en                       ,   
    wr_data                     ,   

    // read port
    dmm_empty                   ,   
    rd_en                       ,   
    tpram_sdu_dval              ,   
    tpram_sdu_data              ,
                   
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
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
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   
input   wire                    clk_emif                            ;   
input   wire                    rst_emif                            ;   

input   wire        [15:0]      run_cycle                           ;   
input   wire        [7:0]       dst_sta_num                         ;   
input   wire        [2:0]       dst_box_num                         ; 
input   wire                    wr_sel                              ;   
input   wire        [3:0]       chn_sel                             ;   
input   wire                    wr_en                               ;   
input   wire        [17:0]      wr_data                             ;
input   wire        [4:0]       chn_type                            ;
input   wire        [7:0]       master_slave_flag                   ;   
input   wire        [15:0]      rd_en                               ;   

// declare output signal
output  reg         [15:0]      tpram_sdu_dval                      ;   
output  reg         [17:0]      tpram_sdu_data                      ;   
output  reg         [15:0]      dmm_empty                           ; 

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [17:0]              rd_data                             ; 
wire                            wr_sop                              ;   
wire        [15:0]              wr_finish                           ;   
wire        [15:0]              tpram_chn_sel                       ; 

// reg signal
reg                             wr_sel_d1                           ;   
reg                             wr_sel_d2                           ; 
reg         [3:0]               chn_sel_d1                          ; 
reg         [17:0]              wr_data_d1                          ;   
reg                             wr_en_d1                            ;   
reg         [9:0]               wr_addr                             ;   
reg         [9:0]               rd_addr                             ;  
reg                             tpram_wr_en                         ; 
reg         [17:0]              tpram_wr_data                       ;
reg         [15:0]              tpram_sel_sync                      ;   
reg         [15:0]              tpram_sel_sync_d1                   ;   
reg         [15:0]              tpram_sel_sync_d2                   ;   
reg         [2:0]               self_head_cnt                       ;   
reg         [15:0]              pkt_lenth                           ;   
reg         [3:0]               slot_num                            ;  
reg         [4:0]               chn_type_d1                         ;   
reg         [4:0]               chn_type_d2                         ;   
reg         [2:0]               dst_box_num_temp                    ;   

reg         [31:0]              wr_finish_dly_cnt[0:15]             ;
reg         [15:0]              wr_finish_dly                       ;   
reg         [31:0]              send_data_slot                      ;
reg         [1:0]               wr_resend_cnt[0:15]                 ;  
    
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
localparam DATA_SLOT_TIME = 32'd162500;

always @( posedge clk_12_5m or negedge rst_12_5m ) begin 
    if( ~rst_12_5m ) begin
            send_data_slot <= DATA_SLOT_TIME ;
    end else begin
        if( run_cycle > 16'd30 )
            send_data_slot <= { run_cycle ,12'b0 } + { run_cycle , 10'b0 } ;
        else
            send_data_slot <= DATA_SLOT_TIME ;
    end
end
/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// write control 
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif ) begin
    chn_sel_d1 <= chn_sel ;                       
    wr_en_d1   <= wr_en   ;                       
    wr_data_d1 <= wr_data ;                     
end

always @ ( posedge clk_emif ) begin
    wr_sel_d1    <=   wr_sel ;
    wr_sel_d2    <=   wr_sel_d1 ;
end

assign  wr_sop  = ( wr_sel_d1 == 1'b1 && wr_sel_d2 == 1'b0 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_emif ) begin
    if( wr_sel_d1 == 1'b1 && wr_en_d1 == 1'b1 ) begin
        tpram_wr_en   <=   1'b1 ;
    end
    else begin
        tpram_wr_en   <=   1'b0 ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        wr_addr   <=   10'h00 ;
    end
    else begin
        if( wr_sop == 1'b1 ) begin
            case( chn_sel_d1 ) 
                4'h0    : wr_addr   <=   BASE0_ADDR ;
                4'h1    : wr_addr   <=   BASE1_ADDR ;
                4'h2    : wr_addr   <=   BASE2_ADDR ;
                4'h3    : wr_addr   <=   BASE3_ADDR ;
                4'h4    : wr_addr   <=   BASE4_ADDR ;
                4'h5    : wr_addr   <=   BASE5_ADDR ;
                4'h6    : wr_addr   <=   BASE6_ADDR ;
                4'h7    : wr_addr   <=   BASE7_ADDR ;
                4'h8    : wr_addr   <=   BASE8_ADDR ;
                4'h9    : wr_addr   <=   BASE9_ADDR ;
                4'ha    : wr_addr   <=   BASEA_ADDR ;
                4'hb    : wr_addr   <=   BASEB_ADDR ;
                4'hc    : wr_addr   <=   BASEC_ADDR ;
                4'hd    : wr_addr   <=   BASED_ADDR ;
                4'he    : wr_addr   <=   BASEE_ADDR ;
                4'hf    : wr_addr   <=   BASEF_ADDR ;
                default : wr_addr   <=   BASE0_ADDR ; 
            endcase
        end
        else if( tpram_wr_en == 1'b1 )begin
            wr_addr   <=   wr_addr + 1'b1 ;
        end
    end
end

always @ ( posedge clk_emif ) begin
    tpram_wr_data   <=   wr_data_d1 ;
end

//----------------------------------------------------------------------------------
// chip selection synchronization
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        tpram_sel_sync      <=   16'h00 ;
    end
    else begin
        tpram_sel_sync      <=   tpram_chn_sel ;
    end
end

always @ ( posedge clk_12_5m ) begin
    tpram_sel_sync_d1   <=   tpram_sel_sync ;
    tpram_sel_sync_d2   <=   tpram_sel_sync_d1 ;
end


//----------------------------------------------------------------------------------
// empty generator
//----------------------------------------------------------------------------------
wire    debug_wr_finish_d;
assign  debug_wr_finish_d   =   |wr_finish_dly ;
wire    debug_wr_finish;
assign  debug_wr_finish     =   |wr_finish  ;

  genvar i;
  generate
  for( i = 0 ; i < 16 ; i = i+1 ) 
  begin : nIOCHN

assign  tpram_chn_sel[i]    =   ( wr_sel_d1 == 1'b1 && chn_sel_d1 == i ) ? 1'b1 : 1'b0 ;
assign  wr_finish[i]        =   ( tpram_sel_sync_d1[i] == 1'b0 && tpram_sel_sync_d2[i] == 1'b1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        dmm_empty[i] <= 1'b1 ;
    end
    else begin
        if( rd_en[i] == 1'b1 && rd_data[16] == 1'b1 && self_head_cnt == 3'd7 ) begin          
            dmm_empty[i] <= 1'b1 ;
        end
        else if( wr_finish[i] == 1'b1 || wr_finish_dly[i] == 1'b1 ) begin
            dmm_empty[i] <= 1'b0 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        wr_finish_dly_cnt[i] <= 32'd0;
    end
    else begin
        if( wr_finish[i] == 1'b1 || ( wr_finish_dly_cnt[i] == 32'd0 && wr_resend_cnt[i] < 2'd2 ) )
            wr_finish_dly_cnt[i] <= send_data_slot;
        else if( wr_finish_dly_cnt[i] != 32'd0 )
            wr_finish_dly_cnt[i] <= wr_finish_dly_cnt[i] - 1;
        else
            ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        wr_resend_cnt[i] <= 32'd0;
    end
    else begin
        if( wr_finish[i] == 1'b1 )
            wr_resend_cnt[i]    <= 2'd0 ;
        else if( wr_finish_dly_cnt[i] == 32'd1 )
            wr_resend_cnt[i]    <= wr_resend_cnt[i] + 1;
        else
            ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        wr_finish_dly[i] <= 1'b0;
    end
    else begin
        if( wr_finish_dly_cnt[i] == 32'd1 )
            wr_finish_dly[i] <= 1'b1;
        else if( wr_finish_dly_cnt[i] == 32'd0 )
            wr_finish_dly[i] <= 1'b0;
    end
end

always @ ( posedge clk_12_5m ) begin
    tpram_sdu_dval[i]   <=   rd_en[i] ;
end

  end
  endgenerate

//----------------------------------------------------------------------------------
// read control
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        self_head_cnt   <=   3'b000 ;
    end
    else begin
        if( | rd_en == 1'b1 ) begin
            if( rd_data[16] == 1'b1 && self_head_cnt == 3'd7 ) begin
                self_head_cnt   <=   3'b000 ;
            end
            else if( self_head_cnt == 3'd7 ) begin
                self_head_cnt   <=   self_head_cnt ;
            end
            else begin
                self_head_cnt   <=   self_head_cnt + 1'b1 ;
            end
        end
    end
end

always @ ( * ) begin
    case( rd_en ) 
        16'b0000000000000001 : slot_num   =   4'h0 ;
        16'b0000000000000010 : slot_num   =   4'h1 ;
        16'b0000000000000100 : slot_num   =   4'h2 ;
        16'b0000000000001000 : slot_num   =   4'h3 ;
        16'b0000000000010000 : slot_num   =   4'h4 ;
        16'b0000000000100000 : slot_num   =   4'h5 ;
        16'b0000000001000000 : slot_num   =   4'h6 ;
        16'b0000000010000000 : slot_num   =   4'h7 ;
        16'b0000000100000000 : slot_num   =   4'h8 ;
        16'b0000001000000000 : slot_num   =   4'h9 ;
        16'b0000010000000000 : slot_num   =   4'ha ;
        16'b0000100000000000 : slot_num   =   4'hb ;
        16'b0001000000000000 : slot_num   =   4'hc ;
        16'b0010000000000000 : slot_num   =   4'hd ;
        16'b0100000000000000 : slot_num   =   4'he ;
        16'b1000000000000000 : slot_num   =   4'hf ;
        default              : slot_num   =   4'h0 ; 
    endcase
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        rd_addr   <=   10'h00 ;
    end
    else begin
        if( self_head_cnt == 3'd5 ) begin
            case( rd_en ) 
                16'b0000000000000001 : rd_addr   <=   BASE0_ADDR ;
                16'b0000000000000010 : rd_addr   <=   BASE1_ADDR ;
                16'b0000000000000100 : rd_addr   <=   BASE2_ADDR ;
                16'b0000000000001000 : rd_addr   <=   BASE3_ADDR ;
                16'b0000000000010000 : rd_addr   <=   BASE4_ADDR ;
                16'b0000000000100000 : rd_addr   <=   BASE5_ADDR ;
                16'b0000000001000000 : rd_addr   <=   BASE6_ADDR ;
                16'b0000000010000000 : rd_addr   <=   BASE7_ADDR ;
                16'b0000000100000000 : rd_addr   <=   BASE8_ADDR ;
                16'b0000001000000000 : rd_addr   <=   BASE9_ADDR ;
                16'b0000010000000000 : rd_addr   <=   BASEA_ADDR ;
                16'b0000100000000000 : rd_addr   <=   BASEB_ADDR ;
                16'b0001000000000000 : rd_addr   <=   BASEC_ADDR ;
                16'b0010000000000000 : rd_addr   <=   BASED_ADDR ;
                16'b0100000000000000 : rd_addr   <=   BASEE_ADDR ;
                16'b1000000000000000 : rd_addr   <=   BASEF_ADDR ;
                default              : rd_addr   <=   BASE0_ADDR ; 
            endcase
        end
        else if( | rd_en == 1'b1 ) begin
            rd_addr   <=   rd_addr + 1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m ) begin
    chn_type_d1   <=   chn_type ;
    chn_type_d2   <=   chn_type_d1 ;
end

always @ ( posedge clk_12_5m ) begin
    if( chn_type_d2 == `COM2_TYPE || chn_type_d2 == `COM3_TYPE ) begin
        pkt_lenth   <=  `COM_DATA_LEN - 4'd8  ;
    end
    else begin
        pkt_lenth   <=  `IO_DATA_LEN - 4'd8  ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        dst_box_num_temp <=   3'd0 ;
    end
    else begin
        dst_box_num_temp    <=   dst_box_num + 1'b1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        tpram_sdu_data   <=   18'h00 ;
    end
    else begin
        if( | rd_en == 1'b1 ) begin
            case ( self_head_cnt )
                3'd0    : tpram_sdu_data   <=  { 2'b10 , 6'd0, dst_sta_num , dst_box_num_temp[2:1] } ; // DA Address 
                3'd1    : tpram_sdu_data   <=  { 2'b00 , dst_box_num_temp[0], slot_num , 2'd0, 5'd0, master_slave_flag[0], 2'd0 } ; // DA Address && SA Address
                3'd2    : tpram_sdu_data   <=  { 2'b00 , 16'd0 } ; // SA Address
                3'd3    : tpram_sdu_data   <=  { 2'b00 , run_cycle } ; // CYCLE
                3'd4    : tpram_sdu_data   <=  { 2'b00 , `DATA_TYPE } ;
                3'd5    : tpram_sdu_data   <=  { 2'b00 , 16'h00 } ; // the position of pkt tick , 16bit
                3'd6    : tpram_sdu_data   <=  { 2'b00 , pkt_lenth } ;
                3'd7    : tpram_sdu_data   <=  { 1'b0  , rd_data[16:0] } ;
                default : tpram_sdu_data   <=  18'h00 ;
            endcase
        end
    end
end

//----------------------------------------------------------------------------------
// LSRAM instance  
//----------------------------------------------------------------------------------
    RAM1K18                     U1_LSRAM_W10D1024 
    (
    .A_DOUT                     ( rd_data                   ), 
    .B_DOUT                     (                           ), 
    .BUSY                       (                           ), 
    .A_CLK                      ( clk_12_5m                 ), 
    .A_DOUT_CLK                 ( 1'b1                      ), 
    .A_ARST_N                   ( 1'b1                      ), 
    .A_DOUT_EN                  ( 1'b1                      ), // 0 : register holds previous data ; 1 : normal register operation 
    .A_BLK                      ( 3'b111                    ), // 111 : perform read or write operation on port A 
    .A_DOUT_ARST_N              ( 1'b1                      ), 
    .A_DOUT_SRST_N              ( 1'b1                      ), 
    .A_DIN                      ( 18'h00                    ),  
    .A_ADDR                     ( { rd_addr[9:0], 4'h0 }    ), // used bits [13:4] , [3:0] to be grounded 
    .A_WEN                      ( 2'b00                     ), // 00 : read operation
    .B_CLK                      ( clk_emif                  ), 
    .B_DOUT_CLK                 ( 1'b1                      ), 
    .B_ARST_N                   ( 1'b1                      ), 
    .B_DOUT_EN                  ( 1'b1                      ), // 0 : register holds previous data ; 1 : normal register operation
    .B_BLK                      ( { tpram_wr_en , 2'b11 }   ), // 011 : no operation ; 111 : read or write operation 
    .B_DOUT_ARST_N              ( 1'b0                      ), 
    .B_DOUT_SRST_N              ( 1'b1                      ), 
    .B_DIN                      ( tpram_wr_data             ), 
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


endmodule

