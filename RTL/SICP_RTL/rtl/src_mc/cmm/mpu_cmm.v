// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   MPU_CMM
// CREATE DATE      :   2017-09-07
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-07  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   Configuration Memory Management of MPU box  
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

module  MPU_CMM
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    clk_emif                    ,   
    rst_emif                    ,   

    // write port 
    run_cycle                   ,   
    dst_sta_num                 ,   
    tpram_sel                   ,   
    wr_en                       ,   
    wr_data                     ,   

    // read port
    master_slave_flag           ,   
    hot_plug_req                ,   
    cfg_empty                   ,  
    rd_en                       ,  
    tpram_sdu_dval              ,   
    tpram_sdu_data           
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   BASE0_ADDR  =   10'd0 ;  
parameter   DST_BOX_NUM =   3'b000 ;  // mpu box

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
input   wire                    tpram_sel                           ;   
input   wire                    wr_en                               ;   
input   wire        [17:0]      wr_data                             ;
input   wire        [7:0]       master_slave_flag                   ;   
input   wire                    hot_plug_req                        ;   
input   wire                    rd_en                               ;   

// declare output signal
output  reg                     tpram_sdu_dval                      ;   
output  reg         [17:0]      tpram_sdu_data                      ;   
output  wire                    cfg_empty                           ;  

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [17:0]              rd_data                             ;  
wire                            wr_start                            ;  
wire        [3:0]               wr_finish                           ;  

// reg signal
reg         [9:0]               wr_addr                             ;   
reg         [9:0]               rd_addr                             ;  
reg                             tpram_wr_en                         ;  
reg                             tpram_sel_d1                        ; 
reg                             tpram_sel_d2                        ;
reg                             wr_en_d1                            ;   
reg         [17:0]              wr_data_d1                          ;   
reg                             cfg_sel_sync                        ;   
reg                             cfg_sel_sync_d1                     ;   
reg                             cfg_sel_sync_d2                     ;   
reg         [2:0]               self_head_cnt                       ; 
reg         [17:0]              tpram_wr_data                       ;   
reg                             cfg_first_empty                     ;   
reg                             hot_plug_req_d1                     ;   
reg                             hot_plug_req_d2                     ;   
reg                             hot_plug_req_d3                     ;   
reg                             hot_plug                            ;   
reg                             cfg_wr_ok                           ;   
reg                             cfg_wr_ok_d1                        ;   
reg                             cfg_wr_ok_d2                        ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// write control 
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif ) begin
    wr_en_d1    <=  wr_en   ;                       
    wr_data_d1  <=  wr_data ;
end

always @ ( posedge clk_emif ) begin
    tpram_sel_d1    <=   tpram_sel ;
    tpram_sel_d2    <=   tpram_sel_d1 ;
end

assign  wr_start    =   ( tpram_sel_d1 == 1'b1 && tpram_sel_d2 == 1'b0 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        cfg_wr_ok    <=   1'b1 ;
    end
    else begin
        if ( tpram_sel_d1 == 1'b0 && tpram_sel_d2 == 1'b1 ) begin
            cfg_wr_ok    <=   1'b0 ;
        end
        else ;
    end
end

always @ ( posedge clk_12_5m ) begin
    cfg_wr_ok_d1   <=   cfg_wr_ok ;
    cfg_wr_ok_d2   <=   cfg_wr_ok_d1 ;
end

always @ ( posedge clk_emif ) begin
    if( tpram_sel_d1 == 1'b1 && wr_en_d1 == 1'b1 ) begin
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
        if( wr_start == 1'b1 ) begin
            wr_addr   <=   BASE0_ADDR ;
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
        cfg_sel_sync      <=   1'b0 ;
    end
    else begin
        cfg_sel_sync      <=   tpram_sel_d1 ;
    end
end

always @ ( posedge clk_12_5m ) begin
    cfg_sel_sync_d1   <=   cfg_sel_sync ;
    cfg_sel_sync_d2   <=   cfg_sel_sync_d1 ;
end

//----------------------------------------------------------------------------------
// empty generator
//----------------------------------------------------------------------------------

assign  wr_finish   =   ( cfg_sel_sync_d1 == 1'b0 && cfg_sel_sync_d2 == 1'b1 ) ? 1'b1 : 1'b0 ;
assign  cfg_empty   =   cfg_first_empty  ; 

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hot_plug_req_d1   <=   1'b0 ;
    end
    else begin
        hot_plug_req_d1   <=   hot_plug_req ;
    end
end

always @ ( posedge clk_12_5m ) begin
    hot_plug_req_d2   <=   hot_plug_req_d1 ;
    hot_plug_req_d3   <=   hot_plug_req_d2 ;
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hot_plug    <=   1'b0 ;
    end
    else begin
        if ( cfg_wr_ok_d2 == 1'b0 ) begin
            if ( hot_plug_req_d2 == 1'b1 && hot_plug_req_d3 == 1'b0 ) begin
                hot_plug    <=   1'b1 ;
            end
            else begin
                hot_plug    <=   1'b0 ;
            end
        end
        else begin
            hot_plug    <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        cfg_first_empty   <=   1'b1 ;
    end
    else begin
        if( rd_en == 1'b1 && rd_data[16] == 1'b1 && self_head_cnt == 3'd7 ) begin          
            cfg_first_empty   <=   1'b1 ;
        end
        else if( wr_finish == 1'b1 || hot_plug == 1'b1 ) begin
            cfg_first_empty   <=   1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// read control
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        self_head_cnt   <=   3'b000 ;
    end
    else if( rd_en == 1'b1 ) begin
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

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        rd_addr   <=   10'h00 ;
    end
    else begin
        if( self_head_cnt == 3'd5 ) begin
            rd_addr   <=   BASE0_ADDR ;
        end
        else if( rd_en == 1'b1 ) begin
            rd_addr   <=   rd_addr + 1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m ) begin
    tpram_sdu_dval   <=   rd_en ;
end

//----------------------------------------------------------------------------------
// 
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        tpram_sdu_data   <=   18'h00 ;
    end
    else begin
        if( rd_en == 1'b1 ) begin
            case ( self_head_cnt )
                3'd0    : tpram_sdu_data   <=  { 2'b10 , 6'd0, dst_sta_num , DST_BOX_NUM[2:1] } ; // DA Address 
                3'd1    : tpram_sdu_data   <=  { 2'b00 , DST_BOX_NUM[0], 5'd0 , 2'd0, 5'd0, master_slave_flag[0], 2'd0 } ; // DA Address && SA Address
                3'd2    : tpram_sdu_data   <=  { 2'b00 , 16'd0 } ; // SA Address
                3'd3    : tpram_sdu_data   <=  { 2'b00 , run_cycle } ; // CYCLE
                3'd4    : tpram_sdu_data   <=   { 2'b00 , `CFG_TYPE } ;
                3'd5    : tpram_sdu_data   <=   { 2'b00 , 16'h00 } ; // the position of pkt tice , 16bit
                3'd6    : tpram_sdu_data   <=   { 2'b00 , `CFG_DATA_LEN - 8 } ;
                3'd7    : tpram_sdu_data   <=   { 1'b0 , rd_data[16:0] } ;
                default : tpram_sdu_data   <=   18'h00 ;
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
    .A_ADDR                     ( {rd_addr[9:0], 4'h0 }     ), // used bits [13:4] , [3:0] to be grounded 
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

