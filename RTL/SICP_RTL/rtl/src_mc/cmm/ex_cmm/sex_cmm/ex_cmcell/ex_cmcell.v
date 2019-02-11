// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   EX_CMCELL
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
// PURPOSE          :   The smallest unit of Extetion box configuration Memory 
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

module  EX_CMCELL               
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    clk_emif                    ,   
    rst_emif                    ,   

    // mpu box configuration 
    master_slave_flag           ,
    hot_plug_req                ,
    dst_sta_num                 ,   

    // write port 
    cfg_sel                     ,   
    exchn_sel                   ,   
    wr_en                       ,   
    wr_data                     ,   

    // read port
    cm_empty                    ,   
    rd_en                       ,   
    tpram_sdu_dval              ,   
    tpram_sdu_data                
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   BASE0_ADDR  =   10'd000 ;  
parameter   BASE1_ADDR  =   10'd256 ;  
parameter   BASE2_ADDR  =   10'd512 ;  
parameter   BASE3_ADDR  =   10'd768 ; 

parameter   DST_BOX_NUM     =   3'd0 ;
parameter   DST_SLOT_NUM1   =   4'd3   ;  // slot number of destination extetion box 
parameter   DST_SLOT_NUM2   =   4'd4   ;  // slot number of destination extetion box 
parameter   DST_SLOT_NUM3   =   4'd5   ;  // slot number of destination extetion box 
parameter   DST_SLOT_NUM4   =   4'd6   ;  // slot number of destination extetion box

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   
input   wire                    clk_emif                            ;   
input   wire                    rst_emif                            ;   

input   wire        [7:0]       dst_sta_num                         ;   
input   wire        [7:0]       master_slave_flag                   ;   
input   wire        [3:0]       hot_plug_req                        ;   
input   wire                    cfg_sel                             ;   
input   wire        [1:0]       exchn_sel                           ;   
input   wire                    wr_en                               ;   
input   wire        [17:0]      wr_data                             ;
input   wire        [3:0]       rd_en                               ;   

// declare output signal
output  reg         [3:0]       cm_empty                            ;   
output  reg         [3:0]       tpram_sdu_dval                      ;   
output  reg         [17:0]      tpram_sdu_data                      ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [17:0]              rd_data                             ;  
wire        [3:0]               wr_finish                           ; 
wire        [3:0]               tpram_chn_sel                       ;
wire                            wr_sop                              ;   
wire                            wr_eop                              ; 
wire        [2:0]               box_num                             ;   

// reg signal
reg         [9:0]               wr_addr                             ;   
reg         [9:0]               rd_addr                             ;  
reg                             tpram_wr_en                         ; 
reg         [17:0]              tpram_wr_data                       ;
reg         [3:0]               tpram_sel_sync                      ;   
reg         [3:0]               tpram_sel_sync_d1                   ;   
reg         [3:0]               tpram_sel_sync_d2                   ;   
reg         [2:0]               self_head_cnt                       ; 
reg         [3:0]               tpram_chn_sel_d1                    ;   
reg         [3:0]               hot_plug_req_d1                     ;   
reg         [3:0]               hot_plug_req_d2                     ;   
reg         [3:0]               hot_plug_req_d3                     ;   
reg         [3:0]               cfg_wr_ok                           ;   
reg         [3:0]               cfg_wr_ok_d1                        ;   
reg         [3:0]               cfg_wr_ok_d2                        ;   
reg         [3:0]               hot_plug                            ; 
reg                             wr_sel_d1                           ;  
reg                             tpram_sel                           ;   
reg         [3:0]               slot_num                            ;   

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
    wr_sel_d1   <=   cfg_sel ;
end

assign  wr_sop    =   ( cfg_sel == 1'b1 && wr_sel_d1 == 1'b0 ) ? 1'b1 : 1'b0 ;
assign  wr_eop    =   ( tpram_wr_en == 1'b1 && tpram_wr_data[16] == 1'b1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        tpram_sel    <=   1'b0 ;
    end
    else begin
        if ( wr_eop == 1'b1 ) begin
            tpram_sel    <=   1'b0 ;
        end
        else if ( wr_sop == 1'b1 ) begin
            tpram_sel    <=   1'b1 ;
        end
    end
end


always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        tpram_chn_sel_d1    <=   4'h0 ;
    end
    else begin
        tpram_chn_sel_d1    <=   tpram_chn_sel ;
    end
end

always @ ( posedge clk_emif ) begin
    if( tpram_sel == 1'b1 && wr_en == 1'b1 ) begin
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
    else if( wr_sop == 1'b1 ) begin
        case( exchn_sel ) 
            2'b00   : wr_addr   <=   BASE0_ADDR ;
            2'b01   : wr_addr   <=   BASE1_ADDR ;
            2'b10   : wr_addr   <=   BASE2_ADDR ;
            2'b11   : wr_addr   <=   BASE3_ADDR ;
            default : wr_addr   <=   BASE0_ADDR ; 
        endcase
    end
    else if( tpram_wr_en == 1'b1 ) begin
        wr_addr   <=   wr_addr + 1'b1 ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        tpram_wr_data   <=   18'h00 ;
    end
    else begin
        tpram_wr_data   <=   wr_data ;
    end
end

//----------------------------------------------------------------------------------
// chip selection synchronization
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        tpram_sel_sync      <=   4'h0 ;
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
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hot_plug_req_d1   <=   4'h0 ;
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
        cfg_wr_ok_d1   <=   4'hf ;
        cfg_wr_ok_d2   <=   4'hf ;
    end
    else begin
        cfg_wr_ok_d1   <=   cfg_wr_ok ;
        cfg_wr_ok_d2   <=   cfg_wr_ok_d1 ;
    end
end

  genvar i;
  generate
  for( i = 0 ; i < 4 ; i = i+1 ) 
  begin : nIOCHN

assign  tpram_chn_sel[i]    =   ( tpram_sel == 1'b1 && exchn_sel == i ) ? 1'b1 : 1'b0 ;
assign  wr_finish[i]        =   ( tpram_sel_sync_d1[i] == 1'b0 && tpram_sel_sync_d2[i] == 1'b1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        cfg_wr_ok[i]    <=   1'b1 ;
    end
    else begin
        if ( tpram_chn_sel[i] == 1'b0 && tpram_chn_sel_d1[i] == 1'b1 ) begin
            cfg_wr_ok[i]    <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hot_plug[i]    <=   1'b0 ;
    end
    else begin
        if ( cfg_wr_ok_d2[i] == 1'b0 ) begin
            if ( hot_plug_req_d2[i] == 1'b1 && hot_plug_req_d3[i] == 1'b0 ) begin
                hot_plug[i]    <=   1'b1 ;
            end
            else begin
                hot_plug[i]    <=   1'b0 ;
            end
        end
        else begin
            hot_plug[i]    <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        cm_empty[i] <= 1'b1 ;
    end
    else begin
        if( rd_en[i] == 1'b1 && rd_data[16] == 1'b1 && self_head_cnt == 3'd7 ) begin          
            cm_empty[i] <= 1'b1 ;
        end
        else if( wr_finish[i] == 1'b1 || hot_plug[i] == 1'b1 ) begin
            cm_empty[i] <= 1'b0 ;
        end
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

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        rd_addr   <=   10'h00 ;
    end
    else if( self_head_cnt == 3'd5 ) begin
        case( rd_en ) 
            4'b0001 : rd_addr   <=   BASE0_ADDR ;
            4'b0010 : rd_addr   <=   BASE1_ADDR ;
            4'b0100 : rd_addr   <=   BASE2_ADDR ;
            4'b1000 : rd_addr   <=   BASE3_ADDR ;
            default : rd_addr   <=   BASE0_ADDR ; 
        endcase
    end
    else if( | rd_en == 1'b1 ) begin
        rd_addr   <=   rd_addr + 1'b1 ;
    end
end

always @ ( * ) begin
    case( rd_en ) 
        4'b0001 : slot_num   =   DST_SLOT_NUM1 ;
        4'b0010 : slot_num   =   DST_SLOT_NUM2 ;
        4'b0100 : slot_num   =   DST_SLOT_NUM3 ;
        4'b1000 : slot_num   =   DST_SLOT_NUM4 ;
        default : slot_num   =   DST_SLOT_NUM1 ; 
    endcase
end

assign  box_num =   DST_BOX_NUM ;   

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        tpram_sdu_data   <=   18'h00 ;
    end
    else begin
        if( | rd_en == 1'b1 ) begin
            case ( self_head_cnt )
                3'd0    : tpram_sdu_data   <=  { 2'b10 , 6'd0, dst_sta_num, box_num[2:1] } ; // DA Address
                3'd1    : tpram_sdu_data   <=  { 2'b00 , box_num[0], 1'b0, slot_num , 2'd0, 5'd0, master_slave_flag[0], 2'd0 } ; // DA Address && SA Address
                3'd2    : tpram_sdu_data   <=  { 2'b00 , 16'd0 } ; // SA Address
                3'd3    : tpram_sdu_data   <=  { 2'b00 , 16'd0 } ;
                3'd4    : tpram_sdu_data   <=  { 2'b00 , `CFG_TYPE } ;
                3'd5    : tpram_sdu_data   <=  { 2'b00 , 16'h00 } ; // the position of pkt tick , 16bit
                3'd6    : tpram_sdu_data   <=  { 2'b00 , `CFG_DATA_LEN - 8 } ;
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

