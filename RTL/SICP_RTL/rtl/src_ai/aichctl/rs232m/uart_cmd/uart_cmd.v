// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-06-10
// DEPARTMENT       :   R&D
// AUTHOR           :   YongjunZhang
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-06-10  YongjunZhang        Original
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

module UART_CMD
(   
        rst_sys_n               ,   
        clk_sys                 ,   
    
        uart_tx_wen             ,   
        uart_tx_wdata           ,   
        uart_tx_rdy             ,   
    
        uart_rx_ren             ,   
        uart_rx_rdata           ,       

        ad_rd_dval              ,   
        ad_rd_value0            ,   
        ad_rd_value1            ,   
        ad_rd_value2            ,   
        ad_rd_value3            ,   
        ad_rd_value4            ,   
        ad_rd_value5            ,   
        ad_rd_value6            ,   
        ad_rd_value7            ,   
        ad_rd_value8            ,   
        ad_rd_value9            ,   
        ad_rd_value10           ,   
        ad_rd_value11           ,
        e2p_urd_dval            ,   
        e2p_rd_value            ,
  
        cal_ch_index            ,   
        uart_tx_wenl            ,   
        uart_tx_wdatal          ,   
        uart_tx_wenh            ,   
        uart_tx_wdatah          ,  
        rd_en                   ,
        wr_en                   ,   
        wr_value0               ,   
        wr_value1               ,   
        wr_value2               ,   
        wr_value3               ,   
        wr_addr                 ,   
        wr_done                 ,   
        e2p_rw_sel              ,
        e2p_busy                   

);

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
localparam  TM_CNT      =   16'hffff ;
localparam  BOARD_ADDR  =   8'b00010000 ;

localparam  IDLE        =   12'b000000000000  ;
localparam  FUN_SEL     =   12'b000000000010  ;
localparam  RD_FST      =   12'b000000000100  ;
localparam  RD_SCD      =   12'b000000001000  ;
localparam  RD_THD      =   12'b000000010000  ;
localparam  RD_FTH      =   12'b000000100000  ;
localparam  CRC_DLY     =   12'b000001000000  ;
localparam  FUN_SUS     =   12'b000010000000  ;
localparam  FUN_ERR     =   12'b000100000000  ;
localparam  FUN_END     =   12'b001000000000  ;

localparam  CAL_ACQ     =   8'h31             ;
localparam  CH_CAL      =   8'h32             ;
localparam  CON_CH_DATA =   8'h33             ;
localparam  DATA_ACQ    =   8'h34             ;
localparam  CAL_END     =   8'h35             ;
localparam  TEST_CMD    =   8'h55             ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    uart_rx_ren                         ;   
input   wire    [7:0]           uart_rx_rdata                       ;   
input   wire                    uart_tx_rdy                         ;   
input   wire                    e2p_busy                            ;   
input   wire                    wr_done                             ; 
input   wire    [11:0]          ad_rd_dval                          ;   
input   wire    [15:0]          ad_rd_value0                        ;   
input   wire    [15:0]          ad_rd_value1                        ;   
input   wire    [15:0]          ad_rd_value2                        ;   
input   wire    [15:0]          ad_rd_value3                        ;   
input   wire    [15:0]          ad_rd_value4                        ;   
input   wire    [15:0]          ad_rd_value5                        ;   
input   wire    [15:0]          ad_rd_value6                        ;   
input   wire    [15:0]          ad_rd_value7                        ;   
input   wire    [15:0]          ad_rd_value8                        ;   
input   wire    [15:0]          ad_rd_value9                        ;   
input   wire    [15:0]          ad_rd_value10                       ;   
input   wire    [15:0]          ad_rd_value11                       ; 
input   wire                    uart_tx_wenl                        ;   
input   wire    [7:0]           uart_tx_wdatal                      ;   
input   wire                    uart_tx_wenh                        ;   
input   wire    [7:0]           uart_tx_wdatah                      ;   
input   wire                    e2p_urd_dval                        ;   
input   wire    [31:0]          e2p_rd_value                        ; 
// declare output signal
output  wire                    e2p_rw_sel                          ;   
output  wire                    uart_tx_wen                         ;   
output  wire   [7:0]            uart_tx_wdata                       ;   
output  wire                    rd_en                               ;  
output  wire                    wr_en                               ;   
output  wire   [31:0]           wr_value0                           ;   
output  wire   [31:0]           wr_value1                           ;   
output  wire   [31:0]           wr_value2                           ;   
output  wire   [31:0]           wr_value3                           ;   
output  wire   [15:0]           wr_addr                             ;   
output  wire    [11:0]          cal_ch_index                        ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            kb_crc_trig                         ;   
wire                            acq_data_trig                       ;   
wire    [15:0]                  acq_ch_num                          ;
wire    [1:0]                   acq_data_sel                        ;
// reg signal
reg     [11:0]                  next_state                          ;   
reg     [1:0]                   rx_cnt                              ; 
reg     [20:0]                  tm_out                              ;   
reg                             cal_con_en                          ;   
   
reg                             con_err_trig                        ;   
reg     [11:0]                  cur_state                           ;   
reg                             cal_end_trig                        ;   
reg     [3:0]                   dly_crc_cnt                         ;   
 
reg                             con_suc_trig                        ;   
reg     [2:0]                   data_fun_sel                        ;   
reg                             cal_acq_trig                        ;   
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign  e2p_rw_sel = cal_con_en ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cur_state   <=  IDLE ;
    end
    else begin
        cur_state   <=  next_state ;
    end
end

always @ ( * ) begin
    case ( cur_state )
        IDLE : begin
            if ( uart_rx_ren == 1'b1 && uart_rx_rdata == BOARD_ADDR ) begin
                next_state = FUN_SEL ;
            end
            else begin
                next_state = IDLE ;
            end
        end
        FUN_SEL : begin
            if ( uart_rx_ren == 1'b1 && uart_rx_rdata == CAL_ACQ ) begin
                next_state = IDLE ;
            end
            else if ( uart_rx_ren == 1'b1 && uart_rx_rdata == CAL_END ) begin
                next_state = IDLE ;
            end
            else if ( uart_rx_ren == 1'b1 && cal_con_en == 1'b1 && uart_rx_rdata == CH_CAL || uart_rx_rdata == CON_CH_DATA || uart_rx_rdata == DATA_ACQ ) begin
                next_state = RD_FST ;
            end
            else if ( tm_out[20] == 1'b1 || uart_rx_ren == 1'b1 && ( uart_rx_rdata != CAL_ACQ || uart_rx_rdata != CH_CAL )) begin
                next_state = FUN_ERR ;
            end
            else begin
                next_state = FUN_SEL ; 
            end
        end
        RD_FST : begin
            if ( uart_rx_ren == 1'b1 && rx_cnt == 2'd3 ) begin
                next_state = RD_SCD ;
            end
            else if ( tm_out[20] == 1'b1 ) begin
                next_state = FUN_ERR ;
            end
            else begin
                next_state = RD_FST ;
            end
        end
        RD_SCD : begin
            if ( uart_rx_ren == 1'b1 && rx_cnt == 2'd3 ) begin
                next_state = RD_THD ;
            end
            else if ( tm_out[20] == 1'b1 ) begin
                next_state = FUN_ERR ;
            end
            else begin
                next_state = RD_SCD ;
            end
        end
        RD_THD : begin
            if ( uart_rx_ren == 1'b1 && rx_cnt == 2'd3 ) begin
                next_state = RD_FTH ;
            end
            else if ( tm_out[20] == 1'b1 ) begin
                next_state = FUN_ERR ;
            end
            else begin
                next_state = RD_THD ;
            end
        end
        RD_FTH : begin
            if ( uart_rx_ren == 1'b1 && rx_cnt == 2'd3 ) begin
                next_state = CRC_DLY ;
            end
            else if ( tm_out[20] == 1'b1 ) begin
                next_state = FUN_ERR ;
            end
            else begin
                next_state = RD_FTH ;
            end
        end
        CRC_DLY : begin
            if ( dly_crc_cnt == 4'd15 ) begin
                next_state = FUN_SUS ;
            end
            else begin
                next_state = CRC_DLY ;
            end
        end
        FUN_SUS : begin
            next_state = FUN_END ;
        end
        FUN_ERR : begin
            next_state = FUN_END ;
        end
        FUN_END : begin
            next_state = IDLE ;
        end
        default : begin
            next_state = IDLE ;
        end
    endcase
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dly_crc_cnt <=  4'd0 ;
    end
    else begin
        if ( cur_state == CRC_DLY ) begin
            if ( dly_crc_cnt == 4'd15 ) begin
                dly_crc_cnt <= 4'd0 ;
            end
            else begin
                dly_crc_cnt <= dly_crc_cnt + 1'b1 ;
            end
        end
        else ;
    end 
end

//----------------------------------------------------------------------------------
// the count of recieve data 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rx_cnt  <=  2'd0 ;
    end
    else begin
        if ( uart_rx_ren == 1'b1 && (cur_state == RD_FST || cur_state == RD_SCD || cur_state == RD_THD || cur_state == RD_FTH ) ) begin
            if ( rx_cnt == 2'd3 ) begin
                rx_cnt  <=  2'd0;
            end
            else begin
                rx_cnt  <=  rx_cnt + 1'b1;
            end
        end
        else if ( cur_state == FUN_END || cur_state == FUN_SEL ) begin
            rx_cnt  <=  2'd0;
        end
    end
end

//----------------------------------------------------------------------------------
// generate uart print signal
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_acq_trig  <=  1'b0 ; 
    end
    else begin
        if ( cur_state == FUN_SEL && uart_rx_ren == 1'b1 && uart_rx_rdata == CAL_ACQ ) begin
            cal_acq_trig  <=  1'b1 ;
        end
        else begin
            cal_acq_trig  <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_con_en  <=  1'b0 ; 
    end
    else begin
        if ( cur_state == FUN_SEL && uart_rx_ren == 1'b1 && ( uart_rx_rdata == CAL_ACQ ) ) begin
            cal_con_en  <=  1'b1 ;
        end
        else if ( cur_state == FUN_SEL && uart_rx_ren == 1'b1 && uart_rx_rdata == CAL_END ) begin
            cal_con_en  <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_end_trig  <=  1'b0 ; 
    end
    else begin
        if ( cur_state == FUN_SEL && uart_rx_ren == 1'b1 &&  uart_rx_rdata == CAL_END ) begin
            cal_end_trig  <=  1'b1 ;
        end
        else begin
            cal_end_trig   <=   1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        data_fun_sel    <=  3'b000 ;
    end
    else begin
        if ( cur_state == FUN_SEL && uart_rx_ren == 1'b1 ) begin
            case ( uart_rx_rdata )
                CH_CAL : begin
                    data_fun_sel    <=  3'b001 ;
                end
                CON_CH_DATA : begin
                    data_fun_sel    <=  3'b010 ;
                end
                DATA_ACQ : begin
                    data_fun_sel    <=  3'b011 ;
                end
                default : begin
                    data_fun_sel    <=  3'b000 ;
                end
            endcase
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        con_suc_trig   <=  1'b0 ; 
    end
    else begin
        if ( cur_state == FUN_SUS ) begin
            con_suc_trig  <=  1'b1 ;
        end
        else begin
            con_suc_trig  <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        con_err_trig  <=  1'b0 ; 
    end
    else begin
        if ( cur_state == FUN_ERR ) begin
            con_err_trig  <=  1'b1 ;
        end
        else begin
            con_err_trig  <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n  ) begin
    if( rst_sys_n == 1'b0 ) begin
        tm_out  <=  21'd0 ;
    end
    else begin
        case ( cur_state )
            IDLE : begin
                tm_out  <=  21'd0 ;
            end
            FUN_SEL : begin
                if ( tm_out[20] == 1'b1 || uart_rx_ren == 1'b1 && uart_rx_rdata == CH_CAL && cal_con_en == 1'b1 ) begin
                    tm_out  <=  21'd0 ;
                end
                else begin
                    tm_out  <=  tm_out + 1'b1 ;
                end
            end
            RD_FST : begin
                if ( tm_out[20] == 1'b1 || uart_rx_ren == 1'b1 && rx_cnt == 2'd3 ) begin
                    tm_out  <=  21'd0 ;
                end
                else begin
                    tm_out  <=  tm_out + 1'b1 ;
                end
            end
            RD_SCD : begin
                if ( tm_out[20] == 1'b1 || uart_rx_ren == 1'b1 && rx_cnt == 2'd3 ) begin
                    tm_out  <=  21'd0 ;
                end
                else begin
                    tm_out  <=  tm_out + 1'b1 ;
                end
            end
            RD_THD : begin
                if ( tm_out[20] == 1'b1 ||  uart_rx_ren == 1'b1 && rx_cnt == 2'd3 ) begin
                    tm_out  <=  21'd0 ;
                end
                else begin
                    tm_out  <=  tm_out + 1'b1 ;
                end
            end
            RD_FTH : begin
                if ( tm_out[20] == 1'b1 || uart_rx_ren == 1'b1 && rx_cnt == 2'd3 ) begin
                    tm_out  <=  21'd0 ;
                end
                else begin
                    tm_out  <=  tm_out + 1'b1 ;
                end
            end
            default : begin
                tm_out  <=  21'd0 ;
            end
        endcase
    end
end

//----------------------------------------------------------------------------------
// the module of WR_EEPROM 
//----------------------------------------------------------------------------------
    WR_EEPROM U_WR_EEPROM
    (   
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    
    .cur_state                  ( cur_state                 ),
    .rx_cnt                     ( rx_cnt                    ),
    .uart_rx_ren                ( uart_rx_ren               ),
    .uart_rx_rdata              ( uart_rx_rdata             ),
    .data_fun_sel               ( data_fun_sel              ),

    .cal_ch_index               ( cal_ch_index              ),
    .acq_data_sel               ( acq_data_sel              ),
    .acq_data_trig              ( acq_data_trig             ),
    .acq_ch_num                 ( acq_ch_num                ),
    .rd_en                      ( rd_en                     ),
    .kb_crc_trig                ( kb_crc_trig               ),
    .wr_en                      ( wr_en                     ),
    .wr_value0                  ( wr_value0                 ),
    .wr_value1                  ( wr_value1                 ),
    .wr_value2                  ( wr_value2                 ),
    .wr_value3                  ( wr_value3                 ),
    .wr_addr                    ( wr_addr                   ),
    .wr_done                    ( wr_done                   ),
    .e2p_busy                   ( e2p_busy                  )
    );

//----------------------------------------------------------------------------------
// the module of PRINT_INFO 
//----------------------------------------------------------------------------------
    PRINT_INFO                  U_PRINT_INFO
    (   
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .uart_rx_ren                ( uart_rx_ren               ),
    .uart_rx_rdata              ( uart_rx_rdata             ),

    .acq_data_sel               ( acq_data_sel              ),
    .cal_con_en                 ( cal_con_en                ),
    .uart_tx_wenl               ( uart_tx_wenl              ),
    .uart_tx_wdatal             ( uart_tx_wdatal            ),
    .uart_tx_wenh               ( uart_tx_wenh              ),
    .uart_tx_wdatah             ( uart_tx_wdatah            ),
    .ad_rd_dval                 ( ad_rd_dval                ),
    .ad_rd_value0               ( ad_rd_value0              ),
    .ad_rd_value1               ( ad_rd_value1              ),
    .ad_rd_value2               ( ad_rd_value2              ),
    .ad_rd_value3               ( ad_rd_value3              ),
    .ad_rd_value4               ( ad_rd_value4              ),
    .ad_rd_value5               ( ad_rd_value5              ),
    .ad_rd_value6               ( ad_rd_value6              ),
    .ad_rd_value7               ( ad_rd_value7              ),
    .ad_rd_value8               ( ad_rd_value8              ),
    .ad_rd_value9               ( ad_rd_value9              ),
    .ad_rd_value10              ( ad_rd_value10             ),
    .ad_rd_value11              ( ad_rd_value11             ),

    .data_fun_sel               ( data_fun_sel              ),
    .cal_acq_trig               ( cal_acq_trig              ),
    .e2p_urd_dval               ( e2p_urd_dval              ),
    .rd_en                      ( rd_en                     ),
    .e2p_rd_value               ( e2p_rd_value              ),
    .acq_data_trig              ( acq_data_trig             ),
    .acq_ch_num                 ( acq_ch_num                ),
    .con_suc_trig               ( con_suc_trig              ),
    .con_err_trig               ( con_err_trig              ),
    .cal_end_trig               ( cal_end_trig              ),
    .kb_crc_trig                ( kb_crc_trig               ),

    .uart_tx_wen                ( uart_tx_wen               ),
    .uart_tx_wdata              ( uart_tx_wdata             ),
    .uart_tx_rdy                ( uart_tx_rdy               )
    );


endmodule
