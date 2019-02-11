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

module PRINT_INFO
(   
        rst_sys_n               ,   
        clk_sys                 ,   
    
        uart_rx_ren             ,   
        uart_rx_rdata           ,   

        acq_data_sel            ,   
        cal_con_en              ,   
        uart_tx_wenl            ,   
        uart_tx_wdatal          ,   
        uart_tx_wenh            ,   
        uart_tx_wdatah          ,  
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

        data_fun_sel            ,   
        rd_en                   , 
        e2p_urd_dval            ,   
        e2p_rd_value            ,
        acq_data_trig           ,   
        acq_ch_num              ,   
        cal_acq_trig            ,   
        cal_end_trig            ,   
        con_suc_trig            ,   
        con_err_trig            ,   
        kb_crc_trig             ,   

        uart_tx_wen             ,   
        uart_tx_wdata           ,   
        uart_tx_rdy               
);

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
localparam  BOARD_ADDR  =   8'h10               ;

localparam  IDLE        =   5'b00000  ;
localparam  RD_RDY      =   5'b00001  ;
localparam  TX_FIFO_RDY =   5'b00010  ;
localparam  UART_TX     =   5'b00100  ;
localparam  DLY         =   5'b01000  ;
localparam  TX_END      =   5'b10000  ;

localparam  CAL_ACQ     =   8'h31             ;
localparam  CH_CAL      =   8'h32             ;
localparam  CON_CH_DATA =   8'h33             ;
localparam  DATA_ACQ    =   8'h34             ;
localparam  CAL_END     =   8'h35             ;
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    rst_sys_n                           ;  
input   wire                    clk_sys                             ;   
input   wire                    cal_acq_trig                        ;   
input   wire                    cal_end_trig                        ;   
input   wire                    uart_rx_ren                         ;   
input   wire    [7:0]           uart_rx_rdata                       ;   
input   wire                    con_suc_trig                        ;   
input   wire                    con_err_trig                        ;   
input   wire                    uart_tx_rdy                         ;   
input   wire                    cal_con_en                          ;   
input   wire                    rd_en                               ;   
input   wire                    e2p_urd_dval                        ;   
input   wire    [31:0]          e2p_rd_value                        ;   
input   wire    [1:0]           acq_data_sel                        ;   
input   wire    [2:0]           data_fun_sel                        ;   

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
input   wire                    acq_data_trig                       ;   
input   wire    [7:0]           acq_ch_num                          ;  
input   wire                    kb_crc_trig                         ;   
input   wire                    uart_tx_wenl                        ;   
input   wire    [7:0]           uart_tx_wdatal                      ;   
input   wire                    uart_tx_wenh                        ;   
input   wire    [7:0]           uart_tx_wdatah                      ; 
// declare output signal

output  wire                    uart_tx_wen                         ;   
output  wire   [7:0]            uart_tx_wdata                       ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            uart_fifo_rdval                     ;   
wire    [7:0]                   uart_fifo_dout                      ;   
wire                            uart_fifo_empty                     ;   
wire                            uart_fifo_full                      ;   
// reg signal
reg     [4:0]                   tx_cnt                              ;   
reg     [15:0]                  ad_rd_value[11:0]                   ;
reg     [4:0]                   cur_state                           ;   
reg     [4:0]                   next_state                          ;  
reg     [7:0]                   tx_num                              ;   
reg                             cal_acq_en                          ;   
reg                             acq_data_en                         ;   
reg                             cal_end_en                          ;   
reg                             con_cal_en                          ;   
reg                             cal_chnum_en                        ;   
reg     [7:0]                   uart_fifo_data                      ;   
reg                             uart_fifo_wren                      ;   
reg                             uart_fifo_rden                      ;   
reg                             tx_fifo_en                          ;  
reg     [7:0]                   uart_data                           ;   
reg                             caluart_tx_wen                      ;   
reg     [7:0]                   caluart_tx_wdata                    ;   
reg                             e2p_en                              ;   
reg     [31:0]                  e2p_value                           ; 
reg                             e2p_data_en                         ;
reg     [2:0]                   fun_sel_en                          ;   
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//assign uart_tx_wen      = ( cal_con_en == 1'b0 ) ? uart_tx_wenl : caluart_tx_wen ;
//assign uart_tx_wdata    = ( cal_con_en == 1'b0 ) ? uart_tx_wdatal : caluart_tx_wdata ;
assign uart_tx_wen      =  caluart_tx_wen ;
assign uart_tx_wdata    =  caluart_tx_wdata ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ad_rd_value[0 ] <=   15'd0 ;
        ad_rd_value[1 ] <=   15'd0 ;
        ad_rd_value[2 ] <=   15'd0 ;
        ad_rd_value[3 ] <=   15'd0 ;
        ad_rd_value[4 ] <=   15'd0 ;
        ad_rd_value[5 ] <=   15'd0 ;
        ad_rd_value[6 ] <=   15'd0 ;
        ad_rd_value[7 ] <=   15'd0 ;
        ad_rd_value[8 ] <=   15'd0 ;
        ad_rd_value[9 ] <=   15'd0 ;
        ad_rd_value[10] <=   15'd0 ;
        ad_rd_value[11] <=   15'd0 ;
    end
    else begin
        if ( ad_rd_dval[0] == 1'b1 ) begin
            ad_rd_value[0]  <=   ad_rd_value0 ;
        end
        else ;
        if ( ad_rd_dval[1] == 1'b1 ) begin
            ad_rd_value[1]  <=   ad_rd_value1 ;
        end
        else ;
        if ( ad_rd_dval[2] == 1'b1 ) begin
            ad_rd_value[2]  <=   ad_rd_value2 ;
        end
        else ;
        if ( ad_rd_dval[3] == 1'b1 ) begin
            ad_rd_value[3]  <=   ad_rd_value3 ;
        end
        else ;
        if ( ad_rd_dval[4] == 1'b1 ) begin
            ad_rd_value[4]  <=   ad_rd_value4 ;
        end
        else ;
        if ( ad_rd_dval[5] == 1'b1 ) begin
            ad_rd_value[5]  <=   ad_rd_value5 ;
        end
        else ;
        if ( ad_rd_dval[6] == 1'b1 ) begin
            ad_rd_value[6]  <=   ad_rd_value6 ;
        end
        else ;
        if ( ad_rd_dval[7] == 1'b1 ) begin
            ad_rd_value[7]  <=   ad_rd_value7 ;
        end
        else ;
        if ( ad_rd_dval[8] == 1'b1 ) begin
            ad_rd_value[8]  <=   ad_rd_value8 ;
        end
        else ;
        if ( ad_rd_dval[9] == 1'b1 ) begin
            ad_rd_value[9]  <=   ad_rd_value9 ;
        end
        else ;
        if ( ad_rd_dval[10] == 1'b1 ) begin
            ad_rd_value[10]  <=   ad_rd_value10 ;
        end
        else ;
        if ( ad_rd_dval[11] == 1'b1 ) begin
            ad_rd_value[11]  <=   ad_rd_value11 ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// read data form eeprom
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        e2p_data_en   <=   1'b0 ;
    end
    else begin
        if ( rd_en == 1'b1 ) begin
            e2p_data_en <=   1'b1 ;
        end
        else if ( tx_fifo_en == 1'b1 && tx_cnt == tx_num ) begin
            e2p_data_en <=   1'b0 ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        e2p_en  <=   1'b0 ;
    end
    else begin
        e2p_en  <=   e2p_urd_dval ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        e2p_value    <=   32'd0 ;
    end
    else begin
        if ( e2p_en == 1'b1 ) begin
            e2p_value   <=   e2p_rd_value ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        tx_fifo_en  <=   1'b0 ;
    end
    else begin
        if ( cal_acq_trig == 1'b1 || cal_end_trig == 1'b1 || con_suc_trig == 1'b1 && e2p_data_en == 1'b0 || con_err_trig == 1'b1 || acq_data_sel == 2'b11 && e2p_en == 1'b1 ) begin
            tx_fifo_en  <=   1'b1 ;
        end
        else if ( tx_cnt == tx_num ) begin
            tx_fifo_en  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fun_sel_en  <=   3'b000 ;
    end
    else begin
        if ( con_suc_trig == 1'b1 ) begin
            fun_sel_en  <=   data_fun_sel ;
        end
        else if ( tx_fifo_en == 1'b1 && tx_cnt == tx_num ) begin
            fun_sel_en  <=   3'b000 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_acq_en  <=   1'b0 ;
    end
    else begin
        if ( cal_acq_trig == 1'b1 ) begin
            cal_acq_en  <=   1'b1 ;
        end
        else if ( tx_fifo_en == 1'b1 && tx_cnt == tx_num ) begin
            cal_acq_en  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_end_en  <=   1'b0 ;
    end
    else begin
        if ( cal_end_trig == 1'b1 ) begin
            cal_end_en  <=   1'b1 ;
        end
        else if ( tx_fifo_en == 1'b1 && tx_cnt == tx_num ) begin
            cal_end_en  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        con_cal_en <=   1'b0 ;
    end
    else begin
        if ( kb_crc_trig == 1'b1 ) begin
            con_cal_en <=   1'b1 ;
        end
        else if ( tx_fifo_en == 1'b1 && tx_cnt == tx_num ) begin
            con_cal_en <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        acq_data_en <=   1'b0 ;
    end
    else begin
        if ( acq_data_trig == 1'b1 ) begin
            acq_data_en <=   1'b1 ;
        end
        else if ( tx_fifo_en == 1'b1 && tx_cnt == tx_num ) begin
            acq_data_en <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
       tx_num   <=   8'd7 ; 
    end
    else begin
        tx_num  <=   8'd7 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        tx_cnt  <=   8'd0 ;
    end
    else begin
        if ( tx_fifo_en == 1'b1 ) begin
            if ( tx_cnt == tx_num ) begin
                tx_cnt  <=   8'd0 ;
            end
            else begin
                tx_cnt  <=   tx_cnt + 1'b1 ;
            end
        end
        else begin
            tx_cnt  <=   8'd0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        uart_fifo_wren <=   1'b0 ;
    end
    else begin
        if ( tx_fifo_en == 1'b1 ) begin
            uart_fifo_wren <=   1'b1 ;
        end
        else begin
            uart_fifo_wren <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_chnum_en  <=   1'b0 ;
    end
    else begin
        if ( kb_crc_trig == 1'b1 || acq_data_trig == 1'b1 || rd_en == 1'b1 ) begin
            cal_chnum_en  <=   1'b1 ;
        end
        else if ( tx_fifo_en == 1'b0 ) begin
            cal_chnum_en  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        uart_fifo_data   <=   8'd0 ;
    end
    else begin
        if ( tx_fifo_en == 1'b1 ) begin
            case ( tx_cnt )
                7'd0 : begin
                    uart_fifo_data   <=   BOARD_ADDR ;
                end
                7'd1 : begin
                    if ( cal_acq_en == 1'b1 ) begin
                        uart_fifo_data   <=   CAL_ACQ ;
                    end
                    else if ( cal_end_en == 1'b1 ) begin
                        uart_fifo_data   <=   CAL_END ;
                    end
                    else if ( fun_sel_en == 3'b001 ) begin
                        uart_fifo_data   <=   CH_CAL ;
                    end
                    else if ( fun_sel_en == 3'b011 ) begin
                        uart_fifo_data   <=   DATA_ACQ ;
                    end
                    else begin
                        uart_fifo_data  <=   8'd0 ;
                    end
                end
                7'd2 : begin
                    if ( cal_chnum_en == 1'b1 ) begin
                        uart_fifo_data    <=   acq_ch_num ;
                    end
                    else begin
                        uart_fifo_data    <=   8'd0 ;
                    end
                end
                7'd3 : begin
                    if ( acq_data_en == 1'b1 ) begin
                        uart_fifo_data   <=   ad_rd_value[acq_ch_num][7:0] ;
                    end
                    else if ( e2p_data_en == 1'b1 ) begin
                        uart_fifo_data   <=   e2p_value[7:0] ;
                    end
                    else begin
                        uart_fifo_data   <=   8'd0 ;
                    end
                end
                7'd4 : begin
                    if ( acq_data_en == 1'b1 ) begin
                        uart_fifo_data   <=   { ad_rd_value[acq_ch_num][15:8] } ;
                    end
                    else if ( e2p_data_en == 1'b1 ) begin
                        uart_fifo_data   <=   e2p_value[15:8] ;
                    end
                    else begin
                        uart_fifo_data   <=   16'd0 ;
                    end
                end
                7'd5 : begin
                    if ( e2p_data_en == 1'b1 ) begin
                        uart_fifo_data  <=   e2p_value[23:16] ; 
                    end
                    else begin
                        uart_fifo_data   <=   8'd0 ;
                    end
                end
                7'd6 : begin
                    if ( e2p_data_en == 1'b1 ) begin
                        uart_fifo_data  <=   e2p_value[31:24] ;
                    end
                    else begin
                        uart_fifo_data   <=   8'd0 ;
                    end

                end
                7'd7 : begin
                    if ( acq_data_en == 1'b1 || cal_acq_en == 1'b1 || cal_end_en == 1'b1 || e2p_data_en == 1'b1 || con_cal_en == 1'b1 ) begin
                        uart_fifo_data   <=   8'h55 ;
                    end
                    else begin
                        uart_fifo_data   <=   8'hAA ;
                    end
                end
            endcase
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// Throuth async fifo, synchronizate the system clock value to emif clock value  
//----------------------------------------------------------------------------------
    aibfifo_w8d64 U_sync_fifo_w8_d64
    (
    // Clocks and Reset
    .WCLOCK                     ( clk_sys                   ),
    .RCLOCK                     ( clk_sys                   ),
    .RESET_W                    ( rst_sys_n                 ),
    .RESET_R                    ( rst_sys_n                 ),
    // Input Data Bus and Control ports
    .WDATA                      ( uart_fifo_data            ),
    .WE                         ( uart_fifo_wren            ),
    .RE                         ( uart_fifo_rden            ),
    // Output Data bus
    .RDVAL                      ( uart_fifo_rdval           ),
    .RDATA                      ( uart_fifo_dout            ),
    // stu Flags
    .FULL                       ( uart_fifo_full            ),
    .EMPTY                      ( uart_fifo_empty           )
    );

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cur_state   <=   IDLE ;
    end
    else begin
        cur_state   <=   next_state ;
    end
end

always @ ( * ) begin
    case ( cur_state )
        IDLE : begin
            if ( uart_fifo_empty == 1'b0 && uart_tx_rdy == 1'b1 ) begin
                next_state = RD_RDY ;
            end
            else begin
                next_state = IDLE ;
            end
        end
        RD_RDY : begin
            next_state = TX_FIFO_RDY ;
        end
        TX_FIFO_RDY : begin
            next_state = UART_TX ;
        end
        UART_TX : begin
            next_state = DLY ;
        end
        DLY : begin
            next_state = TX_END ;
        end
        TX_END : begin
            next_state = IDLE ;
        end
        default : begin
            next_state = IDLE ;
        end
    endcase
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        uart_fifo_rden  <=   1'b0 ;
    end
    else begin
        if ( cur_state == IDLE && uart_fifo_empty == 1'b0 && uart_tx_rdy == 1'b1 ) begin
            uart_fifo_rden  <=   1'b1 ;
        end
        else begin
            uart_fifo_rden  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        uart_data   <=   8'd0 ;
    end
    else begin
        if ( uart_fifo_rdval == 1'b1 ) begin
            uart_data   <=   uart_fifo_dout ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        caluart_tx_wen <=   1'b0 ;
    end
    else begin
        if ( cur_state == UART_TX ) begin
            caluart_tx_wen <=   1'b1 ;
        end
        else begin
            caluart_tx_wen <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        caluart_tx_wdata   <=   8'd0 ;
    end
    else begin
        if ( cur_state == UART_TX ) begin
            caluart_tx_wdata   <=   uart_data ;
        end
        else ;
    end
end

endmodule
