// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-12-12
// DEPARTMENT       :   R&D
// AUTHOR           :   Zhang Yongjun
// AUTHOR'S EMAIL   :   zhangyongjun@cgnpc.com.cn
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-12-12  Zhang Yongjun       Original
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
`timescale 1 ns / 1 ps
`include "DEFINES.v"
module  WDPRC
    (
        rst_sys_n               ,   
        clk_sys                 ,
        rst_12_5m_n             ,   
        clk_12_5m               ,   

        cfg_slink_chen          ,   
        cfg_run_tm              ,   
        slink_tx_eop            ,   
        slink_rx_eop            ,   
        wd_ch0_trig             ,   
        wd_ch1_trig             ,   
        wd_ch2_trig             ,   
        wd_ch3_trig             ,   
        wd_ch4_trig             ,   

        wd_int_fb               ,   
        wd_int_fd               ,
        wd_uart_rx              ,   
        wd_uart_tx              ,

        wd_cfg_en               ,   
        wd_cfg_done             ,   
        wd_clk_fault            ,   
        wd_ch_fault             ,   
        wd_com_fault     

    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
localparam  TM_CNT_US       = 7'd124 ;
localparam  TM_WD_CNT       = 15'd19999 ;
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;
input   wire                    rst_12_5m_n                         ;   
input   wire                    clk_12_5m                           ;   

input   wire    [1:0]           cfg_slink_chen                      ;   
input   wire    [15:0]          cfg_run_tm                          ;   
input   wire    [1:0]           slink_tx_eop                        ;   
input   wire    [1:0]           slink_rx_eop                        ;   
input   wire                    wd_ch0_trig                         ;   
input   wire                    wd_ch1_trig                         ;   
input   wire                    wd_ch2_trig                         ;   
input   wire                    wd_ch3_trig                         ;   
input   wire                    wd_ch4_trig                         ;   

input   wire                    wd_uart_rx                          ;
input   wire    [9:0]           wd_int_fb                           ;   

// output signal
output  wire                    wd_uart_tx                          ;
output  wire    [9:0]           wd_int_fd                           ;
output  reg                     wd_clk_fault                        ;   
output  reg                     wd_ch_fault                         ;   
output  reg                     wd_com_fault                        ;   
output  wire                    wd_cfg_done                         ;
output  reg                     wd_cfg_en                           ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [1:0]                   wd_tx_eop                           ;   
wire    [1:0]                   wd_rx_eop                           ;   
wire                            wd_ch0_en                           ;   
wire                            wd_ch1_en                           ;   
wire                            wd_ch2_en                           ;   
wire                            wd_ch3_en                           ;   
wire                            wd_ch4_en                           ; 
wire    [7:0]                   clc_en                              ;
// reg signal
reg     [15:0]                  wd_run_tm                           ; 
reg     [6:0]                   div_us                              ;   
reg     [14:0]                  wd_cnt                              ;   
reg     [7:0]                   wd_fb_sample                        ;   
reg                             wd_clk_en                           ;   
reg     [7:0]                   wd_fb5_sample                       ;   
reg     [7:0]                   wd_fb0_sample                       ;   
reg     [7:0]                   wd_fb6_sample                       ;   
reg     [15:0]                  wd_ch_cnt                           ;   
   
reg     [15:0]                  wd_tm                               ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// initial the parameter of watch dog
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_run_tm   <=   16'd0 ;
    end
    else begin
        wd_run_tm   <=   (cfg_run_tm<<3) + (cfg_run_tm<<1) + 16'd10 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_tm   <=   16'd0 ;
    end
    else begin
        wd_tm   <=   ( wd_run_tm << 1) + wd_run_tm ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_cfg_en   <=   1'b0 ;
    end
    else begin
        if ( wd_ch0_trig == 1'b1 ) begin
            wd_cfg_en   <=   1'b1 ;
        end
    end
end

    wdg_tx_frame            u_wdg_tx_frame
    (

    .clk_sys                    ( clk_sys                   ),
    .rst_n                      ( rst_sys_n                 ),

    .cfg_done                   ( wd_cfg_en                 ),

    .chn0_data                  ( 16'd42                    ),
    .chn1_data                  ( 16'd42                    ),
    .chn2_data                  ( 16'd42                    ),
    .chn3_data                  ( 16'd42                    ),
    .chn4_data                  ( 16'd188                   ), // 202
    .chn5_data                  ( 16'd210                   ),
    .chn6_data                  ( 16'd102                   ),
    .chn7_data                  ( 16'd102                   ),
    .chn8_data                  ( wd_tm                     ),
    .chn9_data                  ( wd_tm                     ),
    .chn10_data                 ( 16'd0                     ),
    .chn11_data                 ( 16'd0                     ),
    .chn12_data                 ( 16'd0                     ),
    .chn13_data                 ( 16'd0                     ),
    .chn0_en                    ( 1'b1                      ),
    .chn1_en                    ( 1'b1                      ),
    .chn2_en                    ( 1'b1                      ),
    .chn3_en                    ( 1'b1                      ),
    .chn4_en                    ( 1'b0                      ),
    .chn5_en                    ( 1'b1                      ),
    .chn6_en                    ( 1'b1                      ), //cfg_slink_chen[0]
    .chn7_en                    ( 1'b1                      ), // cfg_slink_chen[1]
    .chn8_en                    ( 1'b0                      ),
    .chn9_en                    ( 1'b0                      ),
    .chn10_en                   ( 1'b0                      ),
    .chn11_en                   ( 1'b0                      ),
    .chn12_en                   ( 1'b0                      ),
    .chn13_en                   ( 1'b0                      ),

    .rx                         ( wd_uart_rx                ),
    .tx                         ( wd_uart_tx                ),
    .wd_cfg_done                ( wd_cfg_done               )

    );

//----------------------------------------------------------------------------------
// genrate the signal of feed watch fog
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        div_us  <=  7'd0 ;
    end
    else begin
        if ( div_us == TM_CNT_US ) begin
            div_us  <=  7'd0 ;
        end
        else begin
            div_us  <=  div_us + 1'b1 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
       wd_cnt   <=   15'd0 ; 
    end
    else begin
        if ( div_us == TM_CNT_US ) begin
            if ( wd_cnt == TM_WD_CNT ) begin
                wd_cnt  <=   15'd0 ;
            end
            else begin
                wd_cnt  <=   wd_cnt + 1'b1 ;
            end
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_clk_en   <=   1'b0 ;
    end
    else begin
        if ( wd_cnt == TM_WD_CNT ) begin
            wd_clk_en   <=   1'b1 ;
        end
        else begin
            wd_clk_en   <=   1'b0 ;
        end
    end
end

    WDFDGEN                     U_CH0_WDFDGEN
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .fd_trig                    ( wd_ch0_trig               ),
    .fd_en                      ( wd_ch0_en                 ),
    .fd_fb                      ( wd_int_fb[0]              ),
    .clc_en                     ( clc_en[0]                 )
    ) ;
    
    WDFDGEN                     U_CH1_WDFDGEN
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .fd_trig                    ( wd_ch1_trig               ),
    .fd_en                      ( wd_ch1_en                 ),
    .fd_fb                      ( wd_int_fb[1]              ),
    .clc_en                     ( clc_en[1]                 )
    ) ;

     WDFDGEN                    U_CH2_WDFDGEN
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .fd_trig                    ( wd_ch2_trig               ),
    .fd_en                      ( wd_ch2_en                 ),
    .fd_fb                      ( wd_int_fb[2]              ),
    .clc_en                     ( clc_en[2]                 )
    ) ;

    WDFDGEN                    U_CH3_WDFDGEN
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .fd_trig                    ( wd_ch3_trig               ),
    .fd_en                      ( wd_ch3_en                 ),
    .fd_fb                      ( wd_int_fb[3]              ),
    .clc_en                     ( clc_en[3]                 )
    ) ;

    WDFDGEN                    U_CH4_WDFDGEN
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .fd_trig                    ( wd_ch4_trig               ),
    .fd_en                      ( wd_ch4_en                 ),
    .fd_fb                      ( wd_int_fb[4]              ),
    .clc_en                     ( clc_en[4]                 )
    ) ;

    WDFDGEN                    U_CLK_WDFDGEN
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
    .fd_trig                    ( 1'b0                      ),
    .fd_en                      (                           ),
    .fd_fb                      ( wd_int_fb[5]              ),
    .clc_en                     ( clc_en[5]                 )
    ) ;

    WDFDGEN                     U_TX0_WDFDGEN
    (
    .rst_sys_n                  ( rst_12_5m_n               ),
    .clk_sys                    ( clk_12_5m                 ),
    .fd_trig                    ( slink_tx_eop[0]           ),
    .fd_en                      ( wd_tx_eop[0]              ),
    .fd_fb                      ( wd_int_fb[6]              ),
    .clc_en                     ( clc_en[6]                 )
    ) ;
    
    WDFDGEN                     U_TX1_WDFDGEN
    (
    .rst_sys_n                  ( rst_12_5m_n               ),
    .clk_sys                    ( clk_12_5m                 ),
    .fd_trig                    ( slink_tx_eop[1]           ),
    .fd_en                      ( wd_tx_eop[1]              ),
    .fd_fb                      ( wd_int_fb[7]              ),
    .clc_en                     ( clc_en[7]                 )
    ) ;

assign wd_int_fd[0] =  wd_ch0_en ;
assign wd_int_fd[1] =  wd_ch1_en ;
assign wd_int_fd[2] =  wd_ch2_en ;
assign wd_int_fd[3] =  wd_ch3_en ;
assign wd_int_fd[4] =  wd_ch4_en ;
assign wd_int_fd[5] =  wd_clk_en ;
assign wd_int_fd[6] =  wd_tx_eop[0] ;   
assign wd_int_fd[7] =  wd_tx_eop[1] ;  
assign wd_int_fd[8] =  1'b0 ;//wd_rx_eop[0] ;   
assign wd_int_fd[9] =  1'b0 ;//wd_rx_eop[1] ; 

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_fb5_sample    <=   8'd0 ;
    end
    else begin
        wd_fb5_sample    <=   { wd_fb5_sample[6:0] , wd_int_fb[5] } ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_clk_fault    <=   1'b0 ;
    end
    else begin
        if ( clc_en[5] == 1'b1 ) begin
            wd_clk_fault    <=   1'b0 ;
        end
        else if ( wd_fb5_sample[7:4] == 4'b0000 && wd_fb5_sample[3:0] == 4'b1111 ) begin
            wd_clk_fault    <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_fb0_sample    <=   8'd0 ;
    end
    else begin
        wd_fb0_sample    <=   { wd_fb0_sample[6:0] , | wd_int_fb[3:0] } ; 
    end
end


always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_ch_fault    <=   1'b0 ;
    end
    else begin
        if ( clc_en[3:0] == 4'b1111 ) begin
            wd_ch_fault     <=   1'b0 ;
        end
        else if ( wd_fb0_sample[7:4] == 4'b0000 && wd_fb0_sample[3:0] == 4'b1111 ) begin
            wd_ch_fault    <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_ch_cnt    <=   16'd0 ;
    end
    else begin
        if ( wd_fb0_sample[7:4] == 4'b0000 && wd_fb0_sample[3:0] == 4'b1111 ) begin
            wd_ch_cnt    <=  wd_ch_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_fb6_sample    <=   8'd0 ;
    end
    else begin
        wd_fb6_sample    <=   { wd_fb6_sample[6:0] , | wd_int_fb[7:6] } ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_com_fault    <=   1'b0 ;
    end
    else begin
        if (clc_en[7:6] == 2'b11 ) begin
            wd_com_fault    <=   1'b0 ;
        end
        else if ( wd_fb6_sample[7:4] == 4'b0000 && wd_fb6_sample[3:0] == 4'b1111 ) begin
            wd_com_fault    <=   1'b1 ;
        end
    end
end



endmodule
