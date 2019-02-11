// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-09-10
// DEPARTMENT       :   R&D
// AUTHOR           :   Zhang Yongjun
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com.cn
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-10  Zhang Yongjun       Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active low
// Clock Domains    :   clk_100m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`timescale 1 ns / 1 ns
`include "DEFINES.v"

module AI_LEDM 
    (
    // clock & reset
    clk_sys                     ,   
    rst_sys_n                   ,   

    hw_fault                    ,   
    dw_com_fault                ,   
    enable_slot                 ,  
    cfg_en                      , 
    self_cfg_err                ,   

    macrx_rx_eop                ,   
    lvds_pcs_err                ,  

    cal_ch_index                ,   
    mass_bit                    ,   
    cfg_chn_enable              ,   
    // LED out
    run_led                     ,  
    err_led                     , 
    com_led                     , 
    ch0_led                     ,
    ch1_led                     ,
    ch2_led                     ,
    ch3_led                     ,
    ch4_led                     ,
    ch5_led                     ,
    ch6_led                     ,
    ch7_led                     ,
    ch8_led                     , 
    ch9_led                     , 
    ch10_led                    , 
    ch11_led                      

    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
localparam      FREQ_2HZ_BIT        = 25 ;
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ; 

input   wire    [11:0]          cal_ch_index                        ;   
input   wire                    dw_com_fault                        ;   
input   wire    [1:0]           enable_slot                         ;
input   wire                    cfg_en                              ;  
input   wire                    self_cfg_err                        ;   
input   wire    [1:0]           macrx_rx_eop                        ;   
input   wire    [1:0]           lvds_pcs_err                        ;   
input   wire    [11:0]          mass_bit                            ;   
input   wire    [11:0]          cfg_chn_enable                      ;   
input   wire                    hw_fault                            ;   
// declare output signal
output  reg     [1:0]           run_led                             ;   
output  reg     [1:0]           err_led                             ;   
output  wire    [1:0]           com_led                             ;   
output  wire    [1:0]           ch0_led                             ;   
output  wire    [1:0]           ch1_led                             ;   
output  wire    [1:0]           ch2_led                             ;   
output  wire    [1:0]           ch3_led                             ;   
output  wire    [1:0]           ch4_led                             ;   
output  wire    [1:0]           ch5_led                             ;   
output  wire    [1:0]           ch6_led                             ;   
output  wire    [1:0]           ch7_led                             ;   
output  wire    [1:0]           ch8_led                             ;   
output  wire    [1:0]           ch9_led                             ;   
output  wire    [1:0]           ch10_led                            ;   
output  wire    [1:0]           ch11_led                            ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [1:0]               ch_led_drive       [11:0]           ;
wire                            slot_en                             ;   
wire                            cfg_err                             ;   
wire                            cal_model_en                        ;   

// reg signal
reg                             clk_ms_en                           ;   
reg         [FREQ_2HZ_BIT - 1:0]clk_ms_cnt                          ;    
reg         [1:0]               led_drive_flag                      ;   
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// generate the enable of ms clk
//----------------------------------------------------------------------------------

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        clk_ms_cnt  <=   { FREQ_2HZ_BIT{1'b0} };
    end
    else begin
        if ( clk_ms_cnt[FREQ_2HZ_BIT-1] == 1'b1 ) begin // 0.87ms
            clk_ms_cnt  <=   { FREQ_2HZ_BIT{1'b0} };
        end
        else begin
            clk_ms_cnt  <=   clk_ms_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        clk_ms_en   <=   1'b0;
    end
    else begin
        if ( clk_ms_cnt[FREQ_2HZ_BIT-1] == 1'b1 ) begin
            clk_ms_en   <=   1'b1;
        end
        else begin
            clk_ms_en   <=   1'b0;
        end
    end
end

//----------------------------------------------------------------------------------
// light up the pwr_led at power on
//----------------------------------------------------------------------------------
assign  cfg_err =   ~cfg_en || self_cfg_err ;
//----------------------------------------------------------------------------------
// light up run_led on the communication and optical module working on
//----------------------------------------------------------------------------------
assign  cal_model_en = | cal_ch_index ;
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        run_led <=   2'b00 ;
    end
    else begin
        if ( cal_model_en == 1'b1 ) begin
            run_led[1]  <=   1'b1 ;
        end
        else if ( cfg_en == 1'b1 ) begin
            if ( self_cfg_err == 1'b0 ) begin
                run_led[1] <=   1'b1 ; // light on the green led
            end
            else begin
                if ( clk_ms_en == 1'b1 ) begin
                    run_led[1] <=  ~ run_led[1] ;
                end
            end
        end
        else begin
            run_led[1] <=  1'b0 ;
        end
    end
end
//----------------------------------------------------------------------------------
// light up err_led on the communication and optical module working on
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        err_led <=   2'b00 ;
    end
    else begin
        if ( self_cfg_err == 1'b0 ) begin
            if ( hw_fault == 1'b1 ) begin
                err_led <=   2'b01 ;
            end
            else begin
                err_led <=   2'b00 ;
            end
        end
        else begin
            err_led <=   2'b00 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        led_drive_flag  <=   2'b00 ;
    end
    else begin
        if ( enable_slot == 2'b11 ) begin
            if ( lvds_pcs_err == 2'b10 ) begin
                led_drive_flag  <=   { macrx_rx_eop[0] , lvds_pcs_err[0] || dw_com_fault } ;
            end
            else if ( lvds_pcs_err == 2'b01 ) begin
                led_drive_flag  <=   { macrx_rx_eop[1] , lvds_pcs_err[1] || dw_com_fault } ;
            end
            else begin
                led_drive_flag  <=   { macrx_rx_eop[0] , lvds_pcs_err[0] || dw_com_fault } ;
            end
        end
        else if ( enable_slot == 2'b01 ) begin
            led_drive_flag  <=   { macrx_rx_eop[0] , lvds_pcs_err[0] || dw_com_fault } ;
        end
        else if ( enable_slot == 2'b10 ) begin
            led_drive_flag  <=   { macrx_rx_eop[1] , lvds_pcs_err[1] || dw_com_fault } ;
        end
        else begin
            led_drive_flag  <=   2'b00 ;
        end
    end
end

//----------------------------------------------------------------------------------
// indication of the communication  
//----------------------------------------------------------------------------------
assign  ch0_led    =   ch_led_drive[0] ;
assign  ch1_led    =   ch_led_drive[1] ;
assign  ch2_led    =   ch_led_drive[2] ;
assign  ch3_led    =   ch_led_drive[3] ;
assign  ch4_led    =   ch_led_drive[4] ;
assign  ch5_led    =   ch_led_drive[5] ;
assign  ch6_led    =   ch_led_drive[6] ;
assign  ch7_led    =   ch_led_drive[7] ;
assign  ch8_led    =   ch_led_drive[8] ;
assign  ch9_led    =   ch_led_drive[9] ;
assign  ch10_led   =   ch_led_drive[10];
assign  ch11_led   =   ch_led_drive[11];

assign  slot_en = enable_slot[0] | enable_slot[1] ;

    COMLEDCTL                   U_COM_LED    
    ( 
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),
    .self_cfg_err               ( self_cfg_err              ),
    .clk_ms_en                  ( clk_ms_en                 ),
    .slot_en                    ( slot_en                   ),
    .cfg_err                    ( cfg_err                   ),
    .com_trig                   ( led_drive_flag            ), 
    .com_led                    ( com_led                   )
    ); 

genvar i ;
generate
for ( i=0; i<12; i = i + 1 )
begin : chledctl
    CHLEDCTL                    U_CH_LED
    (
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),

    .cal_model_en               ( cal_model_en              ),
    .cfg_err                    ( cfg_err                   ),
    .cal_ch_index               ( cal_ch_index[i]           ),
    .ch_run_stus                ( mass_bit[i]               ),
    .cfg_chn_enable             ( cfg_chn_enable[i]         ),
    .ch_led                     ( ch_led_drive[i]           )
 
    );
end
endgenerate

endmodule

