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

module EX_LEDM 
    (
    // clock & reset
    clk_sys                     ,   
    rst_sys_n                   ,   

    enable_slot                 ,  
    cfg_en                      , 
    self_cfg_err                ,   

    fiber_tx_eop                ,   
    fiber_rx_eop                ,   
    fiber_slink_err             ,   
    lvds_rx_eop                 ,   
    lvds_slink_err              ,  
    ex_rx_eop                   ,   
    ex_slink_err                ,   

    // LED out
    run_led                     ,   // Indicating module of work running status 
    err_led                     ,   // Indicating module of communication failure status 
    com_led                     ,   // Indicating module I of communication work status 
    mas_led                     ,   
    sla_led                     ,   
    ch1_rled                    ,   // Indicating firest channel recieve communication status
    ch2_rled                    ,   // Indicating second channel recieve communication status 
    ch3_rled                    ,   // Indicating third channel recieve communication status 
    ch4_rled                    ,   // Indicating fourth channel recieve communication status
    ch5_rled                    ,   // Indicating fifth channel recieve communication status
    ch6_rled                    ,   // Indicating sixth channel recieve communication status
    ch7_rled                    ,   // Indicating seventh channel recieve communication status
    ch8_rled                    ,   // Indicating eighth recieve communication status
    ch9_rled                    ,   // Indicating ninth channel recieve communication status
    ch10_rled                   ,   // Indicating tenth channel recieve communication status
    ch11_rled                   ,   // Indicating eleventh channel recieve communication status
    ch12_rled                   ,   // Indicating twelfth channel recieve communication status
    ch13_rled                   ,   // Indicating thirteenth channel recieve communication status
    ch14_rled                   ,   // Indicating fourtheenth channel recieve communication status   
    sff1_tled                   ,   // firest optical module of the tramsmit LED 
    sff1_rled                   ,   // firest optical module of the receive LED 
    sff2_tled                   ,   // second optical module of the tramsmit LED 
    sff2_rled                       // second optical module of the receive LED
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   FREQ_2HZ_BIT    =   25 ; // 

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ; 

input   wire    [16:0]          enable_slot                         ;
input   wire                    cfg_en                              ;  
input   wire                    self_cfg_err                        ;   
input   wire    [1:0]           fiber_tx_eop                        ;   
input   wire    [1:0]           fiber_rx_eop                        ;   
input   wire    [1:0]           fiber_slink_err                     ;   
input   wire    [13:0]          lvds_rx_eop                         ;   
input   wire    [13:0]          lvds_slink_err                      ;  
input   wire    [1:0]           ex_rx_eop                           ;   
input   wire    [1:0]           ex_slink_err                        ;   

// declare output signal
output  reg                     run_led                             ;   
output  reg                     err_led                             ;   
output  wire    [1:0]           com_led                             ;   
output  wire    [1:0]           mas_led                             ;   
output  wire    [1:0]           sla_led                             ;   
output  wire    [1:0]           ch1_rled                            ;   
output  wire    [1:0]           ch2_rled                            ;   
output  wire    [1:0]           ch3_rled                            ;   
output  wire    [1:0]           ch4_rled                            ;   
output  wire    [1:0]           ch5_rled                            ;   
output  wire    [1:0]           ch6_rled                            ;   
output  wire    [1:0]           ch7_rled                            ;   
output  wire    [1:0]           ch8_rled                            ;   
output  wire    [1:0]           ch9_rled                            ;   
output  wire    [1:0]           ch10_rled                           ;   
output  wire    [1:0]           ch11_rled                           ;   
output  wire    [1:0]           ch12_rled                           ;   
output  wire    [1:0]           ch13_rled                           ; 
output  wire    [1:0]           ch14_rled                           ;    
output  wire    [1:0]           sff1_tled                           ;   
output  wire    [1:0]           sff1_rled                           ;   
output  wire    [1:0]           sff2_tled                           ; 
output  wire    [1:0]           sff2_rled                           ;

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [1:0]               led_drive_flag  [19:0]              ;
wire        [1:0]               led_drive       [19:0]              ;
wire        [19:0]              slot_en                             ;   

// reg signal
reg                             clk_ms_en                           ;   
reg         [FREQ_2HZ_BIT-1:0]  clk_ms_cnt                          ;  

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
assign  com_led =   2'b00 ;

//----------------------------------------------------------------------------------
// light up run_led on the communication and optical module working on
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        run_led <=   1'b0 ;
    end
    else begin
        if ( cfg_en == 1'b1 ) begin
            if ( self_cfg_err == 1'b0 ) begin
                run_led <=   1'b1 ; // light on the green led
            end
            else begin
                if ( clk_ms_en == 1'b1 ) begin
                    run_led <=  ~ run_led ;
                end
                else ;
            end
        end
        else begin
            run_led <=  1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// light up err_led on the communication and optical module working on
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        err_led <=   1'b0 ;
    end
    else begin
        err_led <=   1'b0 ; 
    end
end

//----------------------------------------------------------------------------------
// indication of the communication  
//----------------------------------------------------------------------------------
assign  led_drive_flag[0]     =   { lvds_rx_eop[0]  , lvds_slink_err[0]  } ;
assign  led_drive_flag[1]     =   { lvds_rx_eop[1]  , lvds_slink_err[1]  } ;
assign  led_drive_flag[2]     =   { lvds_rx_eop[2]  , lvds_slink_err[2]  } ;
assign  led_drive_flag[3]     =   { lvds_rx_eop[3]  , lvds_slink_err[3]  } ;
assign  led_drive_flag[4]     =   { lvds_rx_eop[4]  , lvds_slink_err[4]  } ;
assign  led_drive_flag[5]     =   { lvds_rx_eop[5]  , lvds_slink_err[5]  } ;
assign  led_drive_flag[6]     =   { lvds_rx_eop[6]  , lvds_slink_err[6]  } ;
assign  led_drive_flag[7]     =   { lvds_rx_eop[7]  , lvds_slink_err[7]  } ;
assign  led_drive_flag[8]     =   { lvds_rx_eop[8]  , lvds_slink_err[8]  } ;
assign  led_drive_flag[9]     =   { lvds_rx_eop[9]  , lvds_slink_err[9]  } ;
assign  led_drive_flag[10]    =   { lvds_rx_eop[10] , lvds_slink_err[10] } ;
assign  led_drive_flag[11]    =   { lvds_rx_eop[11] , lvds_slink_err[11] } ;
assign  led_drive_flag[12]    =   { lvds_rx_eop[12] , lvds_slink_err[12] } ;
assign  led_drive_flag[13]    =   { lvds_rx_eop[13] , lvds_slink_err[13] } ;
assign  led_drive_flag[14]    =   { fiber_tx_eop[0] , 1'b0 } ;
assign  led_drive_flag[15]    =   { fiber_rx_eop[0] , fiber_slink_err[0] } ;
assign  led_drive_flag[16]    =   { fiber_tx_eop[1] , 1'b0 } ;
assign  led_drive_flag[17]    =   { fiber_rx_eop[1] , fiber_slink_err[1] } ;
assign  led_drive_flag[18]    =   { ex_rx_eop[0]  , ex_slink_err[0]  } ;
assign  led_drive_flag[19]    =   { ex_rx_eop[1]  , ex_slink_err[1]  } ;
                    
assign  ch1_rled    =   self_cfg_err?2'b00:led_drive[0] ;// FMQ modified. @2018/6/22 17:01:08
assign  ch2_rled    =   self_cfg_err?2'b00:led_drive[1] ;
assign  ch3_rled    =   self_cfg_err?2'b00:led_drive[2] ;
assign  ch4_rled    =   self_cfg_err?2'b00:led_drive[3] ;
assign  ch5_rled    =   self_cfg_err?2'b00:led_drive[4] ;
assign  ch6_rled    =   self_cfg_err?2'b00:led_drive[5] ;
assign  ch7_rled    =   self_cfg_err?2'b00:led_drive[6] ;
assign  ch8_rled    =   self_cfg_err?2'b00:led_drive[7] ;
assign  ch9_rled    =   self_cfg_err?2'b00:led_drive[8] ;
assign  ch10_rled   =   self_cfg_err?2'b00:led_drive[9]  ;
assign  ch11_rled   =   self_cfg_err?2'b00:led_drive[10] ;
assign  ch12_rled   =   self_cfg_err?2'b00:led_drive[11] ;
assign  ch13_rled   =   self_cfg_err?2'b00:led_drive[12] ;
assign  ch14_rled   =   self_cfg_err?2'b00:led_drive[13] ;
assign  sff1_tled   =   self_cfg_err?2'b00:led_drive[14] ;
assign  sff1_rled   =   self_cfg_err?2'b00:led_drive[15] ;
assign  sff2_tled   =   self_cfg_err?2'b00:led_drive[16] ;
assign  sff2_rled   =   self_cfg_err?2'b00:led_drive[17] ;
assign  mas_led     =   2'b00;// FMQ modified. @2018/6/14 9:51:35//led_drive[18] ;
assign  sla_led     =   2'b00;// FMQ modified. @2018/6/14 9:51:41//led_drive[19] ;
                                
assign  slot_en = { enable_slot[16] , enable_slot[16] , enable_slot[15] , enable_slot[15] ,
                    enable_slot[14] , enable_slot[14] , enable_slot[13:0] } ; 

genvar i;
generate                               
    for( i = 0 ; i < 20 ; i = i+1 ) 
    begin : Nhotplug

    LEDCTL                      U_COM_LED    
    ( 
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_ms_en                  ( clk_ms_en                 ),

    .cfg_en                     ( cfg_en                    ),
    .slot_en                    ( slot_en[i]                ),
    .com_trig                   ( led_drive_flag[i]         ), 
    .com_led                    ( led_drive[i]              )
    ); 

end
endgenerate

endmodule

