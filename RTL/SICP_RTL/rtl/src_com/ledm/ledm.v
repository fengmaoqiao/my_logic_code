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

module LEDM 
    (
    // clock & reset
    clk_sys                     ,   
    rst_sys_n                   ,   
    
    card_type                   ,
    sff_enable                  ,
    enable_slot                 , 
    cfg_en                      ,
    board_type_ok               ,
    self_cfg_err                ,  

    fiber_tx_eop                ,   
    fiber_rx_eop                ,   
    fiber_slink_err             ,   
    lvds_rx_eop                 ,   
    lvds_slink_err              ,   

    // LED out
    run_led                     ,   // Indicating module of work running status 
    err_led                     ,   // Indicating module of communication failure status 
    mc2_led                     ,   // Indicating communication status of module and master module I  
    mc1_led                     ,   // Indicating communication status of master module of master
    com_led                     ,   // Indicating communication status of master module of slave
    sff0_tled                   ,   // Indicating transmit communication status with optcial module I
    sff1_tled                   ,   // Indicating transmit communication status with optcial module II
    sff2_tled                   ,   // Indicating transmit communication status with optcial module III
    sff3_tled                   ,   // Indicating transmit communication status with optcial module IV
    sff0_rled                   ,   // Indicating recieve communication status with optcial module I 
    sff1_rled                   ,   // Indicating recieve communication status with optcial module II 
    sff2_rled                   ,   // Indicating recieve communication status with optcial module III 
    sff3_rled                       // Indicating recieve communication status with optcial module IV
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   FREQ_2HZ_BIT    =   25 ; 

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   

input   wire    [4:0]           card_type                           ;
input   wire    [3:0]           sff_enable                          ;
input   wire    [15:0]          enable_slot                         ; 
input   wire                    cfg_en                              ;  
input   wire                    board_type_ok                       ;
input   wire                    self_cfg_err                        ;  
input   wire    [3:0]           fiber_tx_eop                        ;   
input   wire    [3:0]           fiber_rx_eop                        ;   
input   wire    [3:0]           fiber_slink_err                     ;   
input   wire    [1:0]           lvds_rx_eop                         ;   
input   wire    [1:0]           lvds_slink_err                      ;   

// declare output signal
output  reg                     run_led                             ;   
output  reg                     err_led                             ;   
output  reg     [1:0]           mc2_led                             ;   
output  reg     [1:0]           mc1_led                             ;   
output  wire    [1:0]           com_led                             ;   
output  reg     [1:0]           sff0_tled                           ;   
output  reg     [1:0]           sff1_tled                           ;   
output  reg     [1:0]           sff2_tled                           ;   
output  reg     [1:0]           sff3_tled                           ;   
output  reg     [1:0]           sff0_rled                           ;   
output  reg     [1:0]           sff1_rled                           ;   
output  reg     [1:0]           sff2_rled                           ;   
output  reg     [1:0]           sff3_rled                           ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            com_eop                             ;   
wire                            com_err                             ;   
wire        [1:0]               led_drive_flag  [9:0]               ;
wire        [1:0]               led_drive       [9:0]               ;
wire        [9:0]               slot_en                             ;   

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
        if ( clk_ms_cnt[FREQ_2HZ_BIT-1] == 1'b1 ) begin 
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
                if(card_type == 5'd0) begin
                    run_led <=   1'b0 ; //zero configuration , means no config
                end
                else if ( clk_ms_en == 1'b1 ) begin
                    run_led <=  ~ run_led ;
                end
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
assign  led_drive_flag[0]    =   { lvds_rx_eop[0] , lvds_slink_err[0] } ;
assign  led_drive_flag[1]    =   { lvds_rx_eop[1] , lvds_slink_err[1] } ;
assign  led_drive_flag[2]    =   { fiber_rx_eop[0] , fiber_slink_err[0] } ;
assign  led_drive_flag[3]    =   { fiber_rx_eop[1] , fiber_slink_err[1] } ;
assign  led_drive_flag[4]    =   { fiber_rx_eop[2] , fiber_slink_err[2] } ;
assign  led_drive_flag[5]    =   { fiber_rx_eop[3] , fiber_slink_err[3] } ;
assign  led_drive_flag[6]    =   { fiber_tx_eop[0] , 1'b0 } ;
assign  led_drive_flag[7]    =   { fiber_tx_eop[1] , 1'b0 } ;
assign  led_drive_flag[8]    =   { fiber_tx_eop[2] , 1'b0 } ;
assign  led_drive_flag[9]    =   { fiber_tx_eop[3] , 1'b0 } ;

always @ (posedge clk_sys) begin
      if(self_cfg_err == 1'b0) begin
          mc1_led   <= led_drive[0] ;
          mc2_led   <= led_drive[1] ;
          sff0_rled <= led_drive[2] ;
          sff1_rled <= led_drive[3] ;
          sff2_rled <= led_drive[4] ;
          sff3_rled <= led_drive[5] ;
          sff0_tled <= led_drive[6] ;
          sff1_tled <= led_drive[7] ;
          sff2_tled <= led_drive[8] ;
          sff3_tled <= led_drive[9] ;
      end
      else begin
          mc1_led   <= 2'b00 ;
          mc2_led   <= 2'b00 ;
          sff0_rled <= 2'b00 ;
          sff1_rled <= 2'b00 ;
          sff2_rled <= 2'b00 ;
          sff3_rled <= 2'b00 ;
          sff0_tled <= 2'b00 ;
          sff1_tled <= 2'b00 ;
          sff2_tled <= 2'b00 ;
          sff3_tled <= 2'b00 ;
      end
end

//here changed by sunfeng
//assign  slot_en = ( card_type == `COM3_TYPE ) ? { enable_slot[11:8] , 4'h0 , enable_slot[13] , enable_slot[12] }  : 
assign  slot_en = { enable_slot[11:8] , enable_slot[3:0] , enable_slot[13] , enable_slot[12] } ;

    genvar i ;
    generate
    for( i = 0 ; i < 10 ; i = i+1 ) 
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

