// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   BPFMC01
// CREATE DATE      :   2017-08-15
// DEPARTMENT       :   R&D
// AUTHOR           :   fengmaoqiao
// AUTHOR'S EMAIL   :   fengmaoqiao@cng.com
// AUTHOR'S TEL     :   13881892805
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-15  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active hign
// Clock Domains    :   clk_50m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`include "DEFINES.v"

module  SELF_MCU_STATUS #(
    parameter   UART_TX_PERIOD      =       32'd250000
    )
    (
    // clock & reset
    input   wire                clk_sys             ,
    input   wire                rst_sys_n           ,

    // uart input
    input   wire    [31:0]      rx_frame_data       ,
    input   wire                rx_frame_data_val   ,
    input   wire                crc_check_ok        ,
    input   wire                uart_time_out       ,
 
    // mpu_case_sta input
    output  reg                 mpu_sta_rd_sel      ,
    output  reg     [9:0]       mpu_sta_rd_addr     ,
    input   wire    [15:0]      mpu_sta_rd_data     ,
    // indicate the mcu ms status
    output  reg                 mcu_is_master       ,
    // indicate the self status and mcu status
    output  reg     [15:0]      self_status         ,
    output  reg     [15:0]      mcu_status          ,

    input   wire    [15:0]      slink_err           ,
    input   wire                emif_err            ,
    input   wire    [7:0]       ms_mode             ,
    input   wire                arm_ok              ,

    output  reg                 frame_send_en       ,
    output  reg     [31:0]      frame_send_data     ,

    input   wire                mpu_cfg_wr_ok       ,
    input   wire                send_sta_val        ,
    input   wire    [1:0]       arm_mode            ,
    output  reg                 mcu_arm_run         ,
    output  reg     [1:0]       mcu_arm_mode        , 

    input   wire    [15:0]      current_state_i
                       
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal

// declare output signal
  
// declare inout signal
   

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                self_arm_ok                 ;
wire                load                        ;
reg                 frame_send_back             ;
// reg signal
reg                 rx_frame_data_val_d1        ;
reg     [15:0]      mpu_sta_cfg_pattern         ;
reg     [15:0]      mpu_sta_com_pattern         ;

reg     [31:0]      uart_data                   ;
reg     [31:0]      uart_tx_cnt                 ;

reg     [31:0]      mpu_cfg_ok_cnt              ;

reg                 uart_rd_feedback            ;
reg     [31:0]      tx_reset_cnt;
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
assign self_arm_ok  =   self_status[15];
localparam  TX_RESET_WAIT       =   32'd250000000;

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/


//----------------------------------------------------------------------------------
// UART send main controller state data per UART_TX_PERIOD
//----------------------------------------------------------------------------------
assign load = ( uart_tx_cnt == 32'd0 );

always @(posedge clk_sys or negedge rst_sys_n) begin
    if(~rst_sys_n) begin
         tx_reset_cnt <= TX_RESET_WAIT ;
    end else begin
        if( tx_reset_cnt != 32'd0 )
         tx_reset_cnt <= tx_reset_cnt - 1;
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        uart_tx_cnt <= UART_TX_PERIOD;
    end
    else begin
        if( uart_tx_cnt == 32'd0 )
            uart_tx_cnt <= UART_TX_PERIOD;
        else begin
            if( send_sta_val )
                uart_tx_cnt <= uart_tx_cnt - 1;
            else
                ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        frame_send_en   <= 1'b0;
    end
    else begin
        if( load && tx_reset_cnt == 32'd0 ) 
            frame_send_en   <= 1'b1;
        else
            frame_send_en   <= 1'b0;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        frame_send_data <= 32'd0;
    end
    else begin
        if( load && ms_mode == 8'h00 && current_state_i != 16'd0 && tx_reset_cnt ==32'd0 )
            frame_send_data <=  { 8'haa , 7'h00 , &ms_mode , arm_mode , slink_err[13:0] };
        else if( load && ms_mode == 8'hff && current_state_i != 16'd0 )
            frame_send_data <=  { 8'haa ,7'h00 , &ms_mode , arm_mode , slink_err[13:0] };
        else
            frame_send_data <=  32'd0;
    end
end 

//----------------------------------------------------------------------------------
// 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rx_frame_data_val_d1    <= 16'd0;
    end
    else begin
        rx_frame_data_val_d1    <=  rx_frame_data_val;
    end
end

//----------------------------------------------------------------------------------
// mpu_case_sta read logic
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        mpu_sta_rd_sel  <= 1'b0;
    end
    else begin
        if( rx_frame_data_val )
            mpu_sta_rd_sel  <= 1'b1;
        else if( rx_frame_data_val_d1 )
            mpu_sta_rd_sel  <= 1'b1;
        else
            mpu_sta_rd_sel  <= 1'b0;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin

    end
    else begin
        if( rx_frame_data_val )
            mpu_sta_rd_addr    <= 9'd0;
        else if( rx_frame_data_val_d1 )
            mpu_sta_rd_addr    <= 9'd1;
        else
            mpu_sta_rd_addr    <= 9'd0;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        mpu_sta_cfg_pattern    <= 16'd0;
        mpu_sta_com_pattern   <= 16'd0;
    end
    else begin
        if (rx_frame_data_val )
            mpu_sta_cfg_pattern    <=  mpu_sta_rd_data;
        else if( rx_frame_data_val_d1 )
            mpu_sta_com_pattern    <=  { mpu_sta_rd_data[7:0] , mpu_sta_rd_data[15:8] };        //change the byte order 
        else
            ;
    end
end
//----------------------------------------------------------------------------------
// uart read logic
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        uart_data   <= 32'd0;
    end
    else begin
        if( rx_frame_data_val )
            uart_data   <= rx_frame_data;
        else
            ;
    end
end
//----------------------------------------------------------------------------------
// when self is slaver,wait for the master state req signal.
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        mcu_arm_mode    <= 2'b00;
    end
    else begin
        if( rx_frame_data_val_d1 && ms_mode == 8'hff )begin
            if( uart_data[31:24] == 8'haa ) begin
                mcu_arm_mode     <= uart_data[15:14];
            end
            else
                ;
        end
    end
end

//----------------------------------------------------------------------------------
// arbitrate signal for hotra
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        mcu_is_master   <= 1'b0;
    end
    else begin
        if( rx_frame_data_val_d1 ) begin
            if( uart_data[16] == 1'b1 )
                mcu_is_master   <= 1'b1;
            else
                mcu_is_master   <= 1'b0;
        end
        else
            ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        self_status <= 16'd0;
    end
    else begin
        if( rx_frame_data_val_d1 ) 
            self_status <= { 2'b0 , mpu_sta_com_pattern[13:0] };
        else
            ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        mcu_status  <= 16'd0;
    end
    else begin
        if( rx_frame_data_val_d1 )
            mcu_status  <= { 1'b0 ,  uart_data[16] , uart_data[13:0] };          // uart[16]:ms_flag; uart[13:0]:slink_status
        else
            ;
    end
end


endmodule


