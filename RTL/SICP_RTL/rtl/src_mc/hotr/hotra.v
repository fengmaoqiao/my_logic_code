// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   HOTRA
// CREATE DATE      :   2017-12-12
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-12-12  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   Hot redundancy arbitration
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
`define FMQ 1

module  HOTRA
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    clk_emif                    ,   
    rst_emif                    ,   

    // write port
    wr_sel                      ,   
    wr_en                       ,   
    wr_data                     ,  

    self_status                 ,
    mcu_status                  ,
    uart_err                    ,
    arm_ok                      ,
    hotra_en                    ,
    enable_slot                 ,
    arm_mode                    ,
    send_sta_val                ,
    current_state_o             ,

    slot_num                    ,
    sta_num                     ,
    box_num                     ,
    redundancy_mode             ,  
    hr_online                   , 

    self_cfg_err                ,   
    slink_err                   ,   

    hr_ht_in                    ,   
    self_ht_out                 ,
    hr_ms_in                    ,   
    self_ms_out                 , 

    soft_rst                    ,   
    selfm_ms_flag               ,   
    excfg_ms_flag               ,   
    slot2_ms_flag               ,   
    slot3_ms_flag               ,   
    slot4_ms_flag               ,   
    slot5_ms_flag               ,   
    slot6_ms_flag               ,   
    slot7_ms_flag               ,   
    slot8_ms_flag               ,   
    slot9_ms_flag               ,   
    slot10_ms_flag              ,   
    slot11_ms_flag              ,   
    slot12_ms_flag              ,   
    slot13_ms_flag              ,   
    slot14_ms_flag              ,   
    slot15_ms_flag              ,
    arm_cycle                   ,
    mcu_arm_mode                ,
    uart_rd_val                 ,
    mcu_is_valid                ,
    hw_init_ok                  ,
    arm_tx_finish               ,
    repeat_val
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
`ifdef  SIM
localparam  NORMAL_FREQ         =   4'd3                ; 
localparam  FAULT_FREQ          =   4'd5                ;

localparam  SLAVE_FREQ          =   4'd3                ; 
localparam  MASTER_FREQ         =   4'd5                ;

localparam  SHAKE_DLY           =   16'd50              ;
localparam  HOTRA_EN_TIME       =   32'd200             ;
localparam  ONLINE_SHAKE_DLY    =   16'd100             ;
localparam  ARM_TIMEOUT_CNT     =   32'd1250          ;

localparam ARM_WAIT_TIME        =   32'd1250            ; //wait for arm cycle work 10s
`else
//parameter   NORMAL_FREQ    =   4'd10 ; // 1024 * 80ns = 82us 
//parameter   FAULT_FREQ     =   4'd15 ; // 32768 * 80ns = 2.6ms

localparam  NORMAL_FREQ         =   4'd3                ; // 1024 * 80ns = 82us 
localparam  FAULT_FREQ          =   4'd5                ; // 1024 * 80ns = 82us 

localparam  SLAVE_FREQ          =   4'd10               ; 
localparam  MASTER_FREQ         =   4'd15               ;

localparam  SHAKE_DLY           =   16'd1250            ; // 100us
localparam  HOTRA_EN_TIME       =   32'd25000000         ; // 100ms
localparam  ONLINE_SHAKE_DLY    =   16'd1250            ; // 100us
localparam  ARM_TIMEOUT_CNT     =   32'd7500000          ; // 600ms

localparam  ARM_WAIT_TIME        =   32'd125000000       ; //wait for arm cycle work 10s
`endif

localparam  ARM_MAIT            = 2'b10;
localparam  ARM_DOWN            = 2'b01;
localparam  ARM_RUN             = 2'b11;
localparam  UART_JUDGE_DLY      = 32'd75000;

localparam  ARM_ED_TIME         =   32'd187500;

localparam 
            IDLE            =       16'd0                               ,
            SINGLE_MODE     =       16'd1                               ,   
            DOUBLE_MODE     =       16'd2                               ,   
            FAULT_DIAG      =       16'd4                               ,   
            ARM_DIAG        =       16'd8                               ,   
            SLINK_DIAG      =       16'd16                              ;


localparam      
            CPU_INIT        =       8'h6a                           ,
            CPU_WAIT        =       8'h7a                           ,
            CPU_MS          =       8'h8a                           ,
            CPU_RD          =       8'h50                           ,
            CPU_SYNC        =       8'h51                           ,
            CPU_ALGO        =       8'h52                           ,
            CPU_SD          =       8'h53                           ,
            CPU_MAIT        =       8'h54                           ,
            CPU_IDLE        =       8'h55                           ,
            CPU_FAULT       =       8'ha5                           ;

localparam  HEARTBEAT_FREQ  =       8'd255                           ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   
input   wire                    clk_emif                            ;   
input   wire                    rst_emif                            ;   

input   wire                    wr_sel                              ;   
input   wire                    wr_en                               ;   
input   wire        [15:0]      wr_data                             ;
input   wire        [3:0]       slot_num                            ;   
input   wire        [7:0]       redundancy_mode                     ;  
input   wire                    hr_online                           ;   
input   wire                    self_cfg_err                        ;   
input   wire        [15:0]      slink_err                           ;   
input   wire                    hr_ht_in                            ;   
input   wire                    hr_ms_in                            ;   

// declare output signal
output  reg                     soft_rst                            ;   
output  reg                     self_ht_out                         ;   
output  reg                     self_ms_out                         ;   
output  reg         [7:0]       selfm_ms_flag   /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       excfg_ms_flag   /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot2_ms_flag   /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot3_ms_flag   /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot4_ms_flag   /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot5_ms_flag   /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot6_ms_flag   /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot7_ms_flag   /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot8_ms_flag   /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot9_ms_flag   /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot10_ms_flag  /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot11_ms_flag  /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot12_ms_flag  /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot13_ms_flag  /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot14_ms_flag  /* synthesis syn_preserve = 1 */ ;
output  reg         [7:0]       slot15_ms_flag  /* synthesis syn_preserve = 1 */ ;

input   wire        [15:0]      self_status                         ;   
input   wire        [15:0]      mcu_status                          ;   
input   wire                    uart_err                            ;   
output  reg                     arm_ok                              ;   
input   wire                    hotra_en                            ;   
input   wire        [15:0]      enable_slot                         ;   
output  reg                     send_sta_val                        ;   
output  reg         [1:0]       arm_mode                            ;   
output  reg         [15:0]      current_state_o                     ;   

input   wire        [15:0]      arm_cycle                           ;   
input   wire        [1:0]       mcu_arm_mode                        ;
input   wire                    uart_rd_val                         ;

input   wire        [7:0]       sta_num                             ;
input   wire        [3:0]       box_num                             ;
output  reg                     mcu_is_valid                        ;
output  reg                     hw_init_ok                          ;
output  reg                     arm_tx_finish                       ;
output  reg                     repeat_val                     ;

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            self_err                            ;  
wire                            hr_ht_in_ring                       ;   
wire                            hr_ht_in_fall                       ;   
wire                            hr_ms_in_ring                       ;   
wire                            hr_ms_in_fall                       ;   
wire         [7:0]              master_slave_flag                   ;/* synthesis syn_preserve = 1 */    

// reg signal
reg                             ms_mode                             ;/* synthesis syn_preserve = 1 */  
reg                             hr_online_d1                        ;/* synthesis syn_preserve = 1 */ 
reg                             hr_online_d2                        ;/* synthesis syn_preserve = 1 */ 
reg         [3:0]               slot_num_d1                         ;/* synthesis syn_preserve = 1 */  
reg         [3:0]               slot_num_d2                         ;/* synthesis syn_preserve = 1 */ 
reg         [15:0]              ms_out_cnt                          ;  
reg                             hr_ms_in_d1                         ;   
reg                             hr_ms_in_d2                         ;   
reg                             hr_ms_in_d3                         ;   
reg                             hr_ms_in_d4                         ;   
reg         [15:0]              hr_ms_in_cnt                        ;   
reg         [1:0]               hr_ms_state                         ;/* synthesis syn_preserve = 1 */ 
reg                             self_cfg_err_d1                     ;   
reg                             self_cfg_err_d2                     ;   
reg         [15:0]              slink_err_d1                        ;   
reg         [15:0]              slink_err_d2                        ;/* synthesis syn_preserve = 1 */ 
reg         [15:0]              ht_out_cnt                          ;/* synthesis syn_preserve = 1 */ 
reg                             hr_ht_in_d1                         ;/* synthesis syn_preserve = 1 */ 
reg                             hr_ht_in_d2                         ;/* synthesis syn_preserve = 1 */ 
reg                             hr_ht_in_d3                         ;/* synthesis syn_preserve = 1 */ 
reg                             hr_ht_in_d4                         ;/* synthesis syn_preserve = 1 */ 
reg         [15:0]              hr_ht_in_cnt                        ;/* synthesis syn_preserve = 1 */ 
reg         [1:0]               hr_ht_state                         ;   
reg                             wr_sel_d1                           ;   
reg                             wr_en_d1                            ;   
reg         [15:0]              wr_data_d1                          ;   
reg         [3:0]               wr_data_cnt                         ;  
reg                             arm_initial_ok                      ;  
reg                             arm_ok_d1                           ;   
reg                             arm_ok_d2                           ;  
reg                             soft_reset                          ;   
reg                             soft_reset_d1                       ;  
reg         [15:0]              arm_cycle_d1                        ;
reg         [15:0]              arm_cycle_d2                        ;
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
reg         [15:0]              current_state                       ;/* synthesis syn_preserve = 1 */ 
reg         [15:0]              next_state                          ;/* synthesis syn_preserve = 1 */ 

wire                            mcu_invalid                         ;/* synthesis syn_preserve = 1 */ 
wire        [13:0]              mcu_slink_err                       ;/* synthesis syn_preserve = 1 */ 
wire                            mcu_is_master                       ;/* synthesis syn_preserve = 1 */ 

wire        [1:0]               self_mcu_ms                         ;/* synthesis syn_preserve = 1 */ 

reg                             mcu_is_master_d1                    ;/* synthesis syn_preserve = 1 */ 
reg                             mcu_is_master_d2                    ;/* synthesis syn_preserve = 1 */ 

reg                             self_arm_timeout                    ;/* synthesis syn_preserve = 1 */    
wire        [13:0]              self_slink_err                      ;/* synthesis syn_preserve = 1 */    

reg                             hr_ms_in_shake                      ;/* synthesis syn_preserve = 1 */ 
reg         [15:0]              hr_ms_in_cnt1                       ;/* synthesis syn_preserve = 1 */ 
reg         [15:0]              hr_ms_in_cnt2                       ;/* synthesis syn_preserve = 1 */ 

reg                             hr_ms_in_shake_d1                   ;/* synthesis syn_preserve = 1 */    
reg                             hr_online_shake                     ;/* synthesis syn_preserve = 1 */    
reg                             hr_online_shake_d1                  ;/* synthesis syn_preserve = 1 */    
reg                             hr_online_shake_d2                  ;/* synthesis syn_preserve = 1 */    
reg         [15:0]              hr_online_cnt1                      ;/* synthesis syn_preserve = 1 */    
reg         [15:0]              hr_online_cnt2                      ;/* synthesis syn_preserve = 1 */ 

reg         [1:0]               mcu_arm_mode_d1                     ;/* synthesis syn_preserve = 1 */ 
reg         [1:0]               mcu_arm_mode_d2                     ;/* synthesis syn_preserve = 1 */ 

reg         [1:0]               arm_mode_d1                         ;/* synthesis syn_preserve = 1 */    
reg         [1:0]               arm_mode_d2                         ;/* synthesis syn_preserve = 1 */   

reg         [31:0]              arm_cycle_local                     ;/* synthesis syn_preserve = 1 */ 
reg                             master_slave_flag_d1                ;/* synthesis syn_preserve = 1 */  

reg         [31:0]              uart_judge_dly                      ;/* synthesis syn_preserve = 1 */  
reg         [7:0]               reg_arm_timeout                     ;

reg         [7:0]               high_hold_time                      ;
reg         [7:0]               low_hold_time                       ;
reg                             heart_beat_err                      ;

// the redundency mc board FPGA invalid state
assign mcu_invalid   =       ( hr_online_shake_d2 == 1'b0 || heart_beat_err == 1'b1 ) ? 1'b1 : 1'b0;
assign mcu_is_master =       ( hr_ms_in_shake == 1'b1 && heart_beat_err == 1'b0 ) ? 1'b1 : 1'b0;

assign mcu_slink_err  =       ( mcu_status[13:0] );
assign self_mcu_ms    =       { ms_mode , mcu_is_master };
assign self_slink_err =       slink_err[13:0];

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
       mcu_is_valid      <= 1'b0; 
    end
    else begin
        if( ~mcu_invalid )
            mcu_is_valid <= 1'b1;
        else
            mcu_is_valid <= 1'b0;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hw_init_ok     <= 1'b0;
    end
    else begin
        if(  slot_num_d2 == 4'd0 || slot_num_d2 == 4'd1   )
            hw_init_ok <= 1'b1;
        else
            hw_init_ok <= 1'b0;
    end
end

//resync
reg [7:0]   uart_rd_val_cnt ;
reg         uart_rd_val_dly ;
reg         uart_rd_val_dly_d1 ;
reg         uart_rd_val_dly_d2 ;
always @( posedge clk_emif or negedge rst_emif ) begin 
    if( ~rst_emif ) begin
        uart_rd_val_cnt <= 8'd0;
    end else begin
        if( uart_rd_val )
            uart_rd_val_cnt <= 8'd16 ;
        else begin
            if( uart_rd_val_cnt != 8'd0 )
                uart_rd_val_cnt <= uart_rd_val_cnt - 1 ;
            else ;
        end // else
    end
end

always @(posedge clk_emif or negedge rst_emif) begin
    if( ~rst_emif ) begin
        uart_rd_val_dly <= 1'b0;
    end else begin
        if( uart_rd_val_cnt == 8'd14 )
            uart_rd_val_dly <= 1'b1;
        else if( uart_rd_val_cnt == 8'd1 )
            uart_rd_val_dly <= 1'b0;
        else ;
    end
end

always @( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( ~rst_12_5m ) begin
         uart_rd_val_dly_d1 <= 1'b0;
         uart_rd_val_dly_d2 <= 1'b0;
    end else begin
         uart_rd_val_dly_d1 <= uart_rd_val_dly ;
         uart_rd_val_dly_d2 <= uart_rd_val_dly_d1 ;
    end
end

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// arm status judge
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        arm_cycle_d1    <= 16'd0;
        arm_cycle_d2    <= 16'd0;
    end
    else begin
        arm_cycle_d1    <= arm_cycle;
        arm_cycle_d2    <= arm_cycle_d1;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        arm_cycle_local <= 32'd0;
    end
    else begin
        arm_cycle_local <=  { arm_cycle_d2  , 12'b0 } + 17'h10000 ; // ns/80 + 5ms
    end
end

always @ ( posedge clk_emif ) begin
    wr_sel_d1   <=   wr_sel  ;
    wr_en_d1    <=   wr_en   ;
    wr_data_d1  <=   wr_data ;
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        wr_data_cnt  <=   4'h0 ;
    end
    else begin
        if ( wr_sel_d1 == 1'b1 ) begin
            if ( wr_en_d1 == 1'b1 ) begin
                wr_data_cnt  <=   wr_data_cnt + 1'b1 ;
            end
        end
        else begin
            wr_data_cnt  <=   4'h0 ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        arm_initial_ok  <=   1'b0 ;
    end
    else begin
        if ( wr_data_cnt == 4'd1 && wr_en_d1 == 1'b1 ) begin
            if (  wr_data_d1 == 16'hffff ) begin
                arm_initial_ok  <=   1'b1 ;
            end
            else begin
                arm_initial_ok  <=   1'b0 ;
            end
        end
    end
end
//----------------------------------------------------------------------------------
// arm mode generate
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        arm_mode <= ARM_RUN;
    end
    else begin
        if( wr_data_cnt == 4'd1 && wr_en_d1 == 1'b1 ) begin
            if( wr_data_d1[15:8] == 8'd1 ) 
                arm_mode <= ARM_RUN;
            else if( wr_data_d1[15:8] == 8'd3 )
                arm_mode <= ARM_MAIT;
            else if( wr_data_d1[15:8] == 8'd2 )
                arm_mode <= ARM_DOWN;
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        arm_mode_d1 <= 2'b11;
        arm_mode_d2 <= 2'b11;
    end
    else begin
        arm_mode_d1 <= arm_mode;
        arm_mode_d2 <= arm_mode_d1;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        mcu_arm_mode_d1 <= 2'b11;
        mcu_arm_mode_d2 <= 2'b11;
    end
    else begin
        mcu_arm_mode_d1 <= mcu_arm_mode;
        mcu_arm_mode_d2 <= mcu_arm_mode_d1;
    end
end
//----------------------------------------------------------------------------------
// when reset , wait for arm 10s  
//----------------------------------------------------------------------------------
reg                             arm_cycle_run                       ;/* synthesis syn_preserve = 1 */    
reg [31:0]                      wait_arm_cycle_cnt                  ;/* synthesis syn_preserve = 1 */    

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        wait_arm_cycle_cnt  <= 32'b0;
        arm_cycle_run       <= 1'b0;
    end
    else begin
        if( wait_arm_cycle_cnt != ARM_WAIT_TIME ) begin
            wait_arm_cycle_cnt  <= wait_arm_cycle_cnt + 1;
            arm_cycle_run       <= 1'b0;
        end
        else
            arm_cycle_run       <= 1'b1;
    end
end
//----------------------------------------------------------------------------------
// arm timeout logic
//----------------------------------------------------------------------------------
reg [15:0]                      arm_period_cnt                      ;/* synthesis syn_preserve = 1 */    
reg [15:0]                      arm_period_cnt_d1                   ;/* synthesis syn_preserve = 1 */    
reg                             arm_timeout_debug                   ;/* synthesis syn_preserve = 1 */ 
reg [31:0]                      period_time_cnt                     ;/* synthesis syn_preserve = 1 */    
reg [7:0]                       arm_state                           ;

wire                            arm_step_val;

assign  arm_step_val      =   ( wr_data_d1[7:0] == CPU_INIT || wr_data_d1[7:0] == CPU_WAIT || wr_data_d1[7:0] == CPU_MS || wr_data_d1[7:0] == CPU_RD || wr_data_d1[7:0] == CPU_SYNC || wr_data_d1[7:0] == CPU_ALGO || wr_data_d1[7:0] == CPU_SD ||  wr_data_d1[7:0] == CPU_MAIT || wr_data_d1[7:0] == CPU_IDLE );

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
       arm_period_cnt <= 16'd0; 
    end
    else begin
        if( wr_data_cnt== 4'd1 && wr_en_d1 == 1'b1 ) begin
            if( arm_step_val ) begin
                arm_period_cnt <= arm_period_cnt + 1;
            end
            else;
        end
        else;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        arm_state <= 8'd0;
    end
    else begin
    case( wr_data_d1[7:0] )
        CPU_INIT    :   arm_state   <=      8'd1;
        CPU_WAIT    :   arm_state   <=      8'd2;
        CPU_MS      :   arm_state   <=      8'd3;
        CPU_RD      :   arm_state   <=      8'd4;
        CPU_SYNC    :   arm_state   <=      8'd5;
        CPU_ALGO    :   arm_state   <=      8'd6;
        CPU_SD      :   arm_state   <=      8'd7;
        CPU_MAIT    :   arm_state   <=      8'd8;
        CPU_IDLE    :   arm_state   <=      8'd9;
        default     :   ;
    endcase
    end
end

//----------------------------------------------------------------------------------
// arm tx step detect and generate the repeat signal to type1 and typ1 dp
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        arm_tx_finish <= 1'b0;
    end
    else begin
        if( wr_data_cnt == 4'd1 && wr_en_d1 == 1'b1 && wr_data_d1[7:0] == 8'h53 ) 
                arm_tx_finish <= 1'b1;
            else
                arm_tx_finish <= 1'b0;
    end
end

//per 12ms repeat send the data
localparam  REPEAT_TIME =   32'd1875000;     
reg [31:0]                      re_send_cnt                         ;   
reg [31:0]                      re_send_cnt_d1                      ;   
reg                             repeat_val_sync_d1                  ;   
reg                             repeat_val_sync_d2                  ;  
reg                             repeat_data_val                     ;

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        re_send_cnt <= 32'd1;
    end
    else begin
        if( arm_tx_finish )
            re_send_cnt <= REPEAT_TIME;
        else if( re_send_cnt != 32'd0 )
            re_send_cnt <= re_send_cnt - 1;
        //else if( re_send_cnt == 32'd0 )
        //    re_send_cnt <= REPEAT_TIME;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        re_send_cnt_d1 <= 32'd0;
    end
    else
        re_send_cnt_d1 <= re_send_cnt;
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        repeat_data_val <= 1'b0;
    end
    else begin
        if( re_send_cnt_d1 == 32'd11 && re_send_cnt == 32'd10 )
            repeat_data_val <= 1'b1;
        else if( re_send_cnt == 32'd0 )
            repeat_data_val <= 1'b0;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        repeat_val_sync_d1 <= 1'b0;
        repeat_val_sync_d2 <= 1'b0;
    end
    else begin
        repeat_val_sync_d1 <= repeat_data_val;
        repeat_val_sync_d2 <= repeat_val_sync_d1;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        repeat_val <= 1'b0 ;
    end
    else begin
        repeat_val <= repeat_val_sync_d2;
    end
end
//----------------------------------------------------------------------------------
// arm timeout err detect
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        period_time_cnt  <= 31'd0;
    end
    else begin
        if( period_time_cnt == ARM_ED_TIME )
            period_time_cnt <= 32'd0;
        else
            period_time_cnt <= period_time_cnt + 1;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
       arm_timeout_debug <= 1'b0;
    end
    else begin
        if( period_time_cnt == ARM_ED_TIME ) begin
            if( arm_period_cnt_d1 == arm_period_cnt && arm_cycle_run == 1'b1 )
                arm_timeout_debug <= 1'b1;
            else
                arm_timeout_debug <= 1'b0;
        end
        else;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        arm_period_cnt_d1 <= 16'd0;
    end
    else begin
        if( period_time_cnt == ARM_ED_TIME )
            arm_period_cnt_d1 <= arm_period_cnt;
        else;
    end
end

//----------------------------------------------------------------------------------
// fpga soft reset from arm
//----------------------------------------------------------------------------------
//

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        soft_reset  <=   1'b0 ;
    end
    else begin
        if ( wr_data_cnt == 4'd2 && wr_en_d1 == 1'b1 ) begin
            if (  wr_data_d1 == 16'h5a5a ) begin
                soft_reset  <=   1'b1 ;
            end
            else begin
                soft_reset  <=   1'b0 ;
            end
        end
    end
end



always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        reg_arm_timeout  <=   8'b0 ;
    end
    else begin
        if ( wr_data_cnt == 4'd3 && wr_en_d1 == 1'b1 ) begin
              reg_arm_timeout <= wr_data_d1[15:8] ; 
        end
    end
end

always @ ( posedge clk_emif ) begin
    soft_reset_d1   <=   soft_reset  ;
end

always @ ( posedge clk_emif ) begin
    if ( soft_reset == 1'b1 && soft_reset_d1 == 1'b0 ) begin 
        soft_rst   <=   1'b0  ;
    end
    else begin
        soft_rst   <=   1'b1  ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        arm_ok_d1  <=   1'b0 ;
        arm_ok_d2  <=   1'b0 ;
    end
    else begin
        arm_ok_d1  <=   arm_initial_ok ;
        arm_ok_d2  <=   arm_ok_d1 ;
    end
end

`ifdef FMQ
//----------------------------------------------------------------------------------
// state machine
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        mcu_is_master_d1    <= 1'b0;
        mcu_is_master_d2    <= 1'b0;
    end
    else begin
        mcu_is_master_d1    <= mcu_is_master;
        mcu_is_master_d2    <= mcu_is_master_d1;
    end
end


always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        self_arm_timeout <= 1'b0;
    end
    else begin
        self_arm_timeout <= arm_timeout_debug;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        arm_ok  <= 1'b0;
    end
    else begin
        arm_ok  <= arm_ok_d2;
    end
end

//----------------------------------------------------------------------------------
// mode change counter for software
//----------------------------------------------------------------------------------
reg [15:0]                      mode_alter_cnt                      ;/* synthesis syn_preserve = 1 */    
reg                             ms_mode_d1                          ;/* synthesis syn_preserve = 1 */  
reg                             ms_mode_d2                          ;/* synthesis syn_preserve = 1 */ 

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        mode_alter_cnt  <= 16'd0;
    end
    else begin
        if(current_state != IDLE && ( ms_mode_d1 != ms_mode) )
            mode_alter_cnt <= mode_alter_cnt + 1;
        else
            ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        uart_judge_dly  <= UART_JUDGE_DLY;
    end
    else begin
        if( current_state == SLINK_DIAG && uart_judge_dly != 32'd0 )
            uart_judge_dly <= uart_judge_dly - 1;
        else if( current_state == SLINK_DIAG && uart_judge_dly == 32'd0 )
            uart_judge_dly <= UART_JUDGE_DLY ;
        else
            uart_judge_dly <= UART_JUDGE_DLY;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        ms_mode_d1 <= 1'b0;
        ms_mode_d2 <= 1'b0;
    end
    else begin
        ms_mode_d1 <= ms_mode;
        ms_mode_d2 <= ms_mode_d1;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        current_state_o <= 16'd0;
    end
    else begin
        current_state_o <= current_state;
    end
end
//----------------------------------------------------------------------------------
// main fsm
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m  ) begin
    if( rst_12_5m == 1'b0  ) begin
        current_state       <=  IDLE;
    end
    else begin
        current_state       <=  next_state  ;
    end
end

wire arm_mode_equal;
assign arm_mode_equal = ( ( arm_mode_d2 == ARM_RUN && mcu_arm_mode == ARM_RUN ) || ( arm_mode_d2 == ARM_MAIT && mcu_arm_mode == ARM_MAIT ) );


always @ (*) begin
    case( current_state )
        IDLE:
            if( arm_period_cnt != 16'd0  && ( hr_online_cnt1 == ONLINE_SHAKE_DLY || hr_online_cnt2 == ONLINE_SHAKE_DLY ) && hw_init_ok ) begin
                if( ~hr_online )
                    next_state  =   SINGLE_MODE;
                else
                    next_state  =   DOUBLE_MODE ;
            end
            else
                next_state  =   IDLE ;
        SINGLE_MODE:
            if( mcu_invalid )
                next_state  =   SINGLE_MODE ;
            else
                next_state  =   DOUBLE_MODE ;
        DOUBLE_MODE:
            if( mcu_invalid ) begin
                next_state  =   SINGLE_MODE ;
            end
            else begin
                if( self_arm_timeout && ms_mode == 1'b1 && arm_mode_equal )
                    next_state  =   FAULT_DIAG ;
                else if( ( self_slink_err > mcu_slink_err )  && ms_mode == 1'b1 && arm_mode_equal && uart_rd_val_dly_d2 )
                    next_state =    FAULT_DIAG ;
                else
                    next_state  =   DOUBLE_MODE ;
            end
            // fault case judge
        FAULT_DIAG:begin
            // if mcu is invalid,back to SINGLE_MODE
            if( mcu_invalid ) begin
                next_state  =   SINGLE_MODE ;
            end
            else begin
                if( self_arm_timeout )
                    next_state  = FAULT_DIAG ;
                else if( ( self_slink_err > mcu_slink_err ) && ms_mode == 1'b1 && uart_rd_val_dly_d2 )
                    next_state  = FAULT_DIAG ; 
                else
                    next_state  = DOUBLE_MODE ;
            end
        end // FAULT_DIAG:
        
        default:
            next_state  =   IDLE;
    endcase
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        if( slot_num_d2 == 4'd0 )
            ms_mode <= 1'b1;
        else if( slot_num_d2 == 4'd1 )
            ms_mode <= 1'b0;
        else
            ;
    end
    else begin
        case( current_state )
            // when IDLE state,default ms_mode is slaver.
        IDLE :
            if( slot_num_d2 == 4'd0 ) 
                ms_mode <= 1'b1;
            else if( slot_num_d2 == 4'd1 )
                ms_mode <= 1'b0;
            else;
            // when single main controller,ms_mode must be master.
        SINGLE_MODE :
                    ms_mode <= 1'b1;
        DOUBLE_MODE :
            // normol mode, if master is exist,so self is master.
            // if master is not exist ,according to the slot_number.
                if( slot_num_d2 == 4'd0 ) begin
                    if( ~mcu_is_master || ( hr_ms_in_shake == 1'b0 && hr_ms_in_shake_d1==1'b1 ))
                        ms_mode <= 1'b1;
                    else if( hr_ms_in_shake == 1'b1 && hr_ms_in_shake_d1 == 1'b1 )
                        ms_mode <= 1'b0;
                    else
                        ;
                end
                else if( slot_num_d2 == 4'd1 ) begin
                    if( ms_mode_d1 == 1'b0 ) begin
                        if( mcu_is_master_d2 )
                            ms_mode <= 1'b0;
                        else if( ~mcu_is_master_d2 ) 
                            ms_mode <= 1'b1;
                    end
                end
        FAULT_DIAG : begin
            // fault occur,and judge the fault
            // check the L2 fault,include the arm fault
                ms_mode <= 1'b0 ;
        end 
        default:
           ;
       endcase
   end
end

//----------------------------------------------------------------------------------
// when self is slaver,generate the wirte enable to uart
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        send_sta_val <= 1'b0;
    end
    else begin
        if( current_state != IDLE )
            send_sta_val <= 1'b1;
        else
            send_sta_val <= 1'b0;
    end
end
//----------------------------------------------------------------------------------
// add by fmq
//----------------------------------------------------------------------------------
`endif
assign  master_slave_flag   =   ms_mode == 1'b1 ? 8'hff : 8'h00 ;

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        master_slave_flag_d1 <= 1'b0;
    end
    else begin
        master_slave_flag_d1 <= master_slave_flag;
    end
end


always @ ( posedge clk_12_5m ) begin
    selfm_ms_flag   <=   master_slave_flag ;
    excfg_ms_flag   <=   master_slave_flag ;
    slot2_ms_flag   <=   master_slave_flag ;
    slot3_ms_flag   <=   master_slave_flag ;
    slot4_ms_flag   <=   master_slave_flag ;
    slot5_ms_flag   <=   master_slave_flag ;
    slot6_ms_flag   <=   master_slave_flag ;
    slot7_ms_flag   <=   master_slave_flag ;
    slot8_ms_flag   <=   master_slave_flag ;
    slot9_ms_flag   <=   master_slave_flag ;
    slot10_ms_flag  <=   master_slave_flag ;
    slot11_ms_flag  <=   master_slave_flag ;
    slot12_ms_flag  <=   master_slave_flag ;
    slot13_ms_flag  <=   master_slave_flag ;
    slot14_ms_flag  <=   master_slave_flag ;
    slot15_ms_flag  <=   master_slave_flag ;
end


//----------------------------------------------------------------------------------
// slot number detect
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        slot_num_d1  <=   4'h00 ;
        slot_num_d2  <=   4'h00 ;
    end
    else begin
        slot_num_d1  <=   slot_num ;
        slot_num_d2  <=   slot_num_d1 ;
    end
end

//----------------------------------------------------------------------------------
// master/slave output control -- master : slow  slave : fast
//----------------------------------------------------------------------------------
`ifdef GTT
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        ms_out_cnt  <=   16'h00 ;
    end
    else begin
        if( ms_mode == 1'b1 && ms_out_cnt[MASTER_FREQ] == 1'b1 ) begin
            ms_out_cnt  <=   16'h00 ;
        end
        else if ( ms_mode == 1'b0 && ms_out_cnt[SLAVE_FREQ] == 1'b1 ) begin
            ms_out_cnt  <=   16'h00 ;
        end
        else begin
            ms_out_cnt  <=   ms_out_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        self_ms_out   <=   1'b0 ;
    end
    else begin
        if( ms_mode == 1'b1 && ms_out_cnt[MASTER_FREQ] == 1'b1 ) begin
            self_ms_out  <=   ~ self_ms_out ;
        end
        else if ( ms_mode == 1'b0 && ms_out_cnt[SLAVE_FREQ] == 1'b1) begin
            self_ms_out  <=   ~ self_ms_out ;
        end
    end
end
`else
//----------------------------------------------------------------------------------
// master/slaver flag shake circuit generate
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hr_ms_in_cnt1   <= 16'd0;
        hr_ms_in_cnt2   <= 16'd0;
    end
    else begin
        if( hr_ms_in == 1'b1 ) begin
            hr_ms_in_cnt2 <= 16'd0;
            if(hr_ms_in_cnt1 == SHAKE_DLY )                
                hr_ms_in_cnt1 <= 16'd0;
            else begin
                if( hr_ms_in_cnt1 < SHAKE_DLY )
                    hr_ms_in_cnt1 <= hr_ms_in_cnt1 + 1;
                else
                    hr_ms_in_cnt1 <= hr_ms_in_cnt1;
            end
        end
        else begin
            hr_ms_in_cnt1 <= 16'd0;
            if(hr_ms_in_cnt2 == SHAKE_DLY )
                hr_ms_in_cnt2 <= 16'd0;
            else begin
                if( hr_ms_in_cnt2 < SHAKE_DLY )
                    hr_ms_in_cnt2 <= hr_ms_in_cnt2 + 1;
                else
                    hr_ms_in_cnt2 <= hr_ms_in_cnt2;
            end
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hr_ms_in_shake <= 1'b0;
    end
    else begin
        if(hr_ms_in_cnt1 == SHAKE_DLY )
            hr_ms_in_shake <= 1'b1;
        else if(hr_ms_in_cnt2 == SHAKE_DLY )
            hr_ms_in_shake <= 1'b0;
        else
            ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hr_ms_in_shake_d1 <= 1'b0;
    end
    else begin
        hr_ms_in_shake_d1 <= hr_ms_in_shake;
    end
end
//----------------------------------------------------------------------------------
// online shake circuit generate 
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hr_online_cnt1  <= 16'd0;
        hr_online_cnt2  <= 16'd0;
    end
    else begin
        if( hr_online == 1'b1 ) begin
            hr_online_cnt2 <= 16'd0;
                if( hr_online_cnt1 < ONLINE_SHAKE_DLY )
                    hr_online_cnt1 <= hr_online_cnt1 + 1;
                else
                    hr_online_cnt1 <= hr_online_cnt1;
        end
        else begin
            hr_online_cnt1 <= 16'd0;
                if( hr_online_cnt2 < ONLINE_SHAKE_DLY )
                    hr_online_cnt2 <= hr_online_cnt2 + 1;
                else
                    hr_online_cnt2 <= hr_online_cnt2;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hr_online_shake <= 1'b0;
    end
    else begin
        if( hr_online_cnt1 == ONLINE_SHAKE_DLY )
            hr_online_shake <= 1'b1;
        else if( hr_online_cnt2 == ONLINE_SHAKE_DLY )
            hr_online_shake <= 1'b0;
        else
            ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hr_online_shake_d1 <= 1'b0;
        hr_online_shake_d2 <= 1'b0;
    end
    else begin
        hr_online_shake_d1 <= hr_online_shake;
        hr_online_shake_d2 <= hr_online_shake_d1;
    end
end

//----------------------------------------------------------------------------------
// ms flag out
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        self_ms_out   <=   1'b0 ;
    end
    else begin
        if( ms_mode == 1'b1  ) 
            self_ms_out  <=   1'b1 ;
        else 
            self_ms_out  <=   1'b0 ;
    end
end
`endif

//----------------------------------------------------------------------------------
// master/slave judge of hr -- master : slow , slave : fast  
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hr_ms_in_d1  <=   1'b0 ;
        hr_ms_in_d2  <=   1'b0 ;
        hr_ms_in_d3  <=   1'b0 ;
        hr_ms_in_d4  <=   1'b0 ;
    end
    else begin
        hr_ms_in_d1  <=   hr_ms_in ;
        hr_ms_in_d2  <=   hr_ms_in_d1 ;
        hr_ms_in_d3  <=   hr_ms_in_d2 ;
        hr_ms_in_d4  <=   hr_ms_in_d3 ;
    end
end

assign  hr_ms_in_ring   =   ( hr_ms_in_d3 == 1'b1 && hr_ms_in_d4 == 1'b0 ) ? 1'b1 : 1'b0 ;
assign  hr_ms_in_fall   =   ( hr_ms_in_d3 == 1'b0 && hr_ms_in_d4 == 1'b1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hr_ms_in_cnt  <=   16'h00 ;
    end
    else begin
        if( hr_ms_in_ring == 1'b1 || hr_ms_in_fall == 1'b1 ) begin
            hr_ms_in_cnt  <=   16'h00 ;
        end
        else begin
            hr_ms_in_cnt  <=   hr_ms_in_cnt + 1'b1 ;
        end
    end
end

// master/slave state : 01 : slave 10 : master 11 : heartbeat break 
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hr_ms_state   <=   2'b00 ;
    end
    else begin
        if ( & hr_ms_in_cnt == 1'b1 ) begin
            hr_ms_state  <=   2'b11 ;
        end
        else if( hr_ms_in_ring == 1'b1 || hr_ms_in_fall == 1'b1 ) begin
            if ( hr_ms_in_cnt[MASTER_FREQ] == 1'b1 || hr_ms_in_cnt[MASTER_FREQ - 1] == 1'b1 ) begin
                hr_ms_state  <=   2'b10 ;
            end
            else if( hr_ms_in_cnt[SLAVE_FREQ] == 1'b1 || hr_ms_in_cnt[SLAVE_FREQ - 1] == 1'b1 ) begin
                hr_ms_state  <=   2'b01 ;
            end
            else
                hr_ms_state  <=   2'b11;
        end
    end
end

//----------------------------------------------------------------------------------
// err process
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        self_cfg_err_d1  <=   1'b0 ;
        self_cfg_err_d2  <=   1'b0 ;
    end
    else begin
        self_cfg_err_d1  <=   self_cfg_err ;
        self_cfg_err_d2  <=   self_cfg_err_d1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        slink_err_d1  <=   16'h00 ;
        slink_err_d2  <=   16'h00 ;
    end
    else begin
        slink_err_d1  <=   slink_err ;
        slink_err_d2  <=   slink_err_d1 & enable_slot;
    end
end

assign  self_err = ( arm_ok_d2 == 1'b0 || self_cfg_err_d2 == 1'b1 || ( | ( slink_err_d2 ) == 1'b1 ) ) ? 1'b1 : 1'b0 ;    

//----------------------------------------------------------------------------------
// heartbeat output control -- normal : slow  fault : fast
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        ht_out_cnt  <=   16'h00 ;
    end
    else begin
        if ( ht_out_cnt[NORMAL_FREQ] == 1'b1 ) begin
            ht_out_cnt  <=   16'h00 ;
        end
        else begin
            ht_out_cnt  <=   ht_out_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        self_ht_out <=  1'b0 ;
    end
    else begin
        if( ht_out_cnt[NORMAL_FREQ] == 1'b1 ) begin
            self_ht_out <= ~ self_ht_out ;
        end
    end
end

//----------------------------------------------------------------------------------
// heartbeat input judge -- normal : slow , fault : fast  
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        hr_ht_in_d1  <=   1'b0 ;
        hr_ht_in_d2  <=   1'b0 ;
        hr_ht_in_d3  <=   1'b0 ;
        hr_ht_in_d4  <=   1'b0 ;
    end
    else begin
        hr_ht_in_d1  <=   hr_ht_in ;
        hr_ht_in_d2  <=   hr_ht_in_d1 ;
        hr_ht_in_d3  <=   hr_ht_in_d2 ;
        hr_ht_in_d4  <=   hr_ht_in_d3 ;
    end
end

assign  hr_ht_in_ring   =   ( hr_ht_in_d3 == 1'b1 && hr_ht_in_d4 == 1'b0 ) ? 1'b1 : 1'b0 ;
assign  hr_ht_in_fall   =   ( hr_ht_in_d3 == 1'b0 && hr_ht_in_d4 == 1'b1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        hr_ht_in_cnt  <=   16'h00 ;
    end
    else begin
        if( hr_ht_in_ring == 1'b1 || hr_ht_in_fall == 1'b1 ) begin
            hr_ht_in_cnt  <=   16'h00 ;
        end
        else begin
            hr_ht_in_cnt  <=   hr_ht_in_cnt + 1'b1 ;
        end
    end
end

// heartbeat state : 01 : normal 10 : fault 11 : heartbeat break 
//always @ ( posedge clk_emif or negedge rst_emif ) begin
//    if( rst_emif == 1'b0 ) begin
//        hr_ht_state   <=   2'b00 ;
//    end
//    else begin
//        if ( & hr_ht_in_cnt == 1'b1 ) begin
//            hr_ht_state  <=   2'b11 ;
//        end
//        else if( hr_ht_in_ring == 1'b1 || hr_ht_in_fall == 1'b1 ) begin
//                if( hr_ht_in_cnt[NORMAL_FREQ] == 1'b1 || hr_ht_in_cnt[NORMAL_FREQ - 1] == 1'b1 ) begin
//                    hr_ht_state  <=     2'b01 ;
//                end
//                else
//                ;
//            end
//    end
//end

always @( posedge clk_emif or negedge rst_emif ) begin 
    if( ~rst_emif ) begin
            high_hold_time <= 8'd0;
    end else begin
        if( hr_ht_in ) begin
            if( high_hold_time < HEARTBEAT_FREQ )
                high_hold_time <= high_hold_time + 1;
            else ;
        end // if( hr_ht_in )
        else
            high_hold_time <= 8'd0;
    end
end

always @( posedge clk_emif or negedge rst_emif ) begin 
    if( ~rst_emif ) begin
         low_hold_time <= 8'd0 ;
    end else begin
        if( ~ hr_ht_in ) begin
            if( low_hold_time < HEARTBEAT_FREQ )
                low_hold_time <= low_hold_time + 1;
            else ;
        end // if( ~ hr_ht_in )
        else
            low_hold_time <= 8'd0;
    end
end

always @(posedge clk_emif or negedge rst_emif) begin 
    if( ~rst_emif ) begin
        heart_beat_err <= 1'b0 ;
    end else begin
        if( ( low_hold_time > HEARTBEAT_FREQ - 1 )||( high_hold_time > HEARTBEAT_FREQ - 1 ) )
            heart_beat_err <= 1'b1;
        else
            heart_beat_err <= 1'b0;
    end
end

//----------------------------------------------------------------------------------
// for debug
//----------------------------------------------------------------------------------
reg single_mode_flag;
reg slink_mode_flag;
reg arm_mode_flag;
// 
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        single_mode_flag <= 1'b0;
    end
    else begin
        if( current_state == SINGLE_MODE )
            single_mode_flag <= 1'b1;
        else
            ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        arm_mode_flag <= 1'b0;
    end
    else begin
        if( current_state == ARM_DIAG )
            arm_mode_flag <= 1'b1;
        else
            ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        slink_mode_flag <= 1'b0;
    end
    else begin
        if( current_state == SLINK_DIAG )
            slink_mode_flag <= 1'b1;
        else
            ;
    end
end
//----------------------------------------------------------------------------------
// for simulate
//----------------------------------------------------------------------------------
`ifdef SIM
reg         [15*8:0]        state_str;
always @ (*)begin
    case(current_state)
        IDLE                :   state_str   =  {"IDLE"}           ;
        SINGLE_MODE         :   state_str   =   {"SINGLE_MODE"}     ;    
        DOUBLE_MODE         :   state_str   =   {"DOUBLE_MODE"}     ;
        FAULT_DIAG          :   state_str   =   {"FAULT_DIAG"}      ;
        ARM_DIAG            :   state_str   =   {"ARM_DIAG"}        ;
        SLINK_DIAG          :   state_str   =   {"SLINK_DIAG"}      ;
    endcase
end
`endif
endmodule


