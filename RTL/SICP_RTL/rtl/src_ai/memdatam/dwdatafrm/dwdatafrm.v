// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-11-02
// DEPARTMENT       :   R&D
// AUTHOR           :   YongjunZhang
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-11-02  YongjunZhang        Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active low
// Clock Domains    :   EMIF_CLK
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`include "DEFINES.v"

module DWDATAFRM 
    (
        rst_sys_n               ,   
        clk_sys                 ,   

        slink_dt_dval           ,   
        slink_dt_data           ,   

        cfg_run_tm              ,   
        cfg_done                ,   
        dw_ctr_cmd              ,   
        dw_com_stus             ,   
        com_fault 
    );

/**********************************************************************************\
***************************** declare parameter ************************************/
localparam  TM_MS_CNT           = 17'd124999 ;
localparam  STU_FAULT_UL        = 6'd63 ;
localparam  PERIOD_FAULT_UL     = 6'd63 ;
localparam  PERIOD_TMOUT_CNT    = 16'd5 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input interface signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    slink_dt_dval                       ;   
input   wire    [9:0]           slink_dt_data                       ;   
input   wire                    cfg_done                            ;   
input   wire    [15:0]          cfg_run_tm                          ;
// output interface signal
output  reg     [31:0]          dw_ctr_cmd                          ;   
output  wire    [1:0]           com_fault                           ;   
output  reg     [31:0]          dw_com_stus                         ; // the control command 2'd0 : ; 2'd1 : enable; 2'd3: ;
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg     [7:0]                   rx_addr                             ;   
reg                             dw_done                             ;   
reg                             dw_trig                             ;  
reg     [15:0]                  wd_timer_d2                         ;   
reg                             clk_1ms_flag                        ;
reg                             period_fault_trig                   ;   
reg                             com_stus_fault                      ;   
reg     [15:0]                  run_period                          ;   
reg     [15:0]                  delay_cnt                           ;   
reg     [16:0]                  tm_1ms_cnt                          ; 
reg                             stu_fault_trig                      ;   
reg     [5:0]                   com_fault_cnt                       ;   
reg                             com_period_fault                    ;   
reg     [5:0]                   com_period_cnt                      ; 
reg                             stu_fault_en                        ;
reg                             period_fault_en                     ;   
/**********************************************************************************\
******************************** debug code ****************************************/

/**********************************************************************************\
********************************* main code ****************************************/

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rx_addr <=  8'd0 ;
    end
    else begin
        if ( slink_dt_dval == 1'b1 && slink_dt_data[8] == 1'b1 ) begin
            rx_addr <=  8'd0 ;
        end
        else if ( slink_dt_dval == 1'b1 ) begin
            rx_addr <=  rx_addr + 1'b1 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dw_ctr_cmd   <=  32'h00000000 ;
    end
    else begin
        if ( slink_dt_dval == 1'b1 ) begin
            if ( rx_addr == 8'd0 ) begin
                dw_ctr_cmd[15:8]   <=  slink_dt_data[7:0] ;
            end
            else if ( rx_addr == 8'd1 ) begin
                dw_ctr_cmd[7:0]   <=  slink_dt_data[7:0] ;
            end
            else if ( rx_addr == 8'd2 ) begin
                dw_ctr_cmd[31:24]   <=  slink_dt_data[7:0] ;
            end
            else if ( rx_addr == 8'd3 ) begin
                dw_ctr_cmd[23:16]   <=  slink_dt_data[7:0] ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dw_com_stus   <=  32'h00000000 ;
    end
    else begin
        if ( slink_dt_dval == 1'b1 ) begin
            if ( rx_addr == 8'd116 ) begin
                dw_com_stus[15:8]   <=  slink_dt_data[7:0] ;
            end
            else if ( rx_addr == 8'd117 ) begin
                dw_com_stus[7:0]   <=  slink_dt_data[7:0] ;
            end
            else if ( rx_addr == 8'd118 ) begin
                dw_com_stus[31:24]   <=  slink_dt_data[7:0] ;
            end
            else if ( rx_addr == 8'd119 ) begin
                dw_com_stus[23:16]   <=  slink_dt_data[7:0] ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dw_done <=   1'b0 ;
    end
    else begin
        if ( slink_dt_dval == 1'b1 && rx_addr == 8'd119 ) begin
            dw_done <=   1'b1 ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dw_trig <=   1'b0 ;
    end
    else begin
        if ( slink_dt_dval == 1'b1 && rx_addr == 8'd119 ) begin
            dw_trig <=   1'b1 ;
        end
        else begin
            dw_trig <=   1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// diagnose the down data communition status
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        stu_fault_trig  <=   1'b0 ;
    end
    else begin
        if ( dw_trig == 1'b1 && dw_com_stus != 32'h00000000 ) begin
            stu_fault_trig  <=   1'b1 ;
        end
        else begin
            stu_fault_trig  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        stu_fault_en  <=   1'b0 ;
    end
    else begin
        if ( dw_trig == 1'b1 ) begin
           if ( dw_com_stus != 32'h00000000 ) begin
                stu_fault_en  <=   1'b1 ;
            end
            else begin
                stu_fault_en    <=   1'b0 ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        com_fault_cnt   <=   6'd0 ;
    end
    else begin
        if ( stu_fault_trig == 1'b1 ) begin
            if ( com_fault_cnt == STU_FAULT_UL ) begin
                com_fault_cnt   <=   STU_FAULT_UL ;
            end
            else begin
                com_fault_cnt   <=   com_fault_cnt + 1'b1 ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        com_stus_fault   <=   1'b0 ; 
    end
    else begin
        if ( com_fault_cnt == STU_FAULT_UL ) begin
            com_stus_fault  <=   1'b1 ;
        end
        else begin
            com_stus_fault  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        tm_1ms_cnt   <=   17'd0 ;
    end
    else begin
        if ( cfg_done == 1'b1 ) begin
            if ( tm_1ms_cnt == TM_MS_CNT || dw_trig == 1'b1 ) begin
                tm_1ms_cnt   <=   17'd0 ;
            end
            else begin
                tm_1ms_cnt   <=   tm_1ms_cnt + 1'b1 ;
            end
        end
        else begin
            tm_1ms_cnt   <=   17'd0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        clk_1ms_flag    <=   1'b0 ;
    end
    else begin
        if ( tm_1ms_cnt == TM_MS_CNT ) begin
            clk_1ms_flag    <=   1'b1 ;
        end
        else begin
            clk_1ms_flag    <=   1'b0 ;
        end
    end
end
   
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_timer_d2  <=   16'd0 ;
    end
    else begin
        wd_timer_d2	<= (cfg_run_tm<<1) + PERIOD_TMOUT_CNT ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        delay_cnt   <=   16'd0 ;
    end
    else begin
        if ( dw_trig == 1'b1 ) begin
            delay_cnt   <=   16'd0 ;
        end
        else if ( clk_1ms_flag == 1'b1 ) begin
            if ( delay_cnt == wd_timer_d2 ) begin
                delay_cnt   <=   wd_timer_d2 ;
            end
            else begin
                delay_cnt   <=   delay_cnt + 1'b1 ;
            end
        end
        else ;
    end
end

always @( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin	
        period_fault_en   <=   1'b0 ;
    end
    else begin
        if( cfg_run_tm == 16'd0 ) begin
            period_fault_en   <=   1'b0 ;
        end
        else if ( dw_trig == 1'b1 ) begin
            if( delay_cnt == wd_timer_d2 ) begin
                period_fault_en   <=   1'b1 ;
            end
            else begin
                period_fault_en   <=   1'b0 ;
            end
        end
        else if ( delay_cnt == wd_timer_d2 ) begin
            period_fault_en   <=   1'b1 ;
        end
    end
end

assign com_fault = { stu_fault_en, period_fault_en } ;

endmodule
