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

module CFGINFOPUB 
    (
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 
        clk_12_5m               ,   
        rst_12_5m_n             ,

        self_id_err             ,   
        slink_cfg_dval          ,   
        slink_cfg_data          ,   

        cfg_md_id               ,   
        cfg_code_rev            ,   
        cfg_run_tm              ,   
        cfg_com_mode            ,   
           
        cfg_req_fail            ,   
        cfg_done                ,   
        cfg_done_trig           ,   
        cfg_slink_chen          ,   
        cfg_chn_enable          ,   
        
        // clk 12.5Mhz
        cfg_enable_slot          
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
localparam   CFG_REQ_CNT =   3'd5       ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input interface signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    self_id_err                         ;   
input   wire                    slink_cfg_dval                      ;   
input   wire    [9:0]           slink_cfg_data                      ;   
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m_n                         ; 
// output interface signal
output  reg     [31:0]          cfg_md_id                           ;   
output  reg     [31:0]          cfg_code_rev                        ;   
output  reg     [15:0]          cfg_run_tm                          ;   
output  reg     [7:0]           cfg_com_mode                        ;   
output  reg                     cfg_done                            ;   
output  reg                     cfg_done_trig                       ;   
output  reg     [11:0]          cfg_chn_enable                      ;   
output  reg     [1:0]           cfg_enable_slot                     ;   
output  reg     [1:0]           cfg_slink_chen                      ;   
output  reg                     cfg_req_fail                        ;
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg     [8:0]                   rx_addr                             ;   
reg     [7:0]                   slink_en                            ;   
reg                             slink_en0_d0                        ;   
reg                             slink_en0_d1                        ;   
reg                             slink_en1_d0                        ;   
reg                             slink_en1_d1                        ;
reg     [31:0]                  md_id                               ;   
reg     [31:0]                  md_id_d1                            ;  
reg                             latch_data_en                       ;   
reg                             self_id_errd                        ;   
reg                             self_id_errd1                       ;   
reg     [31:0]                  md_id_d                             ;   
reg     [2:0]                   cfg_req_cnt                         ;   


/**********************************************************************************\
******************************** debug code ****************************************/



/**********************************************************************************\
********************************* main code ****************************************/

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rx_addr <= 9'd0 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 && slink_cfg_data[8] == 1'b1 ) begin
            rx_addr <= 9'd0 ;
        end
        else if ( slink_cfg_dval == 1'b1 ) begin
            rx_addr <= rx_addr + 1'b1 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        md_id   <= 32'h00000000 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 ) begin
            if ( rx_addr == 9'd0 ) begin
                md_id[15:8]   <= slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 9'd1 ) begin
                md_id[7:0]   <= slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 9'd2 ) begin
                md_id[31:24]   <= slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 9'd3 ) begin
                md_id[23:16]   <= slink_cfg_data[7:0] ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        latch_data_en   <=   1'b0 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 && rx_addr[4:0] == 5'd16 ) begin
            latch_data_en   <=   1'b1 ;
        end
        else begin
            latch_data_en   <=   1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// process the signal of cfg_md_id
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        md_id_d   <=   32'd0 ;
    end
    else begin
        if ( latch_data_en == 1'b1 ) begin
            md_id_d   <=   md_id ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        md_id_d1  <= 32'd0 ;
    end
    else begin
        md_id_d1  <= md_id_d ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        cfg_md_id  <= 32'd0 ;
    end
    else begin
        cfg_md_id  <= md_id_d1 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_code_rev   <= 32'h00000000 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 ) begin
            if ( rx_addr == 9'd4 ) begin
                cfg_code_rev[15:8]   <= slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 9'd5 ) begin
                cfg_code_rev[7:0]   <= slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 9'd6 ) begin
                cfg_code_rev[31:24]   <= slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 9'd7 ) begin
                cfg_code_rev[23:16]   <= slink_cfg_data[7:0] ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_chn_enable   <= 12'h000 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 ) begin
            if ( rx_addr == 9'd8 ) begin
                cfg_chn_enable[11:8]   <= slink_cfg_data[3:0] ;
            end
            else if ( rx_addr == 9'd9 ) begin
                cfg_chn_enable[7:0]   <= slink_cfg_data[7:0] ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_run_tm   <= 16'h0000 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 ) begin
            if ( rx_addr == 9'd12 ) begin
                cfg_run_tm[15:8]   <= slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 9'd13 ) begin
                cfg_run_tm[7:0]   <= slink_cfg_data[7:0] ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_com_mode   <= 8'h00 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 && rx_addr == 9'd15 ) begin
            cfg_com_mode   <= slink_cfg_data[7:0] ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        slink_en   <= 8'h00 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 && rx_addr == 9'd14 ) begin
            slink_en   <= slink_cfg_data ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_slink_chen    <=   2'b00 ;
    end
    else begin
        cfg_slink_chen    <=   slink_en ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        slink_en0_d0    <=   1'b0 ;
    end
    else begin
        slink_en0_d0    <=  slink_en[0] ; 
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        slink_en0_d1    <=   1'b0 ;
    end
    else begin
        slink_en0_d1    <=  slink_en0_d0 ; 
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        cfg_enable_slot[0]  <= 1'b0 ;  
    end
    else begin
        cfg_enable_slot[0]  <= slink_en0_d1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        slink_en1_d0    <=   1'b0 ;
    end
    else begin
        slink_en1_d0    <=  slink_en[1] ; 
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        slink_en1_d1    <=   1'b0 ;
    end
    else begin
        slink_en1_d1    <=  slink_en1_d0 ; 
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        cfg_enable_slot[1]  <= 1'b0 ;
    end
    else begin
        cfg_enable_slot[1]  <= slink_en1_d1 ;
    end
end

//----------------------------------------------------------------------------------
// processing asynchronous signal of self_id_err
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        self_id_errd    <=   1'b0 ;
    end
    else begin
        self_id_errd    <=   self_id_err ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        self_id_errd1    <=   1'b0 ;
    end
    else begin
        self_id_errd1    <=   self_id_errd ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_done    <=   1'b0 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 && slink_cfg_data[8] == 1'b1 && cfg_md_id != 32'd0 && cfg_com_mode != 8'd0 ) begin
            cfg_done <= 1'b1 ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_req_cnt <=   3'd0 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 && slink_cfg_data[8] == 1'b1 && md_id_d == 32'd0 && cfg_com_mode == 8'd0 ) begin
            if ( cfg_req_cnt == CFG_REQ_CNT ) begin
                cfg_req_cnt <=  CFG_REQ_CNT ;
            end
            else begin
                cfg_req_cnt <= cfg_req_cnt + 1'b1 ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_req_fail    <=   1'b0 ;
    end
    else begin
        if ( cfg_req_cnt == CFG_REQ_CNT ) begin
            cfg_req_fail    <=   1'b1 ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_done_trig    <=   1'b0 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 && slink_cfg_data[8] == 1'b1 && self_id_errd1 == 1'b0 && cfg_com_mode != 8'd0 ) begin
            cfg_done_trig <= 1'b1 ;
        end
        else begin
            cfg_done_trig <= 1'b0 ;
        end
    end
end

endmodule
