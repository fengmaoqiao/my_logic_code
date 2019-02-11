// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SELF_CMM
// CREATE DATE      :   2017-09-07
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-07  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   The configuration Memory Management of MPU board self
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

module  COM_SELF_CMM
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   

    // write port
    wr_self_cfg_dval            ,   
    wr_self_cfg_data            ,   

    // read port
    cfg_en                      ,   
    cfg_finish_flag             ,
    card_id                     ,   
    code_version                ,   
    enable_slot                 ,
    run_cycle                   ,   
    port1_dst_box               ,   
    port2_dst_box               ,   
    port3_dst_box               ,   
    port4_dst_box                  
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   

input   wire                    wr_self_cfg_dval                    ;   
input   wire    [17:0]          wr_self_cfg_data                    ;   

// declare output signal
output  reg                     cfg_en                              ;   
output  reg                     cfg_finish_flag                     ;
output  reg     [31:0]          card_id                             ;   
output  reg     [15:0]          code_version                        ;   
output  reg     [15:0]          enable_slot                         ;  
output  reg     [15:0]          run_cycle                           ;   
output  wire    [2:0]           port1_dst_box                       ;   
output  wire    [2:0]           port2_dst_box                       ;   
output  wire    [2:0]           port3_dst_box                       ;   
output  wire    [2:0]           port4_dst_box                       ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg         [9:0]               cfg_dval_cnt                        ;  
reg         [31:0]              port1_dst_id                        ;   
reg         [31:0]              port2_dst_id                        ;   
reg         [31:0]              port3_dst_id                        ;   
reg         [31:0]              port4_dst_id                        ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// write control 
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        cfg_dval_cnt   <=   10'h00 ;
    end
    else begin
        if ( wr_self_cfg_dval == 1'b1 ) begin
            cfg_dval_cnt   <=   cfg_dval_cnt + 1'b1 ;
        end
        else begin
            cfg_dval_cnt   <=   10'h00 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        card_id   <=   32'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd0 ) begin
            card_id[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd1 ) begin
            card_id[31:16]    <=   wr_self_cfg_data[15:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        cfg_en   <=   1'b0 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd4 ) begin
            cfg_en    <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        cfg_finish_flag   <=   1'b0 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd4 ) begin
            cfg_finish_flag    <=   1'b1 ;
        end
    end
    else begin
        cfg_finish_flag   <=   1'b0 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        code_version   <=   16'h00 ;
    end
    else begin
        if( wr_self_cfg_dval == 1'b1 && cfg_dval_cnt == 10'd3 ) begin
            code_version    <=   wr_self_cfg_data[15:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        enable_slot   <=   16'h00 ;
    end
    else begin
        if( wr_self_cfg_dval == 1'b1 && cfg_dval_cnt == 10'd4 ) begin
            enable_slot    <=   wr_self_cfg_data[15:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        run_cycle   <=   16'h00 ;
    end
    else begin
        if( wr_self_cfg_dval == 1'b1 && cfg_dval_cnt == 10'd6 ) begin
            run_cycle    <=   wr_self_cfg_data[15:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        port1_dst_id   <=   32'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd24 ) begin
            port1_dst_id[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd25 ) begin
            port1_dst_id[31:16]    <=   wr_self_cfg_data[15:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        port2_dst_id   <=   32'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd28 ) begin
            port2_dst_id[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd29 ) begin
            port2_dst_id[31:16]    <=   wr_self_cfg_data[15:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        port3_dst_id   <=   32'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd32 ) begin
            port3_dst_id[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd33 ) begin
            port3_dst_id[31:16]    <=   wr_self_cfg_data[15:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        port4_dst_id   <=   32'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd36 ) begin
            port4_dst_id[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd37 ) begin
            port4_dst_id[31:16]    <=   wr_self_cfg_data[15:0] ;
        end
    end
end

assign  port1_dst_box   =   port1_dst_id[7:5] ;   
assign  port2_dst_box   =   port2_dst_id[7:5] ;   
assign  port3_dst_box   =   port3_dst_id[7:5] ;   
assign  port4_dst_box   =   port4_dst_id[7:5] ;  

endmodule

