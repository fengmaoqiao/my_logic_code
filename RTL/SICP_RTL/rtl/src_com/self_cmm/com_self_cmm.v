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
    rxsource_addr_cfg           , //configuraiton sa for port1~4
    txdestin_addr_cfg           ,
    cfg_en                      ,   
    cfg_finish_flag             ,
    card_id                     ,   
    code_version                ,   
    enable_slot                 ,
    run_cycle                   
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
output  wire    [18*4-1:0]      rxsource_addr_cfg                   ;
output  wire    [18*4-1:0]      txdestin_addr_cfg                   ;
output  reg                     cfg_en                              ;   
output  reg                     cfg_finish_flag                     ;
output  reg     [31:0]          card_id                             ;   
output  reg     [15:0]          code_version                        ;   
output  reg     [15:0]          enable_slot                         ;  
output  reg     [15:0]          run_cycle                           ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg         [9:0]               cfg_dval_cnt                        ;  
reg         [39:0]              destin_addr_port1                   ;   
reg         [39:0]              destin_addr_port2                   ;   
reg         [39:0]              destin_addr_port3                   ;   
reg         [39:0]              destin_addr_port4                   ;   

reg         [39:0]              source_addr_port1                   ;   
reg         [39:0]              source_addr_port2                   ;   
reg         [39:0]              source_addr_port3                   ;   
reg         [39:0]              source_addr_port4                   ;   

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
        destin_addr_port1   <=   40'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd24 ) begin
            destin_addr_port1[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd25 ) begin
            destin_addr_port1[31:16]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd26 ) begin
            destin_addr_port1[39:32]    <=   wr_self_cfg_data[7:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        destin_addr_port2   <=   40'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd28 ) begin
            destin_addr_port2[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd29 ) begin
            destin_addr_port2[31:16]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd30 ) begin
            destin_addr_port2[39:32]    <=   wr_self_cfg_data[7:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        destin_addr_port3   <=   40'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd32 ) begin
            destin_addr_port3[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd33 ) begin
            destin_addr_port3[31:16]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd34 ) begin
            destin_addr_port3[39:32]    <=   wr_self_cfg_data[7:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        destin_addr_port4   <=   40'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd36 ) begin
            destin_addr_port4[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd37 ) begin
            destin_addr_port4[31:16]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd38 ) begin
            destin_addr_port4[39:32]    <=   wr_self_cfg_data[7:0] ;
        end
    end
end

//port1 sa of configuration
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        source_addr_port1   <=   40'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd8 ) begin
            source_addr_port1[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd9 ) begin
            source_addr_port1[31:16]   <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd10 ) begin
            source_addr_port1[39:32]   <=   wr_self_cfg_data[7:0] ;
        end
    end
end

//port2 sa of configuration
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        source_addr_port2   <=   40'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd12 ) begin
            source_addr_port2[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd13 ) begin
            source_addr_port2[31:16]   <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd14 ) begin
            source_addr_port2[39:32]   <=   wr_self_cfg_data[7:0] ;
        end
    end
end

//port3 sa of configuration
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        source_addr_port3   <=   40'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd16 ) begin
            source_addr_port3[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd17 ) begin
            source_addr_port3[31:16]   <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd18 ) begin
            source_addr_port3[39:32]   <=   wr_self_cfg_data[7:0] ;
        end
    end
end

//port4 sa of configuration
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        source_addr_port4   <=   40'h00 ;
    end
    else if( wr_self_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == 10'd20 ) begin
            source_addr_port4[15:0]    <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd21 ) begin
            source_addr_port4[31:16]   <=   wr_self_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == 10'd22 ) begin
            source_addr_port4[39:32]   <=   wr_self_cfg_data[7:0] ;
        end
    end
end

assign rxsource_addr_cfg = {
                            source_addr_port4[15:0],source_addr_port4[33:32],
                            source_addr_port3[15:0],source_addr_port3[33:32],
                            source_addr_port2[15:0],source_addr_port2[33:32],
                            source_addr_port1[15:0],source_addr_port1[33:32] 
                            };

assign txdestin_addr_cfg = {
                            destin_addr_port4[15:0],destin_addr_port4[33:32],
                            destin_addr_port3[15:0],destin_addr_port3[33:32],
                            destin_addr_port2[15:0],destin_addr_port2[33:32],
                            destin_addr_port1[15:0],destin_addr_port1[33:32] 
                            };
endmodule

