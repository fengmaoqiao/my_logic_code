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

module CFGPARM 
    (
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 

        cfg_param_dval          ,   
        slink_cfg_data          ,   

        cfg_param0              ,   
        cfg_param1              ,   
        cfg_param2              ,   
        cfg_param3              ,   
        cfg_param4              ,   
        cfg_param5              
    );

/**********************************************************************************\
***************************** declare parameter ************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input interface signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
  
input   wire                    cfg_param_dval                      ;   
input   wire    [7:0]           slink_cfg_data                      ;   

// output interface signal
output  reg     [31:0]          cfg_param0                          ;   
output  reg     [31:0]          cfg_param1                          ;   
output  reg     [31:0]          cfg_param2                          ;   
output  reg     [31:0]          cfg_param3                          ;   
output  reg     [31:0]          cfg_param4                          ;   
output  reg     [31:0]          cfg_param5                          ;   

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg     [5:0]                   rx_addr                             ;   
 
/**********************************************************************************\
******************************** debug code ****************************************/

/**********************************************************************************\
********************************* main code ****************************************/

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rx_addr   <=   6'd0 ;
    end
    else begin
        if ( cfg_param_dval == 1'b0 ) begin
            rx_addr   <=   6'd0 ;
        end
        else if ( cfg_param_dval == 1'b1 ) begin
            rx_addr   <=   rx_addr + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// configure the parameter of cfg_quan_ul0
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_param0   <=   32'h00000000 ;
    end
    else begin
        if ( cfg_param_dval == 1'b1 ) begin
            if ( rx_addr == 6'd0 ) begin
                cfg_param0[15:8]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd1 ) begin
                cfg_param0[7:0]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd2 ) begin
                cfg_param0[31:24]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd3 ) begin
                cfg_param0[23:16]   <=   slink_cfg_data[7:0] ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_param1   <=   32'h00000000 ;
    end
    else begin
        if ( cfg_param_dval == 1'b1 ) begin
            if ( rx_addr == 6'd4 ) begin
                cfg_param1[15:8]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd5 ) begin
                cfg_param1[7:0]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd6 ) begin
                cfg_param1[31:24]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd7 ) begin
                cfg_param1[23:16]   <=   slink_cfg_data[7:0] ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_param2   <=   32'h00000000 ;
    end
    else begin
        if ( cfg_param_dval == 1'b1 ) begin
            if ( rx_addr == 6'd8 ) begin
                cfg_param2[15:8]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd9 ) begin
                cfg_param2[7:0]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd10 ) begin
                cfg_param2[31:24]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd11 ) begin
                cfg_param2[23:16]   <=   slink_cfg_data[7:0] ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_param3   <=   32'h00000000 ;
    end
    else begin
        if ( cfg_param_dval == 1'b1 ) begin
            if ( rx_addr == 6'd12 ) begin
                cfg_param3[15:8]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd13 ) begin
                cfg_param3[7:0]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd14 ) begin
                cfg_param3[31:24]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd15 ) begin
                cfg_param3[23:16]   <=   slink_cfg_data[7:0] ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_param4   <=   32'h00000000 ;
    end
    else begin
        if ( cfg_param_dval == 1'b1 ) begin
            if ( rx_addr == 6'd16 ) begin
                cfg_param4[15:8]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd17 ) begin
                cfg_param4[7:0]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd18 ) begin
                cfg_param4[31:24]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd19 ) begin
                cfg_param4[23:16]   <=   slink_cfg_data[7:0] ;
            end
            else ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_param5   <=   32'h00000000 ;
    end
    else begin
        if ( cfg_param_dval == 1'b1 ) begin
            if ( rx_addr == 6'd20 ) begin
                cfg_param5[15:8]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd21 ) begin
                cfg_param5[7:0]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd22 ) begin
                cfg_param5[31:24]   <=   slink_cfg_data[7:0] ;
            end
            else if ( rx_addr == 6'd23 ) begin
                cfg_param5[23:16]   <=   slink_cfg_data[7:0] ;
            end
            else ;
        end
        else ;
    end
end

endmodule
