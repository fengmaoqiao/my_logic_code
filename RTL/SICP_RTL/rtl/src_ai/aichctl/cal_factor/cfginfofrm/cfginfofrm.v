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

module CFGINFOFRM 
    (
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 

        cfg_done                ,   
        slink_cfg_dval          ,   
        slink_cfg_data          ,   
        cfg_chaddr_sel          ,   

        cfg_engn_ul0            ,   
        cfg_engn_ul1            ,   
        cfg_engn_ul2            ,   
        cfg_engn_ul3            ,   
        cfg_engn_ul4            ,   
        cfg_engn_ul5            ,   
                        
        cfg_engn_dl0            ,   
        cfg_engn_dl1            ,   
        cfg_engn_dl2            ,   
        cfg_engn_dl3            ,   
        cfg_engn_dl4            ,   
        cfg_engn_dl5            ,   
                        
        cfg_elec_ul0            ,   
        cfg_elec_ul1            ,   
        cfg_elec_ul2            ,   
        cfg_elec_ul3            ,   
        cfg_elec_ul4            ,   
        cfg_elec_ul5            ,   
                        
        cfg_elec_dl0            ,   
        cfg_elec_dl1            ,   
        cfg_elec_dl2            ,   
        cfg_elec_dl3            ,   
        cfg_elec_dl4            ,   
        cfg_elec_dl5            ,   
                        
        cfg_engn_chkul0         ,   
        cfg_engn_chkul1         ,   
        cfg_engn_chkul2         ,   
        cfg_engn_chkul3         ,   
        cfg_engn_chkul4         ,   
        cfg_engn_chkul5         ,   
                        
        cfg_engn_chkdl0         ,   
        cfg_engn_chkdl1         ,   
        cfg_engn_chkdl2         ,   
        cfg_engn_chkdl3         ,   
        cfg_engn_chkdl4         ,   
        cfg_engn_chkdl5         
       
    );

/**********************************************************************************\
***************************** declare parameter ************************************

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input interface signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    slink_cfg_dval                      ;   
input   wire    [9:0]           slink_cfg_data                      ;   
input   wire                    cfg_chaddr_sel                      ;   
input   wire                    cfg_done                            ;   
// output interface signal
output  wire     [31:0]         cfg_engn_ul0                        ;   
output  wire     [31:0]         cfg_engn_ul1                        ;   
output  wire     [31:0]         cfg_engn_ul2                        ;   
output  wire     [31:0]         cfg_engn_ul3                        ;   
output  wire     [31:0]         cfg_engn_ul4                        ;   
output  wire     [31:0]         cfg_engn_ul5                        ;   

output  wire     [31:0]         cfg_engn_dl0                        ;   
output  wire     [31:0]         cfg_engn_dl1                        ;   
output  wire     [31:0]         cfg_engn_dl2                        ;   
output  wire     [31:0]         cfg_engn_dl3                        ;   
output  wire     [31:0]         cfg_engn_dl4                        ;   
output  wire     [31:0]         cfg_engn_dl5                        ;   

output  wire     [31:0]         cfg_elec_ul0                        ;   
output  wire     [31:0]         cfg_elec_ul1                        ;   
output  wire     [31:0]         cfg_elec_ul2                        ;   
output  wire     [31:0]         cfg_elec_ul3                        ;   
output  wire     [31:0]         cfg_elec_ul4                        ;   
output  wire     [31:0]         cfg_elec_ul5                        ;   

output  wire     [31:0]         cfg_elec_dl0                        ;   
output  wire     [31:0]         cfg_elec_dl1                        ;   
output  wire     [31:0]         cfg_elec_dl2                        ;   
output  wire     [31:0]         cfg_elec_dl3                        ;   
output  wire     [31:0]         cfg_elec_dl4                        ;   
output  wire     [31:0]         cfg_elec_dl5                        ;   
 
output  wire     [31:0]         cfg_engn_chkul0                     ;   
output  wire     [31:0]         cfg_engn_chkul1                     ;   
output  wire     [31:0]         cfg_engn_chkul2                     ;   
output  wire     [31:0]         cfg_engn_chkul3                     ;   
output  wire     [31:0]         cfg_engn_chkul4                     ;   
output  wire     [31:0]         cfg_engn_chkul5                     ;   

output  wire     [31:0]         cfg_engn_chkdl0                     ;   
output  wire     [31:0]         cfg_engn_chkdl1                     ;   
output  wire     [31:0]         cfg_engn_chkdl2                     ;   
output  wire     [31:0]         cfg_engn_chkdl3                     ;   
output  wire     [31:0]         cfg_engn_chkdl4                     ;   
output  wire     [31:0]         cfg_engn_chkdl5                     ;   

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// wire signal
reg     [8:0]                   rx_addr                             ;   
reg                             cfg_engnul_dval                     ;   
reg                             cfg_engndl_dval                     ;   
reg                             cfg_elecul_dval                     ;   
reg                             cfg_elecdl_dval                     ;   
reg                             cfg_mntul_dval                     ;   
reg                             cfg_mntdl_dval                     ;   

/**********************************************************************************\
******************************** debug code ****************************************/

/**********************************************************************************\
********************************* main code ****************************************/

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rx_addr <=  9'd0 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 && slink_cfg_data[8] == 1'b1 && cfg_done == 1'b0 ) begin
            rx_addr <=  9'd0 ;
        end
        else if ( slink_cfg_dval == 1'b1 && cfg_done == 1'b0 ) begin
            rx_addr <=  rx_addr + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// configure the upper limit value of engineering quantity
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_engnul_dval <=   1'b0 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 ) begin 
            if ( cfg_chaddr_sel == 1'b0 && rx_addr == 9'd15 || cfg_chaddr_sel == 1'b1 && rx_addr == 9'd39 ) begin
                cfg_engnul_dval <=   1'b1 ;
            end
            else if ( cfg_chaddr_sel == 1'b0 && rx_addr == 9'd39 || cfg_chaddr_sel == 1'b1 && rx_addr == 9'd63 ) begin
                cfg_engnul_dval <=   1'b0 ;
            end
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// configure the lower limit value of engineering quantity
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_engndl_dval <=   1'b0 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 ) begin 
            if ( cfg_chaddr_sel == 1'b0 && rx_addr == 9'd63 || cfg_chaddr_sel == 1'b1 && rx_addr == 9'd87 ) begin
                cfg_engndl_dval <=   1'b1 ;
            end
            else if ( cfg_chaddr_sel == 1'b0 && rx_addr == 9'd87 || cfg_chaddr_sel == 1'b1 && rx_addr == 9'd111 ) begin
                cfg_engndl_dval <=   1'b0 ;
            end
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// configure the uper limit value of electrical quantity
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_elecul_dval <=   1'b0 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 ) begin 
            if ( cfg_chaddr_sel == 1'b0 && rx_addr == 9'd111 || cfg_chaddr_sel == 1'b1 && rx_addr == 9'd135 ) begin
                cfg_elecul_dval <=   1'b1 ;
            end
            else if ( cfg_chaddr_sel == 1'b0 && rx_addr == 9'd135 || cfg_chaddr_sel == 1'b1 && rx_addr == 9'd159 ) begin
                cfg_elecul_dval <=   1'b0 ;
            end
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// configure the lower limit value of electrical quantity
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_elecdl_dval <=   1'b0 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 ) begin 
            if ( cfg_chaddr_sel == 1'b0 && rx_addr == 9'd159 || cfg_chaddr_sel == 1'b1 && rx_addr == 9'd183 ) begin
                cfg_elecdl_dval <=   1'b1 ;
            end
            else if ( cfg_chaddr_sel == 1'b0 && rx_addr == 9'd183 || cfg_chaddr_sel == 1'b1 && rx_addr == 9'd207 ) begin
                cfg_elecdl_dval <=   1'b0 ;
            end
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// configure the upper limit value of monitoring quantity
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_mntul_dval <=   1'b0 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 ) begin 
            if ( cfg_chaddr_sel == 1'b0 && rx_addr == 9'd207 || cfg_chaddr_sel == 1'b1 && rx_addr == 9'd231 ) begin
                cfg_mntul_dval <=   1'b1 ;
            end
            else if ( cfg_chaddr_sel == 1'b0 && rx_addr == 9'd231 || cfg_chaddr_sel == 1'b1 && rx_addr == 9'd255 ) begin
                cfg_mntul_dval <=   1'b0 ;
            end
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// configure the lower limit value of monitoring quantity
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_mntdl_dval <=   1'b0 ;
    end
    else begin
        if ( slink_cfg_dval == 1'b1 ) begin 
            if ( cfg_chaddr_sel == 1'b0 && rx_addr == 9'd255 || cfg_chaddr_sel == 1'b1 && rx_addr == 9'd279 ) begin
                cfg_mntdl_dval <=   1'b1 ;
            end
            else if ( cfg_chaddr_sel == 1'b0 && rx_addr == 9'd279 || cfg_chaddr_sel == 1'b1 && rx_addr == 9'd303 ) begin
                cfg_mntdl_dval <=   1'b0 ;
            end
        end
        else ;
    end
end

    CFGPARM                     U_CFG_ENGNUL
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .cfg_param_dval             ( cfg_engnul_dval           ),
    .slink_cfg_data             ( slink_cfg_data            ),

    .cfg_param0                 ( cfg_engn_ul0              ),
    .cfg_param1                 ( cfg_engn_ul1              ),
    .cfg_param2                 ( cfg_engn_ul2              ),
    .cfg_param3                 ( cfg_engn_ul3              ),
    .cfg_param4                 ( cfg_engn_ul4              ),
    .cfg_param5                 ( cfg_engn_ul5              )
    );

    CFGPARM                     U_CFG_ENGNDL
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .cfg_param_dval             ( cfg_engndl_dval           ),
    .slink_cfg_data             ( slink_cfg_data            ),

    .cfg_param0                 ( cfg_engn_dl0              ),
    .cfg_param1                 ( cfg_engn_dl1              ),
    .cfg_param2                 ( cfg_engn_dl2              ),
    .cfg_param3                 ( cfg_engn_dl3              ),
    .cfg_param4                 ( cfg_engn_dl4              ),
    .cfg_param5                 ( cfg_engn_dl5              )
    );

    CFGPARM                     U_CFG_ELECUL
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .cfg_param_dval             ( cfg_elecul_dval           ),
    .slink_cfg_data             ( slink_cfg_data            ),

    .cfg_param0                 ( cfg_elec_ul0              ),
    .cfg_param1                 ( cfg_elec_ul1              ),
    .cfg_param2                 ( cfg_elec_ul2              ),
    .cfg_param3                 ( cfg_elec_ul3              ),
    .cfg_param4                 ( cfg_elec_ul4              ),
    .cfg_param5                 ( cfg_elec_ul5              )
    );

    CFGPARM                     U_CFG_ELECDL
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .cfg_param_dval             ( cfg_elecdl_dval           ),
    .slink_cfg_data             ( slink_cfg_data            ),

    .cfg_param0                 ( cfg_elec_dl0              ),
    .cfg_param1                 ( cfg_elec_dl1              ),
    .cfg_param2                 ( cfg_elec_dl2              ),
    .cfg_param3                 ( cfg_elec_dl3              ),
    .cfg_param4                 ( cfg_elec_dl4              ),
    .cfg_param5                 ( cfg_elec_dl5              )
    );

    CFGPARM                     U_CFG_ENGNCHKUL
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .cfg_param_dval             ( cfg_mntul_dval           ),
    .slink_cfg_data             ( slink_cfg_data            ),

    .cfg_param0                 ( cfg_engn_chkul0           ),
    .cfg_param1                 ( cfg_engn_chkul1           ),
    .cfg_param2                 ( cfg_engn_chkul2           ),
    .cfg_param3                 ( cfg_engn_chkul3           ),
    .cfg_param4                 ( cfg_engn_chkul4           ),
    .cfg_param5                 ( cfg_engn_chkul5           )
    );

    CFGPARM                     U_CFG_ENGNCHKDL
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .cfg_param_dval             ( cfg_mntdl_dval           ),
    .slink_cfg_data             ( slink_cfg_data            ),

    .cfg_param0                 ( cfg_engn_chkdl0           ),
    .cfg_param1                 ( cfg_engn_chkdl1           ),
    .cfg_param2                 ( cfg_engn_chkdl2           ),
    .cfg_param3                 ( cfg_engn_chkdl3           ),
    .cfg_param4                 ( cfg_engn_chkdl4           ),
    .cfg_param5                 ( cfg_engn_chkdl5           )
    );

endmodule
