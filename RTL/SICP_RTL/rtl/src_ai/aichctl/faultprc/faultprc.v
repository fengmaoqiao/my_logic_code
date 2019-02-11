// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-12-12
// DEPARTMENT       :   R&D
// AUTHOR           :   Zhang Yongjun
// AUTHOR'S EMAIL   :   zhangyongjun@cgnpc.com.cn
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-12-12  Zhang Yongjun       Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active hign
// Clock Domains    :   clk_125m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`timescale 1 ns / 1 ns
`include "DEFINES.v"

module FAULTPRC
    (
        rst_sys_n               ,   
        clk_sys                 ,   
        rst_12_5m_n             ,   
        clk_12_5m               ,

        wd_cfg_en               ,   
        wd_cfg_done             ,   
        ch_fault                ,   
        e2p_chip_err            ,   
        pwr_err_int             ,
        rdu_fault               ,   
        up_ram_err              ,   
        slink_ram_err           ,   
        txsdu_ram_err           ,   
        rxsdu_ram_err           ,
        wd_clk_fault            ,   
        wd_ch_fault             ,
        wd_com_fault            ,   

        chn_dgd_en              ,   
        acq_dgdad_enl           ,   
        acq_dgdad_enh           ,   
        
        adacq_rd_dval           ,   
        adacq_rd_data0          ,   
        adacq_rd_data1          ,   
        adacq_rd_data2          ,   
        adacq_rd_data3          ,   
        adacq_rd_data4          ,   
        adacq_rd_data5          ,   
        adacq_rd_data6          ,   
        adacq_rd_data7          ,   
        adacq_rd_data8          ,   
        adacq_rd_data9          ,   
        adacq_rd_data10         ,   
        adacq_rd_data11         ,   

        mdu_stus                ,   
        hw_fault                , 
        pwr_ram_fault           ,   
        chn_dgd_err             ,   
        chn_open_short             

    ) ;
    
/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
localparam  TM_CNT_US      = 7'd124 ;
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input singal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    rst_12_5m_n                         ;   
input   wire                    clk_12_5m                           ; 

input   wire                    up_ram_err                          ;   
input   wire    [1:0]           slink_ram_err                       ;   
input   wire    [1:0]           txsdu_ram_err                       ;   
input   wire                    rxsdu_ram_err                       ;

input   wire                    wd_cfg_en                           ;   
input   wire                    wd_cfg_done                         ;   
input   wire                    e2p_chip_err                        ;   
input   wire                    pwr_err_int                         ;   
input   wire                    chn_dgd_en                          ;   
input   wire                    rdu_fault                           ;   
input   wire                    wd_clk_fault                        ;   
input   wire                    wd_ch_fault                         ;   
input   wire                    wd_com_fault                        ;   
input   wire                    ch_fault                            ;

input   wire    [11:0]          adacq_rd_dval                       ;   
input   wire    [15:0]          adacq_rd_data0                      ;   
input   wire    [15:0]          adacq_rd_data1                      ;   
input   wire    [15:0]          adacq_rd_data2                      ;   
input   wire    [15:0]          adacq_rd_data3                      ;   
input   wire    [15:0]          adacq_rd_data4                      ;   
input   wire    [15:0]          adacq_rd_data5                      ;   
input   wire    [15:0]          adacq_rd_data6                      ;   
input   wire    [15:0]          adacq_rd_data7                      ;   
input   wire    [15:0]          adacq_rd_data8                      ;   
input   wire    [15:0]          adacq_rd_data9                      ;   
input   wire    [15:0]          adacq_rd_data10                     ;   
input   wire    [15:0]          adacq_rd_data11                     ;   

input   wire    [5:0]           acq_dgdad_enl                       ;   
input   wire    [5:0]           acq_dgdad_enh                       ;   

// output signal
output  wire    [11:0]          chn_dgd_err                         ;   
output  wire    [11:0]          chn_open_short                      ;   
output  wire                    hw_fault                            ;   
output  reg     [31:0]          mdu_stus                            ;   
output  wire                    pwr_ram_fault                       ;
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
  
wire    [15:0]                  open_cir_dl                         ;   
wire    [15:0]                  short_cir_ul                        ; 
wire                            wd_fault                            ;   

wire    [15:0]                  dgd_volt_dl[11:0]                   ;   
wire    [15:0]                  dgd_volt_ul[11:0]                   ; 
// reg signal             
reg     [15:0]                  acq_dgd_value[11:0]                 ;
reg     [15:0]                  acq_chd_value[11:0]                 ;
reg                             e2p_err                             ;   

reg     [3:0]                   pwr_err_int_d                       ;   
reg     [6:0]                   pwn_div_us                          ;   
reg                             pwr_fault                           ;   
reg     [2:0]                   temp_fault_d                        ;   
reg                             temp_fault                          ;   
reg     [3:0]                   ram_fault_t_d                       ;   
reg                             ram_fault_t                         ;   
reg                             ram_fault                           ;   
reg     [3:0]                   pwr_fault_d                         ;   
reg     [3:0]                   wd_fault_d                          ;   
reg                             wd_fault_d1                         ;
reg     [12:0]                  wd_com_cnt                          ;   
reg                             wd_cfg_fault                        ;   

/**********************************************************************************\
******************************** debug code ****************************************

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign open_cir_dl      = 16'h8045  ;  // 0.2mA 65536*50*I/4.93/1.25/1000

assign dgd_volt_dl[0 ]    = 16'h965D  ;  // 0.820612V V/4.096/1.25*65536
assign dgd_volt_dl[1 ]    = 16'h965D  ;
assign dgd_volt_dl[2 ]    = 16'h965D  ;
assign dgd_volt_dl[3 ]    = 16'h965D  ;
assign dgd_volt_dl[4 ]    = 16'h965D  ;
assign dgd_volt_dl[5 ]    = 16'h965D  ;
assign dgd_volt_dl[6 ]    = 16'h965D  ;
assign dgd_volt_dl[7 ]    = 16'h965D  ;
assign dgd_volt_dl[8 ]    = 16'h965D  ;
assign dgd_volt_dl[9 ]    = 16'h965D  ;
assign dgd_volt_dl[10]    = 16'h965D  ;
assign dgd_volt_dl[11]    = 16'h965D  ;

assign dgd_volt_ul[0 ]    = 16'h96FD  ;  // 0.843546V
assign dgd_volt_ul[1 ]    = 16'h96FD  ;
assign dgd_volt_ul[2 ]    = 16'h96FD  ;
assign dgd_volt_ul[3 ]    = 16'h96FD  ;
assign dgd_volt_ul[4 ]    = 16'h96FD  ;
assign dgd_volt_ul[5 ]    = 16'h96FD  ;
assign dgd_volt_ul[6 ]    = 16'h96FD  ;
assign dgd_volt_ul[7 ]    = 16'h96FD  ;
assign dgd_volt_ul[8 ]    = 16'h96FD  ;
assign dgd_volt_ul[9 ]    = 16'h96FD  ;
assign dgd_volt_ul[10]    = 16'h96FD  ;
assign dgd_volt_ul[11]    = 16'h96FD  ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        acq_dgd_value[0] <= 16'h00000;
        acq_dgd_value[1] <= 16'h00000;
        acq_dgd_value[2] <= 16'h00000;
        acq_dgd_value[3] <= 16'h00000;
        acq_dgd_value[4] <= 16'h00000;
        acq_dgd_value[5] <= 16'h00000;
        acq_dgd_value[6] <= 16'h00000;
        acq_dgd_value[7] <= 16'h00000;
        acq_dgd_value[8] <= 16'h00000;
        acq_dgd_value[9] <= 16'h00000;
        acq_dgd_value[10]<= 16'h00000;
        acq_dgd_value[11]<= 16'h00000;
    end
    else begin
        if ( acq_dgdad_enl[0] == 1'b1 && adacq_rd_dval[0] == 1'b1 ) begin
            acq_dgd_value[0]   <=  adacq_rd_data0 ;
        end
        else ;
        if ( acq_dgdad_enl[1] == 1'b1 && adacq_rd_dval[1] == 1'b1 ) begin
            acq_dgd_value[1]   <=  adacq_rd_data1 ;
        end
        else ;
        if ( acq_dgdad_enl[2] == 1'b1 && adacq_rd_dval[2] == 1'b1 ) begin
            acq_dgd_value[2]   <=  adacq_rd_data2 ;
        end
        else ;
        if ( acq_dgdad_enl[3] == 1'b1 && adacq_rd_dval[3] == 1'b1 ) begin
            acq_dgd_value[3]   <=  adacq_rd_data3 ;
        end
        else ;
        if ( acq_dgdad_enl[4] == 1'b1 && adacq_rd_dval[4] == 1'b1 ) begin
            acq_dgd_value[4]   <=  adacq_rd_data4 ;
        end
        else ;
        if ( acq_dgdad_enl[5] == 1'b1 && adacq_rd_dval[5] == 1'b1 ) begin
            acq_dgd_value[5]   <=  adacq_rd_data5 ;
        end
        else ;
        if ( acq_dgdad_enh[0] == 1'b1 && adacq_rd_dval[6] == 1'b1 ) begin
            acq_dgd_value[6]   <=  adacq_rd_data6 ;
        end
        else ;
        if ( acq_dgdad_enh[1] == 1'b1 && adacq_rd_dval[7] == 1'b1 ) begin
            acq_dgd_value[7]   <=  adacq_rd_data7 ;
        end
        else ;
        if ( acq_dgdad_enh[2] == 1'b1 && adacq_rd_dval[8] == 1'b1 ) begin
            acq_dgd_value[8]   <=  adacq_rd_data8 ;
        end
        else ;
        if ( acq_dgdad_enh[3] == 1'b1 && adacq_rd_dval[9] == 1'b1 ) begin
            acq_dgd_value[9]   <=  adacq_rd_data9 ;
        end
        else ;
        if ( acq_dgdad_enh[4] == 1'b1 && adacq_rd_dval[10] == 1'b1 ) begin
            acq_dgd_value[10]   <=  adacq_rd_data10 ;
        end
        else ;
        if ( acq_dgdad_enh[5] == 1'b1 && adacq_rd_dval[11] == 1'b1 ) begin
            acq_dgd_value[11]   <=  adacq_rd_data11 ;
        end
        else ;
    end
end


always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        acq_chd_value[0] <= 16'h00000;
        acq_chd_value[1] <= 16'h00000;
        acq_chd_value[2] <= 16'h00000;
        acq_chd_value[3] <= 16'h00000;
        acq_chd_value[4] <= 16'h00000;
        acq_chd_value[5] <= 16'h00000;
        acq_chd_value[6] <= 16'h00000;
        acq_chd_value[7] <= 16'h00000;
        acq_chd_value[8] <= 16'h00000;
        acq_chd_value[9] <= 16'h00000;
        acq_chd_value[10]<= 16'h00000;
        acq_chd_value[11]<= 16'h00000;
    end
    else begin
        if ( acq_dgdad_enl[0] == 1'b0 && adacq_rd_dval[0] == 1'b1 ) begin
            acq_chd_value[0]   <=  adacq_rd_data0 ;
        end
        else ;
        if ( acq_dgdad_enl[1] == 1'b0 && adacq_rd_dval[1] == 1'b1 ) begin
            acq_chd_value[1]   <=  adacq_rd_data1 ;
        end
        else ;
        if ( acq_dgdad_enl[2] == 1'b0 && adacq_rd_dval[2] == 1'b1 ) begin
            acq_chd_value[2]   <=  adacq_rd_data2 ;
        end
        else ;
        if ( acq_dgdad_enl[3] == 1'b0 && adacq_rd_dval[3] == 1'b1 ) begin
            acq_chd_value[3]   <=  adacq_rd_data3 ;
        end
        else ;
        if ( acq_dgdad_enl[4] == 1'b0 && adacq_rd_dval[4] == 1'b1 ) begin
            acq_chd_value[4]   <=  adacq_rd_data4 ;
        end
        else ;
        if ( acq_dgdad_enl[5] == 1'b0 && adacq_rd_dval[5] == 1'b1 ) begin
            acq_chd_value[5]   <=  adacq_rd_data5 ;
        end
        else ;
        if ( acq_dgdad_enh[0] == 1'b0 && adacq_rd_dval[6] == 1'b1 ) begin
            acq_chd_value[6]   <=  adacq_rd_data6 ;
        end
        else ;
        if ( acq_dgdad_enh[1] == 1'b0 && adacq_rd_dval[7] == 1'b1 ) begin
            acq_chd_value[7]   <=  adacq_rd_data7 ;
        end
        else ;
        if ( acq_dgdad_enh[2] == 1'b0 && adacq_rd_dval[8] == 1'b1 ) begin
            acq_chd_value[8]   <=  adacq_rd_data8 ;
        end
        else ;
        if ( acq_dgdad_enh[3] == 1'b0 && adacq_rd_dval[9] == 1'b1 ) begin
            acq_chd_value[9]   <=  adacq_rd_data9 ;
        end
        else ;
        if ( acq_dgdad_enh[4] == 1'b0 && adacq_rd_dval[10] == 1'b1 ) begin
            acq_chd_value[10]   <=  adacq_rd_data10 ;
        end
        else ;
        if ( acq_dgdad_enh[5] == 1'b0 && adacq_rd_dval[11] == 1'b1 ) begin
            acq_chd_value[11]   <=  adacq_rd_data11 ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// generate open circuit judgment
//----------------------------------------------------------------------------------
genvar i ;
generate 
for ( i=0 ;i<12; i=i+1 )
begin : open_cir_jug
    JUG_LESSTHAN        U_JUG_LESSTHAN
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
  
    .chn_dgd_en                 ( chn_dgd_en                ),
    .jug_datastd0               ( open_cir_dl               ),
    .jug_data                   ( acq_chd_value[i]          ),
    .jug_result                 ( chn_open_short[i]         )
    ) ;
end
endgenerate 

//----------------------------------------------------------------------------------
// process channel diagnode errer
//----------------------------------------------------------------------------------
genvar m ;
generate 
for ( m=0 ;m<12; m=m+1 )
begin : dgd_jug
    JUG_REGION                  U_JUG_REGION
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .chn_dgd_en                 ( chn_dgd_en                ),
    .jug_datastdh               ( dgd_volt_ul[m]            ),
    .jug_datastdl               ( dgd_volt_dl[m]            ),
    .jug_data                   ( acq_dgd_value[m]          ),
    .jug_result                 ( chn_dgd_err[m]            )
    ) ;
end
endgenerate 

//----------------------------------------------------------------------------------
// porcess the signal of power error 
//----------------------------------------------------------------------------------
//----------------------------------------------------------------------------------
// the us count 
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        pwn_div_us  <=  7'd0 ;
    end
    else begin
        if ( pwn_div_us == TM_CNT_US ) begin
            pwn_div_us  <=  7'd0 ;
        end
        else begin
            pwn_div_us  <=  pwn_div_us + 1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        pwr_err_int_d  <= 4'b0000 ;  
    end
    else begin
        if ( pwn_div_us == TM_CNT_US ) begin
            pwr_err_int_d <= { pwr_err_int_d[2:0] , pwr_err_int } ;
        end
        else ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        pwr_fault   <=   1'b0 ;
    end
    else begin
        if ( pwr_err_int_d == 4'b0000 ) begin
            pwr_fault   <=   1'b1 ;
        end
        else begin
            pwr_fault   <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        wd_com_cnt  <=   13'd0 ;
    end
    else begin
        if ( wd_cfg_en == 1'b1 && pwn_div_us == TM_CNT_US ) begin
            if ( wd_com_cnt[12] == 1'b1 ) begin
                wd_com_cnt[12]  <=   1'b1 ;
            end
            else begin
                wd_com_cnt  <=   wd_com_cnt + 1'b1 ;
            end
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        wd_cfg_fault    <=   1'b0 ;
    end
    else begin
        if ( wd_com_cnt[12] == 1'b1 && wd_cfg_done == 1'b0 ) begin
            wd_cfg_fault    <=   1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// the clk_sys domain
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        temp_fault  <=   1'b0 ;
    end
    else begin
        temp_fault    <=   | {slink_ram_err, rxsdu_ram_err } ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        temp_fault_d    <=   3'd0 ;
    end
    else begin
        temp_fault_d    <=   { temp_fault_d[1:0], temp_fault } ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        ram_fault  <=   1'b0 ;
    end
    else begin
        ram_fault    <= | { temp_fault_d[2], up_ram_err, txsdu_ram_err } ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wd_fault_d1    <=   1'b0 ;
    end
    else begin
        wd_fault_d1    <=  | { wd_clk_fault, wd_ch_fault ,wd_com_fault } ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        wd_fault_d  <=   4'd0 ;
    end
    else begin
        wd_fault_d  <=   { wd_fault_d[2:0], wd_fault_d1 } ;
    end
end

assign wd_fault = wd_fault_d[3] || wd_cfg_fault ;

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        mdu_stus    <=   32'd0 ;
    end
    else begin
        mdu_stus    <=   { 10'd0, pwr_fault ,wd_fault , ch_fault, 4'd0 , ram_fault, 3'd0, rdu_fault, 1'b0, e2p_err, 8'd0 } ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        ram_fault_t  <=   1'b0 ;
    end
    else begin
        ram_fault_t  <=  | { pwr_fault, ch_fault, ram_fault, rdu_fault,wd_cfg_fault } ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        e2p_err     <=   1'b0 ;
    end
    else begin
        e2p_err <=  e2p_chip_err ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ram_fault_t_d    <=   4'd0 ;
    end
    else begin
        ram_fault_t_d    <=   { ram_fault_t_d[2:0], ram_fault_t } ;
    end
end

assign hw_fault = ram_fault_t_d[3] || wd_fault_d1 || e2p_chip_err ; // pwr + ram + wd + chpwr + rdu + e2p

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pwr_fault_d <=   4'd0 ;
    end
    else begin
        pwr_fault_d <=   { pwr_fault_d[2:0] , pwr_fault || ram_fault } ;
    end
end

assign pwr_ram_fault = pwr_fault_d[3] || wd_fault_d1 || e2p_chip_err ; // pwr + ram + wd + e2p

endmodule
