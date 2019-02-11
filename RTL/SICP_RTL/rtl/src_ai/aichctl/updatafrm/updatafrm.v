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

module UPDATAFRM 
    (
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 
        clk_12_5m               ,   
        rst_12_5m_n             ,   

        cfg_done                ,   
        slot_num                ,    
        mdu_stus                ,   

        up_engn_chn0            ,   
        up_engn_chn1            ,   
        up_engn_chn2            ,   
        up_engn_chn3            ,   
        up_engn_chn4            ,   
        up_engn_chn5            ,   
        up_engn_chn6            ,   
        up_engn_chn7            ,   
        up_engn_chn8            ,   
        up_engn_chn9            ,   
        up_engn_chn10           ,   
        up_engn_chn11           ,   
                              
        up_elec_chn0            ,   
        up_elec_chn1            ,   
        up_elec_chn2            ,   
        up_elec_chn3            ,   
        up_elec_chn4            ,   
        up_elec_chn5            ,   
        up_elec_chn6            ,   
        up_elec_chn7            ,   
        up_elec_chn8            ,   
        up_elec_chn9            ,   
        up_elec_chn10           ,   
        up_elec_chn11           ,   
                              
        up_masb_chn0            ,   
        up_masb_chn1            ,   
        up_masb_chn2            ,   
        up_masb_chn3            ,   
        up_masb_chn4            ,   
        up_masb_chn5            ,   
        up_masb_chn6            ,   
        up_masb_chn7            ,   
        up_masb_chn8            ,   
        up_masb_chn9            ,   
        up_masb_chn10           ,   
        up_masb_chn11           ,
        
        ram_dgd_err             ,   
        pfifo_crc_fault         ,   
        txsdu_upm_rdreq         ,   
        upm_txsdu_empty         ,   
        upm_txsdu_dval          ,   
        upm_txsdu_data          , 

    );

/**********************************************************************************\
***************************** declare parameter ************************************/
//localparam   UP_PERIOD   =   32'd124999 ; // 80ns * 125000 = 10ms
localparam   UP_PERIOD   =   32'd8000 ; // 80ns * 125000 = 10ms
localparam   TM_DLY_US          =   7'd124      ;   // 10us
localparam   PARM_CRC_INVALUE   =   16'h3031    ;
localparam   PARM_CRC_OUTVALUE  =   16'h3ee8    ;
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input interface signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    rst_12_5m_n                         ;   
input   wire                    clk_12_5m                           ; 
input   wire    [31:0]          mdu_stus                            ;   
input   wire    [3:0]           slot_num                            ;
input   wire                    cfg_done                            ;   
input   wire                    txsdu_upm_rdreq                     ; 

input   wire    [31:0]          up_engn_chn0                        ;   
input   wire    [31:0]          up_engn_chn1                        ;   
input   wire    [31:0]          up_engn_chn2                        ;   
input   wire    [31:0]          up_engn_chn3                        ;   
input   wire    [31:0]          up_engn_chn4                        ;   
input   wire    [31:0]          up_engn_chn5                        ;   
input   wire    [31:0]          up_engn_chn6                        ;   
input   wire    [31:0]          up_engn_chn7                        ;   
input   wire    [31:0]          up_engn_chn8                        ;   
input   wire    [31:0]          up_engn_chn9                        ;   
input   wire    [31:0]          up_engn_chn10                       ;   
input   wire    [31:0]          up_engn_chn11                       ;   
input   wire    [31:0]          up_elec_chn0                        ;   
input   wire    [31:0]          up_elec_chn1                        ;   
input   wire    [31:0]          up_elec_chn2                        ;   
input   wire    [31:0]          up_elec_chn3                        ;   
input   wire    [31:0]          up_elec_chn4                        ;   
input   wire    [31:0]          up_elec_chn5                        ;   
input   wire    [31:0]          up_elec_chn6                        ;   
input   wire    [31:0]          up_elec_chn7                        ;   
input   wire    [31:0]          up_elec_chn8                        ;   
input   wire    [31:0]          up_elec_chn9                        ;   
input   wire    [31:0]          up_elec_chn10                       ;   
input   wire    [31:0]          up_elec_chn11                       ;   
input   wire    [7:0]           up_masb_chn0                        ;   
input   wire    [7:0]           up_masb_chn1                        ;   
input   wire    [7:0]           up_masb_chn2                        ;   
input   wire    [7:0]           up_masb_chn3                        ;   
input   wire    [7:0]           up_masb_chn4                        ;   
input   wire    [7:0]           up_masb_chn5                        ;   
input   wire    [7:0]           up_masb_chn6                        ;   
input   wire    [7:0]           up_masb_chn7                        ;   
input   wire    [7:0]           up_masb_chn8                        ;   
input   wire    [7:0]           up_masb_chn9                        ;   
input   wire    [7:0]           up_masb_chn10                       ;   
input   wire    [7:0]           up_masb_chn11                       ;   

// output interface signal
output  wire                    upm_txsdu_empty                     ;   
output  reg                     upm_txsdu_dval                      ;   
output  wire    [17:0]          upm_txsdu_data                      ;   
output  reg     [1:0]           pfifo_crc_fault                     ;   
output  wire                    ram_dgd_err                         ;
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [17:0]                  chn_masb[53:0]                      ;
wire    [15:0]                  pfifo_crc_dout_mm                   ;   
wire    [15:0]                  pfifo_crc_dout_ms                   ;   
wire    [17:0]                  pfifo_rddata                        ;   
wire                            pfifo_rden                          ;   
wire                            pfifo_empty                         ;   
wire    [15:0]                  pfifo_wrdata                        ;   
wire    [15:0]                  crc_dout_value                      ;   
wire                            pfifo_crc_wren                      ;   
wire    [15:0]                  pfifo_crc_din                       ;   
wire                            pfifo_sop                           ;
wire                            pfifo_eop                           ;
wire    [15:0]                  fout_crc_din                        ;
// reg signal
reg     [31:0]                  up_period_cnt                       ; 
reg     [6:0]                   wr_fifo_addr                        ;   
reg                             pfifo_wren                          ;   
reg                             pfifo_rden_d1                       ;   
reg                             crc_ch_sel                          ;   
reg                             crc_dgd_en                          ;   
reg                             crc_dgd_close                       ;   
reg                             wr_crc_wren                         ;   
reg                             pfifo_crc_err_d                     ;   
reg     [17:0]                  up_data                             ;   
reg                             pfifo_crc_cap                       ;   
reg                             crc_cap_d1                          ;   
reg                             crc_cap_d2                          ;   
reg     [17:0]                  pfifo_rddata_d1                     ;   
   
reg                             pfifo_crc_err                       ;   
reg                             pfifo_crc_sop                       ;
 
/**********************************************************************************\
******************************** debug code ****************************************/

/**********************************************************************************\
********************************* main code ****************************************/

//----------------------------------------------------------------------------------
// assemb the byte packet
//----------------------------------------------------------------------------------
assign chn_masb[0 ] = { 2'b00, up_elec_chn0[15:0] } ;
assign chn_masb[1 ] = { 2'b00, up_elec_chn0[31:16] } ;
assign chn_masb[2 ] = { 2'b00, up_engn_chn0[15:0] } ;
assign chn_masb[3 ] = { 2'b00, up_engn_chn0[31:16] } ;
assign chn_masb[4 ] = { 2'b00, up_elec_chn1[7:0], up_masb_chn0 } ;
assign chn_masb[5 ] = { 2'b00, up_elec_chn1[23:8] } ;
assign chn_masb[6 ] = { 2'b00, up_engn_chn1[7:0], up_elec_chn1[31:24] } ;
assign chn_masb[7 ] = { 2'b00, up_engn_chn1[23:8] } ;
assign chn_masb[8 ] = { 2'b00, up_masb_chn1, up_engn_chn1[31:24] } ;
assign chn_masb[9 ] = { 2'b00, up_elec_chn2[15:0] } ; 
assign chn_masb[10] = { 2'b00, up_elec_chn2[31:16] } ; 
assign chn_masb[11] = { 2'b00, up_engn_chn2[15:0] } ; 
assign chn_masb[12] = { 2'b00, up_engn_chn2[31:16] } ; 
assign chn_masb[13] = { 2'b00, up_elec_chn3[7:0], up_masb_chn2 } ; 
assign chn_masb[14] = { 2'b00, up_elec_chn3[23:8] } ; 
assign chn_masb[15] = { 2'b00, up_engn_chn3[7:0], up_elec_chn3[31:24] } ; 
assign chn_masb[16] = { 2'b00, up_engn_chn3[23:8] } ; 
assign chn_masb[17] = { 2'b00, up_masb_chn3, up_engn_chn3[31:24] } ; 
assign chn_masb[18] = { 2'b00, up_elec_chn4[15:0] } ;
assign chn_masb[19] = { 2'b00, up_elec_chn4[31:16] } ;
assign chn_masb[20] = { 2'b00, up_engn_chn4[15:0] } ;
assign chn_masb[21] = { 2'b00, up_engn_chn4[31:16] } ;
assign chn_masb[22] = { 2'b00, up_elec_chn5[7:0], up_masb_chn4 } ;
assign chn_masb[23] = { 2'b00, up_elec_chn5[23:8] } ;
assign chn_masb[24] = { 2'b00, up_engn_chn5[7:0], up_elec_chn5[31:24] } ;
assign chn_masb[25] = { 2'b00, up_engn_chn5[23:8] } ;
assign chn_masb[26] = { 2'b00, up_masb_chn5, up_engn_chn5[31:24] } ;
assign chn_masb[27] = { 2'b00, up_elec_chn6[15:0] } ;
assign chn_masb[28] = { 2'b00, up_elec_chn6[31:16] } ;
assign chn_masb[29] = { 2'b00, up_engn_chn6[15:0] } ;
assign chn_masb[30] = { 2'b00, up_engn_chn6[31:16] } ;
assign chn_masb[31] = { 2'b00, up_elec_chn7[7:0], up_masb_chn6 } ;
assign chn_masb[32] = { 2'b00, up_elec_chn7[23:8] } ;
assign chn_masb[33] = { 2'b00, up_engn_chn7[7:0], up_elec_chn7[31:24] } ;
assign chn_masb[34] = { 2'b00, up_engn_chn7[23:8] } ;
assign chn_masb[35] = { 2'b00, up_masb_chn7, up_engn_chn7[31:24] } ;
assign chn_masb[36] = { 2'b00, up_elec_chn8[15:0] } ;
assign chn_masb[37] = { 2'b00, up_elec_chn8[31:16] } ;
assign chn_masb[38] = { 2'b00, up_engn_chn8[15:0] } ;
assign chn_masb[39] = { 2'b00, up_engn_chn8[31:16] } ;
assign chn_masb[40] = { 2'b00, up_elec_chn9[7:0], up_masb_chn8 } ;
assign chn_masb[41] = { 2'b00, up_elec_chn9[23:8] } ;
assign chn_masb[42] = { 2'b00, up_engn_chn9[7:0], up_elec_chn9[31:24] } ;
assign chn_masb[43] = { 2'b00, up_engn_chn9[23:8] } ;
assign chn_masb[44] = { 2'b00, up_masb_chn9, up_engn_chn9[31:24] } ;
assign chn_masb[45] = { 2'b00, up_elec_chn10[15:0] } ; 
assign chn_masb[46] = { 2'b00, up_elec_chn10[31:16] } ;
assign chn_masb[47] = { 2'b00, up_engn_chn10[15:0] } ;
assign chn_masb[48] = { 2'b00, up_engn_chn10[31:16] } ;
assign chn_masb[49] = { 2'b00, up_elec_chn11[7:0], up_masb_chn10 } ;
assign chn_masb[50] = { 2'b00, up_elec_chn11[23:8] } ;
assign chn_masb[51] = { 2'b00, up_engn_chn11[7:0], up_elec_chn11[31:24] } ;
assign chn_masb[52] = { 2'b00, up_engn_chn11[23:8] } ;
assign chn_masb[53] = { 2'b00, up_masb_chn11, up_engn_chn11[31:24] } ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        up_data   <=   18'h0000 ;
    end
    else begin
        case ( wr_fifo_addr )
            7'h00 : up_data   <=   { 2'b10 , 16'd0 } ; // DA Address
            7'h01 : up_data   <=   { 2'b00 , 2'b00, 1'b0, 5'd0, 5'd0, 1'b1, 2'b00 } ; // DA Address && SA Address
            7'h02 : up_data   <=   { 2'b00 , 10'd0, slot_num, 2'b00 } ; // SA Address
            7'h03 : up_data   <=   { 2'b00 , 16'd0 } ; // CYCLE
            7'h04 : up_data   <=   { 2'b00 , `DATA_TYPE } ;
            7'h05 : up_data   <=   { 2'b00 , 16'h00 } ;
            7'h06 : up_data   <=   { 2'b00 , `IO_DATA_LEN - 16'd8 } ;
            7'h07 : up_data   <=   { 2'b00 , mdu_stus[15:0] } ; 
            7'h08 : up_data   <=   { 2'b00 , mdu_stus[31:16] } ;
            7'h09 : up_data   <=   chn_masb[0 ] ;
            7'h0A : up_data   <=   chn_masb[1 ] ;
            7'h0B : up_data   <=   chn_masb[2 ] ;
            7'h0C : up_data   <=   chn_masb[3 ] ;
            7'h0D : up_data   <=   chn_masb[4 ] ;
            7'h0E : up_data   <=   chn_masb[5 ] ;
            7'h0F : up_data   <=   chn_masb[6 ] ;
            7'h10 : up_data   <=   chn_masb[7 ] ;
            7'h11 : up_data   <=   chn_masb[8 ] ;
            7'h12 : up_data   <=   chn_masb[9 ] ;
            7'h13 : up_data   <=   chn_masb[10] ;
            7'h14 : up_data   <=   chn_masb[11] ;
            7'h15 : up_data   <=   chn_masb[12] ;
            7'h16 : up_data   <=   chn_masb[13] ;
            7'h17 : up_data   <=   chn_masb[14] ;
            7'h18 : up_data   <=   chn_masb[15] ;
            7'h19 : up_data   <=   chn_masb[16] ;
            7'h1A : up_data   <=   chn_masb[17] ;
            7'h1B : up_data   <=   chn_masb[18] ;
            7'h1C : up_data   <=   chn_masb[19] ;
            7'h1D : up_data   <=   chn_masb[20] ;
            7'h1E : up_data   <=   chn_masb[21] ;
            7'h1F : up_data   <=   chn_masb[22] ;
            7'h20 : up_data   <=   chn_masb[23] ;
            7'h21 : up_data   <=   chn_masb[24] ;
            7'h22 : up_data   <=   chn_masb[25] ;
            7'h23 : up_data   <=   chn_masb[26] ;
            7'h24 : up_data   <=   chn_masb[27] ;
            7'h25 : up_data   <=   chn_masb[28] ;
            7'h26 : up_data   <=   chn_masb[29] ;
            7'h27 : up_data   <=   chn_masb[30] ;
            7'h28 : up_data   <=   chn_masb[31] ;
            7'h29 : up_data   <=   chn_masb[32] ;
            7'h2A : up_data   <=   chn_masb[33] ;
            7'h2B : up_data   <=   chn_masb[34] ;
            7'h2C : up_data   <=   chn_masb[35] ;
            7'h2D : up_data   <=   chn_masb[36] ;
            7'h2E : up_data   <=   chn_masb[37] ;
            7'h2F : up_data   <=   chn_masb[38] ;
            7'h30 : up_data   <=   chn_masb[39] ;
            7'h31 : up_data   <=   chn_masb[40] ;
            7'h32 : up_data   <=   chn_masb[41] ;
            7'h33 : up_data   <=   chn_masb[42] ;
            7'h34 : up_data   <=   chn_masb[43] ;
            7'h35 : up_data   <=   chn_masb[44] ;
            7'h36 : up_data   <=   chn_masb[45] ;
            7'h37 : up_data   <=   chn_masb[46] ;
            7'h38 : up_data   <=   chn_masb[47] ;
            7'h39 : up_data   <=   chn_masb[48] ;
            7'h3A : up_data   <=   chn_masb[49] ;
            7'h3B : up_data   <=   chn_masb[50] ;
            7'h3C : up_data   <=   chn_masb[51] ;
            7'h3D : up_data   <=   chn_masb[52] ;
            7'h3F : up_data   <=   chn_masb[53] ;
            7'h42 : up_data   <=   { 2'b01, 16'd0 } ;
            default : begin
                up_data   <=   18'h0000 ;
            end
        endcase
    end
end

//----------------------------------------------------------------------------------
// up data period control 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        up_period_cnt    <=   32'h00 ;
    end
    else begin
        if ( cfg_done == 1'b1 ) begin
            if ( up_period_cnt == UP_PERIOD ) begin
                up_period_cnt    <=   32'h00 ;
            end
            else begin
                up_period_cnt    <=   up_period_cnt + 1'b1 ;
            end
        end
        else begin
            up_period_cnt    <=   32'h00 ;
        end
    end
end

//----------------------------------------------------------------------------------
// write up stream data to pfifo  
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pfifo_wren    <=   1'b0 ;
    end
    else begin
        if ( pfifo_wren == 1'b1 && up_data[16] == 1'b1 ) begin
            pfifo_wren    <=   1'b0 ;
        end
        else if ( up_period_cnt == UP_PERIOD ) begin
            pfifo_wren    <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_fifo_addr    <=   7'd0 ;
    end
    else begin
        if ( pfifo_wren == 1'b1 || up_period_cnt == UP_PERIOD ) begin
            wr_fifo_addr    <=   wr_fifo_addr + 1'b1 ;
        end
        else begin
            wr_fifo_addr    <=   7'd0 ;
        end
    end
end

assign crc_dout_value = ( crc_ch_sel == 1'b0 ) ? pfifo_crc_dout_mm : pfifo_crc_dout_ms ;
assign pfifo_wrdata =  ( wr_fifo_addr == 7'h42 ) ? crc_dout_value : up_data ;

assign pfifo_sop = ( pfifo_wren == 1'b1 && up_data[17] == 1'b1 ) ? 1'b1 : 1'b0 ;
assign pfifo_eop = ( pfifo_wren == 1'b1 && up_data[16] == 1'b1 ) ? 1'b1 : 1'b0 ;

//----------------------------------------------------------------------------------
// write up stream data to CRC 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        wr_crc_wren  <=   1'b0 ;
    end
    else begin
        if ( wr_fifo_addr == 7'd7 ) begin
            wr_crc_wren  <=   1'b1 ;
        end
        else if ( wr_fifo_addr == 7'h41 ) begin
            wr_crc_wren  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pfifo_crc_cap   <=   1'b0 ;
    end
    else begin
        if ( wr_fifo_addr == 7'h40 || ( pfifo_crc_err == 1'b1 && crc_dgd_close == 1'b0 )) begin
            pfifo_crc_cap  <=   1'b1 ;
        end
        else begin
            pfifo_crc_cap  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_cap_d1  <=   1'b0 ;
    end
    else begin
        crc_cap_d1  <=   pfifo_crc_cap ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_cap_d2  <=   1'b0 ;
    end
    else begin
        crc_cap_d2  <=   crc_cap_d1 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pfifo_crc_sop   <=   1'b0 ;
    end
    else begin
        pfifo_crc_sop   <=   crc_cap_d2 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pfifo_crc_err   <=   1'b0 ;
    end
    else begin
        if ( crc_cap_d2 == 1'b1 && pfifo_crc_dout_mm != pfifo_crc_dout_ms && crc_dgd_en == 1'b0 ) begin
            pfifo_crc_err   <=   1'b1 ;
        end
        else begin
            pfifo_crc_err   <=   1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// diagnosing the CRC module 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pfifo_crc_err_d <=   1'b0 ;
    end
    else begin
        if ( crc_dgd_close == 1'b0 ) begin
            pfifo_crc_err_d <=   pfifo_crc_err ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_dgd_en  <=   1'b0 ;
    end
    else begin
        if ( pfifo_crc_err == 1'b1 && crc_dgd_close == 1'b0 ) begin
            crc_dgd_en  <=   1'b1 ;
        end
        else if ( crc_cap_d2 == 1'b1 ) begin
            crc_dgd_en  <=   1'b0 ;
        end 
    end
end

//----------------------------------------------------------------------------------
// whether the crc_dgd_close is closed or not
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_dgd_close   <=   1'b0 ;
    end
    else begin
        if ( pfifo_crc_fault[0] == 1'b1 || pfifo_crc_fault[1] == 1'b1 ) begin
            crc_dgd_close   <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pfifo_crc_fault[0]   <=   1'b0 ;
    end
    else begin
        if ( crc_dgd_en == 1'b1 && crc_cap_d1 == 1'b1 ) begin
            if ( pfifo_crc_dout_mm != PARM_CRC_OUTVALUE ) begin
                pfifo_crc_fault[0] <= 1'b1 ;
            end
            else begin
                pfifo_crc_fault[0] <= 1'b0 ;
            end
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        pfifo_crc_fault[1]   <=   1'b0 ;
    end
    else begin
        if ( crc_dgd_en == 1'b1 && crc_cap_d1 == 1'b1 ) begin
            if ( pfifo_crc_dout_ms != PARM_CRC_OUTVALUE ) begin
                pfifo_crc_fault[1] <= 1'b1 ;
            end
            else begin
                pfifo_crc_fault[1] <= 1'b0 ;
            end
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_ch_sel  <=   1'b0 ;
    end
    else begin
        if ( crc_dgd_en == 1'b1 && crc_cap_d1 == 1'b1 ) begin
            if ( pfifo_crc_dout_mm == PARM_CRC_OUTVALUE ) begin
                crc_ch_sel  <=   1'b0 ;
            end
            else if ( pfifo_crc_dout_ms == PARM_CRC_OUTVALUE ) begin
                crc_ch_sel  <=   1'b1 ;
            end
        end
    end
end

assign pfifo_crc_wren = ( crc_dgd_en == 1'b1 ) ? pfifo_crc_err_d : wr_crc_wren ; 
assign pfifo_crc_din = ( crc_dgd_en == 1'b1 ) ? PARM_CRC_INVALUE : up_data[15:0] ;

    IO_CRC16D16                    U_FIFO_INCRC_MM
    (
    //input port
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),

    .crc_din                    ( pfifo_crc_din             ),
    .crc_cap                    ( pfifo_crc_cap             ),
    .crc_sop                    ( pfifo_crc_sop             ),
    .crc_din_vld                ( pfifo_crc_wren            ),

    //output port
    .crc_dout                   ( pfifo_crc_dout_mm         )
    );

    IO_CRC16D16                    U_FIFO_INCRC_MS
    (
    //input port
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),

    .crc_din                    ( pfifo_crc_din             ),
    .crc_cap                    ( pfifo_crc_cap             ),
    .crc_sop                    ( pfifo_crc_sop             ),
    .crc_din_vld                ( pfifo_crc_wren            ),

    //output port
    .crc_dout                   ( pfifo_crc_dout_ms         )
    );

//----------------------------------------------------------------------------------
// Throuth async fifo, synchronizate the system clock value to emif clock value  
//----------------------------------------------------------------------------------
    PFIFO_W18D1024              U_pfifo_w16d1024
    (
    // Inputs
    .wclock                     ( clk_sys                   ),
    .rclock                     ( clk_12_5m                 ),
    .wreset                     ( rst_sys_n                 ),
    .rreset                     ( rst_12_5m_n               ),
    .wdata                      ( pfifo_wrdata              ),
    .wsop                       ( pfifo_sop                 ),
    .weop                       ( pfifo_eop                 ),
    .we                         ( pfifo_wren                ),
    .re                         ( pfifo_rden                ),
    // Outputs
    .empty                      ( pfifo_empty               ),
    .full                       (                           ),
    .rdata                      ( pfifo_rddata              )
    );

assign  pfifo_rden = ( pfifo_empty == 1'b0 && txsdu_upm_rdreq == 1'b1 ) ? 1'b1 : 1'b0 ;

always @( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin	
		pfifo_rden_d1 <=  	1'b0 ;
	end
    else begin
		pfifo_rden_d1 <=  	pfifo_rden ;
	end
end

assign  upm_txsdu_empty = ( pfifo_empty == 1'b0 ) ? 1'b0 : 1'b1 ;

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        upm_txsdu_dval    <=   1'b0 ;
    end
    else begin
        if ( upm_txsdu_dval == 1'b1 && upm_txsdu_data[16] == 1'b1 ) begin
            upm_txsdu_dval    <=   1'b0 ;
        end
        else if ( upm_txsdu_empty == 1'b0 && txsdu_upm_rdreq == 1'b1 ) begin
            upm_txsdu_dval    <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m_n ) begin
    if( rst_12_5m_n == 1'b0 ) begin
        pfifo_rddata_d1 <=   17'd0 ;
    end
    else begin
        pfifo_rddata_d1 <=   pfifo_rddata ;
    end
end

assign upm_txsdu_data =   pfifo_rddata ;

//----------------------------------------------------------------------------------
// CRC check 
//----------------------------------------------------------------------------------

assign fout_crc_din = pfifo_rddata ;
assign fout_crc_dval = upm_txsdu_empty == 1'b0 && upm_txsdu_dval == 1'b1 ;

    CRC_CHK #(
    .CRC_LEN_L                  ( 7'h6                      ),
    .CRC_LEN_H                  ( 7'h41                     )
    )
    U_CRC_CHK
    (
    .clk_sys                    ( clk_12_5m                 ),
    .rst_sys_n                  ( rst_12_5m_n               ),
    .crc_dval                   ( fout_crc_dval             ),
    .crc_din                    ( fout_crc_din              ),
    .crc_err                    ( ram_dgd_err               )
    
    );

endmodule
