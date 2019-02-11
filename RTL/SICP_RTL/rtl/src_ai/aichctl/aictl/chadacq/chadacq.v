// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-07-06
// DEPARTMENT       :   R&D
// AUTHOR           :   YongjunZhang
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-12-8  YongjunZhang        Original
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

module CHADACQ 
(
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 
        
        // input signal
        pw_on_en                ,   
        cal_model_en            ,   
        cal_done                ,   
        cfg_chn_enable          ,   
        adacq_spi_busy          ,   
        adacq_rd_dval           ,   
        adacq_rd_data           , 

        // ouput signal
        ch_ad_diag              ,   
        adacq_rd_en             ,   
        acq_dgdad_en            ,   
        ch_ad_value             ,   
        ad_acq_cpl
);

/**********************************************************************************\
***************************** declare parameter ************************************/
localparam      CAL_TM_US       = 7'd124     ;  // 1000  // 1ms = 100Mhz/100/1000   
localparam      AD_ACQ_MS       = 10'd1000    ;  // 1000  // 1ms = 100Mhz/100/1000   
localparam      RD_AD_DLY       = 19'd0400   ;  // 3.2us
localparam      RD_SW_DLY       = 19'd400000   ;  // 3.2ms 
localparam      DGD_ACQ_MS0     = 23'd500000   ;  // defalut:23'h4C4B40

localparam      IDLE            = 7'b0000000 ;
localparam      ACQ_WAIT        = 7'b0000010 ;
localparam      CH_SW           = 7'b0000100 ;
localparam      DLY_RD          = 7'b0001000 ;
localparam      AD_RDY          = 7'b0010000 ;
localparam      RD_ADC          = 7'b0100000 ;
localparam      AD_DONE         = 7'b1000000 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    pw_on_en                            ;   
input   wire                    cal_model_en                        ;   
input   wire                    cal_done                            ;   
input   wire                    cfg_chn_enable                      ;   
input   wire                    adacq_spi_busy                      ;   
input   wire                    adacq_rd_dval                       ;   
input   wire    [15:0]          adacq_rd_data                       ;   
// output signal
output  reg                     ch_ad_diag                          ;   
output  reg                     adacq_rd_en                         ;   
output  wire                    acq_dgdad_en                        ;   
output  reg                     ad_acq_cpl                          ;   
output  reg     [15:0]          ch_ad_value                         ;   
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
  
// reg signal
reg     [6:0]                   cur_state                           ;   
reg     [6:0]                   next_state                          ;   
reg     [6:0]                   tm_div_us                           ;  
reg     [18:0]                  dly_rdad_cnt                        ;   
reg     [22:0]                  dgd_tm_cnt                          ; 
reg                             acq_dgd_en                          ; 
reg     [9:0]                   ad_div_ms                           ;   
reg                             ad_acq_trig                         ;
reg                             dgd_dly_flag                         ;   
reg                             acq_chn_sel                         ;   
/**********************************************************************************\
******************************** debug code ****************************************/

/**********************************************************************************\
********************************* main code ****************************************/
assign acq_dgdad_en = ch_ad_diag ;
//----------------------------------------------------------------------------------
// the us count 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        tm_div_us  <=  7'd0 ;
    end
    else begin
        if ( tm_div_us == CAL_TM_US ) begin
            tm_div_us  <=  7'd0 ;
        end
        else begin
            tm_div_us  <=  tm_div_us + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// dianoge the time of diagnose acqiration
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dgd_tm_cnt  <=  23'd0 ;
    end
    else begin
        if ( pw_on_en == 1'b1 && tm_div_us == CAL_TM_US ) begin
            if ( dgd_tm_cnt == DGD_ACQ_MS0 ) begin
                dgd_tm_cnt  <=  23'd0 ;
            end
            else begin
                dgd_tm_cnt  <=  dgd_tm_cnt + 1'b1 ;
            end
        end
        else begin
            dgd_tm_cnt  <=  dgd_tm_cnt ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        acq_dgd_en  <=  1'b0 ;
    end
    else begin
        if ( dgd_tm_cnt == DGD_ACQ_MS0 && tm_div_us == CAL_TM_US ) begin
            acq_dgd_en   <=  1'b1 ;
        end
        else if ( cur_state == AD_DONE ) begin
            acq_dgd_en   <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ch_ad_diag  <=  1'b0 ;
    end
    else begin
        if ( cal_model_en == 1'b1 ) begin
            ch_ad_diag  <=   1'b0 ;
        end
        else if ( cur_state == AD_DONE ) begin 
            if ( acq_dgd_en == 1'b1 ) begin
                ch_ad_diag  <=  1'b1 ; //select dgd 
            end
            else begin
                ch_ad_diag  <=  1'b0 ; // select chd
            end
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dgd_dly_flag  <=   1'b0 ;
    end
    else begin
        if ( cal_model_en == 1'b1 ) begin
            dgd_dly_flag <=   1'b0 ;
        end
        else if ( cur_state == AD_DONE ) begin
            if ( acq_dgd_en == 1'b1 || ch_ad_diag == 1'b1 ) begin
                dgd_dly_flag <=   1'b1 ;
            end
            else begin
                dgd_dly_flag <=   1'b0 ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ad_div_ms  <=  10'd0 ;
    end
    else begin
        if ( pw_on_en == 1'b1 && tm_div_us == CAL_TM_US ) begin
            if (ad_div_ms == AD_ACQ_MS) begin
                ad_div_ms  <=  10'd0 ;
            end
            else begin
                ad_div_ms  <=  ad_div_ms + 1'b1;
            end
        end
        else begin
            ad_div_ms  <=  ad_div_ms ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ad_acq_trig  <=  1'b0 ;
    end
    else begin
        if (ad_div_ms == AD_ACQ_MS && tm_div_us == CAL_TM_US ) begin
            ad_acq_trig  <=  1'b1 ;
        end
        else begin
            ad_acq_trig  <=  1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// the ctrol state
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cur_state  <=  IDLE ;
    end
    else begin
        cur_state  <=  next_state ;
    end
end

always @ ( * ) begin
    if( rst_sys_n == 1'b0 ) begin
        next_state = IDLE ;
    end
    else begin
        case ( cur_state )
            IDLE : begin // 14'h00
                if ( pw_on_en == 1'b1 ) begin // && cal_done == 1'b1 
                    next_state = ACQ_WAIT ;
                end
                else begin
                    next_state = IDLE ;
                end
            end
            ACQ_WAIT : begin // 14'h02
                if ( ad_acq_trig == 1'b1 && adacq_spi_busy == 1'b0  && ( cfg_chn_enable == 1'b1 || cal_model_en == 1'b1 ) ) begin 
                    next_state = CH_SW ;
                end
                else begin
                    next_state = ACQ_WAIT ;
                end
            end
            CH_SW : begin // 14'h04
                next_state = DLY_RD ;
            end
            DLY_RD : begin  //14'h08
                if ( dgd_dly_flag == 1'b0 && dly_rdad_cnt == RD_AD_DLY ) begin
                    next_state = AD_RDY ;
                end
                else if ( dgd_dly_flag == 1'b1 && dly_rdad_cnt == RD_SW_DLY ) begin
                    next_state = AD_RDY ;
                end
                else begin
                    next_state = DLY_RD ;
                end
            end
            AD_RDY : begin // 10
                next_state = RD_ADC ;
            end
            RD_ADC : begin // 14'h20
                if ( adacq_rd_dval == 1'b1 ) begin
                    next_state = AD_DONE ;
                end
                else begin
                    next_state = RD_ADC ;
                end
            end
            AD_DONE : begin // 14'h40
                next_state = ACQ_WAIT ;
            end
            default : begin
                next_state = IDLE ;
            end
        endcase
    end
end

//----------------------------------------------------------------------------------
// start read value from ads8689 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        adacq_rd_en  <=  1'b0 ;
    end
    else begin
        if ( cur_state == AD_RDY ) begin
            adacq_rd_en  <=  1'b1 ;
        end
        else begin
            adacq_rd_en  <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ch_ad_value <=   16'h0000 ;
    end
    else begin
        if ( cur_state == RD_ADC && adacq_rd_dval == 1'b1 && dgd_dly_flag == 1'b0 ) begin
            if ( adacq_rd_data[15] == 1'b0 ) begin
                ch_ad_value <=   16'd0 ;
            end
            else begin
                ch_ad_value <=   { 1'b0 ,adacq_rd_data[14:0] } ;
            end
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dly_rdad_cnt    <=   19'd0 ;
    end
    else begin
        if ( cur_state == DLY_RD ) begin
            dly_rdad_cnt    <=   dly_rdad_cnt + 1'b1 ;
        end
        else begin
            dly_rdad_cnt    <=   19'd0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ad_acq_cpl <=  1'b0 ; 
    end
    else begin
        if ( cur_state == AD_DONE ) begin
            ad_acq_cpl <=   1'b1 ;
        end
        else ;
    end
end

endmodule
