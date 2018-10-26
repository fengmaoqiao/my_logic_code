//**********************************************************
//
// Copyright(c) 2017 . Outwitcom Technology Co., LTD.
// All rights reserved.
// 
// ProjectName :  
// Target      :                  
// FileName    : clock_ctrl.v
// Author      : qiupeng
// E_mail      : qiupeng@outwitcom.com
// Date        : 
// Version     :     
// Description :
// Modification history
//--------------------------------------------------------
// $Log:$ 
//
//
//**********************************************************
module clock_ctrl (
        //input
        input   wire                por_rst_n                       ,
        input   wire                soft_reset_req_n                ,
        input   wire                clk_32k                         ,
        input   wire                clk_30m                         ,
        input   wire                clk_80m                         ,
        input   wire                clk_200m                        ,
        input   wire                modem_force20                   ,
        input   wire                platform_wake_up                ,
        input   wire                mac_pri_clken                   ,
        input   wire                mac_pi_tx_clken                 ,
        input   wire                mac_pi_rx_clken                 ,
        input   wire                mac_core_tx_clken               ,
        input   wire                mac_core_rx_clken               ,
        input   wire                mac_crypt_clken                 ,
        input   wire                mac_wt_clken                    ,
        input   wire                mpif_clken                      ,
        input   wire                mac_lp_clkswitch                ,
        input   wire                reg_mac_pi_clk_gating_en        ,
        input   wire                reg_mac_pi_tx_clk_gating_en     ,
        input   wire                reg_mac_pi_rx_clk_gating_en     ,
        input   wire                reg_mac_crypt_clk_gating_en     ,
        input   wire                reg_mac_core_clk_gating_en      ,
        input   wire                reg_mac_core_rx_clk_gating_en   ,
        input   wire                reg_mac_core_tx_clk_gating_en   ,
        input   wire                reg_mac_wt_clk_gating_en        ,
        input   wire                reg_mpif_clk_gating_en          ,
        //output
        output  wire                plf_rst_n                       ,
        output  wire                mac_core_rst_n                  ,
        output  wire                mac_wt_rst_n                    ,
        output  wire                mpif_rst_n                      ,
        output  wire                plf_clk                         ,
        output  wire                mac_pi_free_clk                 ,
        output  wire                mac_pi_clk                      ,
        output  wire                mac_pi_tx_clk                   ,
        output  wire                mac_pi_rx_clk                   ,
        output  wire                mac_core_free_clk               ,
        output  wire                mac_core_clk                    ,
        output  wire                mac_core_tx_clk                 ,
        output  wire                mac_core_rx_clk                 ,
        output  wire                mac_crypt_clk                   ,
        output  wire                mac_lp_clk                      ,
        output  wire                mac_wt_free_clk                 ,
        output  wire                mac_wt_clk                      ,
        output  wire                mpif_free_clk                   ,
        output  wire                mpif_clk
        );

//**********************************************************
//Signal Declation
//**********************************************************
wire                                global_rst_n                    ;
wire                                global_rst                      ;
wire                                async_plf_rst_n                 ;
wire                                g0_clk_ibufg                    ;
wire                                mmc_clk_fb                      ;
wire                                plf_clk_prebufg                 ;
reg                                 reset_req_n_1t                  ;
reg                                 reset_req_n_2t                  ;
reg                                 cleaner_plf_rst_n_m5t           ;
reg                                 cleaner_plf_rst_n_m4t           ;
reg                                 cleaner_plf_rst_n_m3t           ;
reg                                 cleaner_plf_rst_n_m2t           ;
reg                                 cleaner_plf_rst_n_m1t           ;
reg                                 cleaner_tap_rst_n_m5t           ;
reg                                 cleaner_tap_rst_n_m4t           ;
reg                                 cleaner_tap_rst_n_m3t           ;
reg                                 cleaner_tap_rst_n_m2t           ;
reg                                 cleaner_tap_rst_n_m1t           ;
reg                                 cleaner_g2_rst_n_m5t            ;
reg                                 cleaner_g2_rst_n_m4t            ;
reg                                 cleaner_g2_rst_n_m3t            ;
reg                                 cleaner_g2_rst_n_m2t            ;
reg                                 cleaner_g2_rst_n_m1t            ;
wire                                g2_rst_n                        ;
wire                                g0_clk_prebufg                  ;
wire                                g1_clk_prebufg                  ;
wire                                g2_clk_prebufg                  ;
wire                                mac_core_clk_prebufg            ;
wire                                mac_wt_clk_prebufg              ;
wire                                mac_lp_root_clk                 ;
wire                                async_mac_rst_n                 ;
reg                                 mac_rst_n                       ;
reg                                 mac_rst_n_1t                    ;
reg                                 mac_rst_n_2t                    ;
wire                                async_macphy_rst_n              ;
reg                                 macphy_rst_n                    ;
reg                                 macphy_rst_n_1t                 ;
reg                                 macphy_rst_n_2t                 ;
wire                                mmc0_lock                       ;
reg                                 mac_lp_clk_gen                  ;
wire                                mpif_root_clk                   ;

//**********************************************************
//Main Code
//**********************************************************

//MAC clock
assign plf_clk         = clk_80m;
assign mac_pi_free_clk = clk_80m;
assign mac_pi_clk      = clk_80m & (mac_pri_clken     | !reg_mac_pi_clk_gating_en       );
assign mac_pi_tx_clk   = clk_80m & (mac_pi_tx_clken   | !reg_mac_pi_tx_clk_gating_en    );
assign mac_pi_rx_clk   = clk_80m & (mac_pi_rx_clken   | !reg_mac_pi_rx_clk_gating_en    );
assign mac_core_clk    = clk_80m & (mac_pri_clken     | !reg_mac_core_clk_gating_en     );
assign mac_core_tx_clk = clk_80m & (mac_core_tx_clken | !reg_mac_core_tx_clk_gating_en  );
assign mac_core_rx_clk = clk_80m & (mac_core_rx_clken | !reg_mac_core_rx_clk_gating_en  );
assign mac_crypt_clk   = clk_80m & (mac_crypt_clken   | !reg_mac_crypt_clk_gating_en    );

assign mac_lp_clk      = mac_lp_clkswitch ? clk_32k : mac_core_clk;

assign mac_core_free_clk = clk_80m;
assign mac_wt_free_clk   = clk_80m;
assign mac_wt_clk        = clk_80m & (mac_wt_clken | !reg_mac_wt_clk_gating_en);
assign mpif_root_clk     = modem_force20 ? clk_30m : clk_80m;  
assign mpif_clk          = mpif_root_clk & (mpif_clken | !reg_mpif_clk_gating_en);
assign mpif_free_clk     = mpif_root_clk;

//reset
assign global_rst_n = por_rst_n;
assign global_rst   = ~global_rst_n;
  
//platform reset
always @(posedge plf_clk)
begin
    reset_req_n_1t <= soft_reset_req_n;
    reset_req_n_2t <= reset_req_n_1t;
end
  
assign async_plf_rst_n = global_rst_n & reset_req_n_2t;
  
always @(posedge plf_clk or negedge async_plf_rst_n)
begin
    if(async_plf_rst_n==0)
    begin
        cleaner_plf_rst_n_m5t <= 0;
        cleaner_plf_rst_n_m4t <= 0;
        cleaner_plf_rst_n_m3t <= 0;
    end
    else
    begin
        cleaner_plf_rst_n_m5t <= 1;
        cleaner_plf_rst_n_m4t <= cleaner_plf_rst_n_m5t;
        cleaner_plf_rst_n_m3t <= cleaner_plf_rst_n_m4t;
    end
end
 
always @(posedge plf_clk)
begin
    cleaner_plf_rst_n_m2t <= cleaner_plf_rst_n_m3t;
    cleaner_plf_rst_n_m1t <= cleaner_plf_rst_n_m2t;
end
  
assign plf_rst_n = cleaner_plf_rst_n_m1t & cleaner_plf_rst_n_m3t;

//mac reset
assign async_mac_rst_n = global_rst_n & async_plf_rst_n;
  
always @(posedge clk_80m or negedge async_mac_rst_n)
begin
    if(async_mac_rst_n==0)
    begin
        mac_rst_n_2t <= 0;
        mac_rst_n_1t <= 0;
        mac_rst_n    <= 0;
    end
    else
    begin
        mac_rst_n_2t <= 1;
        mac_rst_n_1t <= mac_rst_n_2t;
        mac_rst_n    <= mac_rst_n_1t;
    end
end

//macphy reset
assign async_macphy_rst_n = global_rst_n & async_plf_rst_n;

always @(posedge clk_200m or negedge async_macphy_rst_n)
begin
    if(async_macphy_rst_n==0)
    begin
        macphy_rst_n_2t <= 0;
        macphy_rst_n_1t <= 0;
        macphy_rst_n    <= 0;
    end
    else
    begin
        macphy_rst_n_2t <= 1;
        macphy_rst_n_1t <= macphy_rst_n_2t;
        macphy_rst_n    <= macphy_rst_n_1t;
    end
end

assign mac_core_rst_n = mac_rst_n;
assign mac_wt_rst_n   = mac_rst_n;
assign mpif_rst_n     = macphy_rst_n;

endmodule
