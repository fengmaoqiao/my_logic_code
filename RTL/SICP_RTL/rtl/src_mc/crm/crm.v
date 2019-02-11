// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   CRM
// CREATE DATE      :   2017-08-30
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-30  TingtingGan     Original
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
`include "DEFINES.v"

module CRM
    (
    //input port
    clk_125m_p                  , // external diffrence oscillator input , 125MHz  
    clk_125m_n                  ,   
    hard_rst                    , // button reset , active low   
    soft_rst                    , // register reset write by ARM , active low   

    //output port   
    clk_12_5m                   ,   
    rst_12_5m                   ,   
    rst_125m                    ,   
    clk_125m_0                  ,   
    clk_125m_90                 ,   
    clk_125m_180                ,   
    clk_125m_270    
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
`ifdef  SIM
parameter   PWRUP_RSTTIME   =   5'd20        ;
parameter   PWRUP_RSTWITH   =   3'd5         ;
`else
parameter   PWRUP_RSTTIME   =   32'd20000    ; // 20000000 * 20ns = 400ms
parameter   PWRUP_RSTWITH   =   6'd32        ;
`endif

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_125m_p                          ;   
input   wire                    clk_125m_n                          ;   
input   wire                    hard_rst                            ;   
input   wire                    soft_rst                            ;   

//declare output signal
output  wire                    clk_12_5m                           ;   
output  wire                    rst_12_5m                           ;   
output  wire                    rst_125m                            ;   
output  wire                    clk_125m_0                          ;   
output  wire                    clk_125m_90                         ;   
output  wire                    clk_125m_180                        ;   
output  wire                    clk_125m_270                        ;  

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire singal 
wire                            hard_reset                          ;  
wire                            rst_tmp                             ; 
wire                            pll_12_5m_lock                      ;   
wire                            pll_lvds_lock                       ;   

// reg singal 
reg         [PWRUP_RSTWITH-1:0] pwrup_rst_cnt                       ;   
reg                             pwrup_rst                           ;   
reg         [15:0]              hard_rst_dly                        ;  
reg                             rst_12_5m_tmp_d1                    ;   
reg                             rst_12_5m_tmp_d2                    ;   
reg                             rst_125m_tmp_d1                     ;   
reg                             rst_125m_tmp_d2                     ; 


/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// hard_rst lasts at least 160ns 
//----------------------------------------------------------------------------------
always @( posedge clk_125m_0 ) begin
    hard_rst_dly   <= { hard_rst_dly[14:0] , hard_rst } ;
end

assign hard_reset =  | hard_rst_dly  ;

//----------------------------------------------------------------------------------
// powerup reset generator
//----------------------------------------------------------------------------------
always @( posedge clk_125m_0 ) begin
    if( hard_reset == 1'b0 || soft_rst == 1'b0 )begin
        pwrup_rst_cnt   <= { PWRUP_RSTWITH{1'b0} } ;    
    end
    else if( pwrup_rst_cnt == PWRUP_RSTTIME ) begin
        pwrup_rst_cnt   <=  pwrup_rst_cnt ;    
    end
    else if( pwrup_rst_cnt < PWRUP_RSTTIME ) begin
        pwrup_rst_cnt   <=  pwrup_rst_cnt + 1'b1 ;    
    end
    else begin
        pwrup_rst_cnt   <= { PWRUP_RSTWITH{1'b0} } ;    
    end
end

always @( posedge clk_125m_0 ) begin
    if( pwrup_rst_cnt == PWRUP_RSTTIME ) begin
        pwrup_rst <=  1'b0 ;
    end
    else begin
        pwrup_rst <=  1'b1 ;
    end
end

assign  rst_tmp = ( ~ pwrup_rst ) & pll_12_5m_lock & pll_lvds_lock ;

//----------------------------------------------------------------------------------
// reset generator , Asynchronous Reset , Synchronous Release
//----------------------------------------------------------------------------------
// rst_12_5m
always @( posedge clk_12_5m ) begin
    rst_12_5m_tmp_d1 <= rst_tmp ;
    rst_12_5m_tmp_d2 <= rst_12_5m_tmp_d1 ;
end

assign  rst_12_5m = rst_12_5m_tmp_d2 ;

// rst_125m
always @( posedge clk_125m_0 ) begin
    rst_125m_tmp_d1 <= rst_tmp ;
    rst_125m_tmp_d2 <= rst_125m_tmp_d1 ;
end

assign  rst_125m = rst_125m_tmp_d2 ;

//----------------------------------------------------------------------------------
// PLL instantiated 
//----------------------------------------------------------------------------------
    pll_lvds_if                 u_pll_lvds_if
    (
    .CLK0_PADP                  ( clk_125m_p                ),
    .CLK0_PADN                  ( clk_125m_n                ),
    .GL0                        ( clk_125m_0                ),
    .GL1                        ( clk_125m_90               ),
    .GL2                        ( clk_125m_180              ),
    .GL3                        ( clk_125m_270              ),
    .LOCK                       ( pll_lvds_lock             )
    );

    pll_12_5m                   U_pll_12_5m
    (
    .CLK0                       ( clk_125m_0                ),
    .GL0                        ( clk_12_5m                 ),
    .LOCK                       ( pll_12_5m_lock            )
    );

endmodule


