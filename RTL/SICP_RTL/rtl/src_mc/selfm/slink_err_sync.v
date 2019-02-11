// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SLINK_DIAG
// CREATE DATE      :   2017-12-12
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-12-12  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   SLINK diagnose
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

module  SLINK_ERR_SYNC
    (
    // clock & reset
    clk_sys                     ,   
    rst_sys_n                   ,   

    rd_dval                     ,   
    chn_enable                  ,  

    chn_slink_err               ,   
    slink_err                    
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys_n                           ;   

input   wire                    rd_dval                             ;   
input   wire                    chn_enable                          ;  
input   wire                    chn_slink_err                       ;   

// declare output signal
output  wire                    slink_err                           ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            slink_err_tmp                       ;   

// reg signal
reg                             slink_err_tmp_d1                    ;   
reg                             slink_err_tmp_d2                    ; 

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

assign  slink_err_tmp   =   chn_enable == 1'b1 ? chn_slink_err : 1'b0 ;   

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        slink_err_tmp_d1    <=   1'b0 ;
        slink_err_tmp_d2    <=   1'b0 ;
    end
    else begin
        if ( rd_dval == 1'b0 ) begin
            slink_err_tmp_d1    <=   slink_err_tmp ;
            slink_err_tmp_d2    <=   slink_err_tmp_d1 ;
        end
    end
end

assign  slink_err   =   slink_err_tmp_d2 ;   

endmodule

