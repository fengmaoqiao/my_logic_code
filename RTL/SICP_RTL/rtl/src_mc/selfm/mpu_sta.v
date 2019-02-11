// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   STA
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

module  MPU_STA
    (
    // clock & reset
    clk_150m                    ,   
    rst_150m                    ,   
    
    rd_dval                     ,
    mpu_sta_dval                ,   
    mpu_sta_data                ,   

    mpu_slot_sta1               ,   
    mpu_slot_sta2               
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   SLOT_NUM  =   4'h0 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_150m                            ;   
input   wire                    rst_150m                            ;

input   wire                    rd_dval                             ;   
input   wire                    mpu_sta_dval                        ;   
input   wire    [17:0]          mpu_sta_data                        ;   

// declare output signal
output  reg     [15:0]          mpu_slot_sta1                       ;   
output  reg     [15:0]          mpu_slot_sta2                       ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg         [3:0]               slot_number                         ;   
reg         [3:0]               sta_dval_cnt                        ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// cs generator
//----------------------------------------------------------------------------------
always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        slot_number  <=   4'h0 ;
    end
    else begin
        if ( mpu_sta_dval == 1'b1 && mpu_sta_data[17] == 1'b1 ) begin
            slot_number  <=   mpu_sta_data[3:0] ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        sta_dval_cnt  <=   4'h0 ;
    end
    else begin
        if ( mpu_sta_dval == 1'b1 ) begin
            sta_dval_cnt  <=   sta_dval_cnt + 1'b1 ;
        end
        else begin
            sta_dval_cnt  <=   4'h0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// ex state frme parse
//----------------------------------------------------------------------------------
always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        mpu_slot_sta1  <=   16'h00 ;
    end
    else begin
        if ( rd_dval == 1'b0 && sta_dval_cnt == 4'd1 && slot_number[3:0] == SLOT_NUM ) begin
            mpu_slot_sta1  <=   mpu_sta_data[15:0] ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        mpu_slot_sta2  <=   16'h00 ;
    end
    else begin
        if ( rd_dval == 1'b0 && sta_dval_cnt == 4'd2 && slot_number[3:0] == SLOT_NUM ) begin
            mpu_slot_sta2  <=   mpu_sta_data[15:0] ;
        end
        else ;
    end
end

endmodule

