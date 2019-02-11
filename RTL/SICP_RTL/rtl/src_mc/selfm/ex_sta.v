// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   EX_STA
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

module  EX_STA
    (
    // clock & reset
    clk_150m                    ,   
    rst_150m                    ,   

    rd_dval                     ,   
    ex_sta_dval                 ,   
    ex_sta_data                 ,   

    hot_plug_req                ,   
    ex_slot_sta1                ,   
    ex_slot_sta2                 
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   SLOT_NUM  =   4'b0000 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_150m                            ;   
input   wire                    rst_150m                            ;

input   wire                    rd_dval                             ;   
input   wire                    ex_sta_dval                         ;   
input   wire    [17:0]          ex_sta_data                         ;   

// declare output signal
output  reg                     hot_plug_req                        ;   
output  reg     [15:0]          ex_slot_sta1                        ;   
output  reg     [15:0]          ex_slot_sta2                        ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg         [3:0]               ex_slot_num                         ;   
reg         [3:0]               sta_dval_cnt                        ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        ex_slot_num  <=   4'h0 ;
    end
    else begin
        if ( ex_sta_dval == 1'b1 && ex_sta_data[17] == 1'b1 ) begin
            ex_slot_num  <=   ex_sta_data[3:0] ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        sta_dval_cnt  <=   4'h0 ;
    end
    else begin
        if ( ex_sta_dval == 1'b1 ) begin
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
        hot_plug_req  <=   1'b0 ;
    end
    else begin
        if ( ex_sta_dval == 1'b0 ) begin
            hot_plug_req  <=   1'b0 ;
        end
        else if ( sta_dval_cnt == 4'd1 && ex_slot_num == SLOT_NUM && ex_sta_data[15] == 1'b1 ) begin
            hot_plug_req  <=   1'b1 ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        ex_slot_sta1  <=   16'h00 ;
    end
    else begin
        if ( rd_dval == 1'b0 && sta_dval_cnt == 4'd1 && ex_slot_num == SLOT_NUM ) begin
            ex_slot_sta1  <=   ex_sta_data[15:0] ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        ex_slot_sta2  <=   16'h00 ;
    end
    else begin
        if ( rd_dval == 1'b0 && sta_dval_cnt == 4'd2 && ex_slot_num == SLOT_NUM ) begin
            ex_slot_sta2  <=   ex_sta_data[15:0] ;
        end
        else ;
    end
end


endmodule

