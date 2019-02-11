// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   RX_RR
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
// PURPOSE          :   reduced redundancy of RX path
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

module  RX_RR
    (
    // clock & reset
    clk_150m                    ,   
    rst_150m                    ,   

    slink_err                   ,   

    ex_box_data_ena0            ,   
    ex_box_data_ena1            ,   
    ex_box_data_ena2            ,   
    ex_box_data_ena3            ,  
    ex_box_cfg_ena0             ,   
    ex_box_cfg_ena1             ,   
    ex_box_cfg_ena2             ,   
    ex_box_cfg_ena3             ,   

    ex1_slot_sel                ,   
    ex2_slot_sel                ,   
    ex3_slot_sel                ,   
    ex4_slot_sel                ,   
    rr_sel0                     ,   
    rr_sel1                     ,   
    rr_sel2                     ,   
    rr_sel3                        

    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_150m                            ;   
input   wire                    rst_150m                            ;

input   wire        [3:0]       slink_err                           ;   
input   wire        [3:0]       ex_box_data_ena0                    ;   
input   wire        [3:0]       ex_box_data_ena1                    ;   
input   wire        [3:0]       ex_box_data_ena2                    ;   
input   wire        [3:0]       ex_box_data_ena3                    ;
input   wire        [3:0]       ex_box_cfg_ena0                     ;   
input   wire        [3:0]       ex_box_cfg_ena1                     ;   
input   wire        [3:0]       ex_box_cfg_ena2                     ;   
input   wire        [3:0]       ex_box_cfg_ena3                     ;   

// declare output signal
output  reg         [3:0]       ex1_slot_sel                        ;   
output  reg         [3:0]       ex2_slot_sel                        ;   
output  reg         [3:0]       ex3_slot_sel                        ;   
output  reg         [3:0]       ex4_slot_sel                        ;   
output  wire        [3:0]       rr_sel0                             ;   
output  wire        [3:0]       rr_sel1                             ;   
output  wire        [3:0]       rr_sel2                             ;   
output  wire        [3:0]       rr_sel3                             ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg         [3:0]               ex_box_data_ena0_d1                 ;   
reg         [3:0]               ex_box_data_ena1_d1                 ;   
reg         [3:0]               ex_box_data_ena2_d1                 ;   
reg         [3:0]               ex_box_data_ena3_d1                 ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        ex_box_data_ena0_d1  <=   4'h0 ;
        ex_box_data_ena1_d1  <=   4'h0 ;
        ex_box_data_ena2_d1  <=   4'h0 ;
        ex_box_data_ena3_d1  <=   4'h0 ;
    end
    else begin
        ex_box_data_ena0_d1  <=   ex_box_data_ena0 ;
        ex_box_data_ena1_d1  <=   ex_box_data_ena1 ;
        ex_box_data_ena2_d1  <=   ex_box_data_ena2 ;
        ex_box_data_ena3_d1  <=   ex_box_data_ena3 ;
    end
end

//----------------------------------------------------------------------------------
// rr generator
//----------------------------------------------------------------------------------
always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        ex1_slot_sel  <=   4'b0000 ;
    end
    else begin
        if ( ex_box_data_ena0_d1[0] == 1'b1 && slink_err[0] == 1'b0 ) begin
            ex1_slot_sel  <=   4'b0001 ;
        end
        else if ( ex_box_data_ena1_d1[0] == 1'b1 && slink_err[1] == 1'b0 ) begin
            ex1_slot_sel  <=   4'b0010 ;
        end
        else if ( ex_box_data_ena2_d1[0] == 1'b1 && slink_err[2] == 1'b0 ) begin
            ex1_slot_sel  <=   4'b0100 ;
        end
        else if ( ex_box_data_ena3_d1[0] == 1'b1 && slink_err[3] == 1'b0 ) begin
            ex1_slot_sel  <=   4'b1000 ;
        end
        else begin
            if ( ex_box_data_ena0_d1[0] == 1'b1 ) begin
                ex1_slot_sel  <=   4'b0001 ;
            end
            else if ( ex_box_data_ena1_d1[0] == 1'b1 ) begin
                ex1_slot_sel  <=   4'b0010 ;
            end
            else if ( ex_box_data_ena2_d1[0] == 1'b1 ) begin
                ex1_slot_sel  <=   4'b0100 ;
            end
            else if ( ex_box_data_ena3_d1[0] == 1'b1 ) begin
                ex1_slot_sel  <=   4'b1000 ;
            end
        end
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        ex2_slot_sel  <=   4'b0000 ;
    end
    else begin
        if ( ex_box_data_ena0_d1[1] == 1'b1 && slink_err[0] == 1'b0 ) begin
            ex2_slot_sel  <=   4'b0001 ;
        end
        else if ( ex_box_data_ena1_d1[1] == 1'b1 && slink_err[1] == 1'b0 ) begin
            ex2_slot_sel  <=   4'b0010 ;
        end
        else if ( ex_box_data_ena2_d1[1] == 1'b1 && slink_err[2] == 1'b0 ) begin
            ex2_slot_sel  <=   4'b0100 ;
        end
        else if ( ex_box_data_ena3_d1[1] == 1'b1 && slink_err[3] == 1'b0 ) begin
            ex2_slot_sel  <=   4'b1000 ;
        end
        else begin
            if ( ex_box_data_ena0_d1[1] == 1'b1 ) begin
                ex2_slot_sel  <=   4'b0001 ;
            end
            else if ( ex_box_data_ena1_d1[1] == 1'b1 ) begin
                ex2_slot_sel  <=   4'b0010 ;
            end
            else if ( ex_box_data_ena2_d1[1] == 1'b1 ) begin
                ex2_slot_sel  <=   4'b0100 ;
            end
            else if ( ex_box_data_ena3_d1[1] == 1'b1 ) begin
                ex2_slot_sel  <=   4'b1000 ;
            end
        end
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        ex3_slot_sel  <=   4'b0000 ;
    end
    else begin
        if ( ex_box_data_ena0_d1[2] == 1'b1 && slink_err[0] == 1'b0 ) begin
            ex3_slot_sel  <=   4'b0001 ;
        end
        else if ( ex_box_data_ena1_d1[2] == 1'b1 && slink_err[1] == 1'b0 ) begin
            ex3_slot_sel  <=   4'b0010 ;
        end
        else if ( ex_box_data_ena2_d1[2] == 1'b1 && slink_err[2] == 1'b0 ) begin
            ex3_slot_sel  <=   4'b0100 ;
        end
        else if ( ex_box_data_ena3_d1[2] == 1'b1 && slink_err[3] == 1'b0 ) begin
            ex3_slot_sel  <=   4'b1000 ;
        end
        else begin
            if ( ex_box_data_ena0_d1[2] == 1'b1 ) begin
                ex3_slot_sel  <=   4'b0001 ;
            end
            else if ( ex_box_data_ena1_d1[2] == 1'b1 ) begin
                ex3_slot_sel  <=   4'b0010 ;
            end
            else if ( ex_box_data_ena2_d1[2] == 1'b1 ) begin
                ex3_slot_sel  <=   4'b0100 ;
            end
            else if ( ex_box_data_ena3_d1[2] == 1'b1 ) begin
                ex3_slot_sel  <=   4'b1000 ;
            end
        end
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        ex4_slot_sel  <=   4'b0000 ;
    end
    else begin
        if ( ex_box_data_ena0_d1[3] == 1'b1 && slink_err[0] == 1'b0 ) begin
            ex4_slot_sel  <=   4'b0001 ;
        end
        else if ( ex_box_data_ena1_d1[3] == 1'b1 && slink_err[1] == 1'b0 ) begin
            ex4_slot_sel  <=   4'b0010 ;
        end
        else if ( ex_box_data_ena2_d1[3] == 1'b1 && slink_err[2] == 1'b0 ) begin
            ex4_slot_sel  <=   4'b0100 ;
        end
        else if ( ex_box_data_ena3_d1[3] == 1'b1 && slink_err[3] == 1'b0 ) begin
            ex4_slot_sel  <=   4'b1000 ;
        end
        else begin
            if ( ex_box_data_ena0_d1[3] == 1'b1 ) begin
                ex4_slot_sel  <=   4'b0001 ;
            end
            else if ( ex_box_data_ena1_d1[3] == 1'b1 ) begin
                ex4_slot_sel  <=   4'b0010 ;
            end
            else if ( ex_box_data_ena2_d1[3] == 1'b1 ) begin
                ex4_slot_sel  <=   4'b0100 ;
            end
            else if ( ex_box_data_ena3_d1[3] == 1'b1 ) begin
                ex4_slot_sel  <=   4'b1000 ;
            end
        end
    end
end

assign  rr_sel0 =   { ex4_slot_sel[0] , ex3_slot_sel[0] , ex2_slot_sel[0] , ex1_slot_sel[0] } ;
assign  rr_sel1 =   { ex4_slot_sel[1] , ex3_slot_sel[1] , ex2_slot_sel[1] , ex1_slot_sel[1] } ;
assign  rr_sel2 =   { ex4_slot_sel[2] , ex3_slot_sel[2] , ex2_slot_sel[2] , ex1_slot_sel[2] } ;
assign  rr_sel3 =   { ex4_slot_sel[3] , ex3_slot_sel[3] , ex2_slot_sel[3] , ex1_slot_sel[3] } ;


endmodule

