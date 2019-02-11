// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   EMIF_WR
// CREATE DATE      :   2017-08-19
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-19  TingtingGan     Original
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

module  TYPE2_WR
    (
    clk_emif                    ,   
    rst_emif                    ,   

    cs_fall                     ,   
    wr_en                       ,   
    wr_addr                     ,   
    wr_data                     , 
    wr_eop                      ,   

    type2_wr_sel                ,   
    type2_wr_en                 ,   
    type2_wr_port               ,   
    type2_wr_data
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   SLOT_NUM    =   4'd0 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_emif                            ;   
input   wire                    rst_emif                            ;

input   wire                    cs_fall                             ;   
input   wire                    wr_en                               ;   
input   wire    [22:0]          wr_addr                             ;   
input   wire    [17:0]          wr_data                             ;  
input   wire                    wr_eop                              ;   
                                                    
// declare output signal
output  reg                     type2_wr_sel                        ;   
output  reg                     type2_wr_en                         ;   
output  reg     [2:0]           type2_wr_port                       ;   
output  reg     [17:0]          type2_wr_data                       ; 

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg                             cs_fall_d1                          ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
always @ ( posedge clk_emif ) begin
    cs_fall_d1     <=   cs_fall ;
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        type2_wr_sel    <=   1'b0 ;
    end
    else begin
        if ( wr_eop == 1'b1 ) begin
            type2_wr_sel   <=   1'b0 ;
        end
        else if( cs_fall_d1 == 1'b1 ) begin
            if( wr_addr[22:21] == 2'b00 && wr_addr[18:15] == SLOT_NUM && wr_addr[13] == 1'b0 ) begin 
                type2_wr_sel    <=   1'b1 ;
            end
            else begin
                type2_wr_sel    <=   1'b0 ;
            end
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        type2_wr_port    <=   3'b000 ;
    end
    else begin
        if( cs_fall == 1'b1 ) begin
            type2_wr_port    <=   { wr_addr[20:19] , wr_addr[14] } ;
        end
    end
end

always @ ( posedge clk_emif ) begin
    type2_wr_en     <=   wr_en ;
    type2_wr_data   <=   wr_data ;
end

endmodule

