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

module  TYPE1_WR
    (
    clk_emif                    ,   
    rst_emif                    ,   

    cs_fall                     ,   
    wr_en                       ,   
    wr_addr                     ,   
    wr_data                     , 
    wr_eop                      ,   

    type1_wr_sel                ,   
    type1_wr_en                 ,   
    type1_wr_port               ,   
    type1_wr_data
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

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
output  reg                     type1_wr_sel                        ;   
output  reg                     type1_wr_en                         ;   
output  reg     [7:0]           type1_wr_port                       ;   
output  reg     [17:0]          type1_wr_data                       ; 

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
        type1_wr_sel    <=   1'b0 ;
    end
    else begin
        if ( wr_eop == 1'b1 ) begin
            type1_wr_sel   <=   1'b0 ;
        end
        else if( cs_fall_d1 == 1'b1 ) begin
            if( wr_addr[22] == 1'b0 && wr_addr[13] == 1'b0 ) begin 
                type1_wr_sel    <=   1'b1 ;
            end
            else begin
                type1_wr_sel    <=   1'b0 ;
            end
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        type1_wr_port    <=   8'h00 ;
    end
    else begin
        if( cs_fall == 1'b1 ) begin
            type1_wr_port    <=   wr_addr[21:14] ;
        end
    end
end

always @ ( posedge clk_emif ) begin
    type1_wr_en     <=   wr_en ;
    type1_wr_data   <=   wr_data ;
end

endmodule

