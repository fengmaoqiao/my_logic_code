// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SDU2S1
// CREATE DATE      :   2017-08-23
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-23  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   2 select 1 schedule machine
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

module SDU2S1
    (
    clk_sys                     ,   
    rst_sys                     ,   
   
    chip_cs                     ,   
    chn_sdu_dval                ,    
    chn_sdu_data                ,    
    chn_sdu_empty               ,  
    sdu_chn_rden                ,

    debug_bus
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   CHN_NUM         =   2  ; // 5 - 1 schedule
parameter   CHN_NUM_WIDTH   =   1  ;
parameter   DATA_WIDTH      =   18 ; // [17] : sop [16] : eop [15:0] : data  

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    rst_sys                             ;   
input   wire                    chip_cs                             ;   
input   wire    [CHN_NUM-1:0]   chn_sdu_dval  	                    ;   
input   wire    [DATA_WIDTH-1:0]chn_sdu_data    	                ;   
input   wire    [CHN_NUM-1:0]   chn_sdu_empty  	                    ;   

// declare output signal
output  wire    [CHN_NUM-1:0]   sdu_chn_rden   	                    ; 
output  wire    [15:0]          debug_bus                           ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [CHN_NUM-1:0]       chn_eop_flag                        ;   
wire                            eop_flag                            ;   
wire                            rden_act                            ;   
wire                            rd_req                              ;   
wire        [CHN_NUM-1:0]       chn_rden   	                        ;   
wire        [CHN_NUM-1:0]       sdu_turn_empty  	                ;   

// reg signal
reg         [CHN_NUM_WIDTH-1:0] sdu_num                             ;   
reg                             eop_all_empty                       ;   
reg                             all_empty                           ;   
reg         [CHN_NUM-1:0]       sdu_empty                           ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

assign  sdu_turn_empty =   { chn_sdu_empty[0] , chn_sdu_empty[1] };

genvar i;
generate
for( i = 0 ; i < CHN_NUM ; i = i+1 ) 
begin : nCHN

assign  chn_eop_flag[i] = ( chn_sdu_dval[i] == 1'b1 && chn_sdu_data[DATA_WIDTH-2] == 1'b1 ) ? 1'b1 : 1'b0 ;
assign  sdu_chn_rden[i] = ( chn_sdu_empty[i] == 1'b0 && sdu_num == i && rd_req == 1'b1 ) ? 1'b1 : 1'b0 ;
assign  chn_rden[i] = ( chn_sdu_empty[i] == 1'b0 && sdu_num == i ) ? 1'b1 : 1'b0 ;

end
endgenerate

always @( posedge clk_sys or negedge rst_sys ) begin
    if( rst_sys == 1'b0 ) begin
        sdu_num <= #`U_DLY  1'b0 ;
    end
    else if( all_empty == 1'b1 ) begin
        if( chn_sdu_empty[0] == 1'b0 ) begin
            sdu_num <= #`U_DLY  1'b0 ;    
        end
        else if( chn_sdu_empty[1] == 1'b0 ) begin
            sdu_num <= #`U_DLY  1'b1 ;
        end
    end
    else if( eop_flag == 1'b1 ||( eop_all_empty == 1'b1 && rden_act == 1'b0 ) ) begin
        if( sdu_empty[1] == 1'b0 ) begin
            sdu_num <= #`U_DLY  sdu_num + 1'b1 ;
        end
        else begin
            sdu_num <= #`U_DLY  sdu_num ;
        end
    end 
end

always @( * ) begin
    case( sdu_num )
        1'b0    :   sdu_empty    =  { sdu_turn_empty[0], sdu_turn_empty[1] } ;
        1'b1    :   sdu_empty    =  sdu_turn_empty ;
        default :   sdu_empty    =  sdu_turn_empty ;
    endcase
end

assign  eop_flag = | chn_eop_flag ;
assign  rden_act = | chn_rden ;
assign  rd_req   = ( chip_cs == 1'b1 && all_empty == 1'b0 ) ? 1'b1 : 1'b0 ;

always @( posedge clk_sys or negedge rst_sys ) begin
    if( rst_sys == 1'b0 ) begin
        all_empty   <= #`U_DLY  1'b0 ;
    end
    else if( & chn_sdu_empty == 1'b1 ) begin
        all_empty   <= #`U_DLY  1'b1 ;   
    end
    else begin
        all_empty   <= #`U_DLY  1'b0 ;
    end
end

always @( posedge clk_sys or negedge rst_sys ) begin
    if( rst_sys == 1'b0 ) begin
        eop_all_empty   <= #`U_DLY  1'b0 ;   
    end
    else begin
        if( eop_all_empty == 1'b1 && all_empty == 1'b0 ) begin
            eop_all_empty   <= #`U_DLY  1'b0 ;
        end
        else if( eop_flag == 1'b1 && ( & sdu_empty[CHN_NUM-1:1] == 1'b1 ) ) begin
            eop_all_empty   <= #`U_DLY  1'b1 ;
        end
        else ;
    end
end


endmodule
