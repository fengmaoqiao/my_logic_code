// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SELF_CMM
// CREATE DATE      :   2017-09-07
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-07  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   The configuration Memory Management of MPU board self
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

module  EX_CASE_STA
    (
    // clock & reset
    clk_150m                    ,   
    rst_150m                    ,   

    // cfg
    ex_slot_sel                 ,  

    // connect to EMIF module
    ex_sta_rd_sel               ,   
    ex_rd_addr                  ,   
    ex_rd_data                  ,   

    // hot plug
    hot_plug_req                ,   

    // ex box online signal     
    ex_box_online0              ,
    ex_box_online1              ,
    ex_box_online2              ,
    ex_box_online3              ,

    // state frame
    slot2_sta_dval              ,   
    slot2_sta_data              ,   
    slot3_sta_dval              ,   
    slot3_sta_data              ,   
    slot4_sta_dval              ,   
    slot4_sta_data              ,   
    slot5_sta_dval              ,   
    slot5_sta_data                 
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

input   wire        [3:0]       ex_slot_sel                         ;   
input   wire                    ex_sta_rd_sel                       ;   
input   wire        [8:0]       ex_rd_addr                          ;   

input   wire                    slot2_sta_dval                      ;   
input   wire        [17:0]      slot2_sta_data                      ;   
input   wire                    slot3_sta_dval                      ;   
input   wire        [17:0]      slot3_sta_data                      ;   
input   wire                    slot4_sta_dval                      ;   
input   wire        [17:0]      slot4_sta_data                      ;   
input   wire                    slot5_sta_dval                      ;   
input   wire        [17:0]      slot5_sta_data                      ; 

input   wire        [14:0]      ex_box_online0                      ;
input   wire        [14:0]      ex_box_online1                      ;
input   wire        [14:0]      ex_box_online2                      ;
input   wire        [14:0]      ex_box_online3                      ;

// declare output signal
output  reg         [15:0]      ex_rd_data                          ;   
output  wire        [15:0]      hot_plug_req                        ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [15:0]              ex_slot_sta1    [15:0]              ;   
wire        [15:0]              ex_slot_sta2    [15:0]              ;   

// reg signal
reg                             ex_sta_dval                         ;   
reg         [17:0]              ex_sta_data                         ;   

// debug
reg         [15:0]              ex_online_rd                        ;
/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        ex_online_rd    <=   16'h00 ;
    end
    else if( ex_sta_rd_sel == 1'b1 ) begin
        case( ex_rd_addr )
            9'd1    :   ex_online_rd <=   ex_slot_sta2[0] ;
            default :   ;
        endcase
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        ex_rd_data    <=   16'h00 ;
    end
    else if( ex_sta_rd_sel == 1'b1 ) begin
        case( ex_rd_addr )
            9'd0    :   ex_rd_data <=   { ex_slot_sta1[0][7:0]  , ex_slot_sta1[0][15:8] } ;
            9'd1    :   ex_rd_data <=   16'd0 ;

            9'd2    :   ex_rd_data <=   { ex_slot_sta1[1][7:0]  , ex_slot_sta1[1][15:8] } ;
            9'd3    :   ex_rd_data <=   16'd0 ;

            9'd4    :   ex_rd_data <=   { ex_slot_sta1[2][7:0]  , ex_slot_sta1[2][15:7] , ex_online_rd[0] } ;
            9'd5    :   ex_rd_data <=   { ex_slot_sta2[2][7:0]  , ex_slot_sta2[2][15:8] } ;

            9'd6    :   ex_rd_data <=   { ex_slot_sta1[3][7:0]  , ex_slot_sta1[3][15:7] , ex_online_rd[1] } ;
            9'd7    :   ex_rd_data <=   { ex_slot_sta2[3][7:0]  , ex_slot_sta2[3][15:8] } ;

            9'd8    :   ex_rd_data <=   { ex_slot_sta1[4][7:0]  , ex_slot_sta1[4][15:7] , ex_online_rd[2] } ;
            9'd9    :   ex_rd_data <=   { ex_slot_sta2[4][7:0]  , ex_slot_sta2[4][15:8] } ;

            9'd10   :   ex_rd_data <=   { ex_slot_sta1[5][7:0]  , ex_slot_sta1[5][15:7] , ex_online_rd[3] } ;
            9'd11   :   ex_rd_data <=   { ex_slot_sta2[5][7:0]  , ex_slot_sta2[5][15:8] } ;

            9'd12   :   ex_rd_data <=   { ex_slot_sta1[6][7:0]  , ex_slot_sta1[6][15:7] , ex_online_rd[4] } ;
            9'd13   :   ex_rd_data <=   { ex_slot_sta2[6][7:0]  , ex_slot_sta2[6][15:8] } ;

            9'd14   :   ex_rd_data <=   { ex_slot_sta1[7][7:0]  , ex_slot_sta1[7][15:7] , ex_online_rd[5] } ;
            9'd15   :   ex_rd_data <=   { ex_slot_sta2[7][7:0]  , ex_slot_sta2[7][15:8] } ;

            9'd16   :   ex_rd_data <=   { ex_slot_sta1[8][7:0]  , ex_slot_sta1[8][15:7] , ex_online_rd[6] } ;
            9'd17   :   ex_rd_data <=   { ex_slot_sta2[8][7:0]  , ex_slot_sta2[8][15:8] } ;

            9'd18   :   ex_rd_data <=   { ex_slot_sta1[9][7:0]  , ex_slot_sta1[9][15:7] , ex_online_rd[7] } ;
            9'd19   :   ex_rd_data <=   { ex_slot_sta2[9][7:0]  , ex_slot_sta2[9][15:8] } ;

            9'd20   :   ex_rd_data <=   { ex_slot_sta1[10][7:0] , ex_slot_sta1[10][15:7] , ex_online_rd[8] } ;
            9'd21   :   ex_rd_data <=   { ex_slot_sta2[10][7:0] , ex_slot_sta2[10][15:8] } ;

            9'd22   :   ex_rd_data <=   { ex_slot_sta1[11][7:0] , ex_slot_sta1[11][15:7] , ex_online_rd[9] } ;
            9'd23   :   ex_rd_data <=   { ex_slot_sta2[11][7:0] , ex_slot_sta2[11][15:8] } ;

            9'd24   :   ex_rd_data <=   { ex_slot_sta1[12][7:0] , ex_slot_sta1[12][15:7] , ex_online_rd[10] } ;
            9'd25   :   ex_rd_data <=   { ex_slot_sta2[12][7:0] , ex_slot_sta2[12][15:8] } ;

            9'd26   :   ex_rd_data <=   { ex_slot_sta1[13][7:0] , ex_slot_sta1[13][15:7] , ex_online_rd[11] } ;
            9'd27   :   ex_rd_data <=   { ex_slot_sta2[13][7:0] , ex_slot_sta2[13][15:8] } ;

            9'd28   :   ex_rd_data <=   { ex_slot_sta1[14][7:0] , ex_slot_sta1[14][15:7] , ex_online_rd[12] } ;
            9'd29   :   ex_rd_data <=   { ex_slot_sta2[14][7:0] , ex_slot_sta2[14][15:8] } ;

            9'd30   :   ex_rd_data <=   { ex_slot_sta1[15][7:0] , ex_slot_sta1[15][15:7] , ex_online_rd[13] } ;
            9'd31   :   ex_rd_data <=   { ex_slot_sta2[15][7:0] , ex_slot_sta2[15][15:8] } ;
            default :   ex_rd_data <=   16'h00 ; 
        endcase
    end
    else begin
        ex_rd_data    <=   16'h00 ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        ex_sta_dval  <=   1'b0 ;
    end
    else begin
        if ( ex_slot_sel[0] == 1'b1 ) begin
            ex_sta_dval  <=   slot2_sta_dval ;
        end
        else if ( ex_slot_sel[1] == 1'b1 ) begin
            ex_sta_dval  <=   slot3_sta_dval ;
        end
        else if ( ex_slot_sel[2] == 1'b1 ) begin
            ex_sta_dval  <=   slot4_sta_dval ;
        end
        else if ( ex_slot_sel[3] == 1'b1 ) begin
            ex_sta_dval  <=   slot5_sta_dval ;
        end
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if ( rst_150m == 1'b0 ) begin
        ex_sta_data  <=   17'h00 ;
    end
    else begin
        if ( ex_slot_sel[0] == 1'b1 ) begin
            ex_sta_data  <=   slot2_sta_data ;
        end
        else if ( ex_slot_sel[1] == 1'b1 ) begin
            ex_sta_data  <=   slot3_sta_data ;
        end
        else if ( ex_slot_sel[2] == 1'b1 ) begin
            ex_sta_data  <=   slot4_sta_data ;
        end
        else if ( ex_slot_sel[3] == 1'b1 ) begin
            ex_sta_data  <=   slot5_sta_data ;
        end
    end
end


//----------------------------------------------------------------------------------
// EX case status
//----------------------------------------------------------------------------------
  genvar i ;
  generate
  for( i = 0 ; i < 16 ; i = i+1 ) 
  begin : Nsta

    EX_STA                      #
    (
    .SLOT_NUM                   ( i                         )
    )
    U_EX_STA
    (
    .clk_150m                   ( clk_150m                  ),
    .rst_150m                   ( rst_150m                  ),
    .rd_dval                    ( ex_sta_rd_sel             ),
    .ex_sta_dval                ( ex_sta_dval               ),
    .ex_sta_data                ( ex_sta_data               ),
    .hot_plug_req               ( hot_plug_req[i]           ),
    .ex_slot_sta1               ( ex_slot_sta1[i]           ),
    .ex_slot_sta2               ( ex_slot_sta2[i]           )
    );

  end
  endgenerate


endmodule

