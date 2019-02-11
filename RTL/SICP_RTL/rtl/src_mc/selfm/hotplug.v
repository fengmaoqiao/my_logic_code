// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   HOTPLUG
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

module  HOTPLUG
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   

    other_online                ,
    hot_plug_req                ,   
    
    debug_bus 
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   
input   wire                    other_online                        ;   

// declare output signal
output  wire                    hot_plug_req                        ;   
output  wire        [15:0]      debug_bus                           ;  

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            online_detect                       ;  
wire                            online_ring_detect                  ;   

// reg signal
reg         [31:0]              online_dly                          ;
reg                             online_detect_d1                    ;   
reg                             online_detect_d2                    ; 
reg                             hot_plug_flag                       ;  
reg         [24:0]              cfg_delay_cnt                       ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// debouncing
//----------------------------------------------------------------------------------

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        online_dly  <=   32'hffffffff ;
    end
    else begin
        online_dly  <=   { online_dly[30:0] , other_online } ;
    end
end

assign  online_detect =  & online_dly  ;

//----------------------------------------------------------------------------------
// falling edge detect
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        online_detect_d1  <=   1'b1 ;
        online_detect_d2  <=   1'b1 ;
    end
    else begin
        online_detect_d1  <=   online_detect ;
        online_detect_d2  <=   online_detect_d1 ;
    end
end

assign  online_ring_detect = ( online_detect_d1 == 1'b1 && online_detect_d2 == 1'b0 ) ? 1'b1 : 1'b0 ;

//----------------------------------------------------------------------------------
// hot_plug request generator
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        hot_plug_flag    <=   1'b0 ;
    end
    else begin
        if( cfg_delay_cnt[24] == 1'b1 ) begin
            hot_plug_flag    <=   1'b0 ;
        end
        else if( online_ring_detect == 1'b1 ) begin
            hot_plug_flag    <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        cfg_delay_cnt    <=   25'h00 ;
    end
    else begin
        if( hot_plug_flag == 1'b1 ) begin
            cfg_delay_cnt    <=   cfg_delay_cnt + 1'b1 ;
        end
        else begin
            cfg_delay_cnt    <=   25'h00 ;
        end
    end
end

assign  hot_plug_req = cfg_delay_cnt[24] == 1'b1 ? 1'b1 : 1'b0 ;  

endmodule

