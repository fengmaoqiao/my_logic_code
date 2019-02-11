// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   CRC8D8
// CREATE DATE      :   2018-05-29
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-08-24  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   polynomial: x^8 + x^2 + x^1 + 1
//                      data width: 8 
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active hign
// Clock Domains    :   clk_125m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`timescale 1 ns / 1 ps
module CRC8D8
    (
    //input port
    clk_sys                     ,   
    rst_sys                     ,   

    crc_din                     ,   
    crc_cap                     ,   
    crc_sop                     ,   
    crc_din_vld                 ,   

    //output port
    crc_dout            
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input                           clk_sys                             ;   
input                           rst_sys                             ;   
input   [7:0]                   crc_din                             ;   
input                           crc_cap                             ;   
input                           crc_sop                             ;   
input                           crc_din_vld                         ;   

// declare output signal
output  [7:0]                   crc_dout                            ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [7:0]                   new_crc                             ;   
wire    [7:0]                   crc_dout                            ;   

// reg signal
reg     [7:0]                   crc_tmp                             ;   
reg     [7:0]                   cap_data                            ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign  crc_dout    = cap_data ; 

// crc_tmp
always @( posedge clk_sys or negedge rst_sys ) begin
    if( rst_sys == 1'b0 ) begin
        crc_tmp <=  { 8{1'b0} };
    end
    else begin
        if( crc_sop == 1'b1 ) begin
            crc_tmp <=  { 8{1'b0} };
        end
        else if( crc_din_vld == 1'b1 ) begin
            crc_tmp <=  new_crc ;
        end
        else ;
    end
end

// cap_data
always @( posedge clk_sys or negedge rst_sys ) begin
    if( rst_sys == 1'b0 ) begin 
        cap_data <=   8'h00 ;
    end
    else begin 
        if( crc_cap == 1'b1 ) begin
            cap_data <=  new_crc ;
        end
        else ;
    end
end

assign    new_crc[0] = crc_din[7] ^ crc_din[6] ^ crc_din[0] ^ crc_tmp[0] ^ crc_tmp[6] ^ crc_tmp[7];
assign    new_crc[1] = crc_din[6] ^ crc_din[1] ^ crc_din[0] ^ crc_tmp[0] ^ crc_tmp[1] ^ crc_tmp[6];
assign    new_crc[2] = crc_din[6] ^ crc_din[2] ^ crc_din[1] ^ crc_din[0] ^ crc_tmp[0] ^ crc_tmp[1] ^ crc_tmp[2] ^ crc_tmp[6];
assign    new_crc[3] = crc_din[7] ^ crc_din[3] ^ crc_din[2] ^ crc_din[1] ^ crc_tmp[1] ^ crc_tmp[2] ^ crc_tmp[3] ^ crc_tmp[7];
assign    new_crc[4] = crc_din[4] ^ crc_din[3] ^ crc_din[2] ^ crc_tmp[2] ^ crc_tmp[3] ^ crc_tmp[4];
assign    new_crc[5] = crc_din[5] ^ crc_din[4] ^ crc_din[3] ^ crc_tmp[3] ^ crc_tmp[4] ^ crc_tmp[5];
assign    new_crc[6] = crc_din[6] ^ crc_din[5] ^ crc_din[4] ^ crc_tmp[4] ^ crc_tmp[5] ^ crc_tmp[6];
assign    new_crc[7] = crc_din[7] ^ crc_din[6] ^ crc_din[5] ^ crc_tmp[5] ^ crc_tmp[6] ^ crc_tmp[7];

endmodule
