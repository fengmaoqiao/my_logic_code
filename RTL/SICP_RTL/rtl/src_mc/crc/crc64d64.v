// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   CRC64D64
// CREATE DATE      :   2017-08-24
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
// PURPOSE          :   polynomial: x^64 + x^4 + x^3 + x^1 + 1
//                      data width: 64 
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

module CRC64D64
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
input   [63:0]                  crc_din                             ;   
input                           crc_cap                             ;   
input                           crc_sop                             ;   
input                           crc_din_vld                         ;   

// declare output signal
output  [63:0]                  crc_dout                            ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [63:0]                  new_crc                             ;   
wire    [63:0]                  crc_dout                            ;   

// reg signal
reg     [63:0]                  crc_tmp                             ;   
reg     [63:0]                  cap_data                            ;   

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
        crc_tmp <=  { 64{1'b1} };
    end
    else begin
        if( crc_sop == 1'b1 ) begin
            crc_tmp <=  { 64{1'b1} };
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
        cap_data <=   64'h00 ;
    end
    else begin 
        if( crc_cap == 1'b1 ) begin
            cap_data <=  new_crc ;
        end
        else ;
    end
end

assign    new_crc[0] = crc_din[63] ^ crc_din[61] ^ crc_din[60] ^ crc_din[0] ^ crc_tmp[0] ^ crc_tmp[60] ^ crc_tmp[61] ^ crc_tmp[63];
assign    new_crc[1] = crc_din[63] ^ crc_din[62] ^ crc_din[60] ^ crc_din[1] ^ crc_din[0] ^ crc_tmp[0] ^ crc_tmp[1] ^ crc_tmp[60] ^ crc_tmp[62] ^ crc_tmp[63];
assign    new_crc[2] = crc_din[63] ^ crc_din[61] ^ crc_din[2] ^ crc_din[1] ^ crc_tmp[1] ^ crc_tmp[2] ^ crc_tmp[61] ^ crc_tmp[63];
assign    new_crc[3] = crc_din[63] ^ crc_din[62] ^ crc_din[61] ^ crc_din[60] ^ crc_din[3] ^ crc_din[2] ^ crc_din[0] ^ crc_tmp[0] ^ crc_tmp[2] ^ crc_tmp[3] ^ crc_tmp[60] ^ crc_tmp[61] ^ crc_tmp[62] ^ crc_tmp[63];
assign    new_crc[4] = crc_din[62] ^ crc_din[60] ^ crc_din[4] ^ crc_din[3] ^ crc_din[1] ^ crc_din[0] ^ crc_tmp[0] ^ crc_tmp[1] ^ crc_tmp[3] ^ crc_tmp[4] ^ crc_tmp[60] ^ crc_tmp[62];
assign    new_crc[5] = crc_din[63] ^ crc_din[61] ^ crc_din[5] ^ crc_din[4] ^ crc_din[2] ^ crc_din[1] ^ crc_tmp[1] ^ crc_tmp[2] ^ crc_tmp[4] ^ crc_tmp[5] ^ crc_tmp[61] ^ crc_tmp[63];
assign    new_crc[6] = crc_din[62] ^ crc_din[6] ^ crc_din[5] ^ crc_din[3] ^ crc_din[2] ^ crc_tmp[2] ^ crc_tmp[3] ^ crc_tmp[5] ^ crc_tmp[6] ^ crc_tmp[62];
assign    new_crc[7] = crc_din[63] ^ crc_din[7] ^ crc_din[6] ^ crc_din[4] ^ crc_din[3] ^ crc_tmp[3] ^ crc_tmp[4] ^ crc_tmp[6] ^ crc_tmp[7] ^ crc_tmp[63];
assign    new_crc[8] = crc_din[8] ^ crc_din[7] ^ crc_din[5] ^ crc_din[4] ^ crc_tmp[4] ^ crc_tmp[5] ^ crc_tmp[7] ^ crc_tmp[8];
assign    new_crc[9] = crc_din[9] ^ crc_din[8] ^ crc_din[6] ^ crc_din[5] ^ crc_tmp[5] ^ crc_tmp[6] ^ crc_tmp[8] ^ crc_tmp[9];
assign    new_crc[10] = crc_din[10] ^ crc_din[9] ^ crc_din[7] ^ crc_din[6] ^ crc_tmp[6] ^ crc_tmp[7] ^ crc_tmp[9] ^ crc_tmp[10];
assign    new_crc[11] = crc_din[11] ^ crc_din[10] ^ crc_din[8] ^ crc_din[7] ^ crc_tmp[7] ^ crc_tmp[8] ^ crc_tmp[10] ^ crc_tmp[11];
assign    new_crc[12] = crc_din[12] ^ crc_din[11] ^ crc_din[9] ^ crc_din[8] ^ crc_tmp[8] ^ crc_tmp[9] ^ crc_tmp[11] ^ crc_tmp[12];
assign    new_crc[13] = crc_din[13] ^ crc_din[12] ^ crc_din[10] ^ crc_din[9] ^ crc_tmp[9] ^ crc_tmp[10] ^ crc_tmp[12] ^ crc_tmp[13];
assign    new_crc[14] = crc_din[14] ^ crc_din[13] ^ crc_din[11] ^ crc_din[10] ^ crc_tmp[10] ^ crc_tmp[11] ^ crc_tmp[13] ^ crc_tmp[14];
assign    new_crc[15] = crc_din[15] ^ crc_din[14] ^ crc_din[12] ^ crc_din[11] ^ crc_tmp[11] ^ crc_tmp[12] ^ crc_tmp[14] ^ crc_tmp[15];
assign    new_crc[16] = crc_din[16] ^ crc_din[15] ^ crc_din[13] ^ crc_din[12] ^ crc_tmp[12] ^ crc_tmp[13] ^ crc_tmp[15] ^ crc_tmp[16];
assign    new_crc[17] = crc_din[17] ^ crc_din[16] ^ crc_din[14] ^ crc_din[13] ^ crc_tmp[13] ^ crc_tmp[14] ^ crc_tmp[16] ^ crc_tmp[17];
assign    new_crc[18] = crc_din[18] ^ crc_din[17] ^ crc_din[15] ^ crc_din[14] ^ crc_tmp[14] ^ crc_tmp[15] ^ crc_tmp[17] ^ crc_tmp[18];
assign    new_crc[19] = crc_din[19] ^ crc_din[18] ^ crc_din[16] ^ crc_din[15] ^ crc_tmp[15] ^ crc_tmp[16] ^ crc_tmp[18] ^ crc_tmp[19];
assign    new_crc[20] = crc_din[20] ^ crc_din[19] ^ crc_din[17] ^ crc_din[16] ^ crc_tmp[16] ^ crc_tmp[17] ^ crc_tmp[19] ^ crc_tmp[20];
assign    new_crc[21] = crc_din[21] ^ crc_din[20] ^ crc_din[18] ^ crc_din[17] ^ crc_tmp[17] ^ crc_tmp[18] ^ crc_tmp[20] ^ crc_tmp[21];
assign    new_crc[22] = crc_din[22] ^ crc_din[21] ^ crc_din[19] ^ crc_din[18] ^ crc_tmp[18] ^ crc_tmp[19] ^ crc_tmp[21] ^ crc_tmp[22];
assign    new_crc[23] = crc_din[23] ^ crc_din[22] ^ crc_din[20] ^ crc_din[19] ^ crc_tmp[19] ^ crc_tmp[20] ^ crc_tmp[22] ^ crc_tmp[23];
assign    new_crc[24] = crc_din[24] ^ crc_din[23] ^ crc_din[21] ^ crc_din[20] ^ crc_tmp[20] ^ crc_tmp[21] ^ crc_tmp[23] ^ crc_tmp[24];
assign    new_crc[25] = crc_din[25] ^ crc_din[24] ^ crc_din[22] ^ crc_din[21] ^ crc_tmp[21] ^ crc_tmp[22] ^ crc_tmp[24] ^ crc_tmp[25];
assign    new_crc[26] = crc_din[26] ^ crc_din[25] ^ crc_din[23] ^ crc_din[22] ^ crc_tmp[22] ^ crc_tmp[23] ^ crc_tmp[25] ^ crc_tmp[26];
assign    new_crc[27] = crc_din[27] ^ crc_din[26] ^ crc_din[24] ^ crc_din[23] ^ crc_tmp[23] ^ crc_tmp[24] ^ crc_tmp[26] ^ crc_tmp[27];
assign    new_crc[28] = crc_din[28] ^ crc_din[27] ^ crc_din[25] ^ crc_din[24] ^ crc_tmp[24] ^ crc_tmp[25] ^ crc_tmp[27] ^ crc_tmp[28];
assign    new_crc[29] = crc_din[29] ^ crc_din[28] ^ crc_din[26] ^ crc_din[25] ^ crc_tmp[25] ^ crc_tmp[26] ^ crc_tmp[28] ^ crc_tmp[29];
assign    new_crc[30] = crc_din[30] ^ crc_din[29] ^ crc_din[27] ^ crc_din[26] ^ crc_tmp[26] ^ crc_tmp[27] ^ crc_tmp[29] ^ crc_tmp[30];
assign    new_crc[31] = crc_din[31] ^ crc_din[30] ^ crc_din[28] ^ crc_din[27] ^ crc_tmp[27] ^ crc_tmp[28] ^ crc_tmp[30] ^ crc_tmp[31];
assign    new_crc[32] = crc_din[32] ^ crc_din[31] ^ crc_din[29] ^ crc_din[28] ^ crc_tmp[28] ^ crc_tmp[29] ^ crc_tmp[31] ^ crc_tmp[32];
assign    new_crc[33] = crc_din[33] ^ crc_din[32] ^ crc_din[30] ^ crc_din[29] ^ crc_tmp[29] ^ crc_tmp[30] ^ crc_tmp[32] ^ crc_tmp[33];
assign    new_crc[34] = crc_din[34] ^ crc_din[33] ^ crc_din[31] ^ crc_din[30] ^ crc_tmp[30] ^ crc_tmp[31] ^ crc_tmp[33] ^ crc_tmp[34];
assign    new_crc[35] = crc_din[35] ^ crc_din[34] ^ crc_din[32] ^ crc_din[31] ^ crc_tmp[31] ^ crc_tmp[32] ^ crc_tmp[34] ^ crc_tmp[35];
assign    new_crc[36] = crc_din[36] ^ crc_din[35] ^ crc_din[33] ^ crc_din[32] ^ crc_tmp[32] ^ crc_tmp[33] ^ crc_tmp[35] ^ crc_tmp[36];
assign    new_crc[37] = crc_din[37] ^ crc_din[36] ^ crc_din[34] ^ crc_din[33] ^ crc_tmp[33] ^ crc_tmp[34] ^ crc_tmp[36] ^ crc_tmp[37];
assign    new_crc[38] = crc_din[38] ^ crc_din[37] ^ crc_din[35] ^ crc_din[34] ^ crc_tmp[34] ^ crc_tmp[35] ^ crc_tmp[37] ^ crc_tmp[38];
assign    new_crc[39] = crc_din[39] ^ crc_din[38] ^ crc_din[36] ^ crc_din[35] ^ crc_tmp[35] ^ crc_tmp[36] ^ crc_tmp[38] ^ crc_tmp[39];
assign    new_crc[40] = crc_din[40] ^ crc_din[39] ^ crc_din[37] ^ crc_din[36] ^ crc_tmp[36] ^ crc_tmp[37] ^ crc_tmp[39] ^ crc_tmp[40];
assign    new_crc[41] = crc_din[41] ^ crc_din[40] ^ crc_din[38] ^ crc_din[37] ^ crc_tmp[37] ^ crc_tmp[38] ^ crc_tmp[40] ^ crc_tmp[41];
assign    new_crc[42] = crc_din[42] ^ crc_din[41] ^ crc_din[39] ^ crc_din[38] ^ crc_tmp[38] ^ crc_tmp[39] ^ crc_tmp[41] ^ crc_tmp[42];
assign    new_crc[43] = crc_din[43] ^ crc_din[42] ^ crc_din[40] ^ crc_din[39] ^ crc_tmp[39] ^ crc_tmp[40] ^ crc_tmp[42] ^ crc_tmp[43];
assign    new_crc[44] = crc_din[44] ^ crc_din[43] ^ crc_din[41] ^ crc_din[40] ^ crc_tmp[40] ^ crc_tmp[41] ^ crc_tmp[43] ^ crc_tmp[44];
assign    new_crc[45] = crc_din[45] ^ crc_din[44] ^ crc_din[42] ^ crc_din[41] ^ crc_tmp[41] ^ crc_tmp[42] ^ crc_tmp[44] ^ crc_tmp[45];
assign    new_crc[46] = crc_din[46] ^ crc_din[45] ^ crc_din[43] ^ crc_din[42] ^ crc_tmp[42] ^ crc_tmp[43] ^ crc_tmp[45] ^ crc_tmp[46];
assign    new_crc[47] = crc_din[47] ^ crc_din[46] ^ crc_din[44] ^ crc_din[43] ^ crc_tmp[43] ^ crc_tmp[44] ^ crc_tmp[46] ^ crc_tmp[47];
assign    new_crc[48] = crc_din[48] ^ crc_din[47] ^ crc_din[45] ^ crc_din[44] ^ crc_tmp[44] ^ crc_tmp[45] ^ crc_tmp[47] ^ crc_tmp[48];
assign    new_crc[49] = crc_din[49] ^ crc_din[48] ^ crc_din[46] ^ crc_din[45] ^ crc_tmp[45] ^ crc_tmp[46] ^ crc_tmp[48] ^ crc_tmp[49];
assign    new_crc[50] = crc_din[50] ^ crc_din[49] ^ crc_din[47] ^ crc_din[46] ^ crc_tmp[46] ^ crc_tmp[47] ^ crc_tmp[49] ^ crc_tmp[50];
assign    new_crc[51] = crc_din[51] ^ crc_din[50] ^ crc_din[48] ^ crc_din[47] ^ crc_tmp[47] ^ crc_tmp[48] ^ crc_tmp[50] ^ crc_tmp[51];
assign    new_crc[52] = crc_din[52] ^ crc_din[51] ^ crc_din[49] ^ crc_din[48] ^ crc_tmp[48] ^ crc_tmp[49] ^ crc_tmp[51] ^ crc_tmp[52];
assign    new_crc[53] = crc_din[53] ^ crc_din[52] ^ crc_din[50] ^ crc_din[49] ^ crc_tmp[49] ^ crc_tmp[50] ^ crc_tmp[52] ^ crc_tmp[53];
assign    new_crc[54] = crc_din[54] ^ crc_din[53] ^ crc_din[51] ^ crc_din[50] ^ crc_tmp[50] ^ crc_tmp[51] ^ crc_tmp[53] ^ crc_tmp[54];
assign    new_crc[55] = crc_din[55] ^ crc_din[54] ^ crc_din[52] ^ crc_din[51] ^ crc_tmp[51] ^ crc_tmp[52] ^ crc_tmp[54] ^ crc_tmp[55];
assign    new_crc[56] = crc_din[56] ^ crc_din[55] ^ crc_din[53] ^ crc_din[52] ^ crc_tmp[52] ^ crc_tmp[53] ^ crc_tmp[55] ^ crc_tmp[56];
assign    new_crc[57] = crc_din[57] ^ crc_din[56] ^ crc_din[54] ^ crc_din[53] ^ crc_tmp[53] ^ crc_tmp[54] ^ crc_tmp[56] ^ crc_tmp[57];
assign    new_crc[58] = crc_din[58] ^ crc_din[57] ^ crc_din[55] ^ crc_din[54] ^ crc_tmp[54] ^ crc_tmp[55] ^ crc_tmp[57] ^ crc_tmp[58];
assign    new_crc[59] = crc_din[59] ^ crc_din[58] ^ crc_din[56] ^ crc_din[55] ^ crc_tmp[55] ^ crc_tmp[56] ^ crc_tmp[58] ^ crc_tmp[59];
assign    new_crc[60] = crc_din[60] ^ crc_din[59] ^ crc_din[57] ^ crc_din[56] ^ crc_tmp[56] ^ crc_tmp[57] ^ crc_tmp[59] ^ crc_tmp[60];
assign    new_crc[61] = crc_din[61] ^ crc_din[60] ^ crc_din[58] ^ crc_din[57] ^ crc_tmp[57] ^ crc_tmp[58] ^ crc_tmp[60] ^ crc_tmp[61];
assign    new_crc[62] = crc_din[62] ^ crc_din[61] ^ crc_din[59] ^ crc_din[58] ^ crc_tmp[58] ^ crc_tmp[59] ^ crc_tmp[61] ^ crc_tmp[62];
assign    new_crc[63] = crc_din[63] ^ crc_din[62] ^ crc_din[60] ^ crc_din[59] ^ crc_tmp[59] ^ crc_tmp[60] ^ crc_tmp[62] ^ crc_tmp[63];


endmodule
