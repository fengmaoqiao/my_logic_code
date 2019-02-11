// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-06-10
// DEPARTMENT       :   R&D
// AUTHOR           :   YongjunZhang
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-06-10  YongjunZhang        Original
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
`timescale 1 ns / 100 ps

`define     U_DLY                   2     
`define     SIM

//----------------------------------------------------------------------------------
// The MAX9611 chip relation of register
//----------------------------------------------------------------------------------

`define     WR                          1'b0
`define     RD                          1'b1

`define     ADCDEV_ADDR                 7'b1110000

`define     MAX_ACON1                   8'h0A
`define     MAX_ACON2                   8'h0B
`define     MAX_DCON1                   8'h00
`define     MAX_DCON2                   8'h00
`define     MAX_CAS_MSB                 8'h00
`define     MAX_CAS_LSB                 8'h01

