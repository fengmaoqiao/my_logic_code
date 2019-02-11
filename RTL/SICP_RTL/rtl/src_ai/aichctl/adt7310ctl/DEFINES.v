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

`define     U_DLY                   0     

// s-link side data depth , data width is 8
`define     CFG_DATA_LEN            16'd400  // config packet length 
`define     IO_DATA_LEN             16'd128  // IO or COM1 data packet length , 128B
`define     COM_DATA_LEN            16'd1024 // COM2/COM3/HRM/PRM data packet length , 1024B
`define     STA_DATA_LEN            16'd328  // status packet length , 328B

// emif side data depth , data width is 16
`define     CFG_LEN                 8'd200  // config packet length , 400B/2 = 200
`define     IO_LEN                  8'd64   // IO or COM1 data packet length , 128B/2 = 64
`define     COM_LEN                 11'd512  // COM2/COM3/HRM/PRM data packet length , 1024B/2 = 512
`define     STA_LEN                 11'd164  // status packet length , 328B/2 = 164 
`define     COLL_LEN                11'd40   // collection packet length , 328B/2 = 164 

// board type definition
`define     AI_TYPE                 4'd2     // AI type number
`define     AO_TYPE                 4'd6     // AO type number
`define     DI_TYPE                 4'd3     // DI type number
`define     DO_TYPE                 4'd7     // DO type number
`define     COM1_TYPE               4'd8     // COM1 type number
`define     COM2_TYPE               4'd9     // COM1 type number
`define     COM3_TYPE               4'd10    // COM1 type number
`define     MPU_TYPE                4'd1     // COM1 type number

// packt type definition
`define     CFG_TYPE                16'h1122 // configration packt type
`define     CFG_FB_TYPE             16'h3344 // configration feedback packt type
`define     MT_TYPE                 16'h5566 // maintain packt type
`define     STA_TYPE                16'h7788 // status packt type
`define     DATA_TYPE               16'h99AA // data packt type

`define     CODE_VERSION            16'h3130

`define     CAL_BASE_ADDR           16'h0000  // the base address of calibrate parameter in eeprom

