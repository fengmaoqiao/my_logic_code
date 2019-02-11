
`timescale 1ns/1ps
 

`define     U_DLY                   0  

`define     CODE_VER               32'h0000000 

// s-link side data depth , data width is 8
`define     CFG_DATA_LEN            16'd392  // config packet length 
`define     IO_DATA_LEN             16'd120  // IO or COM1 data packet length , 128B
`define     COM_DATA_LEN            16'd1016 // COM2/COM3/HRM/PRM data packet length , 1024B
`define     STA_DATA_LEN            16'd320  // status packet length , 328B

// emif side data depth , data width is 16
`define     CFG_LEN                 11'd200  // config packet length , 400B/2 = 200
`define     IO_LEN                  11'd64   // IO or COM1 data packet length , 128B/2 = 64
`define     COM_LEN                 11'd512  // COM2/COM3/HRM/PRM data packet length , 1024B/2 = 512
`define     STA_LEN                 11'd164  // status packet length , 328B/2 = 164 

// board type definition
`define     MPU_TYPE                4'd1     // MPU type number
`define     AI_TYPE                 4'd2     // AI type number
`define     AO_TYPE                 4'd6     // AO type number
`define     DI_TYPE                 4'd3     // DI type number
`define     DO_TYPE                 4'd7     // DO type number
`define     COM1_TYPE               4'd8     // COM1 type number
`define     COM2_TYPE               4'd9     // COM2 type number
`define     COM3_TYPE               4'd10    // COM3 type number
`define     EX_TYPE                 4'd11    // EX type number

// packt type definition
`define     CFG_TYPE                16'h1122 // configration packt type
`define     CFG_FB_TYPE             16'h3344 // configration feedback packt type
`define     MT_TYPE                 16'h5566 // maintain packt type
`define     STA_TYPE                16'h7788 // status packt type
`define     DATA_TYPE               16'h99AA // data packt type
