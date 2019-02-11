// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-12-12
// DEPARTMENT       :   R&D
// AUTHOR           :   Zhang Yongjun
// AUTHOR'S EMAIL   :   zhangyongjun@cgnpc.com.cn
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-12-12  Zhang Yongjun       Original
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
`timescale 1 ns / 1 ps
`include "DEFINES.v"
module  CRC_CHK
    (
        clk_sys                 ,   
        rst_sys_n               ,   
        crc_dval                ,   
        crc_din                 ,   
        crc_err
    
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   CRC_LEN_L       = 7'h1 ;
parameter   CRC_LEN_H       = 7'h38 ;
localparam  RAM_DGD_CNT     = 8'd255 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input interface signal
input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;
input   wire                    crc_dval                            ;   
input   wire [15:0]             crc_din                             ;   
        
// output interface signal
output  reg                     crc_err                             ;   

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [15:0]                  crc_dout                            ;   
// reg signal
reg     [6:0]                   din_cnt                             ;   
reg                             crc_cap                             ;   
reg                             crc_cap_d1                          ;   
reg                             crc_cap_d2                          ;   
reg                             crc_sop                             ;   
reg     [7:0]                   dgd_err_cnt                         ;   
reg     [15:0]                  crc_value                           ;   
reg                             crc_vld                             ;   
reg                                 test_trig;
reg [15:0]                          test_value0;
reg [15:0]                          test_value1;
reg [15:0]                          test_value2;
reg [15:0]                          test_value3;

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// write up stream data to CRC 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        din_cnt <=   7'd0 ;
    end
    else begin
        if ( crc_dval == 1'b1 ) begin
            din_cnt <=   din_cnt + 1'b1 ;
        end
        else begin
            din_cnt <=   7'd0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_vld  <=   1'b0 ;
    end
    else begin
        if ( din_cnt == CRC_LEN_L ) begin
            crc_vld  <=   1'b1 ;
        end
        else if ( din_cnt == CRC_LEN_H ) begin
            crc_vld  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_cap   <=   1'b0 ;
    end
    else begin
        if ( din_cnt == CRC_LEN_H - 1'b1 && crc_dval == 1'b1 ) begin
            crc_cap  <=   1'b1 ;
        end
        else begin
            crc_cap  <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_cap_d1  <=   1'b0 ;
    end
    else begin
        crc_cap_d1  <=   crc_cap ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_cap_d2  <=   1'b0 ;
    end
    else begin
        crc_cap_d2  <=   crc_cap_d1 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_sop   <=   1'b0 ;
    end
    else begin
        crc_sop   <=   crc_cap_d2 ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_value   <=   16'd0 ;
    end
    else begin
        if ( din_cnt == CRC_LEN_H + 1'b1 && crc_dval == 1'b1 ) begin
            crc_value   <=   crc_din ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        dgd_err_cnt   <=   8'd0 ;
    end
    else begin
        if ( crc_cap_d2 == 1'b1 && crc_dout != crc_value ) begin
            if ( dgd_err_cnt == RAM_DGD_CNT ) begin
                dgd_err_cnt <=   RAM_DGD_CNT ;
            end
            else begin
                dgd_err_cnt   <=   dgd_err_cnt + 1'b1 ;
            end
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        test_value0   <=   16'd0 ;
    end
    else begin
        if ( crc_cap_d2 == 1'b1 && crc_dout != crc_value ) begin
            test_value0 <=  crc_dout ; 
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        test_value1   <=   16'd0 ;
    end
    else begin
        if ( crc_cap_d2 == 1'b1 && crc_dout != crc_value ) begin
            test_value1 <=  crc_value ; 
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        test_value2   <=   16'd0 ;
    end
    else begin
        if ( crc_cap_d2 == 1'b1 && crc_dout != crc_value && dgd_err_cnt == 8'd5 ) begin
            test_value2 <=  crc_dout ; 
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        test_value3   <=   16'd0 ;
    end
    else begin
        if ( crc_cap_d2 == 1'b1 && crc_dout != crc_value && dgd_err_cnt == 8'd5 ) begin
            test_value3 <=  crc_value ; 
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        test_trig   <=   1'b0 ;
    end
    else begin
        if ( crc_cap_d2 == 1'b1 ) begin
            if ( crc_dout != crc_value ) begin
                test_trig   <=   1'b1 ;
            end
            else begin
                test_trig   <=   1'b0 ;
            end
        end
        else begin
            test_trig   <=   1'b0;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        crc_err <=   1'b0 ;
    end
    else begin
        if ( dgd_err_cnt == RAM_DGD_CNT ) begin
            crc_err <=   1'b1 ;
        end
    end
end

    IO_CRC16D16                    U_FIFO_OUTCRC
    (
    //input port
    .clk_sys                    ( clk_sys                   ),
    .rst_sys_n                  ( rst_sys_n                 ),

    .crc_din                    ( crc_din                   ),
    .crc_cap                    ( crc_cap                   ),
    .crc_sop                    ( crc_sop                   ),
    .crc_din_vld                ( crc_vld                   ),

    //output port
    .crc_dout                   ( crc_dout                  )
    );

endmodule
