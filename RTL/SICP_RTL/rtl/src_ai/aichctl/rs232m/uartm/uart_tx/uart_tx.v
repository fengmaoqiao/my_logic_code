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
`include "DEFINES.v"

module UART_TX 
    (
        // input
        clk_sys                 ,   
        rst_sys_n               ,   

        tx_trig                 ,   
        tx_data                 ,   
        xmit_pulse              ,   
        // output
        txrdy                   ,   
        txd                        
    ) ;
    
/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   
input   wire                    tx_trig                             ;   
input   wire                    rst_sys_n                           ;   
input   wire    [7:0]           tx_data                             ;   
input   wire                    xmit_pulse                          ;   
// declare output signal
output  reg                     txrdy                               ;   
output  wire                    txd                                 ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
  
wire                            stop_bit                            ; 
wire    [10:0]                  value                               ;   
wire                            start_bit                           ;   
// reg signal
reg     [7:0]                   tx_value                            ;   // transmit byte
reg                             tx_parity                           ;   // transmit parity
reg                             tx_en                               ;   
reg     [3:0]                   tx_cnt                              ;   
reg     [3:0]                   tx_bit_cnt                          ;   
reg                             tx_bit_en                           ;   
wire                            tx_parity_bit                       ;  
reg                             parity_bit_en                       ;   
reg     [2:0]                   parity_bit_cnt                      ;   
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        tx_en   <=   1'b0 ; 
    end
    else begin
        if ( tx_trig == 1'b1 ) begin
            tx_en   <=   1'b1 ;
        end
        else if ( tx_cnt == 4'd10 ) begin
            tx_en   <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        tx_cnt  <=   4'd0 ;
    end
    else begin
        if ( tx_trig == 1'b1 ) begin
            tx_cnt  <=   4'd0 ;
        end
        else if ( tx_en == 1'b1 && xmit_pulse == 1'b1 ) begin
            tx_cnt  <=   tx_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        tx_bit_en   <=   1'b0 ;
    end
    else begin
        if ( tx_en == 1'b1 && xmit_pulse == 1'b1 ) begin
            tx_bit_en   <=   1'b1 ;
        end
        else if ( tx_cnt == 5'd10 ) begin
            tx_bit_en   <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        tx_bit_cnt  <=   4'd0 ;
    end
    else begin
        if ( tx_trig == 1'b1 ) begin
            tx_bit_cnt  <=   4'd0 ;
        end
        else if ( tx_bit_en == 1'b1 && xmit_pulse == 1'b1 ) begin
            if ( tx_bit_cnt == 4'd9 ) begin
                tx_bit_cnt  <=   4'd0 ;
            end
            else begin 
                tx_bit_cnt  <=   tx_bit_cnt + 1'b1 ;
            end
        end
    end
end

assign txd = ( tx_bit_en == 1'b1 ) ? value[tx_bit_cnt] : 1'b1 ; 
assign start_bit = 1'b0 ;
assign stop_bit = 1'b1 ;
assign value = { stop_bit , tx_value ,start_bit } ;
//assign tx_parity_bit =( tx_bit_cnt == 4'd9 ) ? odd_n_even ^ tx_parity : 1'b0 ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        tx_value <= #`U_DLY 8'd0 ;
    end
    else begin
        if ( tx_trig == 1'b1 ) begin
            tx_value <= tx_data ;
        end
        else ;
    end
end

//always @ ( posedge clk_sys or negedge rst_sys_n ) begin
//    if( rst_sys_n == 1'b0 ) begin
//        parity_bit_en   <=   1'b0 ;
//    end
//    else begin
//        if ( tx_cnt == 5'd1 ) begin
//            parity_bit_en   <=   1'b1 ;
//        end
//        else if ( tx_cnt == 5'd9 ) begin
//            parity_bit_en   <=   1'b0 ;
//        end
//    end
//end

//always @ ( posedge clk_sys or negedge rst_sys_n ) begin
//    if( rst_sys_n == 1'b0 ) begin
//        parity_bit_cnt  <=   3'd0 ;
//    end
//    else begin
//        if ( tx_trig == 1'b1 ) begin
//            parity_bit_cnt  <=   3'd0 ;
//        end
//        else if ( parity_bit_en == 1'b1 && xmit_pulse == 1'b1 ) begin
//            parity_bit_cnt  <=   parity_bit_cnt + 1'b1 ;
//        end
//        else ;
//    end
//end

//always @( posedge clk_sys or negedge rst_sys_n ) begin
//    if ( rst_sys_n == 1'b0 ) begin
//        tx_parity   <=   1'b0 ;
//    end
//    else begin
//        if ( tx_trig == 1'b1 ) begin
//            tx_parity <= 1'b0 ;
//        end
//        else if ( parity_bit_en == 1'b1 && xmit_pulse == 1'b1 ) begin
//            tx_parity <= tx_parity ^ tx_value[parity_bit_cnt] ;
//        end
//        else ;
//    end
//end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        txrdy   <=   1'b1 ;
    end
    else begin
        if ( tx_trig == 1'b1  ) begin
            txrdy   <=   1'b0 ;
        end
        else if ( tx_cnt == 4'd10 && xmit_pulse == 1'b1 ) begin
            txrdy   <=   1'b1 ;
        end
    end
end

endmodule
