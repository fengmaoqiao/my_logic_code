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
`timescale 1 ns / 1 ns
`include "DEFINES.v"
module UART_RX 
    (
        clk_sys                 ,   
        baud_clock              ,   
        rst_sys_n               ,   
        odd_n_even              ,   
        rxd                     ,   
        parity_err              ,   
        rx_byte                 ,   
        rx_done                 ,   
        rxd_idle
) ;

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
// TYPE receive_states:
localparam      rx_idle          =      4'b0000      ;
localparam      rx_data_bits     =      4'b0001      ;
localparam      rx_stop_bit      =      4'b0010      ;
localparam      rx_wait_state    =      4'b0100      ;
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_sys                             ;   //  system clock
input   wire                    baud_clock                          ;   //  8x baud clock pulse
input   wire                    rst_sys_n                           ;   //  active low async reset  
input   wire                    odd_n_even                          ;   //  if set to one odd parity otherwise even parity
input   wire                    rxd                                 ;   
// declare output signal
output  reg                     parity_err                          ;   //  parity error indicator on recieved data
output  reg     [7:0]           rx_byte                             ;   
output  reg                     rx_done                             ;   
// AS: added idle wire for framing_err assigmnet using
// stop_strobe
output  wire                    rxd_idle                            ;   
// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
// reg signal
reg     [3:0]                   cur_state                           ;   //  receive state machine
reg     [3:0]                   next_state                          ;   
reg     [3:0]                   receive_count                       ;   //  counts bits received
reg                             rx_filtered                         ;   //  filtered rx data
reg     [8:0]                   rx_shift                            ;   //  receive shift register
reg                             rx_parity_calc                      ;   //  received parity, calculated
reg     [3:0]                   rx_bit_cnt                          ;   //  count of received bits 
reg     [2:0]                   samples                             ;   
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// filter the receive data
//----------------------------------------------------------------------------------
always @( posedge clk_sys or negedge rst_sys_n )
begin 
    if ( rst_sys_n == 1'b0 ) begin
        samples <= 3'b111 ;        
    end
    else begin
        if ( baud_clock == 1'b1 ) begin
            samples[1:0] <= samples[2:1] ;  
            samples[2] <= rxd ;      
        end
        else ;
  end
end

//  our voter
always @( * )
begin
    case ( samples )
        3'b000 : begin
            rx_filtered <= 1'b0 ;      
        end
        3'b001 : begin
            rx_filtered <= 1'b0 ;      
        end
        3'b010 : begin
            rx_filtered <= 1'b0 ;      
        end
        3'b011 : begin
            rx_filtered <= 1'b1 ;      
        end
        3'b100 : begin
            rx_filtered <= 1'b0 ;      
        end
        3'b101 : begin
            rx_filtered <= 1'b1 ;      
        end
        3'b110 : begin
            rx_filtered <= 1'b1 ;      
        end
        default : begin
            rx_filtered <= 1'b1 ;      
        end
    endcase
end

//----------------------------------------------------------------------------
// receive bit counter
//----------------------------------------------------------------------------
always @(posedge clk_sys or negedge rst_sys_n)
begin : rcv_cnt
    if ( rst_sys_n == 1'b0 ) begin
        receive_count <= 4'b0000 ; 
    end
    else begin
      //  no start bit yet or begin sample period for data
        if (baud_clock == 1'b1) begin
            if ( ( cur_state == rx_idle && ( rx_filtered == 1'b1 | receive_count == 4'b1000 ) ) || ( cur_state == rx_wait_state && receive_count == 4'b0110 ) ) begin
                receive_count <= 4'b0000 ;   
            end
            else begin
                receive_count <= receive_count + 1'b1 ;      
            end
        end
        else ;
    end
end

assign  rxd_idle = ( cur_state == rx_idle ) ;                                                 

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cur_state <= rx_idle ;
    end
    else begin
        cur_state   <=   next_state ;
    end
end

always @( * ) begin                                                                               
    case ( cur_state )                                                                        
        rx_idle : begin                                                                                
            if ( baud_clock == 1'b1 && receive_count == 4'b1000 ) begin
                next_state <= rx_data_bits ; 
            end
            else begin        
                next_state <= rx_idle ;
            end
        end
        rx_data_bits : begin
          //  last bit has been received
          if ( baud_clock == 1'b1 && rx_bit_cnt == 4'b1000 ) begin
                // overflow    
                next_state <= rx_stop_bit ;
            end              
            else begin              
                next_state <= rx_data_bits ; //  still clocking in bits              
            end
        end
        rx_stop_bit : begin
          // framing error
            if ( baud_clock == 1'b1 && receive_count == 4'b1111 ) begin
                next_state <= rx_wait_state ;
            end
            else begin
                next_state <= rx_stop_bit ;
            end
        end
        rx_wait_state : begin
            if ( baud_clock == 1'b1 && ( rx_filtered == 1'b1 || receive_count == 4'b0110 ) )  begin
                next_state <= rx_idle ;
            end
      	    else begin
                next_state <= rx_wait_state ;
      		end
      	end
        default : begin
            next_state <= rx_idle ; 
        end
    endcase
end

always @( posedge clk_sys or negedge rst_sys_n )
begin
    if ( rst_sys_n == 1'b0 ) begin        
        rx_byte <= 8'b00000000 ;                   
    end                
    else begin                    
        if ( baud_clock == 1'b1 ) begin
            if ( cur_state == rx_wait_state && rx_bit_cnt == 4'b1001 ) begin
                rx_byte <= rx_shift[7:0] ;
            end
            else ;
        end
        else ;
    end
end

// ----------------------------------------------------------------------------
//  receive shift register and parity calculation
// ----------------------------------------------------------------------------
always @(posedge clk_sys or negedge rst_sys_n)
begin
    if ( rst_sys_n == 1'b0 ) begin 
        rx_bit_cnt <= 4'b0000 ;    
    end
    else begin
        if ( baud_clock == 1'b1 )begin
            if (cur_state == rx_idle)begin
                rx_bit_cnt <= 4'b0000 ;      
            end
            else if ( receive_count == 4'b1111 )begin
                //  sample new data bit
                rx_bit_cnt <= rx_bit_cnt + 1'b1 ;    
            end
            else ;
        end
    end
end

always @(posedge clk_sys or negedge rst_sys_n)
begin
    if ( rst_sys_n == 1'b0 ) begin 
        rx_shift[8:0] <= 9'b000000000 ;    
    end
    else begin
        if ( baud_clock == 1'b1 )begin
            if ( cur_state == rx_idle )begin
                rx_shift[8:0] <= 9'b000000000 ;      
            end
            else if ( receive_count == 4'b1111 )begin
                rx_shift[7:0] <= rx_shift[8:1] ;  
                rx_shift[8] <= rx_filtered ;      
            end
            else ;
        end
        else ;
    end
end

// ----------------------------------------------------------------------------
//  receiver parity calculation
// ----------------------------------------------------------------------------
always @(posedge clk_sys or negedge rst_sys_n)
begin 
    if ( rst_sys_n == 1'b0 ) begin 
        rx_parity_calc <= 1'b0 ;   
    end
    else begin
        if ( baud_clock == 1'b1 ) begin
            if (receive_count == 4'b1111 ) begin
                rx_parity_calc <= rx_parity_calc ^ rx_filtered ;     
            end
            else ;
            if (cur_state == rx_stop_bit && receive_count == 4'b1111 )begin
                rx_parity_calc <= 1'b0 ;     
            end
            else ;
        end
    end
end

// ----------------------------------------------------------------------------
//  latch parity error for even or odd parity
// ----------------------------------------------------------------------------
always @(posedge clk_sys or negedge rst_sys_n)
begin
    if ( rst_sys_n == 1'b0 ) begin 
        parity_err <= 1'b0 ;       
    end
    else begin
        if ( baud_clock == 1'b1 && receive_count == 4'b1111 && rx_bit_cnt == 4'b1001 ) begin
            if ( odd_n_even == 1'b0 ) begin
                parity_err <= rx_parity_calc ^ rx_filtered ;      
            end
            else begin
                parity_err <= ~( rx_parity_calc ^ rx_filtered ) ;   
            end
        end
        else begin
            parity_err <= 1'b0 ;    
        end
    end
end

always @(posedge clk_sys or negedge rst_sys_n)
begin  
    if ( rst_sys_n == 1'b0 ) begin 
        rx_done <= 1'b0 ;
    end
    else begin
        if ( baud_clock == 1'b1 ) begin
            if ( cur_state == rx_wait_state && rx_bit_cnt == 4'b1001 )begin
                rx_done <= 1'b1 ;
            end
            else begin
                rx_done <= 1'b0 ;
            end
        end
        else begin
            rx_done  <=   1'b0 ;
        end
    end
end

endmodule 

