// *********************************************************************************
// Project Name :
// Author       : libing
// Email        : lb891004@163.com
// Creat Time   : 2013/12/19 17:11:39
// File Name    : uart_receive.v
// Module Name  : uart_receive
// Called By    : 
// Abstract     :
//
// CopyRight(c) 2012, Zhimingda digital equipment Co., Ltd.. 
// All Rights Reserved
//
// *********************************************************************************
// Modification History:
// 1. initial
// *********************************************************************************/
// *************************
// MODULE DEFINITION
// *************************
`timescale 1 ns / 1 ps


module uart_debug_receive(
//-----------------------------------------------------------------------------------
//Global Sinals 
//-----------------------------------------------------------------------------------     
    input               rst_n                   ,   // Reset, Valid low  
    input               clk_uart                ,   // Uart Refence Clock  
    input               baud_en                 ,   // Baudrate Enable, Last 1 clock cycle    
//-----------------------------------------------------------------------------------
//Software Interface Sinals 
//-----------------------------------------------------------------------------------   
    input               verify_en               ,   // Verify Enable, 1-Enable; 0-Disable
    input               verify_select           ,   // Verify Mode Select, 1-Odd; 0-Even
    input               verify_filter           ,   // Verify faild filter,  1-Enable; 0-Disable
    input [3:0]         data_width              ,   // Data Width, valid rang: 8~5
//-----------------------------------------------------------------------------------
//RX-Line Sinals
//----------------------------------------------------------------------------------- 
    input               rx_in                   ,   // UART Recieve Line
//-----------------------------------------------------------------------------------
//Rx data Sinals 
//-----------------------------------------------------------------------------------    
    output reg [7:0]    rx_data                 ,   // Recieved Data  
    output reg          rx_data_vld                 // Recieved Data Strobe, Last 1 baudrate cycle
);

//***********************************************************************************
//Internal Register & Wire Define
//***********************************************************************************
reg                             rx_in_r1                            ;   
reg                             rx_in_r2                            ;   
reg                             rx_in_r3                            ;   

reg [3:0]                       bit_cnt                             ;   
reg [3:0]                       sample_cnt                          ;   
reg                             sample_flg                          ;   

reg [2:0]                       curr_state                          /* synthesis syn_encoding="safe,gray ",synthesis syn_keep = 1 */;   
reg [2:0]                       next_state                          ; 

reg [1:0]                       sample_reg                          ;   
reg                             sample_bit_val                      ;   

reg                             parity_bit                          ;   
reg [7:0]                       shift_reg                           ;

reg                             parity_bit_cal                      ;   

//***********************************************************************************
//Local Parameter Define
//***********************************************************************************
localparam U_DLY              = 1      ;

localparam X08_SAMPLE_PER_BIT = 4'd7   ; // 8 samples per bit
localparam X08_SAMPLE_BIT1    = 4'd2   ; // 1st sample window
localparam X08_SAMPLE_BIT2    = 4'd3   ; // 2nd sample window
localparam X08_SAMPLE_BIT3    = 4'd4   ; // 3st sample window

localparam IDLE               = 3'b000 ;
localparam CHECK_START        = 3'b001 ;
localparam GET_DATA           = 3'b011 ;
localparam GET_PARITY         = 3'b111 ;
localparam GET_STOP           = 3'b110 ;

//===================================================================================
//rx_in sync
//===================================================================================
always @ (posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        begin
            rx_in_r1 <= #U_DLY 1'b1;
            rx_in_r2 <= #U_DLY 1'b1;
            rx_in_r3 <= #U_DLY 1'b1;
        end
    else
        begin
            rx_in_r1 <= #U_DLY rx_in;
            rx_in_r2 <= #U_DLY rx_in_r1;
            rx_in_r3 <= #U_DLY rx_in_r2;
        end        
end

//===================================================================================
//RX-FSM Section 1
//===================================================================================
always @ (posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        curr_state <= #U_DLY IDLE;
    else
        curr_state <= #U_DLY next_state;        
end

//===================================================================================
//RX-FSM Section 2
//===================================================================================
always @ (*)
begin
    case (curr_state)
        IDLE :
            begin
                if ((rx_in_r3 == 1'b1) && (rx_in_r2 == 1'b0))
                    next_state = CHECK_START;
                else
                    next_state = IDLE;
            end
        CHECK_START :
            begin
                if ((baud_en == 1'b1) && (sample_flg == 1'b1)) 
                    if (sample_bit_val == 1'b0) // valid start bit
                        next_state = GET_DATA; 
                    else
                        next_state = IDLE;
                else
                    next_state = CHECK_START;
            end
        GET_DATA :
            begin
                if ((baud_en == 1'b1) && (sample_flg == 1'b1) && (bit_cnt == (data_width-1))) 
                    if (verify_en == 1'b0)
                        next_state = GET_STOP;
                    else
                        next_state = GET_PARITY;
                else
                    next_state = GET_DATA;           
            end 
        GET_PARITY :
            begin
                if ((baud_en == 1'b1) && (sample_flg == 1'b1)) 
                    next_state = GET_STOP;
                else
                    next_state = GET_PARITY;
            end
        GET_STOP :
            begin
                if ((baud_en == 1'b1) && (sample_flg == 1'b1)) 
                    next_state = IDLE;
                //else if ((baud_en == 1'b1) && (sample_flg == 1'b1))
                //    next_state = IDLE;
                else
                    next_state = GET_STOP;
            end      
        default:
            next_state = IDLE;
    endcase
end

//===================================================================================
//sample_reg Sample the rx_in_r2 3-times per bit
//===================================================================================
always @ (posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        sample_reg <= #U_DLY 2'd0; 
    else
        begin
            if (baud_en == 1'b1)
                begin
                    case (sample_cnt)
                        X08_SAMPLE_BIT1 : sample_reg <= #U_DLY {sample_reg[0],rx_in_r2};
                        X08_SAMPLE_BIT2 : sample_reg <= #U_DLY {sample_reg[0],rx_in_r2};
                        default         : sample_reg <= #U_DLY  sample_reg;
                    endcase
                end
            else
                sample_reg <= #U_DLY sample_reg;
        end
end

// (the number of logic 1 sample bit) >= 2 ----->  sample_bit_val = 1
// (the number of logic 1 sample bit) <  2 ----->  sample_bit_val = 0
always @ (posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        sample_bit_val <= #U_DLY 1'b1;
    else
        begin
            case ({sample_reg,rx_in_r2}) 
                3'b000 : sample_bit_val <= #U_DLY 1'b0;
                3'b001 : sample_bit_val <= #U_DLY 1'b0;
                3'b010 : sample_bit_val <= #U_DLY 1'b0;
                3'b011 : sample_bit_val <= #U_DLY 1'b1;
                3'b100 : sample_bit_val <= #U_DLY 1'b0;
                3'b101 : sample_bit_val <= #U_DLY 1'b1;
                3'b110 : sample_bit_val <= #U_DLY 1'b1;
                3'b111 : sample_bit_val <= #U_DLY 1'b1;
                default: sample_bit_val <= #U_DLY 1'b0;
            endcase
        end
end

//===================================================================================
//sample_cnt - count sample time
//===================================================================================
always @ (posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        sample_cnt <= #U_DLY 4'h0;
    else
        begin
            if (curr_state == IDLE)
                sample_cnt <= #U_DLY 4'h0;
            else
                begin
                    if (baud_en == 1'b1)
                        begin
                            if (sample_cnt == X08_SAMPLE_PER_BIT)
                                sample_cnt <= #U_DLY 4'h0;
                            else
                                sample_cnt <= #U_DLY sample_cnt + 4'h1;
                        end
                    else
                        sample_cnt <= #U_DLY sample_cnt; 
                end
        end
end

always @ (posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        sample_flg <= #U_DLY 1'b0;
    else
        begin
            if (baud_en == 1'b1)
                begin
                    if (sample_cnt == X08_SAMPLE_BIT3)
                        sample_flg <= #U_DLY 1'b1;
                    else
                        sample_flg <= #U_DLY 1'b0;
                end
            else
                sample_flg <= #U_DLY sample_flg; 
        end
end

//===================================================================================
//bit_cnt - count data bit per byte
//===================================================================================
always @ (posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        bit_cnt <= #U_DLY 4'h0;
    else
        begin
            if (curr_state == IDLE)
                bit_cnt <= #U_DLY 4'h0;
            else if ((baud_en == 1'b1) && (curr_state == GET_DATA))
                begin
                    if (sample_flg == 1'b1)
                        bit_cnt <= #U_DLY bit_cnt + 4'h1;
                    else
                        bit_cnt <= #U_DLY bit_cnt;
                end
            else
                bit_cnt <= #U_DLY bit_cnt; 
        end
end

//===================================================================================
//parity_bit recieve
//===================================================================================
always @ (posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        parity_bit <= #U_DLY 1'b0;
    else
        begin
            if (curr_state == IDLE)
                parity_bit <= #U_DLY 1'b0;             
            else if ((baud_en == 1'b1) && (curr_state == GET_PARITY) && (sample_flg == 1'b1))
                parity_bit <= #U_DLY sample_bit_val;
            else
                parity_bit <= #U_DLY parity_bit;
        end
end

//===================================================================================
//data_bit recieve - shift into shift_reg
//===================================================================================
always @ (posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        shift_reg <= #U_DLY 8'h0;
    else
        begin
            if (curr_state == IDLE)
                shift_reg <= #U_DLY 8'h0;
            else if ((baud_en == 1'b1) && (curr_state == GET_DATA) && (sample_flg == 1'b1))
                shift_reg <= #U_DLY {sample_bit_val,shift_reg[7:1]};
            else
                shift_reg <= #U_DLY shift_reg;
        end
end

//===================================================================================
//parity_bit_cal Calculate
//===================================================================================
always @ (posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        parity_bit_cal <= #U_DLY 1'b0;
    else
        begin
            if (curr_state == IDLE)
                parity_bit_cal <= #U_DLY verify_select;
            else if ((baud_en == 1'b1) && (curr_state == GET_DATA) && (sample_flg == 1'b1))
                parity_bit_cal <= #U_DLY sample_bit_val ^ parity_bit_cal;
            else
                parity_bit_cal <= #U_DLY parity_bit_cal;
        end
end

//===================================================================================
//rx_data_vld Generate
//===================================================================================
always @ (posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        rx_data_vld <= #U_DLY 1'b0;
    else
        begin
            if ((curr_state == GET_STOP) && (sample_flg == 1'b1) && (baud_en == 1'b1))
                begin
                    if (verify_en == 1'b1)
                        begin
                            if (parity_bit == parity_bit_cal)
                                rx_data_vld <= #U_DLY 1'b1;
                            else
                                rx_data_vld <= #U_DLY 1'b0; 
                        end
                    else
                        rx_data_vld <= #U_DLY 1'b1;
                end
            else
                rx_data_vld <= #U_DLY 1'b0;
        end
end

//===================================================================================
//rx_data load form the shift_reg
//===================================================================================
always @ (posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        rx_data <= #U_DLY 8'h0;
    else
        begin
            if (curr_state == GET_STOP)
                case (data_width)
                    4'd5    : rx_data <= #U_DLY {{3{1'b0}},shift_reg[7:3]};
                    4'd6    : rx_data <= #U_DLY {{2{1'b0}},shift_reg[7:2]};
                    4'd7    : rx_data <= #U_DLY {{1{1'b0}},shift_reg[7:1]};
                    4'd8    : rx_data <= #U_DLY shift_reg;
                    default : rx_data <= #U_DLY shift_reg;
                endcase                
            else
                rx_data <= #U_DLY rx_data;
        end
end

endmodule
