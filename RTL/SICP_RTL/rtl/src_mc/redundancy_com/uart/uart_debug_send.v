// *********************************************************************************
// Project Name :
// Author       : libing
// Email        : lb891004@163.com
// Creat Time   : 2014/2/18 16:38:37
// File Name    : uart_send.v
// Module Name  : uart_send
// Called By    : 
// Abstract     :
//
// CopyRight(c) 2014, Zhimingda digital equipment Co., Ltd.. 
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


module uart_debug_send(
//-----------------------------------------------------------------------------------
//Global Sinals 
//-----------------------------------------------------------------------------------     
    input               rst_n                   ,   // Reset, Valid low  
    input               clk_uart                ,   // Uart Refence Clock  
    input               baud_en                 ,   // Baudrate Enable, Last 1 clock cycle  
//-----------------------------------------------------------------------------------
//Software Config Sinals 
//-----------------------------------------------------------------------------------  
    input               verify_en               ,   // Verify Enable, 1-Enable; 0-Disable
    input               verify_select           ,   // Verify Mode Select, 1-Odd; 0-Even
    input               stop_bit_sel            ,   // Stop Bit Width Select, 1-2 bit; 0-1 bit 
    input [3:0]         data_width              ,   // Data Width, valid rang: 8~5
//-----------------------------------------------------------------------------------
//Tx Data Load Interface
//-----------------------------------------------------------------------------------                                                   
    input [7:0]         tx_data                 ,   // TX data
    input               tx_start                ,   // TX start signal, Valid high
//-----------------------------------------------------------------------------------
//Software Interface Sinals 
//-----------------------------------------------------------------------------------     
    output reg          tx_busy                 ,   // TX busy, 1-busy; 0-idle
//-----------------------------------------------------------------------------------
//TX-Line Sinals
//-----------------------------------------------------------------------------------     
    output reg          tx_out                      // UART Transmit Line  
);

//***********************************************************************************
//Internal Register & Wire Define
//***********************************************************************************
reg [2:0]                       n_state                             ;   
reg [2:0]                       c_state                             /* synthesis syn_encoding="safe,gray ",synthesis syn_keep = 1 */;   
reg [3:0]                       sample_cnt                          ;   
reg [3:0]                       bit_cnt                             ;   
reg                             parity_bit                          ;   
reg [7:0]                       tx_data_latch                       ;   

//***********************************************************************************
//Local Parameter Define
//***********************************************************************************
localparam IDLE      = 3'b000        ;
localparam SEND_START= 3'b001        ;
localparam SEND_DATA = 3'b011        ;
localparam SEND_ODDP = 3'b010        ;
localparam SEND_STOP1= 3'b110        ;
localparam SEND_STOP2= 3'b111        ;

localparam U_DLY     = 1             ;     
localparam X08_SAMPLE_PER_BIT = 4'd7 ; // 8 samples per bit

//===================================================================================
// tx_data Latch
//===================================================================================
always @(posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        tx_data_latch <= #U_DLY 8'h0;
    else
        begin
            if (tx_start == 1'b1)
                tx_data_latch <= #U_DLY tx_data;
            else
                tx_data_latch <= #U_DLY tx_data_latch;
        end
end

//===================================================================================
//TX-FSM Section 1
//===================================================================================
always @(posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        c_state <= #U_DLY IDLE;
    else
        c_state <= #U_DLY n_state;
end

//===================================================================================
//TX-FSM Section 2
//===================================================================================
always@(*)
begin
    case(c_state)
        IDLE:
            if((tx_start == 1'b1)&&(baud_en == 1'b1))
                n_state = SEND_START;
            else
                n_state = IDLE;
        SEND_START:
            if((sample_cnt == X08_SAMPLE_PER_BIT)&&(baud_en == 1'b1))
                n_state = SEND_DATA;
            else
                n_state = SEND_START;
        SEND_DATA:
            if((bit_cnt == data_width)&&(sample_cnt == X08_SAMPLE_PER_BIT)&&(baud_en == 1'b1))
				begin
					if(verify_en == 1'b1)
					    n_state = SEND_ODDP;
			        else
                        n_state = SEND_STOP1;
				end
            else
                n_state = SEND_DATA;
        SEND_ODDP:
            if((sample_cnt == X08_SAMPLE_PER_BIT)&&(baud_en == 1'b1))
                n_state = SEND_STOP1;
            else
                n_state = SEND_ODDP;   
        SEND_STOP1:
            if((sample_cnt == X08_SAMPLE_PER_BIT)&&(baud_en == 1'b1))
				begin
					if(stop_bit_sel == 1'b1)
						n_state = SEND_STOP2;
				    else
                        n_state = IDLE;
				end
            else
                n_state = SEND_STOP1;
        SEND_STOP2:
            if((sample_cnt == X08_SAMPLE_PER_BIT)&&(baud_en == 1'b1))
                n_state = IDLE;
            else
                n_state = SEND_STOP2;
        default:
            n_state = IDLE;
    endcase
end

//===================================================================================
//sample_cnt Counter
//===================================================================================
always @(posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        sample_cnt <= #U_DLY 4'b0000;
    else if(c_state == IDLE)
        sample_cnt <= #U_DLY 4'b0000;
    else if(baud_en == 1'b1)
        begin
            if(sample_cnt == X08_SAMPLE_PER_BIT)
                sample_cnt <= #U_DLY 4'b0000;
            else
                sample_cnt <= #U_DLY sample_cnt + 1'b1; 
	    end
    else
        sample_cnt <= #U_DLY sample_cnt;    
end

//===================================================================================
//bit_cnt Counter
//===================================================================================
always @(posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        bit_cnt <= #U_DLY 4'b0000;
    else if(c_state == IDLE)
        bit_cnt <= #U_DLY 4'b0000;
    else if((sample_cnt == X08_SAMPLE_PER_BIT)&&(baud_en == 1'b1))
        bit_cnt <= #U_DLY bit_cnt + 1'b1;
    else
        bit_cnt <= #U_DLY bit_cnt;
end

//===================================================================================
//parity_bit Calculate
//===================================================================================
always @(posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        parity_bit <= #U_DLY 1'b0;
    else if((baud_en == 1'b1) && (c_state == SEND_DATA))
        case (data_width)
            4'h8    : parity_bit <= #U_DLY tx_data_latch[0] + tx_data_latch[1] + tx_data_latch[2] +tx_data_latch[3] +tx_data_latch[4] + tx_data_latch[5] + tx_data_latch[6] + tx_data_latch[7];
            4'h7    : parity_bit <= #U_DLY tx_data_latch[0] + tx_data_latch[1] + tx_data_latch[2] +tx_data_latch[3] +tx_data_latch[4] + tx_data_latch[5] + tx_data_latch[6];
            4'h6    : parity_bit <= #U_DLY tx_data_latch[0] + tx_data_latch[1] + tx_data_latch[2] +tx_data_latch[3] +tx_data_latch[4] + tx_data_latch[5];
            4'h5    : parity_bit <= #U_DLY tx_data_latch[0] + tx_data_latch[1] + tx_data_latch[2] +tx_data_latch[3] +tx_data_latch[4];
            default : parity_bit <= 1'b0;
        endcase
    else if((baud_en == 1'b1) && (c_state == SEND_STOP1))
        parity_bit <= #U_DLY 1'b0;
    else
        parity_bit <= #U_DLY parity_bit;
end

//===================================================================================
//tx_out Process
//===================================================================================
always @(posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        tx_out <= #U_DLY 1'b1;
    else if(baud_en == 1'b1)
        case(c_state)
            IDLE:
                tx_out <= #U_DLY 1'b1;
            SEND_START:
                tx_out <= #U_DLY 1'b0;
            SEND_DATA:
                tx_out <= #U_DLY tx_data_latch[bit_cnt-1];
		    SEND_ODDP:
				if(verify_select == 1'b1)
				    tx_out <= #U_DLY ~parity_bit;
			    else
					tx_out <= #U_DLY parity_bit;
            SEND_STOP1:
                tx_out <= #U_DLY 1'b1;
            SEND_STOP2:
                tx_out <= #U_DLY 1'b1;
            default:
                tx_out <= #U_DLY 1'b1;
        endcase
end

//===================================================================================
//tx_busy Process, 1-in transmiting, 0-idle
//===================================================================================
always @(posedge clk_uart or negedge rst_n)
begin
    if (rst_n == 1'b0)
        tx_busy <= #U_DLY 1'b0;
    else
        case(c_state)
            IDLE      :  tx_busy <= #U_DLY 1'b0;
            SEND_START:  tx_busy <= #U_DLY 1'b1;
            SEND_DATA :  tx_busy <= #U_DLY 1'b1;
		    SEND_ODDP :  tx_busy <= #U_DLY 1'b1;
            SEND_STOP1:  tx_busy <= #U_DLY 1'b1;
            SEND_STOP2:  tx_busy <= #U_DLY 1'b1;
            default   :  tx_busy <= #U_DLY 1'b0;
        endcase              
end

endmodule
