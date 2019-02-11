// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-06-23
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-06-23  TingtingGan     Original
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

module PCSRX
    (
    clk_125m                    ,   
    rst_125m                    ,

    pmarx_pcsrx_dval            ,   
    pmarx_pcsrx_data            ,  

    pcsrx_macrx_dval            ,   
    pcsrx_macrx_sop             ,   
    pcsrx_macrx_eop             ,   
    pcsrx_macrx_data            , 

    pcs_err                      
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter    POS = 2'b10 ; // positive
parameter    NEU = 2'b00 ; // neutral
parameter    NEG = 2'b01 ; // negtive

parameter    POS_IDLE = 10'h0fa ; // positive idle
parameter    NEG_IDLE = 10'h305 ; // negtive ilde

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_125m                            ;   
input   wire                    rst_125m                            ;   
input   wire                    pmarx_pcsrx_dval                    ;   
input   wire       [9:0]        pmarx_pcsrx_data                    ;   

// declare output signal
output  reg                     pcsrx_macrx_dval                    ;   
output  reg                     pcsrx_macrx_sop                     ;   
output  reg                     pcsrx_macrx_eop                     ;   
output  reg       [7:0]         pcsrx_macrx_data                    ;   
output  wire                    pcs_err                             ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            data_all_zero                       ;   
wire                            data_all_one                        ; 
wire                            idle_flag_ring                      ;   
wire                            idle_flag_fall                      ;  
wire                            eop_tmp                             ;   

// reg signal
reg         [4:0]               decoder_6b                          ;  
reg         [1:0]               disp_6b                             ;
reg         [2:0]               decoder_4b                          ;  
reg         [1:0]               disp_4b                             ;
reg                             pcsrx_dval_d1                       ;   
reg                             pcsrx_dval_d2                       ;   
reg                             pcsrx_dval_d3                       ;   
reg         [9:0]               pcsrx_data_d1                       ;
reg         [9:0]               pcsrx_data_d2                       ;
reg         [1:0]               current_disp                        ;   
reg                             disp_err                            ;  
reg                             idel_err                            ;  
reg         [4:0]               timeout_cnt                         ;
reg                             idle_flag                           ;   
reg                             idle_flag_d1                        ;  
reg                             sop_flag                            ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
assign  pcs_err = ( idel_err == 1'b1 || disp_err == 1'b1 ) ? 1'b1 : 1'b0 ;

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m ) begin
    pcsrx_dval_d1   <=  pmarx_pcsrx_dval ;  
    pcsrx_dval_d2   <=  pcsrx_dval_d1 ;  
    pcsrx_dval_d3   <=  pcsrx_dval_d2 ;  
end

always @ ( posedge clk_125m ) begin
    pcsrx_data_d1   <=  pmarx_pcsrx_data ; 
    pcsrx_data_d2   <=  pcsrx_data_d1 ; 
end

//----------------------------------------------------------------------------------
// 6b decoder
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        decoder_6b <=  5'b0 ; 
        disp_6b <=  NEU ; 
    end 
    else begin
        if ( pcsrx_dval_d1 == 1'b1 ) begin
            case ( pcsrx_data_d1[9:4] )
                6'b100111 : begin
                    decoder_6b  <=  5'd0 ;
                    disp_6b     <=  POS ;  
                end
                6'b011000 : begin
                    decoder_6b  <=  5'd0 ;  
                    disp_6b     <=  NEG ;  
                end
                6'b011101 : begin
                    decoder_6b  <=  5'd1 ;  
                    disp_6b     <=  POS ;  
                end
                6'b100010 : begin
                    decoder_6b  <=  5'd1 ;  
                    disp_6b     <=  NEG ;  
                end
                6'b101101 : begin
                    decoder_6b  <=  5'd2 ;
                    disp_6b     <=  POS ;  
                end
                6'b010010 : begin
                    decoder_6b  <=  5'd2 ; 
                    disp_6b     <=  NEG ;  
                end
                6'b110001 : begin
                    decoder_6b  <=  5'd3 ;
                    disp_6b     <=  NEU ;  
                end
                6'b110101 : begin
                    decoder_6b  <=  5'd4 ;
                    disp_6b     <=  POS ;  
                end
                6'b001010 : begin
                    decoder_6b  <=  5'd4 ;
                    disp_6b     <=  NEG ;  
                end
                6'b101001 : begin
                    decoder_6b  <=  5'd5 ;
                    disp_6b     <=  NEU ;  
                end
                6'b011001 : begin
                    decoder_6b  <=  5'd6 ;
                    disp_6b     <=  NEU ;  
                end
                6'b111000 : begin
                    decoder_6b  <=  5'd7 ;
                    disp_6b     <=  NEU ;  
                end        
                6'b000111 : begin
                    decoder_6b  <=  5'd7 ;
                    disp_6b     <=  NEU ;
                end        
                6'b111001 : begin
                    decoder_6b  <=  5'd8 ;
                    disp_6b     <=  POS ; 
                end
                6'b000110 : begin
                    decoder_6b  <=  5'd8 ; 
                    disp_6b     <=  NEG ;  
                end
                6'b100101 : begin
                    decoder_6b  <=  5'd9 ;
                    disp_6b     <=  NEU ;  
                end
                6'b010101 : begin
                    decoder_6b  <=  5'd10 ;
                    disp_6b     <=  NEU ;  
                end
                6'b110100 : begin
                    decoder_6b  <=  5'd11 ;
                    disp_6b     <=  NEU ;  
                end
                6'b001101 : begin
                    decoder_6b  <=  5'd12 ;
                    disp_6b     <=  NEU ;  
                end
                6'b101100 : begin
                    decoder_6b  <=  5'd13 ;
                    disp_6b     <=  NEU ;  
                end
                6'b011100 : begin
                    decoder_6b  <=  5'd14 ;
                    disp_6b     <=  NEU ;
                end
                6'b010111 : begin
                    decoder_6b  <=  5'd15 ;
                    disp_6b     <=  POS ;  
                end
                6'b101000 : begin
                    decoder_6b  <=  5'd15 ;
                    disp_6b     <=  NEG ;  
                end
                6'b011011 : begin
                    decoder_6b  <=  5'd16 ;
                    disp_6b     <=  POS ;  
                end
                6'b100100 : begin
                    decoder_6b  <=  5'd16 ;
                    disp_6b     <=  NEG ;
                end
                6'b100011 : begin
                    decoder_6b  <=  5'd17 ; 
                    disp_6b     <=  NEU ;  
                end
                6'b010011 : begin
                    decoder_6b  <=  5'd18 ; 
                    disp_6b     <=  NEU ;  
                end
                6'b110010 : begin
                    decoder_6b  <=  5'd19 ;
                    disp_6b     <=  NEU ; 
                end
                6'b001011 : begin
                    decoder_6b  <=  5'd20 ;
                    disp_6b     <=  NEU ;  
                end
                6'b101010 : begin
                    decoder_6b  <=  5'd21 ;
                    disp_6b     <=  NEU ; 
                end
                6'b011010 : begin
                    decoder_6b  <=  5'd22 ;
                    disp_6b     <=  NEU ;  
                end
                6'b111010 : begin
                    decoder_6b  <=  5'd23 ;
                    disp_6b     <=  POS ;  
                end
                6'b000101 : begin
                    decoder_6b  <=  5'd23 ; 
                    disp_6b     <=  NEG ;  
                end
                6'b110011 : begin
                    decoder_6b  <=  5'd24 ;
                    disp_6b     <=  POS ;  
                end
                6'b001100 : begin
                    decoder_6b  <=  5'd24 ;
                    disp_6b     <=  NEG ;  
                end
                6'b100110 : begin
                    decoder_6b  <=  5'd25 ; 
                    disp_6b     <=  NEU ;  
                end
                6'b010110 : begin
                    decoder_6b  <=  5'd26 ;
                    disp_6b     <=  NEU ;  
                end
                6'b110110 : begin
                    decoder_6b  <=  5'd27 ; 
                    disp_6b     <=  POS ;  
                end
                6'b001001 : begin
                    decoder_6b  <=  5'd27 ; 
                    disp_6b     <=  NEG ;  
                end
                6'b001110 : begin
                    decoder_6b  <=  5'd28 ;
                    disp_6b     <=  NEU ;  
                end
                6'b001111 : begin
                    decoder_6b  <=  5'd28 ;
                    disp_6b     <=  POS ;  
                end
                6'b110000 : begin
                    decoder_6b  <=  5'd28 ;
                    disp_6b     <=  NEG ;  
                end
                6'b101110 : begin
                    decoder_6b  <=  5'd29 ; 
                    disp_6b     <=  POS ;  
                end
                6'b010001 : begin
                    decoder_6b  <=  5'd29 ; 
                    disp_6b     <=  NEG ;  
                end
                6'b011110 : begin
                    decoder_6b  <=  5'd30 ; 
                    disp_6b     <=  POS ;  
                end
                6'b100001 : begin
                    decoder_6b  <=  5'd30 ;
                    disp_6b     <=  NEG ;  
                end
                6'b101011 : begin
                    decoder_6b  <=  5'd31 ; 
                    disp_6b     <=  POS ;  
                end
                6'b010100 : begin
                    decoder_6b  <=  5'd31 ; 
                    disp_6b     <=  NEG ;  
                end 
                default   : begin
                    decoder_6b  <=  5'd0 ;  
                    disp_6b     <=  NEU ;  
                end
            endcase
        end
    end
end

//----------------------------------------------------------------------------------
// 4b decoder
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        decoder_4b <=  3'd0 ; 
        disp_4b <=  NEU ; 
    end 
    else begin
        if ( pcsrx_dval_d1 == 1'b1 ) begin
            case ( pcsrx_data_d1[3:0] )
                4'b1011 : begin
                    decoder_4b  <=  3'd0 ;
                    disp_4b     <=  POS ;
                end
                4'b0100 : begin
                    decoder_4b  <=  3'd0 ;
                    disp_4b     <=  NEG ;
                end
                4'b1001 : begin
                    decoder_4b  <=  3'd1 ;
                    disp_4b     <=  NEU ; 
                end
                4'b0101 : begin
                    decoder_4b  <=  3'd2 ;
                    disp_4b     <=  NEU ; 
                end
                4'b1100 : begin
                    decoder_4b  <=  3'd3 ;
                    disp_4b     <=  NEU ;  
                end
                4'b0011 : begin
                    decoder_4b  <=  3'd3 ;
                    disp_4b     <=  NEU ;  
                end
                4'b1101 : begin
                    decoder_4b  <=  3'd4 ;
                    disp_4b     <=  POS ;  
                end
                4'b0010 : begin
                    decoder_4b  <=  3'd4 ;
                    disp_4b     <=  NEG ;
                end
                4'b1010 : begin
                    decoder_4b  <=  3'd5 ;
                    disp_4b     <=  NEU ;  
                end
                4'b0110 : begin
                    decoder_4b  <=  3'd6 ;
                    disp_4b     <=  NEU ;  
                end
                4'b1110 : begin
                    decoder_4b  <=  3'd7 ;  
                    disp_4b     <=  POS ;
                end        
                4'b0001 : begin
                    decoder_4b  <=  3'd7 ;
                    disp_4b     <=  NEG ;  
                end        
                4'b0111 : begin
                    decoder_4b  <=  3'd7 ;
                    disp_4b     <=  POS ;
                end        
                4'b1000 : begin
                    decoder_4b  <=  3'd7 ;
                    disp_4b     <=  NEG ;
                end  
                default : begin
                    decoder_4b  <=  3'd0 ;
                    disp_4b     <=  NEU ;
                end
            endcase
        end
    end
end

//----------------------------------------------------------------------------------
// dvalid 
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m ) begin
    if ( pcsrx_data_d2 == POS_IDLE || pcsrx_data_d2 == NEG_IDLE ) begin
        idle_flag <=  1'b1 ; 
    end
    else begin
        idle_flag <=  1'b0 ; 
    end
end

always @ ( posedge clk_125m ) begin
    idle_flag_d1    <=  idle_flag ; 
end

assign  idle_flag_ring  =   ( idle_flag == 1'b1 && idle_flag_d1 == 1'b0 ) ? 1'b1 : 1'b0 ;
assign  idle_flag_fall  =   ( idle_flag == 1'b0 && idle_flag_d1 == 1'b1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        sop_flag <=  1'b0 ; 
    end 
    else begin
        if ( pcsrx_dval_d3 == 1'b1 ) begin
            sop_flag <=  1'b0 ; 
        end
        else if ( idle_flag_fall == 1'b1 ) begin
            sop_flag <=  1'b1 ; 
        end
    end
end

always @ ( posedge clk_125m ) begin
    if ( pcsrx_dval_d3 == 1'b1 && idle_flag == 1'b0 ) begin
        pcsrx_macrx_dval <=  1'b1 ; 
    end
    else begin
        pcsrx_macrx_dval <=  1'b0 ; 
    end
end

always @ ( posedge clk_125m ) begin
    if ( pcsrx_dval_d3 == 1'b1 && sop_flag == 1'b1 ) begin
        pcsrx_macrx_sop <=  1'b1 ;
    end
    else begin
        pcsrx_macrx_sop <=  1'b0 ; 
    end
end

assign  eop_tmp = ( idle_flag_ring == 1'b1 && { decoder_4b , decoder_6b } == 8'hfd ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_125m ) begin
    pcsrx_macrx_eop <= eop_tmp ; 
end

always @ ( posedge clk_125m ) begin
    pcsrx_macrx_data    <=  { decoder_4b , decoder_6b } ; 
end

//----------------------------------------------------------------------------------
// disparity & idle error check
//----------------------------------------------------------------------------------
assign data_all_zero = | pcsrx_data_d1 ;
assign data_all_one  = & pcsrx_data_d1 ;

always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        disp_err <=  1'b0 ; 
    end 
    else begin
        if ( pcsrx_dval_d1 == 1'b1 ) begin
            if ( data_all_one == 1'b1 || data_all_zero == 1'b0 ) begin
                disp_err <=  1'b1 ; 
            end
            else begin
                disp_err <=  1'b0 ; 
            end
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// idel error
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        timeout_cnt <=  5'h00 ; 
    end 
    else begin
        if ( pcsrx_dval_d1 == 1'b1 ) begin
            timeout_cnt <=  5'h00 ; 
        end
        else if( timeout_cnt == 5'b11111 ) begin
            timeout_cnt <=  timeout_cnt ; 
        end 
        else begin
            timeout_cnt <=  timeout_cnt + 1'b1 ; 
        end
    end
end

always @ ( posedge clk_125m ) begin
    if( timeout_cnt == 5'b11111 ) begin
        idel_err <=  1'b1 ; 
    end 
    else begin
        idel_err <=  1'b0 ; 
    end
end

endmodule

