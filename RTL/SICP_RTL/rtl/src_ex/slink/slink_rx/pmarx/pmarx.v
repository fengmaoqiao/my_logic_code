// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-06-10
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-06-10  TingtingGan     Original
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

module  PMARX
    (
    clk_125m_0                  ,   
    clk_125m_90                 ,   
    clk_125m_180                ,   
    clk_125m_270                , 
    rst_125m                    , 

    rx_en                       ,
    lvds_rxp_in                 ,   
    lvds_rxn_in                 ,   
    pmarx_pcsrx_dval            ,   
    pmarx_pcsrx_data         
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter    POS_IDLE = 10'h0fa ; // positive idle
parameter    NEG_IDLE = 10'h305 ; // negtive ilde

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_125m_0                          ;   
input   wire                    clk_125m_90                         ;   
input   wire                    clk_125m_180                        ;   
input   wire                    clk_125m_270                        ;   
input   wire                    rst_125m                            ;  

input   wire                    rx_en                               ;
input   wire                    lvds_rxp_in                         ;   
input   wire                    lvds_rxn_in                         ;   

// declare output signal
output  reg                     pmarx_pcsrx_dval                    ;   
output  reg       [9:0]         pmarx_pcsrx_data                    ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            lvds_rx_in                          ;  

// reg signal
reg                             rx_in_0_d1                          ;   
reg                             rx_in_0_d2                          ;   
reg                             rx_in_0_d3                          ;   
reg                             rx_in_0_d4                          ;   

reg                             rx_in_90_d1                         ;   
reg                             rx_in_90_d2                         ;   
reg                             rx_in_90_d3                         ;   
reg                             rx_in_90_d4                         ;  

reg                             rx_in_180_d1                        ;   
reg                             rx_in_180_d2                        ;   
reg                             rx_in_180_d3                        ;   
reg                             rx_in_180_d4                        ;   

reg                             rx_in_270_d1                        ;   
reg                             rx_in_270_d2                        ;   
reg                             rx_in_270_d3                        ;   
reg                             rx_in_270_d4                        ;  

reg     [3:0]                   rx_in_syn_d1                        ;   
reg     [3:0]                   rx_in_syn_d2                        ;   
reg     [3:0]                   rx_in_syn_d3                        ;   
reg     [3:0]                   rx_in_syn_d4                        ;   

reg     [2:0]                   tail_remainder                      ;   
reg     [2:0]                   wr_data_temp                        ;
reg     [2:0]                   wr_data_temp1                       ;   
reg     [2:0]                   wr_data_temp2                       ;   
reg     [2:0]                   wr_data_temp3                       ;   
reg     [2:0]                   wr_data_temp4                       ;   
reg     [2:0]                   wr_data_temp5                       ;   
reg     [2:0]                   wr_data_temp6                       ;   
reg     [2:0]                   wr_data                             ;   
reg                             remain_bit                          ;   
reg                             wr_en                               ;   

reg     [9:0]                   data_tmp                            ;   
reg     [3:0]                   bit_cnt                             ;  
reg                             rx_en_d1                            ;   
reg                             rx_en_d2                            ;  
reg                             overflow_flag                       ;  
reg                             dval_tmp                            ;   
reg                             dval_tmp_d1                         ;   
reg                             dval_tmp_d2                         ;   
reg                             dval_tmp_d3                         ;  

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

//----------------------------------------------------------------------------------
// LVDS difference convert to sigle-ended
//----------------------------------------------------------------------------------
    INBUF_DIFF                  #
    ( 
    .IOSTD                      ( "LVDS33"                  )
    ) 
    U_INBUF_DIFF
    (
    .PADP                       ( lvds_rxp_in               ), 
    .PADN                       ( lvds_rxn_in               ), 
    .Y                          ( lvds_rx_in                )
    );

//----------------------------------------------------------------------------------
// over sample
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m_0 or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        rx_in_0_d1  <=   1'b0 ;
    end
    else begin
        rx_in_0_d1  <=   lvds_rx_in ;
    end
end

always @ ( posedge clk_125m_0 ) begin
    rx_in_0_d2  <=   rx_in_0_d1 ;
    rx_in_0_d3  <=   rx_in_0_d2 ;
    rx_in_0_d4  <=   rx_in_0_d3 ;
end

always @ ( posedge clk_125m_90 or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        rx_in_90_d1  <=   1'b0 ;
    end
    else begin
        rx_in_90_d1  <=   lvds_rx_in ;
    end
end

always @ ( posedge clk_125m_90 ) begin
    rx_in_90_d2  <=   rx_in_90_d1 ;
    rx_in_90_d3  <=   rx_in_90_d2 ;
    rx_in_90_d4  <=   rx_in_90_d3 ;
end

always @ ( posedge clk_125m_180 or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        rx_in_180_d1  <=   1'b0 ;
    end
    else begin
        rx_in_180_d1  <=   lvds_rx_in ;
    end
end

always @ ( posedge clk_125m_180 ) begin
    rx_in_180_d2  <=   rx_in_180_d1 ;
    rx_in_180_d3  <=   rx_in_180_d2 ;
    rx_in_180_d4  <=   rx_in_180_d3 ;
end

always @ ( posedge clk_125m_270 or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        rx_in_270_d1  <=   1'b0 ;
    end
    else begin
        rx_in_270_d1  <=   lvds_rx_in ;
    end
end

always @ ( posedge clk_125m_270 ) begin
    rx_in_270_d2  <=   rx_in_270_d1 ;
    rx_in_270_d3  <=   rx_in_270_d2 ;
    rx_in_270_d4  <=   rx_in_270_d3 ;
end

//----------------------------------------------------------------------------------
// signal synchronization
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m_0 or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        rx_in_syn_d1[3]  <=   1'b0 ;
        rx_in_syn_d1[2]  <=   1'b0 ;
        rx_in_syn_d1[1]  <=   1'b0 ;
        rx_in_syn_d1[0]  <=   1'b0 ;
    end
    else begin
        rx_in_syn_d1[3]  <=   rx_in_0_d4 ;
        rx_in_syn_d1[2]  <=   rx_in_90_d4 ;
        rx_in_syn_d1[1]  <=   rx_in_180_d4 ;
        rx_in_syn_d1[0]  <=   rx_in_270_d4 ;
    end
end

always @ ( posedge clk_125m_0 ) begin
    rx_in_syn_d2  <=   rx_in_syn_d1 ;
    rx_in_syn_d3  <=   rx_in_syn_d2 ;
    rx_in_syn_d4  <=   rx_in_syn_d3 ;
end

//----------------------------------------------------------------------------------
// tail_remainder [2]: tail_remainder is 0 or 1 ; [1:0] : number of tail_remainder
//----------------------------------------------------------------------------------
always @( posedge clk_125m_0 ) begin
    case( rx_in_syn_d3 )
        4'b0000 : 
        begin
            if( tail_remainder[2] == 1'b1 ) begin
                tail_remainder   <=   3'b000 ;
            end
            else begin
                tail_remainder   <=   tail_remainder ;
            end
        end
        4'b0001 : tail_remainder   <=   3'b101 ;
        4'b0011 : tail_remainder   <=   3'b110 ;
        4'b0111 : tail_remainder   <=   3'b111 ;
        4'b1111 : 
        begin
            if( tail_remainder[2] == 1'b0 ) begin
                tail_remainder   <=   3'b000 ;
            end
            else begin
                tail_remainder   <=   tail_remainder ;
            end
        end
        4'b1110 : tail_remainder   <=   3'b001 ;
        4'b1100 : tail_remainder   <=   3'b010 ;
        4'b1000 : tail_remainder   <=   3'b011 ;
        default : tail_remainder   <=   3'b000 ;
    endcase
end

//----------------------------------------------------------------------------------
// wr_data_temp [2]: total number of write data [1]:fisrt data  [0]:second data
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m_0 ) begin
    if( tail_remainder == 3'b111 ) begin
        wr_data_temp1   <=   3'b110 ;
    end
    else begin
        wr_data_temp1   <=   3'b010 ;
    end
end

always @ ( posedge clk_125m_0 ) begin
    if( tail_remainder == 3'b111 ) begin
        wr_data_temp2   <=   3'b011 ;
    end
    else if( tail_remainder[2] == 1'b0 && tail_remainder[1:0] != 2'b00 ) begin
        wr_data_temp2   <=   3'b010 ;
    end
    else begin
        wr_data_temp2   <=   3'b000 ;
    end
end

always @ ( posedge clk_125m_0 ) begin
    if( tail_remainder == 3'b111 ) begin
        wr_data_temp3   <=   3'b011 ;
    end
    else if( tail_remainder[2:1] == 2'b01 ) begin
        wr_data_temp3   <=   3'b010 ;
    end
    else begin
        wr_data_temp3   <=   3'b000 ;
    end
end

always @ ( posedge clk_125m_0 ) begin
    if( tail_remainder == 2'b011 ) begin
        wr_data_temp4   <=   3'b101 ;
    end
    else begin
        wr_data_temp4   <=   3'b011 ;
    end
end

always @ ( posedge clk_125m_0 ) begin
    if( tail_remainder[2] == 1'b1 ) begin
        wr_data_temp5   <=   3'b011 ;
    end
    else if( tail_remainder == 3'b011 ) begin
        wr_data_temp5   <=   3'b010 ;
    end
    else begin
        wr_data_temp5   <=   3'b000 ;
    end
end

always @ ( posedge clk_125m_0 ) begin
    if( tail_remainder == 3'b011 ) begin
        wr_data_temp6   <=   3'b010 ;
    end
    else if( tail_remainder[2:1] == 2'b11 ) begin
        wr_data_temp6   <=   3'b011 ;
    end
    else begin
        wr_data_temp6   <=   3'b000 ;
    end
end

always @( posedge clk_125m_0 ) begin
    case( rx_in_syn_d4 )
        4'b0000 :   wr_data_temp   <=   wr_data_temp1 ;
        4'b0001 :   wr_data_temp   <=   wr_data_temp1 ;
        4'b0011 :   wr_data_temp   <=   wr_data_temp2 ; 
        4'b0111 :   wr_data_temp   <=   wr_data_temp3 ; 
        4'b1111 :   wr_data_temp   <=   wr_data_temp4 ;
        4'b1110 :   wr_data_temp   <=   wr_data_temp4 ; 
        4'b1100 :   wr_data_temp   <=   wr_data_temp5 ; 
        4'b1000 :   wr_data_temp   <=   wr_data_temp6 ; 
        default :   wr_data_temp   <=   3'b000 ;
    endcase
end

//----------------------------------------------------------------------------------
// FIFO write control
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m_0 ) begin
    wr_data      <=   wr_data_temp ;
end

always @ ( posedge clk_125m_0 ) begin
    remain_bit   <=   wr_data[0] ;
end

always @ ( posedge clk_125m_0 ) begin
    if( wr_data_temp == 3'b000 ) begin
        wr_en   <=   1'b0 ;
    end
    else begin
        wr_en   <=   1'b1 ;
    end
end

//----------------------------------------------------------------------------------
// serious to parallel
//----------------------------------------------------------------------------------
always @ ( posedge clk_125m_0 or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
		rx_en_d1	<=	 1'b0 ;
		rx_en_d2	<=	 1'b0 ;
	end
    else begin
		rx_en_d1	<=	 rx_en ;
		rx_en_d2	<=	 rx_en_d1 ;
    end
end

always @ ( posedge clk_125m_0 or negedge rst_125m ) begin
    if( rst_125m == 1'b0 ) begin
        bit_cnt  <=   4'hf  ;   
    end
    else begin
        if ( wr_en == 1'b1 ) begin
            if ( ( wr_data[2] == 1'b0 && bit_cnt == 4'd9 ) || ( wr_data[2] == 1'b1 && bit_cnt == 4'd8 ) ) begin
                bit_cnt  <=   4'd0  ; 
            end
            else if ( wr_data[2] == 1'b1 && bit_cnt == 4'd9 ) begin
                bit_cnt  <=   4'd1  ; 
            end
            else if ( ( data_tmp == POS_IDLE || data_tmp == NEG_IDLE ) && overflow_flag == 1'b0 ) begin
                bit_cnt  <=   4'h0  ; 
            end
            else if ( wr_data[2] == 1'b0 ) begin
                bit_cnt  <=   bit_cnt + 1'b1  ;  
            end
            else if ( wr_data[2] == 1'b1 ) begin
                bit_cnt  <=   bit_cnt + 2'd2  ;  
            end
        end
    end
end

always @ ( posedge clk_125m_0 ) begin
    if( wr_en == 1'b1 ) begin
        if ( wr_data[2] == 1'b0 ) begin
            if ( overflow_flag == 1'b1 ) begin
                data_tmp  <=    { wr_data[0] , remain_bit , data_tmp[9:2] } ; 
            end
            else begin
                data_tmp  <=    { wr_data[0] , data_tmp[9:1] } ; 
            end
        end
        else begin
            if( bit_cnt == 4'd8 ) begin
                data_tmp  <=    { wr_data[1] , data_tmp[9:1] } ;
            end
            else if ( overflow_flag == 1'b1 ) begin
                data_tmp  <=    { wr_data[0] , wr_data[1] , remain_bit , data_tmp[9:3] } ;
            end
            else begin
                data_tmp  <=    { wr_data[0] , wr_data[1] , data_tmp[9:2] } ;
            end
        end
    end
    else begin
        if ( overflow_flag == 1'b1 ) begin
            data_tmp  <=    { remain_bit , data_tmp[9:1] } ; 
        end
    end
end

always @ ( posedge clk_125m_0 ) begin
    if( bit_cnt == 4'd8 && wr_data[2] == 1'b1 ) begin
        overflow_flag	<=	 1'b1 ;
    end
    else begin
		overflow_flag	<=	 1'b0 ;
    end
end

always @ ( posedge clk_125m_0 ) begin
    if( ( bit_cnt == 4'd9 && wr_en == 1'b1 ) || overflow_flag == 1'b1 ) begin
        dval_tmp	<=	 1'b1 ;
    end
    else begin
		dval_tmp	<=	 1'b0 ;
    end
end

always @ ( posedge clk_125m_0 ) begin
    if( bit_cnt == 4'd9 || overflow_flag == 1'b1 ) begin
        pmarx_pcsrx_data  <=    data_tmp ; 
    end
    else ;
end

always @ ( posedge clk_125m_0 ) begin
    if ( rx_en_d2 == 1'b1 ) begin
        dval_tmp_d1 <=    dval_tmp ; 
    end
    else begin
        dval_tmp_d1 <=    1'b0 ; 
    end
end

always @ ( posedge clk_125m_0 ) begin
    dval_tmp_d2       <=    dval_tmp_d1 ; 
    dval_tmp_d3       <=    dval_tmp_d2 ; 
    pmarx_pcsrx_dval  <=    dval_tmp_d3 ; 
end

endmodule

