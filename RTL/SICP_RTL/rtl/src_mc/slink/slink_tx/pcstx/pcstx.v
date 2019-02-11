// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-06-21
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-06-21  TingtingGan     Original
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

module PCSTX
    (
    clk_12_5m                   ,   
    rst_12_5m                   ,   

    mactx_pcstx_data            ,   
    mactx_pcstx_dval            ,   

    pcstx_pmatx_data              
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter    POS = 2'b10 ; // positive
parameter    NEU = 2'b00 ; // neutral
parameter    NEG = 2'b01 ; // negtive

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   
input   wire       [7:0]        mactx_pcstx_data                    ;   
input   wire                    mactx_pcstx_dval                    ;   

// declare output signal
output  reg       [9:0]         pcstx_pmatx_data                    ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [1:0]               rd_6b                               ;   
wire        [1:0]               rd_4b                               ; 
wire        [5:0]               encoder_6b_new                      ;  
wire                            reveral_flag                        ;   

// reg signal
reg         [5:0]               encoder_6b                          ;   
reg         [1:0]               disp_6b                             ;   
reg         [3:0]               encoder_4b                          ;   
reg         [1:0]               disp_4b                             ;
reg         [5:0]               encoder_6b_new_tmp                  ;   
reg         [3:0]               encoder_4b_new                      ;  
reg                             mactx_pcstx_dval_d1                 ;   
reg                             sp_4b_rdp                           ;   
reg                             sp_4b_rdn                           ; 
reg         [1:0]               rd                                  ;

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// 6b_disp: 00 null   10 RD-  01 RD+
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        encoder_6b  <=   6'h00 ;
        disp_6b     <=   NEU ;
    end
    else begin
        if( mactx_pcstx_dval == 1'b1 ) begin
            case ( mactx_pcstx_data[4:0] )
                5'd0    :  begin
                    encoder_6b  <=   6'b100111 ;   
                    disp_6b     <=   POS ; 
                end  
                5'd1    :  begin
                    encoder_6b  <=   6'b011101 ; 
                    disp_6b     <=   POS ; 
                end 
                5'd2    :  begin
                    encoder_6b  <=   6'b101101 ;
                    disp_6b     <=   POS ; 
                end 
                5'd3    :  begin 
                    encoder_6b  <=   6'b110001 ;  
                    disp_6b     <=   NEU ; 
                end 
                5'd4    :  begin
                    encoder_6b  <=   6'b110101 ;
                    disp_6b     <=   POS ;
                end 
                5'd5    :  begin
                    encoder_6b  <=   6'b101001 ; 
                    disp_6b     <=   NEU ; 
                end 
                5'd6    :  begin
                    encoder_6b  <=   6'b011001 ;
                    disp_6b     <=   NEU ; 
                end 
                5'd7    :  begin 
                    encoder_6b  <=   6'b111000 ; 
                    disp_6b     <=   NEU ;
                end 
                5'd8    :  begin
                    encoder_6b  <=   6'b111001 ;
                    disp_6b     <=   POS ; 
                end 
                5'd9    :  begin
                    encoder_6b  <=   6'b100101 ;
                    disp_6b     <=   NEU ; end 
                5'd10   :  begin
                    encoder_6b  <=   6'b010101 ;
                    disp_6b     <=   NEU ;
                end 
                5'd11   :  begin
                    encoder_6b  <=   6'b110100 ;
                    disp_6b     <=   NEU ; 
                end 
                5'd12   :  begin
                    encoder_6b  <=   6'b001101 ;
                    disp_6b     <=   NEU ; 
                end 
                5'd13   :  begin
                    encoder_6b  <=   6'b101100 ;
                    disp_6b     <=   NEU ; 
                end 
                5'd14   :  begin
                    encoder_6b  <=   6'b011100 ;
                    disp_6b     <=   NEU ;
                end 
                5'd15   :  begin
                    encoder_6b  <=   6'b010111 ;
                    disp_6b     <=   POS ;
                end
                5'd16   :  begin
                    encoder_6b  <=   6'b011011 ;
                    disp_6b     <=   POS ; 
                end 
                5'd17   :  begin
                    encoder_6b  <=   6'b100011 ;
                    disp_6b     <=   NEU ; 
                end 
                5'd18   :  begin
                    encoder_6b  <=   6'b010011 ;
                    disp_6b     <=   NEU ; 
                end 
                5'd19   :  begin
                    encoder_6b  <=   6'b110010 ;
                    disp_6b     <=   NEU ;
                end 
                5'd20   :  begin
                    encoder_6b  <=   6'b001011 ;
                    disp_6b     <=   NEU ; 
                end 
                5'd21   :  begin
                    encoder_6b  <=   6'b101010 ;
                    disp_6b     <=   NEU ; 
                end 
                5'd22   :  begin
                    encoder_6b  <=   6'b011010 ;
                    disp_6b     <=   NEU ;
                end 
                5'd23   :  begin
                    encoder_6b  <=   6'b111010 ;
                    disp_6b     <=   POS ; 
                end 
                5'd24   :  begin
                    encoder_6b  <=   6'b110011 ;
                    disp_6b     <=   POS ;
                end 
                5'd25   :  begin
                    encoder_6b  <=   6'b100110 ;
                    disp_6b     <=   NEU ;
                end 
                5'd26   :  begin
                    encoder_6b  <=   6'b010110 ;   
                    disp_6b     <=   NEU ;
                end 
                5'd27   :  begin
                    encoder_6b  <=   6'b110110 ;
                    disp_6b     <=   POS ; 
                end 
                5'd28   :  begin
                    encoder_6b  <=   6'b001110 ;
                    disp_6b     <=   NEU ; 
                end
                5'd29   :  begin
                    encoder_6b  <=   6'b101110 ; 
                    disp_6b     <=   POS ; 
                end 
                5'd30   :  begin
                    encoder_6b  <=   6'b011110 ;
                    disp_6b     <=   POS ; 
                end 
                5'd31   :  begin
                    encoder_6b  <=   6'b101011 ;
                    disp_6b     <=   POS ;
                end 
            endcase
        end
        else begin
            encoder_6b  <=   6'b001111 ;
            disp_6b     <=   POS ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
      sp_4b_rdp     <=   1'b0 ;
    end
    else begin
        if ( mactx_pcstx_data[7:5] == 3'd7 && mactx_pcstx_dval == 1'b1 ) begin
            case ( mactx_pcstx_data[4:0] )
              11 : sp_4b_rdp    <=    1'b1 ;
              13 : sp_4b_rdp    <=    1'b1 ;
              14 : sp_4b_rdp    <=    1'b1 ;
              default : begin
                  sp_4b_rdp <=   1'b0 ;
                  end
            endcase
        end
        else begin
          sp_4b_rdp     <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
      sp_4b_rdn     <=   1'b0 ;
    end
    else begin
        if ( mactx_pcstx_data[7:5] == 3'd7 && mactx_pcstx_dval == 1'b1 ) begin
            case ( mactx_pcstx_data[4:0] )
              17 : sp_4b_rdn    <=    1'b1 ;
              18 : sp_4b_rdn    <=    1'b1 ;
              20 : sp_4b_rdn    <=    1'b1 ;
              default : begin
                  sp_4b_rdn <=   1'b0 ;
                  end
            endcase
        end
        else begin
          sp_4b_rdn     <=   1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// 3B/4B
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        encoder_4b  <=   4'h0 ;
        disp_4b     <=   NEU ;
    end
    else begin
        if( mactx_pcstx_dval == 1'b1 ) begin
            case ( mactx_pcstx_data[7:5] )
                3'd0    :  begin 
                    encoder_4b  <=   4'b0100 ;   
                    disp_4b     <=   NEG ; 
                end  
                3'd1    :  begin
                    encoder_4b  <=   4'b1001 ;   
                    disp_4b     <=   NEU ; 
                end 
                3'd2    :  begin
                    encoder_4b  <=   4'b0101 ;
                    disp_4b     <=   NEU ; 
                end 
                3'd3    :  begin
                    encoder_4b  <=   4'b0011 ;
                    disp_4b     <=   NEU ; 
                end 
                3'd4    :  begin
                    encoder_4b  <=   4'b0010 ;
                    disp_4b     <=   NEG ; 
                end 
                3'd5    :  begin
                    encoder_4b  <=   4'b1010 ;
                    disp_4b     <=   NEU ; 
                end 
                3'd6    :  begin 
                    encoder_4b  <=   4'b0110 ;  
                    disp_4b     <=   NEU ; 
                end 
                3'd7    :  begin 
                    encoder_4b  <=   4'b0001 ;
                    disp_4b     <=   NEG ; 
                end 
            endcase
        end
        else begin
            encoder_4b  <=   4'b1010 ;
            disp_4b     <=   NEU ;
        end
    end
end

//----------------------------------------------------------------------------------
// disparity control
//----------------------------------------------------------------------------------
assign  rd_6b = ( disp_6b == NEU ) ? rd : ( disp_6b == rd || reveral_flag == 1'b1 ) ? ~ disp_6b : disp_6b ;
assign  rd_4b = ( disp_4b == NEU ) ? rd_6b : ( disp_4b == rd_6b ) ? ~ disp_4b : disp_4b ;

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        rd   <=   NEG ;
    end
    else begin
        rd   <=   rd_4b ;
    end
end

//----------------------------------------------------------------------------------
// new data
//----------------------------------------------------------------------------------

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        mactx_pcstx_dval_d1   <=   1'b0 ;
    end
    else begin
        mactx_pcstx_dval_d1   <=   mactx_pcstx_dval ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        encoder_6b_new_tmp   <=   6'h0 ;
    end
    else begin
        if( disp_6b == NEU ) begin
            if( encoder_6b == 6'b111000 && rd == POS ) begin
                encoder_6b_new_tmp  <=   ~ encoder_6b  ;
            end
            else begin
                encoder_6b_new_tmp  <=   encoder_6b ;
            end
        end 
        else begin
            if( disp_6b == rd ) begin
                encoder_6b_new_tmp  <=  ~ encoder_6b ;
            end
            else begin
                encoder_6b_new_tmp  <=  encoder_6b ;
            end
        end
    end
end

assign  reveral_flag   = ( encoder_4b_new == 4'b1110 && ( encoder_6b_new_tmp == 6'b011011 || 
                           encoder_6b_new_tmp == 6'b110011 || encoder_6b_new_tmp == 6'b101011 ) ) ;

assign  encoder_6b_new = reveral_flag == 1'b1 ? ~ encoder_6b_new_tmp : encoder_6b_new_tmp ;

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        encoder_4b_new   <=   4'h0 ;
    end
    else begin
        if( disp_4b == NEU ) begin
            if( rd_6b == NEG && mactx_pcstx_dval_d1 == 1'b0 ) begin
                encoder_4b_new  <=  ~ encoder_4b ;
            end
            else if( encoder_4b == 4'b0011 && encoder_6b_new[5:3] == 3'b111 ) begin
                encoder_4b_new  <=  ~ encoder_4b ;
            end
            else begin
                encoder_4b_new  <=   encoder_4b ;
            end
        end
        else begin
            if( disp_4b == rd_6b ) begin
                if( sp_4b_rdn == 1'b1 ) begin
                    encoder_4b_new  <=   4'b0111 ;
                end
                else begin
                    encoder_4b_new  <=   ~ encoder_4b ;
                end
            end
            else begin
                if( sp_4b_rdp == 1'b1 ) begin
                    encoder_4b_new  <=   4'b1000 ;
                end
                else begin
                    encoder_4b_new  <=   encoder_4b ;
                end
            end
        end
    end
end

always @ ( posedge clk_12_5m ) begin
    pcstx_pmatx_data <= { encoder_6b_new , encoder_4b_new } ;
end



endmodule

