// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SELF_CMM
// CREATE DATE      :   2017-09-07
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-07  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   The configuration Memory Management of MPU board self
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

module  SELF_CMM
    (
    // clock & reset
    clk_emif                    ,   
    rst_emif                    ,   

    // write port
    wr_sel                      ,   
    wr_en                       ,   
    wr_data                     ,   

    // read port
    cfg_wr_ok                   ,   
    chn_type0                   ,   
    chn_type1                   ,   
    chn_type2                   ,   
    chn_type3                   ,   
    chn_type4                   ,   
    chn_type5                   ,   
    chn_type6                   ,   
    chn_type7                   ,   
    chn_type8                   ,   
    chn_type9                   ,   
    chn_type10                  ,   
    chn_type11                  ,   
    chn_type12                  ,   
    chn_type13                  ,   
    ex_box_data_ena0            ,   
    ex_box_data_ena1            ,   
    ex_box_data_ena2            ,   
    ex_box_data_ena3            ,   
    ex_box_cfg_ena0             ,   
    ex_box_cfg_ena1             ,   
    ex_box_cfg_ena2             ,   
    ex_box_cfg_ena3             ,   
    card_id                     ,   
    code_version                ,   
    enable_slot                 ,   
    run_cycle                   ,   
    redundancy_mode                
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   BASE0_ADDR  =   10'd0 ;  

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_emif                            ;   
input   wire                    rst_emif                            ;   

input   wire                    wr_sel                              ;   
input   wire                    wr_en                               ;   
input   wire        [17:0]      wr_data                             ;

// declare output signal
output  reg         [4:0]       chn_type0                           ;   
output  reg         [4:0]       chn_type1                           ;   
output  reg         [4:0]       chn_type2                           ;   
output  reg         [4:0]       chn_type3                           ;   
output  reg         [4:0]       chn_type4                           ;   
output  reg         [4:0]       chn_type5                           ;   
output  reg         [4:0]       chn_type6                           ;   
output  reg         [4:0]       chn_type7                           ;   
output  reg         [4:0]       chn_type8                           ;   
output  reg         [4:0]       chn_type9                           ;   
output  reg         [4:0]       chn_type10                          ;   
output  reg         [4:0]       chn_type11                          ;   
output  reg         [4:0]       chn_type12                          ;   
output  reg         [4:0]       chn_type13                          ;   
output  reg         [3:0]       ex_box_data_ena0                    ;   
output  reg         [3:0]       ex_box_data_ena1                    ;   
output  reg         [3:0]       ex_box_data_ena2                    ;   
output  reg         [3:0]       ex_box_data_ena3                    ;   
output  reg         [3:0]       ex_box_cfg_ena0                     ;   
output  reg         [3:0]       ex_box_cfg_ena1                     ;   
output  reg         [3:0]       ex_box_cfg_ena2                     ;   
output  reg         [3:0]       ex_box_cfg_ena3                     ;   
output  reg         [31:0]      card_id                             ;   
output  reg         [15:0]      code_version                        ;   
output  reg         [15:0]      enable_slot                         ;   
output  reg         [15:0]      run_cycle                           ;   
output  reg         [7:0]       redundancy_mode                     ;   
output  reg                     cfg_wr_ok                           ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg                             wr_sel_d1                           ; 
reg                             wr_en_d1                            ;   
reg         [17:0]              wr_data_d1                          ;   
reg         [7:0]               cfg_len_cnt                         ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// write control 
//----------------------------------------------------------------------------------

always @ ( posedge clk_emif ) begin
    wr_sel_d1   <=   wr_sel ;
    wr_en_d1    <=   wr_en ;
    wr_data_d1  <=   wr_data ;
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        cfg_wr_ok    <=   1'b1 ;
    end
    else begin
        if ( cfg_len_cnt == 8'd100 ) begin
            cfg_wr_ok    <=   1'b0 ;
        end
        else ;
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        cfg_len_cnt   <=   8'h00 ;
    end
    else begin
        if( wr_sel_d1 == 1'b1 )begin
            if ( wr_en_d1 == 1'b1 ) begin
                cfg_len_cnt   <=   cfg_len_cnt + 1'b1 ;
            end
        end
        else begin
            cfg_len_cnt   <=   8'h00 ;
        end
    end
end

//----------------------------------------------------------------------------------
// important field parse
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        card_id   <=   32'h00 ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && wr_sel_d1 == 1'b1 ) begin
            if( cfg_len_cnt == 8'd0 ) begin
                card_id[15:0]    <=   wr_data_d1[15:0] ;
            end
            else if( cfg_len_cnt == 8'd1 ) begin
                card_id[31:16]    <=   wr_data_d1[15:0] ;
            end
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        code_version   <=   16'h00 ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd3 ) begin
            code_version    <=   wr_data_d1[15:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        enable_slot   <=   16'h00 ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd4 ) begin
            enable_slot     <=   wr_data_d1[15:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        run_cycle   <=   16'h00 ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd6 ) begin
            run_cycle   <=   wr_data_d1[15:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        redundancy_mode   <=   8'h00 ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd7 ) begin
            redundancy_mode   <=   wr_data_d1[7:0] ;
        end
    end
end

//----------------------------------------------------------------------------------
// slot type
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type0   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd20 ) begin
            chn_type0   <=   wr_data_d1[4:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type1   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd20 ) begin
            chn_type1   <=   wr_data_d1[12:8] ;
        end
    end
end
            
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type2   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd21 ) begin
            chn_type2   <=   wr_data_d1[4:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type3   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd21 ) begin
            chn_type3   <=   wr_data_d1[12:8] ;
        end
    end
end
            
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type4   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd22 ) begin
            chn_type4   <=   wr_data_d1[4:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type5   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd22 ) begin
            chn_type5   <=   wr_data_d1[12:8] ;
        end
    end
end
            
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type6   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd23 ) begin
            chn_type6   <=   wr_data_d1[4:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type7   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd23 ) begin
            chn_type7   <=   wr_data_d1[12:8] ;
        end
    end
end
            
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type8   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd24 ) begin
            chn_type8   <=   wr_data_d1[4:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type9   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd24 ) begin
            chn_type9   <=   wr_data_d1[12:8] ;
        end
    end
end
            
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type10   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd25 ) begin
            chn_type10   <=   wr_data_d1[4:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type11   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd25 ) begin
            chn_type11   <=   wr_data_d1[12:8] ;
        end
    end
end
            
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type12   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd26 ) begin
            chn_type12   <=   wr_data_d1[4:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        chn_type13   <=   `COM3_TYPE ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd26 ) begin
            chn_type13   <=   wr_data_d1[12:8] ;
        end
    end
end

//----------------------------------------------------------------------------------
// extention box connect topology 
//----------------------------------------------------------------------------------
always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        ex_box_data_ena0   <=   4'h0 ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd28 ) begin
            ex_box_data_ena0   <=   wr_data_d1[3:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        ex_box_data_ena1   <=   4'h0 ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd28 ) begin
            ex_box_data_ena1   <=   wr_data_d1[11:8] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        ex_box_data_ena2   <=   4'h0 ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd29 ) begin
            ex_box_data_ena2   <=   wr_data_d1[3:0] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        ex_box_data_ena3   <=   4'h0 ;
    end
    else begin
        if( wr_en_d1 == 1'b1 && cfg_len_cnt == 8'd29 ) begin
            ex_box_data_ena3   <=   wr_data_d1[11:8] ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        ex_box_cfg_ena0   <=   4'h0 ;
    end
    else begin
        ex_box_cfg_ena0   <=   ex_box_data_ena0 ;
    end
end

genvar i ;
generate
  for( i = 0 ; i < 4 ; i = i+1 ) begin : nslot

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        ex_box_cfg_ena1[i]   <=   4'h0 ;
    end
    else begin
        if( ex_box_data_ena0[i] == 1'b0 && ex_box_data_ena1[i] == 1'b1 ) begin
            ex_box_cfg_ena1[i]   <=   1'b1 ;
        end
        else begin
            ex_box_cfg_ena1[i]   <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        ex_box_cfg_ena2[i]   <=   4'h0 ;
    end
    else begin
        if( ex_box_data_ena0[i] == 1'b0 && ex_box_data_ena1[i] == 1'b0 && ex_box_data_ena2[i] == 1'b1 ) begin
            ex_box_cfg_ena2[i]   <=   1'b1 ;
        end
        else begin
            ex_box_cfg_ena2[i]   <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_emif or negedge rst_emif ) begin
    if( rst_emif == 1'b0 ) begin
        ex_box_cfg_ena3[i]   <=   4'h0 ;
    end
    else begin
        if( ex_box_data_ena0[i] == 1'b0 && ex_box_data_ena1[i] == 1'b0 && ex_box_data_ena2[i] == 1'b0 && ex_box_data_ena3[i] == 1'b1 ) begin
            ex_box_cfg_ena3[i]   <=   1'b1 ;
        end
        else begin
            ex_box_cfg_ena3[i]   <=   1'b0 ;
        end
    end
end

  end
endgenerate

endmodule

