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

module  EX_SELF_CMM
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   

    // cfg pkt from anoter ex
    ex_rxsdu_empty              ,   
    rxsdu_ex_rdreq              ,   
    ex_rxsdu_dval               ,   
    ex_rxsdu_data               ,   

    // write port
    wr_self_cfg_dval            ,   
    wr_self_cfg_data            ,   

    // read port
    slot_num                    ,   
    cfg_en                      ,   
    card_id                     ,   
    code_version                ,   
    enable_slot                 ,
    run_cycle                   ,

    src_id1                     ,
    src_port1                   ,
    src_id2                     ,
    src_port2                   ,

    dst_id1                     ,
    dst_port1                   ,
    dst_id2                     ,
    dst_port2                       
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   

input   wire    [3:0]           slot_num                            ;   
input   wire                    ex_rxsdu_empty                      ;   
input   wire                    ex_rxsdu_dval                       ;   
input   wire    [17:0]          ex_rxsdu_data                       ;   
input   wire                    wr_self_cfg_dval                    ;   
input   wire    [17:0]          wr_self_cfg_data                    ;   

// declare output signal
output  wire                    rxsdu_ex_rdreq                      ;   
output  reg                     cfg_en                              ;   
output  reg     [31:0]          card_id                             ;   
output  reg     [15:0]          code_version                        ;   
output  reg     [31:0]          enable_slot                         ;   
output  reg     [15:0]          run_cycle                           ;

output  reg     [31:0]          src_id1                             ;   
output  reg     [31:0]          src_id2                             ;   
output  reg     [31:0]          dst_id1                             ;   
output  reg     [31:0]          dst_id2                             ;   

output  reg     [7:0]           src_port1                           ;   
output  reg     [7:0]           src_port2                           ;   
output  reg     [7:0]           dst_port1                           ;   
output  reg     [7:0]           dst_port2                           ;      

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            cfg_from_ex                         ;   
wire        [17:0]              cfg_from_ex_data                    ;  
wire                            wr_self_cfg_ring                    ;   
wire                            cfg_from_ex_ring                    ;   

// reg signal
reg                             data_sop                            ;   
reg                             data_sop_d1                         ;   
reg                             data_sop_d2                         ;   
reg                             data_eop                            ;   
reg                             data_eop_d1                         ;   
reg                             data_eop_d2                         ;   
reg         [17:0]              tx_data                             ;   
reg         [17:0]              tx_data_d1                          ;   
reg         [17:0]              tx_data_d2                          ;   
reg         [7:0]               dest_addr                           ;   
reg         [7:0]               sour_addr                           ;   
reg         [15:0]              pkt_type                            ;   
reg         [9:0]               cfg_dval_cnt                        ; 
reg                             cfg_from_ex_dval                    ; 
reg                             wr_cfg_dval                         ;   
reg         [17:0]              wr_cfg_data                         ;  
reg                             wr_self_cfg_dval_d1                 ;   
reg                             cfg_from_ex_dval_d1                 ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
localparam      OCTET_ID_SEQ    =   5'd0        ,
                OCTET_HW_VER    =   5'd2        ,
                OCTET_CH_ENA    =   5'd4        ,
                OCTET_CM_CFG    =   5'd6        ,
                OCTET_RX_PORT1  =   5'd8        , 
                OCTET_RX_PORT2  =   5'd12       ,
                OCTET_TX_PORT1  =   5'd24       ,
                OCTET_TX_PORT2  =   5'd28       ;

            
/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign  rxsdu_ex_rdreq  =   ex_rxsdu_empty == 1'b0 ? 1'b1 : 1'b0 ; 

//----------------------------------------------------------------------------------
// data delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        data_sop   <=   1'b0 ;
    end
    else if( ex_rxsdu_dval == 1'b1 && ex_rxsdu_data[17] == 1'b1 )begin
        data_sop   <=   1'b1 ;
    end
    else begin
        data_sop   <=   1'b0 ;
    end
end

always @ ( posedge clk_12_5m ) begin
    data_sop_d1   <=   data_sop ;
    data_sop_d2   <=   data_sop_d1 ;
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        data_eop   <=   1'b0 ;
    end
    else if( ex_rxsdu_dval == 1'b1 && ex_rxsdu_data[16] == 1'b1 )begin
        data_eop   <=   1'b1 ;
    end
    else begin
        data_eop   <=   1'b0 ;
    end
end

always @ ( posedge clk_12_5m ) begin
    data_eop_d1   <=   data_eop ;
    data_eop_d2   <=   data_eop_d1 ;
end


always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        tx_data   <=   10'h00 ;
    end
    else if( ex_rxsdu_dval == 1'b1 )begin
        tx_data   <=   ex_rxsdu_data ;
    end
    else begin
        tx_data   <=   10'h00 ;
    end
end

always @ ( posedge clk_12_5m ) begin
    tx_data_d1   <=   tx_data ;
    tx_data_d2   <=   tx_data_d1 ;
end

//----------------------------------------------------------------------------------
// DA & SA & TYPE parse
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        dest_addr   <=   8'h00 ;
    end
    else if( ex_rxsdu_dval == 1'b1 && ex_rxsdu_data[17] == 1'b1 )begin
        dest_addr   <=   ex_rxsdu_data[15:8] ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sour_addr   <=   8'h00 ;
    end
    else if( ex_rxsdu_dval == 1'b1 && ex_rxsdu_data[17] == 1'b1 )begin
        sour_addr   <=   ex_rxsdu_data[7:0] ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_type   <=   16'h00 ;
    end
    else if( data_sop == 1'b1 )begin
        pkt_type   <=   ex_rxsdu_data[15:0] ;
    end
end

//----------------------------------------------------------------------------------
// self configuration 
//----------------------------------------------------------------------------------
assign  cfg_from_ex  = dest_addr[3:0] == slot_num && sour_addr[7] == 1'b1 && pkt_type == `CFG_TYPE ;  

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        cfg_from_ex_dval   <=   1'b0 ;
    end
    else begin
        if( ex_rxsdu_dval == 1'b1 && ex_rxsdu_data[16] == 1'b1 )begin
            cfg_from_ex_dval   <=   1'b0 ;
        end
        else if( data_sop_d2 == 1'b1 && cfg_from_ex == 1'b1 )begin
            cfg_from_ex_dval   <=   1'b1 ;
        end
    end
end

assign  cfg_from_ex_data    =   ex_rxsdu_data ;

//----------------------------------------------------------------------------------
// cfg data 
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        wr_cfg_dval   <=   1'b0 ;
    end
    else begin
        if ( cfg_en == 1'b0 ) begin
            if ( wr_self_cfg_dval == 1'b1 ) begin 
                wr_cfg_dval   <=   1'b1 ;
            end
            else if ( cfg_from_ex_dval == 1'b1 ) begin
                wr_cfg_dval   <=   1'b1 ;
            end
        end
        else begin
            wr_cfg_dval   <=   1'b0 ;
        end
    end
end


always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        wr_cfg_data   <=   18'h00 ;
    end
    else begin
        if( cfg_en == 1'b0 ) begin 
            if ( wr_self_cfg_dval == 1'b1 ) begin 
                wr_cfg_data   <=   wr_self_cfg_data ;
            end
            else if ( cfg_from_ex_dval == 1'b1 ) begin
                wr_cfg_data   <=   cfg_from_ex_data ;
            end
        end // if( cfg_en == 1'b0 )
        else begin
            wr_cfg_data <= 18'h00;
        end
    end
end

//----------------------------------------------------------------------------------
// write control 
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        cfg_dval_cnt   <=   10'h00 ;
    end
    else begin
        if ( wr_cfg_dval == 1'b1 ) begin
            cfg_dval_cnt   <=   cfg_dval_cnt + 1'b1 ;
        end
        else begin
            cfg_dval_cnt   <=   10'h00 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        cfg_en     <=   1'b0 ;
    end
    else if( wr_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == OCTET_TX_PORT2 ) begin
            cfg_en <=   1'b1 ;
        end
        else
        ;
    end // else if( wr_cfg_dval == 1'b1 )
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        card_id   <=   32'h00 ;
    end
    else if( wr_cfg_dval == 1'b1 ) begin
        if( cfg_dval_cnt == OCTET_ID_SEQ ) begin
            card_id[15:0]    <=   wr_cfg_data[15:0] ;
        end
        else if( cfg_dval_cnt == OCTET_ID_SEQ + 1 ) begin
            card_id[31:16]    <=   wr_cfg_data[15:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        code_version   <=   16'h00 ;
    end
    else begin
        if( wr_cfg_dval == 1'b1 && cfg_dval_cnt == OCTET_HW_VER + 1 ) begin
            code_version    <=   wr_cfg_data[15:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        enable_slot                <=   32'h0000c000;
    end
    else begin
        if( wr_cfg_dval == 1'b1 ) begin
            if ( cfg_dval_cnt == OCTET_CH_ENA ) begin
                enable_slot[15:0]  <=   wr_cfg_data[15:0] ;
            end
            else if ( cfg_dval_cnt == OCTET_CH_ENA + 1 ) begin
                enable_slot[31:16] <=   wr_cfg_data[15:0] ;
            end
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        run_cycle     <=   16'h00 ;
    end
    else begin
        if( wr_cfg_dval == 1'b1 && cfg_dval_cnt == OCTET_CM_CFG ) begin
            run_cycle <=   wr_cfg_data[15:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        src_id1                <= 32'd0;
    end
    else begin
        if( wr_cfg_dval == 1'b1 ) begin
            if( cfg_dval_cnt == OCTET_RX_PORT1 ) begin
                src_id1[15:0]  <= wr_cfg_data[15:0] ;
            end
            else if ( cfg_dval_cnt == OCTET_RX_PORT1 + 1 ) begin
                src_id1[31:16] <= wr_cfg_data[15:0] ;
            end
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        src_port1     <= 8'd0;
    end
    else begin
        if( wr_cfg_dval == 1'b1 && cfg_dval_cnt == OCTET_RX_PORT1 + 2 ) 
            src_port1 <= wr_cfg_data[7:0];
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        src_id2                <= 32'd0;
    end
    else begin
        if( wr_cfg_dval == 1'b1) begin
            if( cfg_dval_cnt == OCTET_RX_PORT2 ) begin
                src_id2[15:0]  <= wr_cfg_data[15:0] ;
            end
            else if( cfg_dval_cnt == OCTET_RX_PORT2 + 1 ) begin
                src_id2[31:16] <= wr_cfg_data[15:0] ;
            end
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        src_port2     <= 8'd0;
    end
    else begin
        if( wr_cfg_dval == 1'b1 && cfg_dval_cnt == OCTET_RX_PORT2 + 2 ) 
            src_port2 <= wr_cfg_data[7:0];
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        dst_id1                <= 32'd0;
    end
    else begin
        if( wr_cfg_dval == 1'b1 ) begin
            if( cfg_dval_cnt == OCTET_TX_PORT1 ) 
                dst_id1[15:0]  <= wr_cfg_data[15:0] ;
            else if( cfg_dval_cnt == OCTET_TX_PORT1 + 1 )
                dst_id1[31:16] <= wr_cfg_data[15:0] ; 
        end 
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        dst_port1     <= 8'd0;
    end
    else begin
        if ( wr_cfg_dval == 1'b1 && cfg_dval_cnt == OCTET_TX_PORT2 + 2)
            dst_port1 <= wr_cfg_data[7:0] ; 
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        dst_id2                <= 32'd0;
    end
    else begin
        if( wr_cfg_dval == 1'b1 ) begin
            if( cfg_dval_cnt == OCTET_TX_PORT2 )
                dst_id2[15:0]  <= wr_cfg_data[15:0] ; 
            else if( cfg_dval_cnt == OCTET_TX_PORT2 + 1)
                dst_id2[31:16] <= wr_cfg_data[15:0] ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        dst_port2     <= 8'd0;
    end
    else begin
        if( wr_cfg_dval == 1'b1 && cfg_dval_cnt == OCTET_TX_PORT2 + 2) 
            dst_port2 <= wr_cfg_data[7:0] ;
    end
end


endmodule

