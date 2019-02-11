// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SELFM
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
// PURPOSE          :   self management
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

module  COM_SELFM
    (
    // clock & reset
    clk_12_5m                   ,   
    rst_12_5m                   ,   

    // self hardware configurantion
    slot_num                    ,

    // configurantion frame interface
    cfg_en                      ,   
    board_type_ok               ,
    card_id                     ,   
    code_version                ,   
    enable_slot                 ,   
    card_type                   ,
    self_cfg_err                ,
    sff_sd                      ,   

    // slink diagnose flag
    lvds_slink_err              ,   
    fiber_slink_err             ,   

    // status frame interface 
    rxsdu_sfm_rdreq             ,   
    sfm_rxsdu_empty             ,   
    sfm_rxsdu_dval              ,   
    sfm_rxsdu_data              ,   

    // debug signals
    debug_bus 
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
`ifdef  SIM  
parameter   SF_PERIOD   =   32'd2500 ;
`else
parameter   SF_PERIOD   =   32'd125000 ; // 80ns * 125000 = 10ms
`endif

parameter   COM_STA_LEN =   16'd16 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_12_5m                           ;   
input   wire                    rst_12_5m                           ;   

input   wire    [3:0]           slot_num                            ; 
input   wire                    cfg_en                              ;   
input   wire    [31:0]          card_id                             ;   
input   wire    [15:0]          code_version                        ;   
input   wire    [15:0]          enable_slot                         ;  
input   wire    [3:0]           sff_sd                              ;   

input   wire    [1:0]           lvds_slink_err                      ;   
input   wire    [3:0]           fiber_slink_err                     ;   
input   wire                    rxsdu_sfm_rdreq                     ;   

// declare output signal
output  reg     [4:0]           card_type                           ;   
output  reg                     sfm_rxsdu_empty                     ;   
output  wire                    sfm_rxsdu_dval                      ;   
output  reg     [17:0]          sfm_rxsdu_data                      ;   
output  wire                    self_cfg_err                        ;   
output  wire                    board_type_ok                       ;

output  wire    [63:0]          debug_bus                           ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [7:0]               cfg_feedback                        ;  
wire        [3:0]               fiber_enable                        ;  
wire        [5:0]               chn_enable                          ;   

wire        [5:0]               chn_slink_err                       ;   
wire        [5:0]               slink_err                           ;  
wire        [3:0]               self_status                         ;   

// reg signal
reg         [3:0]               slot_num_d1                         ;   
reg         [3:0]               slot_num_d2                         ;   
reg         [3:0]               sff_sd_d1                           ;   
reg         [3:0]               sff_sd_d2                           ;   
reg                             slot_num_feedback                   ;   
reg                             board_type_feedback                 ;   
reg                             version_feedback                    ;   
reg                             enable_slot_feedback                ;  
reg         [31:0]              sf_period_cnt                       ;  
reg         [4:0]               sfm_data_addr                       ;   
reg                             sfm_rxsdu_dval_tmp                  ;   
            
/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// card type
//----------------------------------------------------------------------------------
assign board_type_ok = ~board_type_feedback;

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        card_type    <=   `COM1_TYPE ;
    end
    else if ( cfg_en == 1'b1 ) begin
        card_type    <=   card_id[22:18] ;
    end
end

//----------------------------------------------------------------------------------
// external interface signal delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        slot_num_d1   <=   4'h0 ;
        slot_num_d2   <=   4'h0 ;
    end
    else begin
        slot_num_d1   <=   slot_num ;
        slot_num_d2   <=   slot_num_d1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sff_sd_d1   <=   4'h0 ;
        sff_sd_d2   <=   4'h0 ;
    end
    else begin
        sff_sd_d1   <=   sff_sd ;
        sff_sd_d2   <=   sff_sd_d1 ;
    end
end

//----------------------------------------------------------------------------------
// configuration feedback
//----------------------------------------------------------------------------------
assign  cfg_feedback = { ~ cfg_en , 2'b00 , slot_num_feedback , version_feedback , 
                         1'b0 , board_type_feedback , enable_slot_feedback } ;

assign  self_cfg_err =  | cfg_feedback ; 

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        slot_num_feedback    <=   1'b0 ;
    end
    else if ( card_id[3:0] == slot_num_d2 ) begin
        slot_num_feedback    <=   1'b0 ;
    end
    else begin
        slot_num_feedback    <=   1'b1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        board_type_feedback    <=   1'b0 ;
    end
    else if( card_id[22:18] == `COM1_TYPE ) begin
        board_type_feedback    <=   1'b0 ;
    end
    else begin
        board_type_feedback    <=   1'b1 ;
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        enable_slot_feedback    <=   1'b0 ;
    end
    else begin
        if( | enable_slot == 1'b1) begin
            enable_slot_feedback    <=   1'b0 ;
        end
        else begin
            enable_slot_feedback    <=   1'b1 ;
        end
        //if ( ( enable_slot[0] == 1'b1 && sff_sd_d2[0] == 1'b0 ) ||  
        //     ( enable_slot[1] == 1'b1 && sff_sd_d2[1] == 1'b0 ) ||
        //     ( enable_slot[2] == 1'b1 && sff_sd_d2[2] == 1'b0 ) ||
        //     ( enable_slot[3] == 1'b1 && sff_sd_d2[3] == 1'b0 ) ) begin
        //    enable_slot_feedback    <=   1'b1 ;
        //end
        //else begin
        //    enable_slot_feedback    <=   1'b0 ;
        //end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        version_feedback    <=   1'b0 ;
    end
    else if( code_version == `CODE_VERSION ) begin
        version_feedback    <=   1'b0 ;
    end
    else begin
        version_feedback    <=   1'b1 ;
    end
end

//----------------------------------------------------------------------------------
// status frame control
//----------------------------------------------------------------------------------
always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sf_period_cnt    <=   32'h00 ;
    end
    else begin
        if ( sf_period_cnt == SF_PERIOD ) begin
            sf_period_cnt    <=   32'h00 ;
        end
        else begin
            sf_period_cnt    <=   sf_period_cnt + 1'b1 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sfm_rxsdu_empty    <=   1'b1 ;
    end
    else begin
        if ( sfm_rxsdu_dval == 1'b1 && sfm_rxsdu_data[16] == 1'b1 ) begin
            sfm_rxsdu_empty    <=   1'b1 ;
        end
        else if ( sf_period_cnt == SF_PERIOD ) begin
            sfm_rxsdu_empty    <=   1'b0 ;
        end
    end
end

assign  self_status =   4'h0 ;

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sfm_rxsdu_dval_tmp    <=   1'b0 ;
    end
    else begin
        sfm_rxsdu_dval_tmp    <=   rxsdu_sfm_rdreq ;
    end
end

assign  sfm_rxsdu_dval  = ( sfm_rxsdu_dval_tmp == 1'b1 && sfm_rxsdu_empty == 1'b0 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sfm_rxsdu_data    <=   18'h00 ;
    end
    else begin
        if( rxsdu_sfm_rdreq == 1'b1 ) begin
            case( sfm_data_addr )
                9'd0    :   sfm_rxsdu_data <=   { 2'b10 , 4'b1000 , slot_num_d2 , 8'h00 } ;
                9'd1    :   sfm_rxsdu_data <=   { 2'b00 , `STA_TYPE } ;
                9'd2    :   sfm_rxsdu_data <=   { 2'b00 , 16'h00 } ;
                9'd3    :   sfm_rxsdu_data <=   { 2'b00 , COM_STA_LEN } ;
                9'd4    :   sfm_rxsdu_data <=   { 2'b00 , cfg_feedback , self_status , 4'h0 } ;
                9'd5    :   sfm_rxsdu_data <=   { 2'b00 , 10'h00 , slink_err } ;
                9'd11   :   sfm_rxsdu_data <=   { 2'b01 , 16'h00 } ;
                default :   sfm_rxsdu_data <=   18'h00 ; 
            endcase
        end
        else begin
            sfm_rxsdu_data    <=   18'h00 ;
        end
    end
end

always @ ( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        sfm_data_addr    <=   5'h00 ;
    end
    else begin
        if ( sfm_rxsdu_dval == 1'b1 && sfm_rxsdu_data[16] == 1'b1 ) begin
            sfm_data_addr    <=   5'h00 ;
        end
        else if ( rxsdu_sfm_rdreq == 1'b1 ) begin
            sfm_data_addr    <=   sfm_data_addr + 1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// slink diagnose
//----------------------------------------------------------------------------------
assign  chn_slink_err   =   { lvds_slink_err , fiber_slink_err } ;   

assign  fiber_enable = enable_slot[3:0] ; 
assign  chn_enable = { enable_slot[13] , enable_slot[12] , fiber_enable } ;

  genvar j ;
  generate
  for( j = 0 ; j < 6 ; j = j+1 ) 
  begin : Nslinkdiag

    SELF_COM_SLINK_DIAG              U_SLINK_DIAG
    (
    .clk_12_5m                  ( clk_12_5m                 ),
    .rst_12_5m                  ( rst_12_5m                 ),

    .chn_enable                 ( chn_enable[j]             ),
   
    .chn_slink_err              ( chn_slink_err[j]          ),
    .slink_err                  ( slink_err[j]              )
    );

  end
  endgenerate

endmodule

