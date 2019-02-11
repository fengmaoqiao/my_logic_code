// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :
// CREATE DATE      :   2017-07-06
// DEPARTMENT       :   R&D
// AUTHOR           :   YongjunZhang
// AUTHOR'S EMAIL   :   zhangyongjun@cng.com
// AUTHOR'S TEL     :   18683432830
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-07-25  YongjunZhang        Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :
// ============================================================================
// REUSE ISSUES
// Reset Strategy   :   Async clear, active low
// Clock Domains    :   EMIF_CLK
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`include "DEFINES.v"

module CAL_FACTOR 
(
        rst_sys_n               ,   
        clk_sys                 ,   // system clock input 
        
        cfg_done_trig           ,   
        slink_cfg_dval          ,   
        slink_cfg_data          ,
        cfg_chaddr_sel          ,   

        fas_done                ,   
        fas_result              ,   
        fd_done                 ,   
        fd_result               , 
        fm_done                 ,   
        fm_result               ,   
        
        fas_adsb_sel            , 
        fas_data_a              ,   
        fas_data_b              ,   
        fas_start_trig          ,   
        fd_data_a               ,   
        fd_data_b               ,   
        fd_start_trig           ,   
        fm_data_a               ,   
        fm_data_b               ,   
        fm_start_trig           ,   

        cal_done                ,   

        k_factor0               ,   
        k_factor1               ,   
        k_factor2               ,   
        k_factor3               ,   
        k_factor4               ,   
        k_factor5               ,   

        kqe_factor0             ,   
        kqe_factor1             ,   
        kqe_factor2             ,   
        kqe_factor3             ,   
        kqe_factor4             ,   
        kqe_factor5             ,   

        bq_coeff0               ,   
        bq_coeff1               ,   
        bq_coeff2               ,   
        bq_coeff3               ,   
        bq_coeff4               ,   
        bq_coeff5               ,   

        ke_coeff0               ,   
        ke_coeff1               ,   
        ke_coeff2               ,   
        ke_coeff3               ,   
        ke_coeff4               ,   
        ke_coeff5               ,

        cfg_engn_chkul0         ,   
        cfg_engn_chkul1         ,   
        cfg_engn_chkul2         ,   
        cfg_engn_chkul3         ,   
        cfg_engn_chkul4         ,   
        cfg_engn_chkul5         ,   
                                   
        cfg_engn_chkdl0         ,   
        cfg_engn_chkdl1         ,   
        cfg_engn_chkdl2         ,   
        cfg_engn_chkdl3         ,   
        cfg_engn_chkdl4         ,   
        cfg_engn_chkdl5         ,

        cfg_elec_chkul0         ,   
        cfg_elec_chkul1         ,   
        cfg_elec_chkul2         ,   
        cfg_elec_chkul3         ,   
        cfg_elec_chkul4         ,   
        cfg_elec_chkul5         ,   
                                   
        cfg_elec_chkdl0         ,   
        cfg_elec_chkdl1         ,   
        cfg_elec_chkdl2         ,   
        cfg_elec_chkdl3         ,   
        cfg_elec_chkdl4         ,   
        cfg_elec_chkdl5         
);

/**********************************************************************************\
***************************** declare parameter ************************************/
localparam      CAL_IDLE            =   14'b00000000000000     ;
localparam      CAL_RDY             =   14'b00000000000001     ;
localparam      CAL_SUBQ            =   14'b00000000000010     ;
localparam      CAL_SUBE            =   14'b00000000000100     ;
localparam      CAL_DIVQE           =   14'b00000000001000     ;
localparam      CAL_MULK            =   14'b00000000010000     ;
localparam      CAL_MULQEE          =   14'b00000000100000     ;
localparam      CAL_SUBB            =   14'b00000001000000     ;
localparam      CAL_DIVEQ           =   14'b00000010000000     ;
localparam      CAL_CHKRDY          =   14'b00000100000000     ;
localparam      CAL_SUBQL           =   14'b00001000000000     ;
localparam      CAL_MULKEQ          =   14'b00010000000000     ;
localparam      CAL_ADDEL           =   14'b00100000000000     ;
localparam      CAL_NEXT            =   14'b01000000000000     ;
localparam      CAL_CPL             =   14'b10000000000000     ;
/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// input signal

input   wire                    rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input   wire                    cfg_done_trig                       ;
input   wire                    slink_cfg_dval                      ;   
input   wire    [9:0]           slink_cfg_data                      ;
input   wire                    cfg_chaddr_sel                      ;   

input   wire    [31:0]          k_factor0                           ;   
input   wire    [31:0]          k_factor1                           ;   
input   wire    [31:0]          k_factor2                           ;   
input   wire    [31:0]          k_factor3                           ;   
input   wire    [31:0]          k_factor4                           ;   
input   wire    [31:0]          k_factor5                           ; 

input   wire                    fas_done                            ;   
input   wire    [31:0]          fas_result                          ;   
input   wire                    fd_done                             ;   
input   wire    [31:0]          fd_result                           ;   
input   wire                    fm_done                             ;   
input   wire    [31:0]          fm_result                           ; 
// output signal
output  wire    [31:0]          ke_coeff0                           ;   
output  wire    [31:0]          ke_coeff1                           ;   
output  wire    [31:0]          ke_coeff2                           ;   
output  wire    [31:0]          ke_coeff3                           ;   
output  wire    [31:0]          ke_coeff4                           ;   
output  wire    [31:0]          ke_coeff5                           ;   

output  wire    [31:0]          kqe_factor0                         ;   
output  wire    [31:0]          kqe_factor1                         ;   
output  wire    [31:0]          kqe_factor2                         ;   
output  wire    [31:0]          kqe_factor3                         ;   
output  wire    [31:0]          kqe_factor4                         ;   
output  wire    [31:0]          kqe_factor5                         ;   

output  wire    [31:0]          bq_coeff0                           ;   
output  wire    [31:0]          bq_coeff1                           ;   
output  wire    [31:0]          bq_coeff2                           ;   
output  wire    [31:0]          bq_coeff3                           ;   
output  wire    [31:0]          bq_coeff4                           ;   
output  wire    [31:0]          bq_coeff5                           ;   

output  reg                     cal_done                            ;   
output  reg                     fas_adsb_sel                        ;   
output  reg     [31:0]          fas_data_a                          ;   
output  reg     [31:0]          fas_data_b                          ;   
output  reg                     fas_start_trig                      ;   
output  reg     [31:0]          fd_data_a                           ;   
output  reg     [31:0]          fd_data_b                           ;   
output  reg                     fd_start_trig                       ; 
output  reg     [31:0]          fm_data_a                           ;   
output  reg     [31:0]          fm_data_b                           ;   
output  reg                     fm_start_trig                       ;   

output  wire    [31:0]          cfg_engn_chkul0                     ;   
output  wire    [31:0]          cfg_engn_chkul1                     ;   
output  wire    [31:0]          cfg_engn_chkul2                     ;   
output  wire    [31:0]          cfg_engn_chkul3                     ;   
output  wire    [31:0]          cfg_engn_chkul4                     ;   
output  wire    [31:0]          cfg_engn_chkul5                     ;   
  
output  wire    [31:0]          cfg_engn_chkdl0                     ;   
output  wire    [31:0]          cfg_engn_chkdl1                     ;   
output  wire    [31:0]          cfg_engn_chkdl2                     ;   
output  wire    [31:0]          cfg_engn_chkdl3                     ;   
output  wire    [31:0]          cfg_engn_chkdl4                     ;   
output  wire    [31:0]          cfg_engn_chkdl5                     ;   

output  wire    [31:0]          cfg_elec_chkul0                     ;   
output  wire    [31:0]          cfg_elec_chkul1                     ;   
output  wire    [31:0]          cfg_elec_chkul2                     ;   
output  wire    [31:0]          cfg_elec_chkul3                     ;   
output  wire    [31:0]          cfg_elec_chkul4                     ;   
output  wire    [31:0]          cfg_elec_chkul5                     ;   

output  wire    [31:0]          cfg_elec_chkdl0                     ;   
output  wire    [31:0]          cfg_elec_chkdl1                     ;   
output  wire    [31:0]          cfg_elec_chkdl2                     ;   
output  wire    [31:0]          cfg_elec_chkdl3                     ;   
output  wire    [31:0]          cfg_elec_chkdl4                     ;   
output  wire    [31:0]          cfg_elec_chkdl5                     ;   

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire    [31:0]                  cfg_engn_ul0                        ;   
wire    [31:0]                  cfg_engn_ul1                        ;   
wire    [31:0]                  cfg_engn_ul2                        ;   
wire    [31:0]                  cfg_engn_ul3                        ;   
wire    [31:0]                  cfg_engn_ul4                        ;   
wire    [31:0]                  cfg_engn_ul5                        ;   

wire    [31:0]                  cfg_engn_dl0                        ;   
wire    [31:0]                  cfg_engn_dl1                        ;   
wire    [31:0]                  cfg_engn_dl2                        ;   
wire    [31:0]                  cfg_engn_dl3                        ;   
wire    [31:0]                  cfg_engn_dl4                        ;   
wire    [31:0]                  cfg_engn_dl5                        ;   
wire    [31:0]                  cfg_elec_dl0                        ;   
wire    [31:0]                  cfg_elec_dl1                        ;   
wire    [31:0]                  cfg_elec_dl2                        ;   
wire    [31:0]                  cfg_elec_dl3                        ;   
wire    [31:0]                  cfg_elec_dl4                        ;   
wire    [31:0]                  cfg_elec_dl5                        ;   

wire    [31:0]                  cfg_elec_ul0                        ;   
wire    [31:0]                  cfg_elec_ul1                        ;   
wire    [31:0]                  cfg_elec_ul2                        ;   
wire    [31:0]                  cfg_elec_ul3                        ;   
wire    [31:0]                  cfg_elec_ul4                        ;   
wire    [31:0]                  cfg_elec_ul5                        ;   

wire    [31:0]                  k_constant                          ;   
// reg signal
reg     [13:0]                  cur_state                           ;   
reg     [13:0]                  next_state                          ;   
reg     [2:0]                   cal_chn_sel                         ; 
reg                             kqe_factor_en                       ;   
reg     [31:0]                  kqe_var                             ;   
reg                             ke_coeff_en                         ;   
reg                             bq_coeff_en                         ;   
reg                             chkudl_flag                         ;
reg     [31:0]                  f_sub_elec                          ;   
reg     [31:0]                  f_sub_engn                          ;   
reg     [31:0]                  keq_var                             ;   
reg                             elec_chkul_en                       ;   
reg                             elec_chkdl_en                       ;   
reg                             cfg_done                            ;   
/**********************************************************************************\
******************************** debug code ****************************************/

/**********************************************************************************\
********************************* main code ****************************************/
//assign k_constant =     32'h3a1ce09f ; // 0.000588561117 // 1.25*4.096*38.3*1000/65536/49.9/(61.9+38.3) = 0.000588561117
assign k_constant =     32'h3b3c40bf ; // 0.00287251151// 3*4.096*38.3*1000/32768/49.9/(61.9+38.3) = 0.00287251151

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cur_state  <=  CAL_IDLE ;
    end
    else begin
        cur_state  <=  next_state ;
    end
end

always @ ( * ) begin
    case ( cur_state ) 
        CAL_IDLE : begin
            if ( cfg_done_trig == 1'b1 ) begin
                next_state = CAL_RDY ;
            end 
            else begin
                next_state = CAL_IDLE ;
            end
        end
        CAL_RDY : begin
            next_state = CAL_SUBQ ;
        end
        CAL_SUBQ : begin // qmax-qmin
            if ( fas_done == 1'b1 ) begin
                next_state = CAL_SUBE ;
            end
            else begin
                next_state = CAL_SUBQ ; 
            end
        end
        CAL_SUBE : begin // emax-emin
            if ( fas_done == 1'b1 ) begin
                next_state = CAL_DIVQE ;
            end
            else begin
                next_state = CAL_SUBE ; 
            end
        end
        CAL_DIVQE : begin // qmax-qmin / emax-emin
            if ( fd_done == 1'b1 ) begin
                next_state = CAL_MULK ;
            end
            else begin
                next_state = CAL_DIVQE ; 
            end
        end
        CAL_MULK : begin
            if ( fm_done == 1'b1 ) begin
                next_state = CAL_MULQEE ;
            end
            else begin
                next_state = CAL_MULK ; 
            end
        end
        CAL_MULQEE : begin
            if ( fm_done == 1'b1 ) begin
                next_state = CAL_SUBB ;
            end
            else begin
                next_state = CAL_MULQEE ; 
            end
        end
        CAL_SUBB : begin
            if ( fas_done == 1'b1 ) begin
                next_state = CAL_DIVEQ ;
            end
            else begin
                next_state = CAL_SUBB ; 
            end
        end
        CAL_DIVEQ : begin // emax-emin / qmax-qmin 
            if ( fd_done == 1'b1 ) begin
                next_state = CAL_CHKRDY ;
            end
            else begin
                next_state = CAL_DIVEQ ;
            end
        end
        CAL_CHKRDY : begin
            next_state = CAL_SUBQL ;
        end
        CAL_SUBQL : begin // QIN - QL
            if ( fas_done == 1'b1 ) begin
                next_state = CAL_MULKEQ ;
            end
            else begin
                next_state = CAL_SUBQL ;
            end
        end
        CAL_MULKEQ : begin // KEQ * ( QIN - QL )
            if ( fm_done == 1'b1 ) begin
                next_state = CAL_ADDEL ;
            end
            else begin
                next_state = CAL_MULKEQ ;
            end
        end
        CAL_ADDEL : begin // KEQ * ( QIN - QL ) + eL
            if ( fas_done == 1'b1 ) begin
                if ( chkudl_flag == 1'b0 ) begin
                    next_state =  CAL_CHKRDY ;
                end
                else begin
                    next_state = CAL_NEXT ;
                end
            end
            else begin
                next_state = CAL_ADDEL ;
            end
        end
        CAL_NEXT : begin
            if( cal_chn_sel == 3'd5 ) begin
                next_state = CAL_CPL ;
            end
            else begin
                next_state = CAL_RDY ;
            end
        end
        CAL_CPL : begin
            next_state = CAL_CPL ;
        end
        default : begin
            next_state = CAL_IDLE ;
        end
    endcase
end

//----------------------------------------------------------------------------------
// channel parameer calculation
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_chn_sel <=  3'd0 ;
    end
    else begin
        if ( cur_state == CAL_IDLE ) begin
            cal_chn_sel <=  3'd0 ;
        end
        else if ( cur_state == CAL_NEXT )  begin
            if ( cal_chn_sel == 3'd5 ) begin
                cal_chn_sel <=   3'd0 ;
            end
            else begin
                cal_chn_sel <=  cal_chn_sel + 1'b1 ;
            end
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        chkudl_flag     <=   1'b0 ;
    end
    else begin
        if ( cur_state == CAL_RDY ) begin
            chkudl_flag     <=   1'b0 ;
        end
        else if ( cur_state == CAL_ADDEL && fas_done == 1'b1 ) begin
            chkudl_flag <=   1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// floating point subtraction operation 
// calculate the formation of qmax - qmin and emax - emin
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fas_adsb_sel   <=  1'b0 ;
    end
    else begin
        if ( cur_state == CAL_RDY || ( cur_state == CAL_SUBQ && fas_done == 1'b1 ) ||  cur_state == CAL_MULQEE && fm_done == 1'b1 || cur_state == CAL_CHKRDY ) begin
            fas_adsb_sel   <=  1'b0 ;
        end
        else if ( cur_state == CAL_MULKEQ && fm_done == 1'b1 ) begin
            fas_adsb_sel   <=  1'b1 ;
        end
    end
end


always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fas_start_trig   <=  1'b0 ;
    end
    else begin
        if ( cur_state == CAL_RDY || ( cur_state == CAL_SUBQ && fas_done == 1'b1 ) || ( cur_state == CAL_MULQEE || cur_state == CAL_MULKEQ ) && fm_done == 1'b1 || cur_state == CAL_CHKRDY ) begin
            fas_start_trig   <=  1'b1 ;
        end
        else begin
            fas_start_trig   <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fas_data_a   <=  32'd0 ;
    end
    else begin
        if ( cur_state == CAL_RDY ) begin
            case ( cal_chn_sel ) 
                3'd0 : begin
                    fas_data_a   <=  cfg_engn_ul0 ;
                end
                3'd1 : begin
                    fas_data_a   <=  cfg_engn_ul1 ;
                end
                3'd2 : begin
                    fas_data_a   <=  cfg_engn_ul2 ;
                end
                3'd3 : begin
                    fas_data_a   <=  cfg_engn_ul3 ;
                end
                3'd4 : begin
                    fas_data_a   <=  cfg_engn_ul4 ;
                end
                3'd5 : begin
                    fas_data_a   <=  cfg_engn_ul5 ;
                end
            endcase
        end
        else if ( cur_state == CAL_SUBQ && fas_done == 1'b1 ) begin
            case ( cal_chn_sel ) 
                3'd0 : begin
                    fas_data_a   <=  cfg_elec_ul0 ;
                end
                3'd1 : begin
                    fas_data_a   <=  cfg_elec_ul1 ;
                end
                3'd2 : begin
                    fas_data_a   <=  cfg_elec_ul2 ;
                end
                3'd3 : begin
                    fas_data_a   <=  cfg_elec_ul3 ;
                end
                3'd4 : begin
                    fas_data_a   <=  cfg_elec_ul4 ;
                end
                3'd5 : begin
                    fas_data_a   <=  cfg_elec_ul5 ;
                end
            endcase
        end
        else if ( cur_state == CAL_MULQEE && fm_done == 1'b1 ) begin
            case ( cal_chn_sel ) 
                3'd0 : begin
                    fas_data_a   <=  cfg_engn_dl0 ;
                end
                3'd1 : begin
                    fas_data_a   <=  cfg_engn_dl1 ;
                end
                3'd2 : begin
                    fas_data_a   <=  cfg_engn_dl2 ;
                end
                3'd3 : begin
                    fas_data_a   <=  cfg_engn_dl3 ;
                end
                3'd4 : begin
                    fas_data_a   <=  cfg_engn_dl4 ;
                end
                3'd5 : begin
                    fas_data_a   <=  cfg_engn_dl5 ;
                end
            endcase
        end
        else if ( cur_state == CAL_CHKRDY ) begin
            if ( chkudl_flag == 1'b0 ) begin
                case ( cal_chn_sel ) 
                    3'd0 : begin
                        fas_data_a   <=  cfg_engn_chkdl0 ;
                    end
                    3'd1 : begin
                        fas_data_a   <=  cfg_engn_chkdl1 ;
                    end
                    3'd2 : begin
                        fas_data_a   <=  cfg_engn_chkdl2 ;
                    end
                    3'd3 : begin
                        fas_data_a   <=  cfg_engn_chkdl3 ;
                    end
                    3'd4 : begin
                        fas_data_a   <=  cfg_engn_chkdl4 ;
                    end
                    3'd5 : begin
                        fas_data_a   <=  cfg_engn_chkdl5 ;
                    end
                endcase
            end
            else if ( chkudl_flag == 1'b1 ) begin
                case ( cal_chn_sel ) 
                    3'd0 : begin
                        fas_data_a   <=  cfg_engn_chkul0 ;
                    end
                    3'd1 : begin
                        fas_data_a   <=  cfg_engn_chkul1 ;
                    end
                    3'd2 : begin
                        fas_data_a   <=  cfg_engn_chkul2 ;
                    end
                    3'd3 : begin
                        fas_data_a   <=  cfg_engn_chkul3 ;
                    end
                    3'd4 : begin
                        fas_data_a   <=  cfg_engn_chkul4 ;
                    end
                    3'd5 : begin
                        fas_data_a   <=  cfg_engn_chkul5 ;
                    end
                endcase
            end
            else ;
        end
        else if ( cur_state == CAL_MULKEQ && fm_done == 1'b1 ) begin
            fas_data_a  <=   fm_result ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fas_data_b   <=  32'd0 ;
    end
    else begin
        if ( cur_state == CAL_RDY || cur_state == CAL_CHKRDY ) begin
            case ( cal_chn_sel ) 
                3'd0 : begin
                    fas_data_b   <=  cfg_engn_dl0 ;
                end
                3'd1 : begin
                    fas_data_b   <=  cfg_engn_dl1 ;
                end
                3'd2 : begin
                    fas_data_b   <=  cfg_engn_dl2 ;
                end
                3'd3 : begin
                    fas_data_b   <=  cfg_engn_dl3 ;
                end
                3'd4 : begin
                    fas_data_b   <=  cfg_engn_dl4 ;
                end
                3'd5 : begin
                    fas_data_b   <=  cfg_engn_dl5 ;
                end
            endcase                
        end
        else if ( cur_state == CAL_SUBQ && fas_done == 1'b1 || cur_state == CAL_MULKEQ && fm_done == 1'b1 ) begin
            case ( cal_chn_sel ) 
                3'd0 : begin
                    fas_data_b   <=  cfg_elec_dl0 ;
                end
                3'd1 : begin
                    fas_data_b   <=  cfg_elec_dl1 ;
                end
                3'd2 : begin
                    fas_data_b   <=  cfg_elec_dl2 ;
                end
                3'd3 : begin
                    fas_data_b   <=  cfg_elec_dl3 ;
                end
                3'd4 : begin
                    fas_data_b   <=  cfg_elec_dl4 ;
                end
                3'd5 : begin
                    fas_data_b   <=  cfg_elec_dl5 ;
                end
            endcase
        end
        else if ( cur_state == CAL_MULQEE && fm_done == 1'b1 ) begin
            fas_data_b  <=   fm_result ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        f_sub_engn   <=   32'd0 ;
    end
    else begin
        if ( ( cur_state == CAL_SUBQ ) && fas_done == 1'b1 ) begin
            f_sub_engn <=   fas_result ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        f_sub_elec  <=   32'd0 ;
    end
    else begin
        if ( cur_state == CAL_SUBE && fas_done == 1'b1 ) begin
            f_sub_elec  <=   fas_result ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        elec_chkdl_en   <=   1'b0 ;
    end
    else begin
        if ( cur_state == CAL_ADDEL && fas_done == 1'b1 && chkudl_flag == 1'b0 ) begin
            elec_chkdl_en   <=   1'b1 ;
        end
        else begin
            elec_chkdl_en   <=   1'b0 ;
        end
    end
end

    ASSIGN_RESULT               U_CHKDL_FACTOR
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    .data_en                    ( elec_chkdl_en             ),
    .data_sel                   ( cal_chn_sel               ),
    .data_in                    ( fas_result                ),

    .result0                    ( cfg_elec_chkdl0           ),
    .result1                    ( cfg_elec_chkdl1           ),
    .result2                    ( cfg_elec_chkdl2           ),
    .result3                    ( cfg_elec_chkdl3           ),
    .result4                    ( cfg_elec_chkdl4           ),
    .result5                    ( cfg_elec_chkdl5           )
    );

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        elec_chkul_en   <=   1'b0 ;
    end
    else begin
        if ( cur_state == CAL_ADDEL && fas_done == 1'b1 && chkudl_flag == 1'b1 ) begin
            elec_chkul_en   <=   1'b1 ;
        end
        else begin
            elec_chkul_en   <=   1'b0 ;
        end
    end
end

    ASSIGN_RESULT               U_CHKUL_FACTOR
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    .data_en                    ( elec_chkul_en             ),
    .data_sel                   ( cal_chn_sel               ),
    .data_in                    ( fas_result                ),

    .result0                    ( cfg_elec_chkul0           ),
    .result1                    ( cfg_elec_chkul1           ),
    .result2                    ( cfg_elec_chkul2           ),
    .result3                    ( cfg_elec_chkul3           ),
    .result4                    ( cfg_elec_chkul4           ),
    .result5                    ( cfg_elec_chkul5           )
    );

//----------------------------------------------------------------------------------
// calulate the formula of f_sub_engn / f_sub_elec
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fd_start_trig   <=  1'b0 ;
    end
    else begin
        if ( (cur_state == CAL_SUBE || cur_state == CAL_SUBB ) && fas_done == 1'b1 ) begin
            fd_start_trig   <=  1'b1 ;
        end
        else begin
            fd_start_trig   <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fd_data_a   <=  32'd0 ;
    end
    else begin
        if ( cur_state == CAL_SUBE && fas_done == 1'b1 ) begin
            fd_data_a   <=  f_sub_engn ;
        end
        else if ( cur_state == CAL_SUBB && fas_done == 1'b1 ) begin
            fd_data_a   <=  f_sub_elec ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fd_data_b   <=  32'd0 ;
    end
    else begin
        if ( cur_state == CAL_SUBE && fas_done == 1'b1 ) begin
            fd_data_b   <=  fas_result ;
        end
        if ( cur_state == CAL_SUBB && fas_done == 1'b1 ) begin
            fd_data_b   <=  f_sub_engn ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        kqe_var <=   32'd0 ;
    end
    else begin
        if ( cur_state == CAL_DIVQE && fd_done == 1'b1 ) begin
            kqe_var <=   fd_result ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        keq_var <=   32'd0 ;
    end
    else begin
        if ( cur_state == CAL_DIVEQ && fd_done == 1'b1 ) begin
            keq_var <=   fd_result ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// calculate the format of kcons = 0.0015625k and 
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fm_start_trig   <=   1'b0 ;
    end
    else begin
        if ( cur_state == CAL_DIVQE && fd_done == 1'b1 || cur_state == CAL_MULK && fm_done == 1'b1 || cur_state == CAL_SUBQL && fas_done == 1'b1 ) begin
            fm_start_trig   <=   1'b1 ;
        end
        else begin
            fm_start_trig   <=   1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fm_data_a   <=   32'd0 ;
    end
    else begin
        if ( cur_state == CAL_DIVQE && fd_done == 1'b1 ) begin
            fm_data_a   <=   k_constant ;
        end
        else if ( cur_state == CAL_MULK && fm_done == 1'b1 ) begin
            fm_data_a   <=   kqe_var ;
        end
        else if ( cur_state == CAL_SUBQL && fas_done == 1'b1 ) begin
            fm_data_a   <=   keq_var ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        fm_data_b   <=   32'd0 ;
    end
    else begin
        if ( cur_state == CAL_DIVQE && fd_done == 1'b1 ) begin
            case ( cal_chn_sel ) 
                3'd0 : begin
                    fm_data_b   <=  k_factor0 ;
                end
                3'd1 : begin
                    fm_data_b   <=  k_factor1 ;
                end
                3'd2 : begin
                    fm_data_b   <=  k_factor2 ;
                end
                3'd3 : begin
                    fm_data_b   <=  k_factor3 ;
                end
                3'd4 : begin
                    fm_data_b   <=  k_factor4 ;
                end
                3'd5 : begin
                    fm_data_b   <=  k_factor5 ;
                end
            endcase
        end
        else if ( cur_state == CAL_MULK && fm_done == 1'b1 ) begin
            case ( cal_chn_sel ) 
                3'd0 : begin
                    fm_data_b   <=  cfg_elec_dl0 ;
                end
                3'd1 : begin
                    fm_data_b   <=  cfg_elec_dl1 ;
                end
                3'd2 : begin
                    fm_data_b   <=  cfg_elec_dl2 ;
                end
                3'd3 : begin
                    fm_data_b   <=  cfg_elec_dl3 ;
                end
                3'd4 : begin
                    fm_data_b   <=  cfg_elec_dl4 ;
                end
                3'd5 : begin
                    fm_data_b   <=  cfg_elec_dl5 ;
                end
            endcase
        end
        else if ( cur_state == CAL_SUBQL && fas_done == 1'b1 ) begin
            fm_data_b   <=   fas_result ;
        end
        else ;
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        ke_coeff_en   <=   1'b0 ;
    end
    else begin
        if ( cur_state == CAL_MULK && fm_done == 1'b1 ) begin
            ke_coeff_en   <=   1'b1 ;
        end
        else begin
            ke_coeff_en   <=   1'b0 ;
        end
    end
end

    ASSIGN_RESULT               U_KE_FACTOR
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    .data_en                    ( ke_coeff_en               ),
    .data_sel                   ( cal_chn_sel               ),
    .data_in                    ( fm_result                 ),

    .result0                    ( ke_coeff0                 ),
    .result1                    ( ke_coeff1                 ),
    .result2                    ( ke_coeff2                 ),
    .result3                    ( ke_coeff3                 ),
    .result4                    ( ke_coeff4                 ),
    .result5                    ( ke_coeff5                 )
    );

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        kqe_factor_en   <=   1'b0 ;
    end
    else begin
        if ( cur_state == CAL_DIVQE && fd_done == 1'b1 ) begin
            kqe_factor_en   <=   1'b1 ;
        end
        else begin
            kqe_factor_en   <=   1'b0 ;
        end
    end
end

    ASSIGN_RESULT               U_KQE_FACTOR
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    .data_en                    ( kqe_factor_en             ),
    .data_sel                   ( cal_chn_sel               ),
    .data_in                    ( fd_result                 ),

    .result0                    ( kqe_factor0               ),
    .result1                    ( kqe_factor1               ),
    .result2                    ( kqe_factor2               ),
    .result3                    ( kqe_factor3               ),
    .result4                    ( kqe_factor4               ),
    .result5                    ( kqe_factor5               )
    );

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        bq_coeff_en   <=   1'b0 ;
    end
    else begin
        if ( cur_state == CAL_SUBB && fas_done == 1'b1 ) begin
            bq_coeff_en   <=   1'b1 ;
        end
        else begin
            bq_coeff_en   <=   1'b0 ;
        end
    end
end

    ASSIGN_RESULT               U_BQ_FACTOR
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),
        
    .data_en                    ( bq_coeff_en               ),
    .data_sel                   ( cal_chn_sel               ),
    .data_in                    ( fas_result                ),

    .result0                    ( bq_coeff0                 ),
    .result1                    ( bq_coeff1                 ),
    .result2                    ( bq_coeff2                 ),
    .result3                    ( bq_coeff3                 ),
    .result4                    ( bq_coeff4                 ),
    .result5                    ( bq_coeff5                 )
    );
//----------------------------------------------------------------------------------
// generate calibrate done signal
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cal_done  <=  1'b0 ;
    end
    else begin
        if ( cur_state == CAL_IDLE && cfg_done_trig == 1'b1 ) begin
            cal_done  <=  1'b0 ;
        end
        else if ( cur_state == CAL_CPL ) begin
            cal_done    <=   1'b1 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cfg_done    <=   1'b0 ;
    end
    else begin
        if ( cfg_done_trig == 1'b1 ) begin
            cfg_done    <=   1'b1 ;
        end
        else ;
    end
end

    CFGINFOFRM                  U_CFGINFOFRM
    (
    .rst_sys_n                  ( rst_sys_n                 ),
    .clk_sys                    ( clk_sys                   ),

    .cfg_done                   ( cfg_done                  ),
    .slink_cfg_dval             ( slink_cfg_dval            ),
    .slink_cfg_data             ( slink_cfg_data            ),
    .cfg_chaddr_sel             ( cfg_chaddr_sel            ),

    .cfg_engn_ul0               ( cfg_engn_ul0              ),
    .cfg_engn_ul1               ( cfg_engn_ul1              ),
    .cfg_engn_ul2               ( cfg_engn_ul2              ),
    .cfg_engn_ul3               ( cfg_engn_ul3              ),
    .cfg_engn_ul4               ( cfg_engn_ul4              ),
    .cfg_engn_ul5               ( cfg_engn_ul5              ),
                        
    .cfg_engn_dl0               ( cfg_engn_dl0              ),
    .cfg_engn_dl1               ( cfg_engn_dl1              ),
    .cfg_engn_dl2               ( cfg_engn_dl2              ),
    .cfg_engn_dl3               ( cfg_engn_dl3              ),
    .cfg_engn_dl4               ( cfg_engn_dl4              ),
    .cfg_engn_dl5               ( cfg_engn_dl5              ),
                        
    .cfg_elec_ul0               ( cfg_elec_ul0              ),
    .cfg_elec_ul1               ( cfg_elec_ul1              ),
    .cfg_elec_ul2               ( cfg_elec_ul2              ),
    .cfg_elec_ul3               ( cfg_elec_ul3              ),
    .cfg_elec_ul4               ( cfg_elec_ul4              ),
    .cfg_elec_ul5               ( cfg_elec_ul5              ),
                        
    .cfg_elec_dl0               ( cfg_elec_dl0              ),
    .cfg_elec_dl1               ( cfg_elec_dl1              ),
    .cfg_elec_dl2               ( cfg_elec_dl2              ),
    .cfg_elec_dl3               ( cfg_elec_dl3              ),
    .cfg_elec_dl4               ( cfg_elec_dl4              ),
    .cfg_elec_dl5               ( cfg_elec_dl5              ),

                        
    .cfg_engn_chkul0            ( cfg_engn_chkul0           ),
    .cfg_engn_chkul1            ( cfg_engn_chkul1           ),
    .cfg_engn_chkul2            ( cfg_engn_chkul2           ),
    .cfg_engn_chkul3            ( cfg_engn_chkul3           ),
    .cfg_engn_chkul4            ( cfg_engn_chkul4           ),
    .cfg_engn_chkul5            ( cfg_engn_chkul5           ),
                        
    .cfg_engn_chkdl0            ( cfg_engn_chkdl0           ),
    .cfg_engn_chkdl1            ( cfg_engn_chkdl1           ),
    .cfg_engn_chkdl2            ( cfg_engn_chkdl2           ),
    .cfg_engn_chkdl3            ( cfg_engn_chkdl3           ),
    .cfg_engn_chkdl4            ( cfg_engn_chkdl4           ),
    .cfg_engn_chkdl5            ( cfg_engn_chkdl5           )
       
    );

endmodule
