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

module  SELFM
    (
    // clock & reset
    clk_150m                    ,   
    rst_150m                    ,   

    // connect to EMIF module
    selfm_rd_sel                ,   
    selfm_rd_addr               ,   
    selfm_rd_data               ,   

    // configuration
    slot_num                    ,   
    sta_num                     ,   
    box_num                     ,   
    master_slave_flag           ,
    mpu_cfg_wr_ok               ,   

    // port status
    chn0_empty                  ,   
    chn1_empty                  ,   
    chn2_empty                  ,   
    chn3_empty                  ,   
    chn4_empty                  ,   
    chn5_empty                  ,   
    chn6_empty                  ,   
    chn7_empty                  ,   
    chn8_empty                  ,   
    chn9_empty                  ,   
    chn10_empty                 ,   
    chn11_empty                 ,   
    chn12_empty                 ,   
    chn13_empty                 ,
    //
    mcu_is_valid                ,
    redundancy_mode                       
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_150m                            ;    
input   wire                    rst_150m                            ;    

input   wire                    selfm_rd_sel                        ;   
input   wire        [8:0]       selfm_rd_addr                       ;   
input   wire        [3:0]       slot_num                            ;   
input   wire        [7:0]       sta_num                             ;   
input   wire        [2:0]       box_num                             ;   
input   wire        [7:0]       master_slave_flag                   ; 
input   wire                    mpu_cfg_wr_ok                       ;   

input   wire        [3:0]       chn0_empty                          ;   
input   wire        [3:0]       chn1_empty                          ;   
input   wire        [3:0]       chn2_empty                          ;   
input   wire        [3:0]       chn3_empty                          ;   
input   wire        [3:0]       chn4_empty                          ;   
input   wire        [3:0]       chn5_empty                          ;   
input   wire        [3:0]       chn6_empty                          ;   
input   wire        [3:0]       chn7_empty                          ;   
input   wire        [3:0]       chn8_empty                          ;   
input   wire        [3:0]       chn9_empty                          ;   
input   wire        [3:0]       chn10_empty                         ;   
input   wire        [3:0]       chn11_empty                         ;   
input   wire        [3:0]       chn12_empty                         ;   
input   wire        [3:0]       chn13_empty                         ;  

// declare output signal
output  reg         [15:0]      selfm_rd_data                       ; 
input   wire                    mcu_is_valid                        ;

input   wire        [7:0]       redundancy_mode                     ;

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal

// reg signal
reg         [3:0]               chn0_empty_d1                       ;   
reg         [3:0]               chn1_empty_d1                       ;   
reg         [3:0]               chn2_empty_d1                       ;   
reg         [3:0]               chn3_empty_d1                       ;   
reg         [3:0]               chn4_empty_d1                       ;   
reg         [3:0]               chn5_empty_d1                       ;   
reg         [3:0]               chn6_empty_d1                       ;   
reg         [3:0]               chn7_empty_d1                       ;   
reg         [3:0]               chn8_empty_d1                       ;   
reg         [3:0]               chn9_empty_d1                       ;   
reg         [3:0]               chn10_empty_d1                      ;   
reg         [3:0]               chn11_empty_d1                      ;   
reg         [3:0]               chn12_empty_d1                      ;   
reg         [3:0]               chn13_empty_d1                      ;
reg         [7:0]               master_slave_flag_d1                ;   
reg         [7:0]               master_slave_flag_d2                ;   
reg         [3:0]               slot_num_d1                         ;   
reg         [3:0]               slot_num_d2                         ;   
reg         [7:0]               sta_num_d1                          ;   
reg         [7:0]               sta_num_d2                          ;   
reg         [2:0]               box_num_d1                          ;   
reg         [2:0]               box_num_d2                          ; 

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
//----------------------------------------------------------------------------------
// empty delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn0_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn0_empty_d1    <=   chn0_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn1_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn1_empty_d1    <=   chn1_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn2_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn2_empty_d1    <=   chn2_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn3_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn3_empty_d1    <=   chn3_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn4_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn4_empty_d1    <=   chn4_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn5_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn5_empty_d1    <=   chn5_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn6_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn6_empty_d1    <=   chn6_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn7_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn7_empty_d1    <=   chn7_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn8_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn8_empty_d1    <=   chn8_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn9_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn9_empty_d1    <=   chn9_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn10_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn10_empty_d1    <=   chn10_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn11_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn11_empty_d1    <=   chn11_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn12_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn12_empty_d1    <=   chn12_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        chn13_empty_d1    <=   4'hf ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            chn13_empty_d1    <=   chn13_empty ;
        end
        else ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        master_slave_flag_d1    <=   8'h00 ;
        master_slave_flag_d2    <=   8'h00 ;
    end
    else begin
        if ( selfm_rd_sel == 1'b0 ) begin
            master_slave_flag_d1    <=   master_slave_flag ;
            master_slave_flag_d2    <=   master_slave_flag_d1 ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// write control 
//----------------------------------------------------------------------------------

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        selfm_rd_data    <=   16'h00 ;
    end
    else if( selfm_rd_sel == 1'b1 ) begin
        case( selfm_rd_addr )
            9'd0    :   selfm_rd_data <=   { chn3_empty_d1 , chn2_empty_d1 , chn1_empty_d1 , chn0_empty_d1 } ;
            9'd1    :   selfm_rd_data <=   { chn7_empty_d1 , chn6_empty_d1 , chn5_empty_d1 , chn4_empty_d1 } ;
            9'd2    :   selfm_rd_data <=   { chn11_empty_d1 , chn10_empty_d1 , chn9_empty_d1 , chn8_empty_d1 } ;
            9'd3    :   selfm_rd_data <=   { 8'h00 , chn13_empty_d1 , chn12_empty_d1 } ;
            //9'd4    :   selfm_rd_data <=   { sta_num_d2 , 1'b0 , box_num_d2 , slot_num_d2 } ;
            9'd4    :   selfm_rd_data <=   { sta_num_d2 , ( ~mcu_is_valid && ( redundancy_mode == 8'h20 ) ) , box_num_d2 , slot_num_d2 } ;
            9'd5    :   selfm_rd_data <=   { 8'h00 , master_slave_flag_d2 } ;
            9'd6    :   selfm_rd_data <=   { 4'h0 , mpu_cfg_wr_ok , 8'h00 } ;
            9'd7    :   selfm_rd_data <=   { 16'h00 } ;
            default :   selfm_rd_data <=   16'h00 ; 
        endcase
    end
    else begin
        selfm_rd_data    <=   16'h00 ;
    end
end

//----------------------------------------------------------------------------------
// external interface signal delay
//----------------------------------------------------------------------------------
always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        slot_num_d1   <=   4'h00 ;
        slot_num_d2   <=   4'h00 ;
    end
    else begin
        slot_num_d1   <=   slot_num ;
        slot_num_d2   <=   slot_num_d1 ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        sta_num_d1   <=   8'h00 ;
        sta_num_d2   <=   8'h00 ;
    end
    else begin
        sta_num_d1   <=   sta_num ;
        sta_num_d2   <=   sta_num_d1 ;
    end
end

always @ ( posedge clk_150m or negedge rst_150m ) begin
    if( rst_150m == 1'b0 ) begin
        box_num_d1   <=   3'h00 ;
        box_num_d2   <=   3'h00 ;
    end
    else begin
        box_num_d1   <=   box_num ;
        box_num_d2   <=   box_num_d1 ;
    end
end


endmodule

