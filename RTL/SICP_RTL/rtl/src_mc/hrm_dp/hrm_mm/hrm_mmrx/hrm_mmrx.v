// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   HRM_MMRX
// CREATE DATE      :   2017-09-22
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-22  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   memory management of Hot-Redunancy MCU
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

module  HRM_MMRX
    (
    clk_100m                    ,   
    rst_100m                    , 

    // connect to EMIF module
    chn_sel                     ,
    hrm_pkt_num                 ,
    rd_addr                     ,   
    rd_data                     ,   

    // these signals from slink protocol stack
    slink_mm_empty              ,
    slink_mmrx_dval             ,   
    slink_mmrx_data             ,
    mmrx_slink_rdreq            ,

    mm_delay_err                   
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   BASE0_ADDR  =   10'd000 ;  
parameter   BASE1_ADDR  =   10'd512 ;  

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_100m                            ;   
input   wire                    rst_100m                            ;   
input   wire                    chn_sel                             ;
input   wire        [3:0]       hrm_pkt_num                         ;
input   wire        [8:0]       rd_addr                             ;
input   wire                    slink_mm_empty                      ;   
input   wire                    slink_mmrx_dval                     ;   
input   wire        [17:0]      slink_mmrx_data                     ;   

// declare output signal
output  wire        [17:0]      rd_data                             ;   
output  wire                    mmrx_slink_rdreq                    ;  
output  wire                    mm_delay_err                        ;   

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [17:0]              wr_data                             ;
wire                            wr_en                               ;   
wire        [1:0]               tpram_wr_en                         ;  
wire                            chn_sel_ring                        ;   
wire                            rd_start                            ;  
wire        [17:0]              rd_data0                            ;   
wire        [17:0]              rd_data1                            ;
wire                            wr_sel0                             ;   
wire                            wr_sel1                             ;   
wire                            rd_sel0                             ;   
wire                            rd_sel1                             ;   
wire                            new_sop_d2                          ;   

// reg signal
reg         [7:0]               dest_addr                           ;   
reg         [15:0]              pkt_type                            ;  
reg                             new_sop                             ;   
reg         [1:0]               new_sop_d1                          ;   
reg                             new_sop_d3                          ;   
reg                             wr_en_flag                          ;   
reg         [9:0]               wr_addr                             ;   
reg                             wr_sel                              ;   
reg                             wr_finish                           ;   
reg                             wr_start                            ; 
reg                             pkt_full_flag0                      ;   
reg                             pkt_full_flag1                      ;   
reg                             chn_sel_d1                          ;  
reg         [1:0]               rd_sel                              ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
assign  mm_delay_err = 1'b0 ;

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign mmrx_slink_rdreq = slink_mm_empty == 1'b0 ? 1'b1 : 1'b0 ;

//----------------------------------------------------------------------------------
// DA & SA & TYPE parse
//----------------------------------------------------------------------------------
always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        dest_addr   <=   8'h00 ;
    end
    else if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[17] == 1'b1 )begin
        dest_addr   <=   slink_mmrx_data[15:8] ;
    end
    else ;
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        pkt_type   <=   16'h00 ;
    end
    else if( new_sop == 1'b1 )begin
        pkt_type   <=   slink_mmrx_data[15:0] ;
    end
    else ;
end

//----------------------------------------------------------------------------------
// write control
//----------------------------------------------------------------------------------
always @ ( posedge clk_100m ) begin
    if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[17] == 1'b1 )begin
        new_sop   <=   1'b1 ;
    end
    else begin
        new_sop   <=   1'b0 ;
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        new_sop_d1   <=   2'b00 ;
    end
    else begin
        if( slink_mmrx_dval == 1'b1 ) begin
            if ( slink_mmrx_data[17] == 1'b1 )begin
                new_sop_d1   <=   2'b00 ;
            end
            else if ( new_sop_d1 == 2'b11 ) begin
                new_sop_d1   <=   new_sop_d1 ;
            end
            else begin
                new_sop_d1   <=   new_sop_d1 + 1'b1 ;
            end
        end
    end
end

assign  new_sop_d2  =   ( new_sop_d1 == 2'b10 ) ? 1'b1 : 1'b0 ; 

always @ ( posedge clk_100m ) begin
    new_sop_d3   <=   new_sop_d2 ;
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        wr_en_flag   <=   1'b0 ;
    end
    else if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[16] == 1'b1 )begin
        wr_en_flag   <=   1'b0 ;
    end
    else if( new_sop_d2 == 1'b1 && pkt_type == `DATA_TYPE ) begin
        wr_en_flag   <=   1'b1 ;
    end
end

assign  wr_en = ( wr_en_flag == 1'b1 && slink_mmrx_dval == 1'b1 ) ? 1'b1 : 1'b0  ;

assign  tpram_wr_en[0] = ( wr_en == 1'b1 && dest_addr[3:1] == 3'd0 ) ? 1'b1 : 1'b0 ;
assign  tpram_wr_en[1] = ( wr_en == 1'b1 && dest_addr[3:1] == 3'd1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        wr_addr   <=   10'h00 ;
    end
    else if( new_sop_d2 == 1'b1 && pkt_type == `DATA_TYPE ) begin
        if( dest_addr[0] == 1'b0 ) begin
            wr_addr <=   BASE0_ADDR ;
        end
        else begin
            wr_addr <=   BASE1_ADDR ;
        end
    end
    else if( wr_en == 1'b1 ) begin
        wr_addr   <=   wr_addr + 1'b1 ;
    end
end

assign  wr_data   =   slink_mmrx_data ;


always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        wr_sel  <=  1'b0 ;
    end
    else if( wr_finish == 1'b1  )begin
        wr_sel  <=  ~ wr_sel ;
    end
end

assign  wr_sel0  =   ( wr_sel == 1'b0 ) ? 1'b1 : 1'b0 ;
assign  wr_sel1  =   ( wr_sel == 1'b1 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_100m ) begin
    if( wr_en == 1'b1 && dest_addr[3:0] == 4'd3 && wr_data[16] == 1'b1 )begin
        wr_finish   <=   1'b1 ;
    end
    else begin
        wr_finish   <=   1'b0 ;
    end
end

always @ ( posedge clk_100m ) begin
    if( wr_en == 1'b1 && dest_addr[3:0] == 4'h0 && new_sop_d3 == 1'b1 )begin
        wr_start   <=   1'b1 ;
    end
    else begin
        wr_start   <=   1'b0 ;
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        pkt_full_flag0   <=  1'b0 ;
    end
    else if ( wr_sel == 1'b0 ) begin
        if ( wr_start == 1'b1 )begin
            pkt_full_flag0   <=  1'b0 ;
        end
        else if ( wr_finish == 1'b1 ) begin
            pkt_full_flag0   <=  1'b1 ;
        end
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        pkt_full_flag1   <=  1'b0 ;
    end
    else if ( wr_sel == 1'b1 ) begin
        if ( wr_start == 1'b1 )begin
            pkt_full_flag1   <=  1'b0 ;
        end
        else if ( wr_finish == 1'b1 ) begin
            pkt_full_flag1   <=  1'b1 ;
        end
    end
end

//----------------------------------------------------------------------------------
// read control
//----------------------------------------------------------------------------------
always @ ( posedge clk_100m ) begin
    chn_sel_d1   <=   chn_sel ;
end

assign  chn_sel_ring = ( chn_sel == 1'b1 && chn_sel_d1 == 1'b0 ) ? 1'b1 : 1'b0 ;
assign  rd_start = ( chn_sel_ring == 1'b1 && hrm_pkt_num == 4'd0 ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        rd_sel  <=  2'b10 ;
    end
    else if( rd_start == 1'b1  ) begin
        if ( pkt_full_flag0 == 1'b1 && pkt_full_flag1 == 1'b1 ) begin
            if ( wr_sel == 1'b0 ) begin
                rd_sel  <=  2'b01 ;
            end
            else begin
                rd_sel  <=  2'b00 ;
            end
        end
        else if ( pkt_full_flag0 == 1'b1 ) begin
            rd_sel  <=  2'b00 ;
        end
        else if ( pkt_full_flag1 == 1'b1 ) begin
            rd_sel  <=  2'b01 ;
        end
        else begin
            rd_sel  <=  2'b10 ;
        end
    end
end

assign  rd_data =  rd_sel[1] == 1'b1 ? 18'h00 : rd_sel[0] == 1'b0 ? rd_data0 : rd_data1 ;

assign  rd_sel0 =   ( rd_sel  ==  2'b00 ) ? 1'b1 : 1'b0 ;    
assign  rd_sel1 =   ( rd_sel  ==  2'b01 ) ? 1'b1 : 1'b0 ;   

//----------------------------------------------------------------------------------
// sub-module 
//----------------------------------------------------------------------------------
    HRM_MMRX_S                  U_0_HRM_MMRX
    (
    .clk_100m                   ( clk_100m                  ),
    .rst_100m                   ( rst_100m                  ),

    .rd_sel                     ( rd_sel0                   ),
    .chn_sel                    ( chn_sel                   ),
    .hrm_pkt_num                ( hrm_pkt_num               ),
    .rd_addr                    ( rd_addr                   ),
    .rd_data                    ( rd_data0                  ),

    .wr_sel                     ( wr_sel0                   ),
    .wr_en                      ( tpram_wr_en               ),
    .wr_addr                    ( wr_addr                   ),
    .wr_data                    ( wr_data                   )
    );

    HRM_MMRX_S                  U_1_HRM_MMRX
    (
    .clk_100m                   ( clk_100m                  ),
    .rst_100m                   ( rst_100m                  ),

    .rd_sel                     ( rd_sel1                   ),
    .chn_sel                    ( chn_sel                   ),
    .hrm_pkt_num                ( hrm_pkt_num               ),
    .rd_addr                    ( rd_addr                   ),
    .rd_data                    ( rd_data1                  ),

    .wr_sel                     ( wr_sel1                   ),
    .wr_en                      ( tpram_wr_en               ),
    .wr_addr                    ( wr_addr                   ),
    .wr_data                    ( wr_data                   )
    );


endmodule

