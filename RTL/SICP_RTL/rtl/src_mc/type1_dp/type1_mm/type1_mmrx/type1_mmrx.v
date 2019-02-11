// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   TYPE1_MMRX
// CREATE DATE      :   2017-09-09
// DEPARTMENT       :   R&D
// AUTHOR           :   TingtingGan
// AUTHOR'S EMAIL   :   gantingting@cng.com
// AUTHOR'S TEL     :   18280151291
// ============================================================================
// RELEASE  HISTORY
// VERSION  DATE        AUTHOR          DESCRIPTION
// V100     2017-09-09  TingtingGan     Original
// ============================================================================
// KEYWORDS         :
// PURPOSE          :   memory management of TYPE1 recive data path
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

module  TYPE1_MMRX
    (
    clk_100m                    ,   
    rst_100m                    , 

    chn_type                    ,   
    rd_dmm_empty                ,
    rr_sel                      ,

    // connect to EMIF module
    rd_sel                      ,   
    rd_port                     ,   
    rd_addr                     , 
    rd_dval                     ,   
    rd_data                     ,   

    // these signals from slink protocol stack
    slink_mm_empty              ,
    slink_mmrx_dval             ,   
    slink_mmrx_data             ,
    mmrx_slink_rdreq            ,

    // state frame 
    mpu_sta_dval                ,   
    mpu_sta_data                ,   
    ex1_sta_dval                ,   
    ex1_sta_data                ,   
    ex2_sta_dval                ,   
    ex2_sta_data                ,   
    ex3_sta_dval                ,   
    ex3_sta_data                ,   
    ex4_sta_dval                ,   
    ex4_sta_data                ,   
    hot_plug_req                ,   
    
    mm_delay_err                ,

    ex1_box_online              ,
    ex2_box_online              ,
    ex3_box_online              ,
    ex4_box_online              
    );

/**********************************************************************************\
***************************** declare parameter ************************************
\**********************************************************************************/
parameter   MPU_SLOT = 4'd0 ;

parameter   BASE0_ADDR  =   10'd000 ;  
parameter   BASE1_ADDR  =   10'd064 ;  
parameter   BASE2_ADDR  =   10'd128 ;  
parameter   BASE3_ADDR  =   10'd192 ;  
parameter   BASE4_ADDR  =   10'd256 ;  
parameter   BASE5_ADDR  =   10'd320 ;  
parameter   BASE6_ADDR  =   10'd384 ;  
parameter   BASE7_ADDR  =   10'd448 ;  
parameter   BASE8_ADDR  =   10'd512 ;  
parameter   BASE9_ADDR  =   10'd576 ;  
parameter   BASEA_ADDR  =   10'd640 ;  
parameter   BASEB_ADDR  =   10'd704 ;  
parameter   BASEC_ADDR  =   10'd768 ;  
parameter   BASED_ADDR  =   10'd832 ;  
parameter   BASEE_ADDR  =   10'd896 ;  
parameter   BASEF_ADDR  =   10'd960 ;

/**********************************************************************************\
***************************** declare interface signal *****************************
\**********************************************************************************/
// declare input singal
input   wire                    clk_100m                            ;   
input   wire                    rst_100m                            ;   

input   wire    [4:0]           chn_type                            ;   
input   wire    [3:0]           rr_sel                              ;   

input   wire                    rd_sel                              ;   
input   wire    [6:0]           rd_port                             ;   
input   wire    [8:0]           rd_addr                             ;   

input   wire                    slink_mm_empty                      ;   
input   wire                    slink_mmrx_dval                     ;   
input   wire    [17:0]          slink_mmrx_data                     ;   

// declare output signal
output  reg                     rd_dval                             ;   
output  reg     [17:0]          rd_data                             ; 
output  reg                     mpu_sta_dval  /* synthesis syn_preserve = 1 */     ;   
output  reg     [17:0]          mpu_sta_data  /* synthesis syn_preserve = 1 */     ;   
output  reg                     ex1_sta_dval  /* synthesis syn_preserve = 1 */     ;   
output  reg     [17:0]          ex1_sta_data  /* synthesis syn_preserve = 1 */     ;   
output  reg                     ex2_sta_dval  /* synthesis syn_preserve = 1 */     ;   
output  reg     [17:0]          ex2_sta_data  /* synthesis syn_preserve = 1 */     ;   
output  reg                     ex3_sta_dval  /* synthesis syn_preserve = 1 */     ;   
output  reg     [17:0]          ex3_sta_data  /* synthesis syn_preserve = 1 */     ;   
output  reg                     ex4_sta_dval  /* synthesis syn_preserve = 1 */     ;   
output  reg     [17:0]          ex4_sta_data  /* synthesis syn_preserve = 1 */     ;   
output  wire                    mmrx_slink_rdreq                    ;  
output  reg     [3:0]           rd_dmm_empty                        ;
output  wire                    mm_delay_err                        ;  
output  reg                     hot_plug_req                        ;   
output  reg     [14:0]          ex1_box_online                       ;
output  reg     [14:0]          ex2_box_online                       ;
output  reg     [14:0]          ex3_box_online                       ;
output  reg     [14:0]          ex4_box_online                       ;

// declare inout signal

/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire        [17:0]              wr_data                             ;
wire        [3:0]               rd_port_sel                         ;   
wire                            wr_en                               ;
wire        [17:0]              rd_data_tmp     [3:0]               ;
wire        [3:0]               wr_finish                           ;  
wire        [2:0]               ex_box_num                          ; 
wire        [2:0]               ex_box_num_tmp                      ;   
wire                            pfifo_sop                           ;   
wire                            pfifo_eop                           ;   
wire        [15:0]              pfifo_wrdata                        ;  
wire                            sta_dval                            ;   
wire        [17:0]              sta_data                            ;   
wire                            new_sop_d2                          ;   
wire                            data_sop                            ;   
// reg signal
reg         [7:0]               dest_addr                           ;   
reg         [15:0]              pkt_type                            ;  
reg                             new_sop                             ;  
reg         [2:0]               new_sop_d1                          ;   
reg                             new_sop_d3                          ;   
reg                             wr_en_flag                          ;   
reg         [9:0]               wr_addr                             ;   
reg                             mmrx_slink_rdreq_tmp                ;  
reg                             pfifo_wren                          ;  
reg                             pfifo_rden_d1                       ;  
reg         [4:0]               chn_type_d1                         ;   
   
reg         [15:0]              sour_addr                           ;   
reg         [13:0]              data_sop_dly                        ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/
assign  mm_delay_err = 1'b0 ;

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/

always @ ( posedge clk_100m ) begin
    chn_type_d1   <=   chn_type ;
end

//----------------------------------------------------------------------------------
// read request
//----------------------------------------------------------------------------------
assign mmrx_slink_rdreq = ( slink_mm_empty == 1'b0 && mmrx_slink_rdreq_tmp == 1'b1 ) ? 1'b1 : 1'b0 ; 

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        mmrx_slink_rdreq_tmp   <=   1'b1 ;
    end
    else if( | rd_port_sel == 1'b0 ) begin
        mmrx_slink_rdreq_tmp   <=   1'b1 ;
    end
    else if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[17] == 1'b1 && slink_mmrx_data[15] == 1'b0 )begin
        if( chn_type_d1 == `COM1_TYPE || chn_type_d1 == `COM2_TYPE || chn_type_d1 == `COM3_TYPE ) begin
            if( rd_port[5:4] == ex_box_num_tmp[1:0] && rd_port[3:0] == slink_mmrx_data[11:8] ) begin
                mmrx_slink_rdreq_tmp   <=   1'b0 ;
            end
            else begin
                mmrx_slink_rdreq_tmp   <=   1'b1 ;
            end
        end
        else begin
            mmrx_slink_rdreq_tmp   <=   1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// DA & SA & TYPE parse
//----------------------------------------------------------------------------------
//----------------------------------------------------------------------------------
// data delay
//----------------------------------------------------------------------------------
//always @ ( posedge clk_100m or negedge rst_100m ) begin
//    if( rst_100m == 1'b0 ) begin
//        data_sop   <=   1'b0 ;
//    end
//    else if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[17] == 1'b1 )begin
//        data_sop   <=   1'b1 ;
//    end
//    else begin
//        data_sop   <=   1'b0 ;
//    end
//end

assign data_sop = slink_mmrx_dval == 1'b1 && slink_mmrx_data[17] == 1'b1 ;

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        data_sop_dly   <=   14'd0 ;
    end
    else begin
        data_sop_dly   <=   { data_sop_dly[12:0] , data_sop } ;
    end
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        sour_addr   <=   16'd0 ;
    end
    else if( data_sop_dly[1] == 1'b1  )begin
        sour_addr   <=   slink_mmrx_data ;
    end
end

//always @ ( posedge clk_100m or negedge rst_100m ) begin
//    if( rst_100m == 1'b0 ) begin
//        dest_addr   <=   8'h00 ;
//    end
//    else if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[17] == 1'b1 )begin
//        dest_addr   <=   slink_mmrx_data[15:8] ;
//    end
//    else ;
//end

assign ex_box_num_tmp =  ( chn_type_d1 == `COM1_TYPE ) ? ( sour_addr[9:7] - 1'b1 ) : sour_addr[9:7] ; 
assign ex_box_num =  ( chn_type_d1 == `COM1_TYPE ) ? ( sour_addr[9:7] - 1'b1 ) : sour_addr[9:7] ; 

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        pkt_type   <=   16'h00 ;
    end
    else if ( data_sop_dly[3] == 1'b1 ) begin
        pkt_type   <=   slink_mmrx_data[15:0] ;
    end
    else ;
end

//----------------------------------------------------------------------------------
// state frame pfifo control
//----------------------------------------------------------------------------------
assign  pfifo_sop   =   new_sop_d2 ;
assign  pfifo_eop   =   ( slink_mmrx_dval == 1'b1 && slink_mmrx_data[16] == 1'b1 ) ? 1'b1 : 1'b0 ; 
assign  pfifo_wrdata =  new_sop_d2 == 1'b1 ? { 8'h00, 1'b0, sour_addr[9:7], sour_addr[5:2] } : slink_mmrx_data ;

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        pfifo_wren   <=   1'b0 ;
    end
    else begin
        if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[16] == 1'b1 )begin
            pfifo_wren   <=   1'b0 ;
        end
        else if ( new_sop_d1 == 3'd4 && pkt_type == `STA_TYPE ) begin
            pfifo_wren   <=   1'b1 ;
        end
    end
end

assign  sta_dval = pfifo_wren ;
assign  sta_data = { pfifo_sop , pfifo_eop , pfifo_wrdata } ;

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        hot_plug_req  <=   1'b0 ;
    end
    else begin
        if ( sta_dval == 1'b0 ) begin
            hot_plug_req  <=   1'b0 ;
        end
        else if ( new_sop_d3 == 1'b1 && sour_addr[9:7] == 3'b000 && slink_mmrx_data[15] == 1'b1 ) begin
            hot_plug_req  <=   1'b1 ;
        end
        else ;
    end
end

always @ ( posedge clk_100m ) begin
    if ( sour_addr[9:7] == 3'b000 ) begin
        mpu_sta_dval   <=   sta_dval ;
    end
    else begin
        mpu_sta_dval   <=   1'b0 ;
    end
end

always @ ( posedge clk_100m ) begin
    if ( sour_addr[9:7] == 3'b001 ) begin
        ex1_sta_dval   <=   sta_dval ;
    end
    else begin
        ex1_sta_dval   <=   1'b0 ;
    end
end

always @ ( posedge clk_100m ) begin
    if ( sour_addr[9:7] == 3'b010 ) begin
        ex2_sta_dval   <=   sta_dval ;
    end
    else begin
        ex2_sta_dval   <=   1'b0 ;
    end
end

always @ ( posedge clk_100m ) begin
    if ( sour_addr[9:7] == 3'b011 ) begin
        ex3_sta_dval   <=   sta_dval ;
    end
    else begin
        ex3_sta_dval   <=   1'b0 ;
    end
end

always @ ( posedge clk_100m ) begin
    if ( sour_addr[9:7] == 3'b100 ) begin
        ex4_sta_dval   <=   sta_dval ;
    end
    else begin
        ex4_sta_dval   <=   1'b0 ;
    end
end

always @ ( posedge clk_100m ) begin
    mpu_sta_data   <=   sta_data ;
    ex1_sta_data   <=   sta_data ;
    ex2_sta_data   <=   sta_data ;
    ex3_sta_data   <=   sta_data ;
    ex4_sta_data   <=   sta_data ;
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
        new_sop_d1   <=   3'd0 ;
    end
    else begin
        if( slink_mmrx_dval == 1'b1 ) begin
            if ( slink_mmrx_data[17] == 1'b1 )begin
                new_sop_d1   <=   3'd0 ;
            end
            else if ( new_sop_d1 == 3'd7 ) begin
                new_sop_d1   <=   new_sop_d1 ;
            end
            else begin
                new_sop_d1   <=   new_sop_d1 + 1'b1 ;
            end
        end
    end
end

assign  new_sop_d2  =   ( new_sop_d1 == 3'd5 ) ? 1'b1 : 1'b0 ; 

always @ ( posedge clk_100m ) begin
    new_sop_d3   <=   new_sop_d2 ;
end

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        wr_en_flag   <=   1'b0 ;
    end
    else begin
        if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[16] == 1'b1 )begin
            wr_en_flag   <=   1'b0 ;
        end
        else if( new_sop_d2 == 1'b1 && pkt_type == `DATA_TYPE ) begin
            wr_en_flag   <=   1'b1 ;
        end
    end
end

// FMQ modified. @2018/8/1 16:57:58
always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        ex1_box_online   <=  15'b0;
    end
    else begin
        if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[16] == 1'b1 && dest_addr == 3'b001 ) begin
            ex1_box_online   <=  slink_mmrx_data[14:0] ;
        end
    end
end

// FMQ modified. @2018/8/1 16:57:58
always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        ex2_box_online   <=  15'b0;
    end
    else begin
        if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[16] == 1'b1 && dest_addr == 3'b010 ) begin
            ex2_box_online   <=  slink_mmrx_data[14:0] ;
        end
    end
end
// FMQ modified. @2018/8/1 16:57:58
always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        ex3_box_online   <=  15'b0;
    end
    else begin
        if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[16] == 1'b1 && dest_addr == 3'b011 ) begin
            ex3_box_online   <=  slink_mmrx_data[14:0] ;
        end
    end
end
// FMQ modified. @2018/8/1 16:57:58
always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        ex4_box_online   <=  15'b0;
    end
    else begin
        if( slink_mmrx_dval == 1'b1 && slink_mmrx_data[16] == 1'b1 && dest_addr == 3'b100 ) begin
            ex4_box_online   <=  slink_mmrx_data[14:0] ;
        end
    end
end

assign  wr_en = ( wr_en_flag == 1'b1 && slink_mmrx_dval == 1'b1 ) ? 1'b1 : 1'b0  ;

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        wr_addr   <=   10'h00 ;
    end
    else begin
        if( new_sop_d2 == 1'b1 && pkt_type == `DATA_TYPE ) begin
            if( chn_type_d1 == `COM1_TYPE ) begin
                case( sour_addr[5:2] ) 
                    4'h0    : wr_addr   <=   BASE0_ADDR ;
                    4'h1    : wr_addr   <=   BASE1_ADDR ;
                    4'h2    : wr_addr   <=   BASE2_ADDR ;
                    4'h3    : wr_addr   <=   BASE3_ADDR ;
                    4'h4    : wr_addr   <=   BASE4_ADDR ;
                    4'h5    : wr_addr   <=   BASE5_ADDR ;
                    4'h6    : wr_addr   <=   BASE6_ADDR ;
                    4'h7    : wr_addr   <=   BASE7_ADDR ;
                    4'h8    : wr_addr   <=   BASE8_ADDR ;
                    4'h9    : wr_addr   <=   BASE9_ADDR ;
                    4'ha    : wr_addr   <=   BASEA_ADDR ;
                    4'hb    : wr_addr   <=   BASEB_ADDR ;
                    4'hc    : wr_addr   <=   BASEC_ADDR ;
                    4'hd    : wr_addr   <=   BASED_ADDR ;
                    4'he    : wr_addr   <=   BASEE_ADDR ;
                    4'hf    : wr_addr   <=   BASEF_ADDR ;
                    default : wr_addr   <=   BASE0_ADDR ; 
                endcase
            end
            else begin
                wr_addr   <=   BASE0_ADDR ;
            end
        end
        else if( wr_en == 1'b1 ) begin
            wr_addr   <=   wr_addr + 1'b1 ;
        end
    end
end

assign  wr_data   =   slink_mmrx_data ;

//----------------------------------------------------------------------------------
// read back data
//----------------------------------------------------------------------------------
always @ ( posedge clk_100m ) begin
    case( rd_port_sel )
        4'b0001   :   rd_data    =  rd_data_tmp[0] ; 
        4'b0010   :   rd_data    =  rd_data_tmp[1] ; 
        4'b0100   :   rd_data    =  rd_data_tmp[2] ; 
        4'b1000   :   rd_data    =  rd_data_tmp[3] ; 
        default   :   rd_data    =  18'h00 ; 
    endcase
end

always @ ( posedge clk_100m ) begin
    if( | rd_port_sel == 1'b1 )begin
        rd_dval   <=   1'b1 ;
    end
    else begin
        rd_dval   <=   1'b0 ;
    end
end

//----------------------------------------------------------------------------------
// empty generator
//----------------------------------------------------------------------------------
genvar j ;
generate
for( j = 0 ; j < 4 ; j = j+1 ) 
begin : nIOCHN

assign  wr_finish[j]    =   ( wr_en == 1'b1 && wr_data[16] == 1'b1 && ex_box_num[1:0] == j ) ? 1'b1 : 1'b0 ;

always @ ( posedge clk_100m or negedge rst_100m ) begin
    if( rst_100m == 1'b0 ) begin
        rd_dmm_empty[j] <= 1'b1 ;
    end
    else begin
        if( rd_port_sel[j] == 1'b1 && rd_data_tmp[j][16] == 1'b1 ) begin          
            rd_dmm_empty[j] <= 1'b1 ;
        end
        else if( wr_finish[j] == 1'b1 ) begin
            rd_dmm_empty[j] <= 1'b0 ;
        end
    end
end

end
endgenerate

//----------------------------------------------------------------------------------
// 4 port logic copy 
//----------------------------------------------------------------------------------
  genvar i;
  generate
  for( i = 0 ; i < 4 ; i = i+1 ) 
  begin : nLSRAM

    TYPE1_DMMRX                 #
    (
    .MPU_SLOT                   ( MPU_SLOT                  ),
    .EX_NUM                     ( i                         )
    )
    U_TYPE1_DMMRX
    (
    .clk_100m                   ( clk_100m                  ),
    .rst_100m                   ( rst_100m                  ),

    .ex_box_num                 ( ex_box_num[1:0]           ),
    .wr_en                      ( wr_en                     ),
    .wr_addr                    ( wr_addr                   ),
    .wr_data                    ( wr_data                   ),

    .rr_sel                     ( rr_sel[i]                 ),
    .rd_sel                     ( rd_sel                    ),
    .rd_port                    ( rd_port                   ),
    .rd_addr                    ( rd_addr                   ),

    .rd_port_sel                ( rd_port_sel[i]            ),
    .rd_data_tmp                ( rd_data_tmp[i]            )
    );

  end
  endgenerate

endmodule

