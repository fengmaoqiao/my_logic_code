// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   MACTX
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
// Clock Domains    :   clk_12_5m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`include "DEFINES.v"

module EX_MACTX
    (
    clk_12_5m                   ,   
    rst_12_5m                   ,   

    mmtx_mactx_data             ,   
	mmtx_mactx_dval             ,   
    mactx_mmtx_rdreq            ,   

    mactx_pcstx_data            ,   
    mactx_pcstx_dval            ,  

    slink_tx_eop    
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
input   wire        [17:0]      mmtx_mactx_data                     ;   
input   wire                    mmtx_mactx_dval                     ;   

// declare output signal
output  wire                    mactx_mmtx_rdreq                    ;   
output  reg         [7:0]       mactx_pcstx_data                    ;   
output  reg                     mactx_pcstx_dval                    ;  
output  reg                     slink_tx_eop                        ;   

// declare inout signal
       
/**********************************************************************************\
**************************** declare singal attribute ******************************
\**********************************************************************************/
// wire signal
wire                            sop_flag                            ;   
wire                            eop_flag                            ;   
wire                            chksum_dval                         ;   
wire                            chksum_eop                          ;   
wire        [31:0]              chksum_dout                         ;   
wire        [7:0]               chksum_data                         ;  

// reg signal
reg                             premble_flag                        ;   
reg         [7:0]               insert_premble                      ;   
reg         [3:0]               premble_byte_cnt                    ;   
reg			[15:0]		        pkt_head			                ;   
reg                             chksum_eop_d1                       ;   
reg                             eop_insert                          ;   
reg                             eop_insert_d1                       ;   
reg         [3:0]               eop_insert_cnt                      ;   
reg                             byte_convert                        ;   
reg                             eop_flag_d1                         ;   
reg         [15:0]              mmtx_mactx_data_d1                  ;   
reg         [7:0]               mmtx_mactx_data_d2                  ;  
reg                             sop_flag_d1                         ; 
reg         [7:0]               crc_insert                          ;   

/**********************************************************************************\
******************************** debug code ****************************************
\**********************************************************************************/

/**********************************************************************************\
********************************* main code ****************************************
\**********************************************************************************/
assign  mactx_mmtx_rdreq = ( premble_flag == 1'b0 && eop_flag_d1 == 1'b0 
                              && eop_insert == 1'b0 && mmtx_mactx_dval == 1'b0 ) ? 1'b1 : 1'b0 ;

assign  sop_flag = ( mmtx_mactx_dval == 1'b1 && mmtx_mactx_data[17] == 1'b1 ) ? 1'b1 : 1'b0 ;
assign  eop_flag = ( mmtx_mactx_dval == 1'b1 && mmtx_mactx_data[16] == 1'b1 ) ? 1'b1 : 1'b0 ;

always @( posedge clk_12_5m ) begin
    slink_tx_eop   <=   chksum_eop_d1 ;
end

//----------------------------------------------------------------------------------
// byte convert
//----------------------------------------------------------------------------------
always @( posedge clk_12_5m ) begin
    if( mmtx_mactx_dval == 1'b1 ) begin
        byte_convert   <=   1'b0 ;
    end
    else begin
        byte_convert   <=   1'b1 ;    
    end
end

always @( posedge clk_12_5m ) begin
    sop_flag_d1 <= sop_flag ; 
end

always @( posedge clk_12_5m ) begin
    mmtx_mactx_data_d1   <= mmtx_mactx_data[15:0] ;    
    mmtx_mactx_data_d2   <= mmtx_mactx_data_d1[7:0] ;    
end

//----------------------------------------------------------------------------------
// insert preamble: 55 55 55 55 55 55 55 D5
//----------------------------------------------------------------------------------
always @( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        premble_flag <=   1'b0 ;           
    end
    else begin
        if( premble_byte_cnt[3] == 1'b1 ) begin
            premble_flag <=   1'b0 ;
        end
        else if( sop_flag == 1'b1 ) begin // add premblele after sop 
            premble_flag <=   1'b1 ;   
        end
    end
end

always @( posedge clk_12_5m ) begin
    if( premble_flag == 1'b1 ) begin
        premble_byte_cnt <=   premble_byte_cnt + 1'b1 ;
    end
    else begin
        premble_byte_cnt <=   4'h0 ;   
    end
end

always @( posedge clk_12_5m ) begin
    if ( premble_byte_cnt == 4'd6 ) begin
        insert_premble  <=   8'hd5 ;
    end
    else if ( premble_byte_cnt == 4'd7 ) begin
        insert_premble  <=   pkt_head[15:8] ;
    end
    else if ( premble_byte_cnt == 4'd8 ) begin
        insert_premble  <=   pkt_head[7:0] ;
    end
    else begin
        insert_premble  <=   8'h55 ;   
    end
end

always @( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        pkt_head    <=   16'h00 ;
    end
    else begin
        if( sop_flag == 1'b1 ) begin
            pkt_head    <=   mmtx_mactx_data[15:0] ; 
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// FCS32 input signal generator
//----------------------------------------------------------------------------------
assign  chksum_dval = ( mmtx_mactx_dval == 1'b1 || byte_convert == 1'b0 ) ? 1'b1 : 1'b0 ;
assign  chksum_eop  = eop_flag_d1 ;
assign  chksum_data = ( mmtx_mactx_dval == 1'b1 ) ? mmtx_mactx_data[15:8] : mmtx_mactx_data_d1 ;

always @( posedge clk_12_5m ) begin
    eop_flag_d1   <=   eop_flag ;
end

always @( posedge clk_12_5m ) begin
    chksum_eop_d1   <=   chksum_eop ;
end

    FCS32                       U_FCS32 
    (
    //input port
    .clk_sys                    ( clk_12_5m                 ),
    .rst_sys                    ( ~rst_12_5m                ),
    .crc_din                    ( chksum_data               ),
    .crc_cap                    ( chksum_eop                ),
    .crc_sop                    ( chksum_eop_d1             ),
    .crc_din_vld                ( chksum_dval               ),
    //output port
    .crc_dout                   ( chksum_dout               )
    );

//----------------------------------------------------------------------------------
// after old eop insert fcs( 4 byte ) and ipg ( 12 byre )
//----------------------------------------------------------------------------------
always @( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        eop_insert  <=   1'b0 ;
    end
    else begin
        if( eop_insert_cnt == 4'd15 ) begin
            eop_insert  <=   1'b0 ;    
        end
        else if( chksum_eop == 1'b1 ) begin
            eop_insert  <=   1'b1 ;    
        end
    end
end

always @( posedge clk_12_5m ) begin
    eop_insert_d1   <=   eop_insert ;
end

always @( posedge clk_12_5m ) begin
    if( eop_insert == 1'b1 ) begin
        eop_insert_cnt  <=   eop_insert_cnt + 1'b1 ;     
    end
    else begin
        eop_insert_cnt  <=   4'h0 ;  
    end
end

always @( * ) begin
    case( eop_insert_cnt )
        4'b0000 : crc_insert    <=   chksum_dout[31:24] ;
        4'b0001 : crc_insert    <=   chksum_dout[23:16] ;
        4'b0010 : crc_insert    <=   chksum_dout[15:8] ;
        4'b0011 : crc_insert    <=   chksum_dout[7:0] ;
        4'b0100 : crc_insert    <=   8'hfd ;
        default : crc_insert    <=   8'h00 ;
    endcase
end

//----------------------------------------------------------------------------------
// output 
//----------------------------------------------------------------------------------
always @( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        mactx_pcstx_data    <=   8'h00 ;            
    end
    else begin
        if( premble_flag == 1'b1 || premble_byte_cnt[3] == 1'b1 ) begin
            mactx_pcstx_data    <=   insert_premble ;
        end
        else if( eop_insert == 1'b1 ) begin
            mactx_pcstx_data    <=   crc_insert ;
        end
        else if( mmtx_mactx_dval == 1'b1 )begin
            mactx_pcstx_data    <=   mmtx_mactx_data[15:8] ;
        end
        else begin
            mactx_pcstx_data    <=   mmtx_mactx_data_d1[7:0] ;  
        end
    end
end

always @( posedge clk_12_5m or negedge rst_12_5m ) begin
    if( rst_12_5m == 1'b0 ) begin
        mactx_pcstx_dval   <=   1'b0 ;    
    end
    else begin
        if( eop_insert_cnt == 4'd5 ) begin
            mactx_pcstx_dval   <=   1'b0 ;   
        end
        else if( sop_flag_d1 == 1'b1 ) begin
            mactx_pcstx_dval   <=   1'b1 ;    
        end
    end
end

endmodule
