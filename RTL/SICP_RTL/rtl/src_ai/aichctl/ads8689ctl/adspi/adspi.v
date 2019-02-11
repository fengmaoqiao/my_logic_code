// +FHDR***********************************************************************
// Copyright        :   CNG
// Confidential     :   I LEVEL
// ============================================================================
// FILE NAME        :   SPIM
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
// Reset Strategy   :   Async clear, active low
// Clock Domains    :   clk_100m
// Critical Timing  :   N/A
// Instantiations   :   N/A
// Ynthesizable     :   N/A
// Others           :
// -FHDR***********************************************************************
`timescale 1 ns / 1 ns
`include "DEFINES.v"

module ADSPI  
    (	
        rst_sys_n               ,   // system reset
        clk_sys                 ,   // system clock

        wr_trig                 ,   // data transmit enable
        rw_len                  ,   // send data length
        wr_value                ,   // parallel data in
        rd_trig                 ,   // data recieve enable
        rd_value                ,   // parallel data out
        done                    ,   // send done
        spi_rst                 ,   
        spi_cs                  ,   // chip selection of spi master interface 
        spi_clk                 ,   // clock of spi master interface
        spi_sdi                 ,   // master output and slave input
        spi_sdo                     // master input and slave output
	);

/**********************************************************************************\
|******************************** declare parameter *******************************|
\**********************************************************************************/
parameter    DIV_CNT         =   5'd5       ; // spi_clk is 3.125M , div_cnt = 100M/3.125M/2 - 1 = 15
localparam   CNV_TMCNT       =   8'd511      ; // cnv_tm = 100M/5us - 1 = 499
localparam   CNV_LOWCNT      =   8'd100      ; // convert the time of CS pull down
/**********************************************************************************\
|**************************** declare interface signal ****************************|
\**********************************************************************************/
// declare input singal
input                           rst_sys_n                           ;   
input   wire                    clk_sys                             ;   
input                           wr_trig                             ;   
input   wire    [5:0]           rw_len                              ;   
input   wire                    rd_trig                             ;   
input   wire    [31:0]          wr_value                            ;   
input   wire                    spi_sdo                             ;   
//declare output signal
output  reg     [31:0]          rd_value                            ;   
output  reg                     done                                ;   
output  reg                     spi_cs                              ;   
output  reg                     spi_clk                             ;   
output  reg                     spi_sdi                             ;   
output  wire                    spi_rst                             ;   
//declare inout signal

/*********************************************************************************\
|*********************** declare singal attribute ********************************|
\*********************************************************************************/
// wire singal

// reg singal
reg     [31:0]                  temp_data                           ;   
reg     [4:0]                   div_cnt                             ;   
reg     [5:0]                   clk_cnt                             ;   
reg                             sdo_d1                              ;   
reg                             sdo_d2                              ;   
reg                             cs_en                               ;   
reg                             cs_ph_en                            ;   
reg     [7:0]                   cnv_cnt                             ;   
reg                             cs_pd_en                            ;   
reg     [7:0]                   cnv_low_cnt                         ;   
reg                             rx_en                               ;   
reg                             rd_trig_en                          ;   
reg                             sclk_en                             ;   
/********************************************************************************\
|******************************* main code **************************************|
\********************************************************************************/
assign spi_rst  = 1'b1 ;

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        cs_en  <=  1'b0 ;
    end
    else begin
        if ( wr_trig == 1'b1 ) begin
            cs_en  <=  1'b1 ;
        end
        else if ( clk_cnt == 6'd18 || rd_trig == 1'b1 ) begin
            cs_en  <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_trig_en   <=  1'b0;
    end
    else begin
        if ( rd_trig == 1'b1 ) begin
            rd_trig_en   <=  1'b1;
        end
        else if ( done == 1'b1 ) begin
            rd_trig_en   <=  1'b0;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
       sclk_en  <=  1'b0; 
    end
    else begin
        if ( wr_trig == 1'b1 || rd_trig == 1'b1 ) begin
            sclk_en     <=  1'b1;
        end
        else if ( done == 1'b1 && cs_en == 1'b1 ) begin
            sclk_en <=  1'b0;
        end
        
    end
end
//----------------------------------------------------------------------------------
// recieve enable
//----------------------------------------------------------------------------------
always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
       cs_pd_en  <=  1'b0 ; 
    end
    else begin
        if ( rd_trig == 1'b1 ) begin
            cs_pd_en    <=  1'b1 ;
        end
        else if ( cnv_low_cnt == CNV_LOWCNT ) begin
            cs_pd_en    <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
       cnv_low_cnt  <=  8'd0 ; 
    end
    else begin
        if ( cs_pd_en == 1'b1 ) begin
            cnv_low_cnt  <=  cnv_low_cnt + 1'b1 ;
        end
        else begin
            cnv_low_cnt <=  8'd0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
       cs_ph_en  <=  1'b0 ; 
    end
    else begin
        if (cnv_low_cnt == CNV_LOWCNT - 1'b1 ) begin
            cs_ph_en     <=  1'b1 ;
        end
        else if ( cnv_cnt == CNV_TMCNT ) begin
            cs_ph_en <=  1'b0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
       cnv_cnt  <=  8'd0 ; 
    end
    else begin
        if ( cs_ph_en == 1'b1 ) begin
            cnv_cnt  <=  cnv_cnt + 1'b1 ;
        end
        else begin
            cnv_cnt <=  7'd0 ;
        end
    end
end

always @ ( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
       rx_en  <=  1'b0 ; 
    end
    else begin
        if (cnv_cnt == CNV_TMCNT ) begin
            rx_en     <=  1'b1 ;
        end
        else begin
            rx_en <=  1'b0 ;
        end
    end
end

//----------------------------------------------------------------------------------
// busy control 
//----------------------------------------------------------------------------------
always @( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        spi_cs  <=  1'b1 ;
    end
    else begin 
        if ( clk_cnt == rw_len && spi_clk == 1'b0 && div_cnt == DIV_CNT-5'd2 || cs_ph_en == 1'b1 ) begin
            spi_cs  <=  1'b1;
        end
        else if ( rx_en == 1'b1 || wr_trig == 1'b1 || cs_pd_en == 1'b1 ) begin
            spi_cs  <=  1'b0;
        end
        else ;
    end
end

always @( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        done  <=  1'b0 ;
    end
    else if( div_cnt == DIV_CNT-5'd3 && (clk_cnt == rw_len && spi_clk == 1'b0) ) begin
        done  <=  1'b1 ;
    end
    else begin
        done  <=  1'b0 ;
    end
end

//----------------------------------------------------------------------------------
// spi_clk generator
//----------------------------------------------------------------------------------
always @( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        div_cnt  <=  4'h0 ;
    end
    else if( spi_cs == 1'b0 && cs_pd_en == 1'b0 || ( clk_cnt == rw_len && rw_len != 8'd0 ) ) begin
        if( div_cnt == DIV_CNT ) begin
            div_cnt  <=  4'h0 ;
        end
        else begin
            div_cnt  <=  div_cnt + 1'b1 ;
        end
    end
    else begin
        div_cnt  <=  4'h0 ;  
    end
end

always @( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        spi_clk  <=  1'b0 ;
    end
    else begin
        if ( wr_trig == 1'b1 || rx_en == 1'b1 || spi_cs == 1'b1 || cs_pd_en == 1'b1  ) begin
            spi_clk  <=  1'b0 ;
        end
        else if( div_cnt == DIV_CNT && sclk_en == 1'b1 ) begin
            spi_clk  <=  ~ spi_clk ;
        end
        else ;
    end
end

//----------------------------------------------------------------------------------
// spi_clk count
//----------------------------------------------------------------------------------
always @( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        clk_cnt  <=  6'h00 ;
    end
    else if ( wr_trig == 1'b1 || rx_en == 1'b1 )  begin
        clk_cnt  <=  6'h00 ;
    end
    else if( div_cnt == DIV_CNT && spi_clk == 1'b0 ) begin
        if( clk_cnt == rw_len  ) begin
            clk_cnt  <=  6'h00 ;
        end
        else begin
            clk_cnt  <=  clk_cnt + 1'b1 ;
        end
    end
    else ;
end

//----------------------------------------------------------------------------------
// receive data serial to parallel
//----------------------------------------------------------------------------------
always @( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        sdo_d1  <=  1'b1 ;
        sdo_d2  <=  1'b1 ;
    end
    else begin
        sdo_d1  <=  spi_sdo ;
        sdo_d2  <=  sdo_d1 ;
    end
end

always @( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        rd_value  <=  32'd0 ;
    end
	else if ( spi_cs == 1'b0 && spi_clk == 1'b1 && div_cnt == DIV_CNT )  begin
        rd_value  <=  { rd_value[30:0] , sdo_d2 } ;
    end
    else ;
end

//----------------------------------------------------------------------------------
// write data convert to serial
//----------------------------------------------------------------------------------
always @( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        temp_data  <=  32'h00 ;
    end
    else if( wr_trig == 1'b1 ) begin
        temp_data  <=  wr_value ;
    end
    else if( spi_clk == 1'b1 && div_cnt == DIV_CNT - 5'd3 && clk_cnt != 6'h00 ) begin  
        temp_data  <=  { temp_data[30:0] , 1'b0 } ;
    end
    else ;
end

always @( posedge clk_sys or negedge rst_sys_n ) begin
    if( rst_sys_n == 1'b0 ) begin
        spi_sdi  <=  1'b0 ;
    end
    else begin
        if( spi_clk == 1'b0 && div_cnt == DIV_CNT - 5'd2 ) begin
            spi_sdi  <=  temp_data[31] ;
        end
    end
end

endmodule
