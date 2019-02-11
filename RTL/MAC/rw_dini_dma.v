//**********************************************************
//
// Copyright(c) 2017 . Outwitcom Technology Co., LTD.
// All rights reserved.
//
// ProjectName :
// target      :
// FileName    : rw_dini_dma.sv
// Author      : qiupeng
// E_mail      : qiupeng@outwitcom.com
// Date        :
// Version     :
//
// Modification history
//--------------------------------------------------------
// $Log:$
//
//
//**********************************************************

`default_nettype wire
(* dont_touch = "true" *)
module rw_dini_dma (
        //clock and reset
        input       wire               clk                         ,
        input       wire               rst_n                       ,
        //interrupt
        output      wire [15:0]         lli_irq                     ,
        output      wire [ 3:0]         channel_irq                 ,
        output      wire                error_irq                   ,
        //proc_ahb
        input       wire               hready_in_regb              ,
        input       wire               hsel_regb                   ,
        input       wire [ 7:0]        haddr_regb                  ,
        input       wire [ 1:0]        htrans_regb                 ,
        input       wire               hwrite_regb                 ,
        output      wire [31:0]         hrdata_regb                 ,
        input       wire [31:0]        hwdata_regb                 ,
        output      wire [ 1:0]         hresp_regb                  ,
        output      wire                hready_regb                 ,
        //lli_ahb
        input       wire               hready_lli                  ,
        output      wire [31:0]         haddr_lli                   ,
        output      wire [ 1:0]         htrans_lli                  ,
        output      wire                hwrite_lli                  ,
        input       wire [31:0]        hrdata_lli                  ,
        input       wire [ 1:0]        hresp_lli                   ,
                
        //   
		input 						s0_axis_fromhost_tvalid		,
		output						s0_axis_fromhost_tready		,
		input 	[63:0]				s0_axis_fromhost_tdata		,	
		input	[7:0]				s0_axis_fromhost_tkeep		,
		input						s0_axis_fromhost_tlast		,
		 
		output						m0_axis_tohost_tvalid		,
		input						m0_axis_tohost_tready		,
		output	[63:0]				m0_axis_tohost_tdata		,
		output	[7:0]				m0_axis_tohost_tkeep		,
		output						m0_axis_tohost_tlast		,
		//downstream 
		input 						s1_axis_fromhost_tvalid		,
		output						s1_axis_fromhost_tready		,
		input 	[63:0]				s1_axis_fromhost_tdata		,
		input	[7:0]				s1_axis_fromhost_tkeep		,
		input						s1_axis_fromhost_tlast		,
		
		output						m1_axis_tohost_tvalid		,
		input						m1_axis_tohost_tready		,
		output	[63:0]				m1_axis_tohost_tdata		,
		output	[7:0]				m1_axis_tohost_tkeep		,
		output						m1_axis_tohost_tlast 		,
        
        
        
        //Bus interfaces
        //
        input       wire                      hready_upstream             ,
        output      wire [31:0]               haddr_upstream              ,
        output      wire [1:0]                htrans_upstream             ,
        input       wire [31:0]               hrdata_upstream             ,
        //upstream
        input       wire                     dma0_ready                  ,
        output      wire [31:0]              dma0_addr                   ,
        output      wire                     dma0_trans                  ,
        input       wire [63:0]              dma0_rdata                  ,
        //downstream
        input       wire                     dma1_ready                  ,
        output      wire [31:0]              dma1_addr                   ,
        output      wire                     dma1_trans                  ,
        output      wire [7:0]               dma1_we                     ,
        output      wire [63:0]              dma1_wdata
        );
//**********************************************************
//Signal Declation
//**********************************************************
wire                                channel_dir                 ;
wire                                channel_req                 ;
wire    [31:0]                      channel_saddr               ;
wire    [31:0]                      channel_daddr               ;
wire    [15:0]                      channel_length              ;
wire    [ 3:0]                      channel_tag                 ;

wire                                upstream_sel                ;
wire                                upstream_busy               ;
wire                                upstream_ack                ;
wire    [ 3:0]                      upstream_ack_tag            ;
wire    [15:0]                      upstream_ack_length         ;
wire                                upstream_ack_ack            ;
wire    [31:0]                      upstream_src_addr           ;
wire    [31:0]                      upstream_dst_addr           ;
wire    [15:0]                      upstream_length             ;

reg                                 upstream_busif_start        ;
wire    [63:0]                      upstream_aligner_data       ;
wire                                upstream_aligner_data_en    ;
wire    [63:0]                      upstream_busif_data         ;
wire                                upstream_busif_data_en      ;
wire                                upstream_busif_data_last    ;

reg                                 upstream_ahbif_start        ;
wire    [63:0]                      upstream_ahbif_data         ;
wire                                upstream_ahbif_data_en      ;
wire                                upstream_ahbif_data_last    ;

wire                                upstream_start              ;
reg     [63:0]                      upstream_data               ;
reg                                 upstream_data_en            ;
reg                                 upstream_data_last          ;

wire                                downstream_sel              ;
wire                                downstream_busy             ;
wire                                downstream_ack              ;
wire    [ 3:0]                      downstream_ack_tag          ;
wire    [15:0]                      downstream_ack_length       ;
wire                                downstream_ack_ack          ;

wire                                downstream_busif_start      ;
wire                                downstream_busif_done       ;
wire                                downstream_busif_stall      ;

wire    [63:0]                      downstream_data             ;
wire                                downstream_data_en          ;
wire                                downstream_data_last        ;

wire    [63:0]                      downstream_aligner_data     ;
wire                                downstream_aligner_data_en  ;

wire    [ 2:0]                      downstream_src_addr         ;
wire    [31:0]                      downstream_dst_addr         ;
wire    [15:0]                      downstream_length           ;

//upstream interface 
wire    [63:0]                      dma0_fromhost_data          ;
wire    [ 7:0]                      dma0_fromhost_ctrl          ;
wire                                dma0_fromhost_valid         ;
wire                                dma0_fromhost_accept        ;

wire    [63:0]                      dma0_tohost_data            ;
wire    [ 7:0]                      dma0_tohost_ctrl            ;
wire                                dma0_tohost_valid           ;
wire                                dma0_tohost_almost_full     ;
//downstream interface 
wire    [63:0]                      dma1_fromhost_data          ;
wire    [7:0]                       dma1_fromhost_ctrl          ;
wire                                dma1_fromhost_valid         ;
wire                                dma1_fromhost_accept        ;

wire    [63:0]                      dma1_tohost_data            ;
wire    [ 7:0]                      dma1_tohost_ctrl            ;
wire                                dma1_tohost_valid           ;
wire                                dma1_tohost_almost_full     ;
//**********************************************************
//Main Code
//**********************************************************
dma_interface u_dma_interface(
        //clock and reset        
        .clk                        (clk                        ),
        .rst_n                      (rst_n                      ),
                
        //upstream interface with the axi-stream fifo

        .s0_axis_fromhost_tvalid		(s0_axis_fromhost_tvalid),
		.s0_axis_fromhost_tready		(s0_axis_fromhost_tready),
		.s0_axis_fromhost_tdata			(s0_axis_fromhost_tdata),
		.s0_axis_fromhost_tkeep			(s0_axis_fromhost_tkeep),
		.s0_axis_fromhost_tlast			(s0_axis_fromhost_tlast),
		 
		.m0_axis_tohost_tvalid			(m0_axis_tohost_tvalid),
		.m0_axis_tohost_tready			(m0_axis_tohost_tready),
		.m0_axis_tohost_tdata			(m0_axis_tohost_tdata),
		.m0_axis_tohost_tkeep			(m0_axis_tohost_tkeep),
		.m0_axis_tohost_tlast			(m0_axis_tohost_tlast),
		 
		 //downstrem interface with the axi-stream fifo
		.s1_axis_fromhost_tvalid		(s1_axis_fromhost_tvalid),
		.s1_axis_fromhost_tready		(s1_axis_fromhost_tready),
		.s1_axis_fromhost_tdata			(s1_axis_fromhost_tdata),
		.s1_axis_fromhost_tkeep			(s1_axis_fromhost_tkeep),
		.s1_axis_fromhost_tlast			(s1_axis_fromhost_tlast),
		  
		.m1_axis_tohost_tvalid			(m1_axis_tohost_tvalid),
		.m1_axis_tohost_tready			(m1_axis_tohost_tready),
		.m1_axis_tohost_tdata			(m1_axis_tohost_tdata),
		.m1_axis_tohost_tkeep			(m1_axis_tohost_tkeep),
		.m1_axis_tohost_tlast			(m1_axis_tohost_tlast),
		
		//upstream interface with the upstream ack
		.dma0_fromhost_data				(dma0_fromhost_data),
		.dma0_fromhost_ctrl				(dma0_fromhost_ctrl),
		.dma0_fromhost_valid			(dma0_fromhost_valid),
		.dma0_fromhost_accept			(dma0_fromhost_accept),
		//upstream interface with the upstream req and data
		.dma0_tohost_data				(dma0_tohost_data),
		.dma0_tohost_ctrl				(dma0_tohost_ctrl),
		.dma0_tohost_valid				(dma0_tohost_valid),
		.dma0_tohost_almost_full			(dma0_tohost_almost_full),
		//downstream interface with the downstream data and ack
		.dma1_fromhost_data				(dma1_fromhost_data),
		.dma1_fromhost_ctrl				(dma1_fromhost_ctrl),
		.dma1_fromhost_valid			(dma1_fromhost_valid),
		.dma1_fromhost_accept			(dma1_fromhost_accept),
		//downstream interface with the downstream req
		.dma1_tohost_data				(dma1_tohost_data),
		.dma1_tohost_ctrl				(dma1_tohost_ctrl),
		.dma1_tohost_valid				(dma1_tohost_valid),
		.dma1_tohost_almost_full			(dma1_tohost_almost_full)
		
		
		
        );

dma_ctrl u_dma_ctrl (
        //clock and reset
        .clk                    (clk                    ),
        .rst_n                  (rst_n                  ),

        //interrupts
        .lli_irq                (lli_irq                ),
        .channel_irq            (channel_irq            ),
        .error_irq              (error_irq              ),
    
        //proc_ahb
        .hready_in_regb         (hready_in_regb         ),
        .hsel_regb              (hsel_regb              ),
        .haddr_regb             (haddr_regb             ),
        .htrans_regb            (htrans_regb            ),
        .hwrite_regb            (hwrite_regb            ),
        .hrdata_regb            (hrdata_regb            ),
        .hwdata_regb            (hwdata_regb            ),
        .hready_regb            (hready_regb            ),
        .hresp_regb             (hresp_regb             ),
        //lli_ahb
        .hready_lli             (hready_lli             ),
        .haddr_lli              (haddr_lli              ),
        .htrans_lli             (htrans_lli             ),
        .hwrite_lli             (hwrite_lli             ),
        .hrdata_lli             (hrdata_lli             ),
        .hresp_lli              (hresp_lli              ),

        //physical channel interface
        //fragment request
        .channel_dir            (channel_dir            ),
        .channel_req            (channel_req            ),
    
        //fragment request parameters
        .channel_saddr          (channel_saddr          ),
        .channel_daddr          (channel_daddr          ),
        .channel_length         (channel_length         ),
        .channel_tag            (channel_tag            ),
        
        //upstream physical busy), can't accept request
        .upstream_busy          (upstream_busy          ),
    
        //upstream physical channel acknowledge 
        .upstream_ack           (upstream_ack           ),
        .upstream_ack_tag       (upstream_ack_tag       ),
        .upstream_ack_length    (upstream_ack_length    ),
        .upstream_ack_ack       (upstream_ack_ack       ),
        
        // upstream physical busy, can't accept request
        .downstream_busy        (downstream_busy        ),
        
        // associated address requried if data are returned out-of-order 
        .downstream_oft_saddr   (downstream_src_addr    ),
        .downstream_oft_daddr   (downstream_dst_addr    ),
        .downstream_oft_length  (downstream_length      ),
        
        // upstream physical channel acknowledge 
        .downstream_ack         (downstream_ack         ),
        .downstream_ack_tag     (downstream_ack_tag     ),
        .downstream_ack_length  (downstream_ack_length  ),
        .downstream_ack_ack     (downstream_ack_ack     )
        );

//UPSTREAM PATH
assign upstream_sel = ~channel_dir;
  
upstream_req_n_data u_upstream_req_n_data (
        //clock and reset
        .clk                    (clk                    ),
        .rst_n                  (rst_n                  ),
        //channel request
        .channel_sel            (upstream_sel           ),
        .channel_req            (channel_req            ),
        .channel_saddr          (channel_saddr          ),
        .channel_daddr          (channel_daddr          ),
        .channel_length         (channel_length         ),
        .channel_tag            (channel_tag            ),
        .channel_busy           (upstream_busy          ),
        //fragment parameters
        .src_addr               (upstream_src_addr      ),
        .dst_addr               (upstream_dst_addr      ),
        .byte_length            (upstream_length        ),
        //aligner interface
        .busif_start            (upstream_start         ),
        .aligner_data           (upstream_aligner_data  ),
        .aligner_data_en        (upstream_aligner_data_en),
        //dini tohost interface
        .tohost_almost_full     (dma0_tohost_almost_full),
        .tohost_data            (dma0_tohost_data       ),
        .tohost_ctrl            (dma0_tohost_ctrl       ),
        .tohost_valid           (dma0_tohost_valid      )
        );

aligner u_upstream_aligner (
        //clock and reset
        .clk                    (clk                    ),
        .rst_n                  (rst_n                  ),
        //
        .start                  (upstream_start         ),
        .src_addr               (upstream_src_addr[2:0] ),
        .dst_addr               (upstream_dst_addr[2:0] ),
        //
        .datai                  (upstream_data          ),
        .datai_en               (upstream_data_en       ),
        .datai_last             (upstream_data_last     ),
        //
        .datao                  (upstream_aligner_data  ),
        .datao_en               (upstream_aligner_data_en)
        );



always @*
begin
    // If the source Addr is in the SRAM, the upstream_busif interface is used
    if (upstream_src_addr[24:23] == 2'b0)
    begin
        upstream_busif_start = upstream_start;
        upstream_ahbif_start = 1'b0;
        upstream_data        = upstream_busif_data;
        upstream_data_en     = upstream_busif_data_en;
        upstream_data_last   = upstream_busif_data_last;
    end
    else  
    // If the source Addr is not in the SRAM, the upstream_ahbif interface is used
    begin
        upstream_busif_start = 1'b0;
        upstream_ahbif_start = upstream_start;
        upstream_data        = upstream_ahbif_data;
        upstream_data_en     = upstream_ahbif_data_en;
        upstream_data_last   = upstream_ahbif_data_last;
    end
end
  
  
upstream_busif u_upstream_busif (
        //clock and reset
        .clk                    (clk                    ),
        .rst_n                  (rst_n                  ),
        //control/state
        .start                  (upstream_busif_start   ),
        .pause                  (dma0_tohost_almost_full),
        .done                   (                       ),
        //Static parameters
        .src_addr               (upstream_src_addr      ),
        .src_length             (upstream_length        ),
        //bus interface
        .bus_ready              (dma0_ready             ),
        .bus_addr               (dma0_addr              ),
        .bus_trans              (dma0_trans             ),
        .bus_data               (dma0_rdata             ),
        //aligner interface
        .data                   (upstream_busif_data    ),
        .data_en                (upstream_busif_data_en ),
        .data_last              (upstream_busif_data_last)            
        );

upstream_ahbif u_upstream_ahbif (
        //clock and reset
        .clk                    (clk                    ),
        .rst_n                  (rst_n                  ),
        //control/state
        .start                  (upstream_ahbif_start   ),
        .pause                  (dma0_tohost_almost_full),
        .done                   (                       ),
        //Static paramters
        .src_addr               (upstream_src_addr      ),
        .src_length             (upstream_length        ),
        //AHB interface
        .hready                 (hready_upstream        ),
        .haddr                  (haddr_upstream         ),
        .htrans                 (htrans_upstream        ),
        .hrdata                 (hrdata_upstream        ),
        //aligner interface
        .data                   (upstream_ahbif_data    ),
        .data_en                (upstream_ahbif_data_en ),
        .data_last              (upstream_ahbif_data_last)            
        );

upstream_ack u_upstream_ack (
        //clock and reset
        .clk                    (clk                    ),
        .rst_n                  (rst_n                  ),
        //Dini fromhost interface
        .fromhost_data          (dma0_fromhost_data     ),
        .fromhost_ctrl          (dma0_fromhost_ctrl     ),
        .fromhost_valid         (dma0_fromhost_valid    ),
        .fromhost_accept        (dma0_fromhost_accept   ),
        //Dini fromhost interface
        .upstream_ack           (upstream_ack           ),
        .upstream_ack_tag       (upstream_ack_tag       ),
        .upstream_ack_length    (upstream_ack_length    ),
        .upstream_ack_ack       (upstream_ack_ack       )
        );
 
//DOWNSTREAM PATH
assign downstream_sel = channel_dir;

downstream_req u_downstream_req (
        //clock and reset
        .clk                    (clk                    ),
        .rst_n                  (rst_n                  ),
        //channel request
        .channel_sel            (downstream_sel         ),
        .channel_req            (channel_req            ),
        .channel_saddr          (channel_saddr          ),
        .channel_length         (channel_length         ),
        .channel_tag            (channel_tag            ),
        .channel_busy           (downstream_busy        ),
        //Dini tohost interface
        .tohost_almost_full     (dma1_tohost_almost_full),
        .tohost_data            (dma1_tohost_data       ),
        .tohost_ctrl            (dma1_tohost_ctrl       ),
        .tohost_valid           (dma1_tohost_valid      )
        );

downstream_data_n_ack u_downstream_data_n_ack (
        //clock and reset
        .clk                    (clk                    ),
        .rst_n                  (rst_n                  ),
        //Dini fromhost interface
        .fromhost_data          (dma1_fromhost_data     ),
        .fromhost_ctrl          (dma1_fromhost_ctrl     ),
        .fromhost_valid         (dma1_fromhost_valid    ),
        .fromhost_accept        (dma1_fromhost_accept   ),
        //DMA controller interface (ACK)
        .downstream_ack         (downstream_ack         ),
        .downstream_ack_tag     (downstream_ack_tag     ),
        .downstream_ack_length  (downstream_ack_length  ),
        .downstream_ack_ack     (downstream_ack_ack     ),
        //bus interface
        .busif_start            (downstream_busif_start ),
        .busif_done             (downstream_busif_done  ),
        .busif_stall            (downstream_busif_stall ),
        //Aligner interface
        .aligner_data           (downstream_data        ),
        .aligner_data_en        (downstream_data_en     ),
        .aligner_data_last      (downstream_data_last   )
        );

aligner u_downstream_aligner (
        //clock and reset
        .clk                    (clk                    ),
        .rst_n                  (rst_n                  ),
        //
        .start                  (downstream_busif_start ),
        .src_addr               (downstream_src_addr[2:0]),
        .dst_addr               (downstream_dst_addr[2:0]),
        //
        .datai                  (downstream_data        ),
        .datai_en               (downstream_data_en     ),
        .datai_last             (downstream_data_last   ),
        .datao                  (downstream_aligner_data),
        .datao_en               (downstream_aligner_data_en)
        );

downstream_busif u_downstream_busif (
        //clock and reset
        .clk                    (clk                    ),
        .rst_n                  (rst_n                  ),
        //control/state
        .start                  (downstream_busif_start ),
        .stall                  (downstream_busif_stall ),
        .done                   (downstream_busif_done  ),
        //Static parameters
        .dst_addr               (downstream_dst_addr    ),
        .dst_length             (downstream_length      ),
        //aligner interface
        .data                   (downstream_aligner_data),
        .data_en                (downstream_aligner_data_en),
        //bus interface
        .bus_ready              (dma1_ready             ),
        .bus_addr               (dma1_addr              ),
        .bus_trans              (dma1_trans             ),
        .bus_we                 (dma1_we                ),
        .bus_data               (dma1_wdata             )
        );

endmodule
