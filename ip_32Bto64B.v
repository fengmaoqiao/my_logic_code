//**********************************************************
//
// Copyright(c) 2017 . Outwitcom Technology Co., LTD.
// All rights reserved.
//
// ProjectName :
// target      :
// FileName    : 
// Author      :fengmaoqiao 
// E_mail      :fengmaoqiao@outwitcom.com 
// Date        :
// Version     :
//
// Modification history
//--------------------------------------------------------
// $Log:$convert  and transfer 
// the 32Bit data from axi_dma to 64Bit fifo
//
//
//**********************************************************
module(
     //clock and reset
     input              clk                                 ,
     input              rst_n                               ,     
     //user port
     input  [3:0]       s_axis_mm2s_tkeep                   ,
     input  [31:0]      s_axis_mm2s_tdata                   ,
     input              s_axis_mm2s_tlast                   ,
     input              s_axis_mm2s_tvalid                  ,
     output             s_axis_mm2s_tready                  ,
        
     output [7:0]       m_axis_fifo_tkeep                   ,
     output [63:0]      m_axis_fifo_tdata                   ,
     output             m_axis_fifo_tvalid                  ,
     output             m_axis_fifo_tlast                   ,
     input              m_axis_fifo_tready                       

      );

//**********************************************************
//Signal Declation
//**********************************************************
reg   [15:0] dma_32B_counter;
reg
reg

wire
wire
wire
//**********************************************************
//Main Code
//**********************************************************
assign s_axis_mm2s_tready = m_axis_fifo_tready;

always @(posedge clk or negedge rst_n)begin
     if(!rst_n) == 1'b0)begin
         dma_32B_counter <= 16'd0;
     end
     else begin
         if(s_axis_mm2s_tvalid && m_axis_fifo_tready && !s_axis_mm2s_tlast)
            dma_32B_counter <= dma_data_counter + 1;
         else if(s_axis_mm2s_tvalid && m_axis_fifo_tready && s_axis_mm2s_tlast)
            dma_32B_counter <= 16'd0;
         else
             ;
     end
end

always @(*)begin

    if( counter_data[0] == 1'b0 && s1_axis_fromhost_tready)
        m1_axis_fromhost_tdata = {s1_axis_fromhost_temp,s1_axis_fromhost_tdata};

    else if(counter_data[0] == 1'b1 && s1_axis_fromhost_tlast == 1'b0 && s1_axis_fromhost_tready)
        s1_axis_fromhost_temp = s1_axis_fromhost_tdata;

    else if(counter_data[0] == 1'b1 && s1_axis_fromhost_tlast == 1'b1 && s1_axis_fromhost_tready)
        m1_axis_fromhost_tdata = {32'b0,s1_axis_fromhost_temp};

    else
        ;
end

endmodule



