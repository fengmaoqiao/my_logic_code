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
// $Log:$
// from the 32bit fifo into 64bit dinidma interface
//
//**********************************************************
module dma_if_32to64(
    //clock and reset
    input               clk                                 ,
    input               rst_n                               ,
    //user port
    input   [31:0]      s1_axis_fromhost_tdata              ,
    input               s1_axis_fromhost_tvalid             ,
    input   [3:0]       s1_axis_fromhost_tkeep              ,
    input               s1_axis_fromhost_tlast              ,
    output              s1_axis_fromhost_tready             ,

    output  [63:0]      m1_axis_fromhost_tdata              ,
    output              m1_axis_fromhost_tvalid             ,
    output              m1_axis_fromhost_tlast              ,
    output  [7:0]       m1_axis_fromhost_tkeep              ,
    input               m1_axis_fromhost_tready             
        
      );

//**********************************************************
//Signal Declation
//**********************************************************
reg counter_data; 
wire [31:0] s1_axis_fromhost_temp;
//**********************************************************
//Main Code
//**********************************************************
always @(posedge clk or negedge rst_n)begin
     if(!rst_n)begin
        counter_data    <= 1'b0;    
     end
     else begin
         if(s1_axis_fromhost_tlast && counter_data == 1'b1)
             counter_data <= 1'b0;
         else begin
            if(s1_axis_fromhost_tready && s1_axis_fromhost_tvalid)
                counter_data <= counter_data + 1'b1;
            else
            ;
         end
    end
 end

assign s1_axis_fromhost_temp    =(counter_data == 1'b1) ? s1_axis_fromhost_tdata : s1_axis_fromhost_temp;
assign s1_axis_fromhost_tready = m1_axis_fromhost_tready;
assign m1_axis_fromhost_tvalid = (counter_data == 1'b0) ? s1_axis_fromhost_tvalid : 1'b0;
assign m1_axis_fromhost_tlast = s1_axis_fromhost_tlast;
assign m1_axis_fromhost_tdata = (counter_data == 1'b1) ? {s1_axis_fromhost_tdata,32'b0} : {s1_axis_fromhost_temp,s1_axis_fromhost_tdata};
assign m1_axis_fromhost_tkeep = (counter_data == 1'b1) ? 8'b00001111 : 8'b11111111;

endmodule




