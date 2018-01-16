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
//
//
//**********************************************************
module dma_if_64to32(
     //clock and reset
     input              clk                                 ,
     input              rst_n                               ,
     //user port, 
     //fifo output 
     input              s0_axis_tohost_tvalid                       ,
     input [63:0]       s0_axis_tohost_tdata                        ,
     input [7:0]        s0_axis_tohost_tkeep                        ,
     input              s0_axis_tohost_tlast                        ,
     output reg         s0_axis_tohost_tready                       ,
     //axi_dma if
     output reg         m0_axis_tohost_tvalid                       ,
     output reg [31:0]  m0_axis_tohost_tdata                        ,
     output reg [7:0]   m0_axis_tohost_tkeep                        ,
     output reg         m0_axis_tohost_tlast                        ,
     input              m0_axis_tohost_tready                       

      );

//**********************************************************
//Signal Declation
//**********************************************************
//compute the data from fifo
reg [15:0] counter_data;
//temp data from fifo
reg [63:0] data_fromfifo64;
//**********************************************************
//Main Code
//**********************************************************
localparam S_IDEL = 3'b000;
localparam S_RD1  = 3'b001;
localparam S_RD2  = 3'b010;
 
always @(posedge clk or negedge rst_n)begin
    if(!rst_n) == 1'b0)begin
        current_state <= IDLE;
    end
    else begin
        current_state <= next_state;
    end
end


always @(*)begin
    case(current_state)begin
        IDLE:begin
            //once the fifo has data and axi_dma ready to get data,then fsm work
            if(m0_axis_tohost_tready && s0_axis_tohost_valid)begin
                next_state = S_RD1;
            end
            else begin
                next_state = IDLE;
            end
        end
        S_RD1:begin
            if(m0_axis_tohost_tvalid)begin
                 next_state = S_RD2;                
            end
            else begin
                next_state = IDLE;
            end
        S_RD2:begin
                 next_state = IDLE;
            default : next_state=IDLE;
        end
    endcase
end


always @(posedge clk or negedge rst_n)begin
     if(!rst_n) == 1'b0)begin
         m0_axis_tohost_tvalid <= 1'b;
         m0_axis_tohost_tkeep  <= 4'h0;
         m0_axis_tohost_tdata  <= 32'b0;
         m0_axis_tohost_tlast  <= 1'b0;
         s0_axis_tohost_tready <= 1'b0;
     end
     else begin
         case(current_state)
             IDLE:begin
                 m0_axis_tohost_tvalid <= 1'b0;
                 m0_axis_tohost_tdata <= 32'b0;
                 m0_axis_tohost_tkeep <= 4'b0;
                 m0_axis_tohost_tlast <= 1'b0;
                end
             S_RD1:begin
                 s0_axis_tohost_tready <= 1'b1;
                 m0_axis_tohost_tvalid <= 1'b1;
                 m0_axis_tohost_tkeep  <= 4'hff;
                 m0_axis_tohost_tdata  <= s0_axis_tohost_tdata[63:32];
                 if(s0_axis_tohost_tkeep == 8'h0f && s0_axis_tohost_tlast)
                     m0_axis_tohost_tlast <= 1'b1;
                 else
                     m0_axis_tohost_tlast <= 1'b0;
                end
             S_RD2:begin
                 s0_axis_tohost_tready <= 1'b0;
                 m0_axis_tohost_tvalid <= 1'b1;
                 m0_axis_tohost_tkeep <= 4'hff;
                 m0_axis_tohost_tdata <= s0_axis_tohost_tdata[31:0];
             end    
     end
end





















endmodule
