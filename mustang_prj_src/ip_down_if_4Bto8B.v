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

    output  reg [63:0]  m1_axis_fromhost_tdata              ,
    output  reg         m1_axis_fromhost_tvalid             ,
    output              m1_axis_fromhost_tlast              ,
    output  reg [7:0]   m1_axis_fromhost_tkeep              ,
    input               m1_axis_fromhost_tready             
        
      );

//**********************************************************
//Signal Declation
//**********************************************************
reg     [7:0]       counter_data                            ; 
reg    [31:0]       s1_axis_fromhost_temp                   ;
wire                dma_data_valid                          ;
wire                first_data                              ;
wire                second_data                             ;
//**********************************************************
//Main Code
//**********************************************************
assign s1_axis_fromhost_tready      = m1_axis_fromhost_tready;
assign m1_axis_fromhost_tlast       = s1_axis_fromhost_tlast;
assign dma_data_valid               = s1_axis_fromhost_tready && s1_axis_fromhost_tvalid;
assign first_data                   = (counter_data[0] == 1'b0) ? 1'b1 : 1'b0;
assign second_data                  = (counter_data[0] == 1'b1) ? 1'b1 : 1'b0;

//compute the number of dword trans just use for index
always @(posedge clk or negedge rst_n)begin
     if(!rst_n)begin
        counter_data    <= 8'b0;    
     end
     else begin
       
        if(dma_data_valid && (!s1_axis_fromhost_tlast) )
            counter_data <= counter_data + 8'd1; 

        else if(dma_data_valid && s1_axis_fromhost_tlast)
            counter_data <= 8'd0;

        else
            ;
    end
end
//save the first 4B data
always @(posedge clk or negedge rst_n)begin
    if(!rst_n)
        s1_axis_fromhost_temp <= 32'b0;
    else
    begin
    
        if(first_data && !s1_axis_fromhost_tlast  && dma_data_valid)
            s1_axis_fromhost_temp <= s1_axis_fromhost_tdata;
        else
            ;
    end
end

//convert the data from 32bit to 64bit
always @(*)begin

    if( second_data && s1_axis_fromhost_tready)
        //combine temp and second 4B data into 8B data
        m1_axis_fromhost_tdata = {s1_axis_fromhost_temp,s1_axis_fromhost_tdata};
        //the end data
    else if(first_data && s1_axis_fromhost_tlast == 1'b1 && dma_data_valid)
        m1_axis_fromhost_tdata = {32'b0,s1_axis_fromhost_tdata};

    else
        ;
end

//convert the tvalid signal to dma_if
always @(*)begin

    if( second_data && dma_data_valid)
        m1_axis_fromhost_tvalid = s1_axis_fromhost_tvalid;

    else if(first_data && s1_axis_fromhost_tlast == 1'b0 && dma_data_valid)
        m1_axis_fromhost_tvalid = 1'b0;

    else if(first_data && s1_axis_fromhost_tlast == 1'b1 && dma_data_valid)
        m1_axis_fromhost_tvalid = s1_axis_fromhost_tvalid;

    else
        m1_axis_fromhost_tvalid = 1'b0;
end

//convert the tkeep signal to dma_if
always @(*)begin
    
    //add byte trans
    if( second_data && dma_data_valid)
        m1_axis_fromhost_tkeep = 8'hff;

    else if(first_data && s1_axis_fromhost_tlast == 1'b0 && dma_data_valid)
        m1_axis_fromhost_tkeep = 8'h00;

    else if(first_data && s1_axis_fromhost_tlast == 1'b1 && dma_data_valid)
        m1_axis_fromhost_tkeep = 8'h0f;

    else
        m1_axis_fromhost_tkeep = 8'h00;
end

endmodule

