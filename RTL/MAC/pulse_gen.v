//**********************************************************
//
// Copyright(c) 2017 . Outwitcom Technology Co., LTD.
// All rights reserved.
//
// ProjectName :
// target      :
// FileName    : pluse_gen.sv
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
module pluse_gen(
        //clock and reset
        input                       clk                     ,
        input                       rst_n                   ,
        //
        input       [31:0]          pluse_addr              ,
        input                       wr                      ,
        input       [31:0]          waddr                   ,
        input       [31:0]          wdata                   ,
        output                      pluse  
        );

//**********************************************************
//Signal Declation
//**********************************************************
wire                                wr_hit                  ;
reg                                 wr_hit_1d               ;
reg     [31:0]                      pluse_cnt               ;
reg                                 pluse_vld               ;
//**********************************************************
//Main Code
//**********************************************************
assign  wr_hit = wr && (waddr == pluse_addr);

always @(posedge clk or negedge rst_n)
begin
    if (!rst_n)
        wr_hit_1d <= 1'b0;
    else
        wr_hit_1d <= wr_hit;
end

always @(posedge clk or negedge rst_n)
begin
    if (!rst_n)
        pluse_cnt <= 32'd0;
    else if (wr_hit_1d)
        pluse_cnt <= wdata;
    else if (pluse_vld && (pluse_cnt==32'd0))
        pluse_cnt <= 32'd0;
    else if (pluse_vld)
        pluse_cnt <= pluse_cnt - 32'd1;
    else
        pluse_cnt <= 32'd0;
end

always @(posedge clk or negedge rst_n)
begin
    if (!rst_n)
        pluse_vld <= 1'b0;
    else if (wr_hit_1d)
        pluse_vld <= 1'b1;
    else if (pluse_vld && (pluse_cnt==32'd0))
        pluse_vld <= 1'b0;
    else
        pluse_vld <= pluse_vld;
end

assign pluse = pluse_vld;

endmodule

