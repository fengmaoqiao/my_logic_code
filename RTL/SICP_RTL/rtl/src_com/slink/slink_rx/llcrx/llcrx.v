// *********************************************************************************/
// Project Name : 
// Author       : sunfeng
// Email        : fyyysun@qq.com
// Creat Time   : 2018/08/09 16:32:44
// File Name    : llcrx.v
// Module Name  : 
// Abstract     : 
//
module LLCRX 
(
    input                               clk_125m                ,   
    input                               rst_125m                ,   

    input      [17:0]                   destin_addr_cfg         ,   
    input      [17:0]                   source_addr_cfg         ,   
    input      [3:0]                    destin_addr_chk         , //enable DA check
    input      [3:0]                    source_addr_chk         , //enable SA check

    input      [7:0]                    macrx_llcrx_data        ,   
    input                               macrx_llcrx_dval        ,   
    input                               macrx_llcrx_sop         ,   
    input                               macrx_llcrx_eop         ,   

    output reg [7:0]                    llcrx_rxfifo_data       ,
    output reg                          llcrx_rxfifo_dval       ,
    output reg                          llcrx_rxfifo_sop        ,
    output reg                          llcrx_rxfifo_eop        ,

    output reg [15:0]                   rxchan_run_cycle        ,
    output                              slink_addr_error         

);

reg  [10:0]                     pkt_cnt                             ;   
reg                             pkt_sop_flag                        ;   
reg  [3:0]                      pkt_da_error                        ;   
reg  [3:0]                      pkt_sa_error                        ;   

reg  [47:0]                     macrx_llcrx_data_dly                ;   
reg  [5:0]                      macrx_llcrx_dval_dly                ;   
reg  [5:0]                      macrx_llcrx_sop_dly                 ;   
reg  [5:0]                      macrx_llcrx_eop_dly                 ;   

reg  [23:0]                     destin_addr_rx                      ;   
reg  [23:0]                     source_addr_rx                      ;   
reg  [2:0]                      send_head_cnt                       ;   
reg                             send_head_flag                      ;   

wire                            pkt_da_error_tmp                    ;   
wire                            pkt_sa_error_tmp                    ;   


always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        macrx_llcrx_data_dly <= 48'h00;
    end
    else if(macrx_llcrx_dval == 1'b1) begin
        macrx_llcrx_data_dly <= {macrx_llcrx_data_dly[39:0],macrx_llcrx_data};
    end
end

always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        macrx_llcrx_dval_dly <= 6'h00;
    end
    else begin
        macrx_llcrx_dval_dly <= {macrx_llcrx_dval_dly[4:0],macrx_llcrx_dval};
    end
end

always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        macrx_llcrx_sop_dly <= 6'h00;
    end
    else if(macrx_llcrx_dval == 1'b1) begin
        macrx_llcrx_sop_dly <= {macrx_llcrx_sop_dly[4:0],macrx_llcrx_sop};
    end
end

always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        macrx_llcrx_eop_dly <= 6'h00;
    end
    else begin
        macrx_llcrx_eop_dly <= {macrx_llcrx_eop_dly[4:0],macrx_llcrx_eop};
    end
end

always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        pkt_sop_flag <= 1'b0;
    end
    else if(macrx_llcrx_dval == 1'b1 && macrx_llcrx_sop == 1'b1) begin
        pkt_sop_flag <= 1'b1;
    end
    else if(macrx_llcrx_dval == 1'b1 && macrx_llcrx_eop == 1'b1) begin
        pkt_sop_flag <= 1'b0;
    end
end

always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        pkt_cnt <= 11'h000;
    end
    else if(macrx_llcrx_dval == 1'b1 && pkt_sop_flag == 1'b1) begin
        pkt_cnt <= pkt_cnt + 1'b1;
    end
    else if(pkt_sop_flag == 1'b1) begin
        pkt_cnt <= pkt_cnt;
    end
    else begin
        pkt_cnt <= 11'h000;
    end
end

//rx pkt destination address 
always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        destin_addr_rx <= 24'h000000;
    end
    else begin
        if(macrx_llcrx_dval == 1'b1) begin
            if(macrx_llcrx_sop == 1'b1) begin // sop : 3th bytes
                destin_addr_rx[23:16] <= macrx_llcrx_data;       //3th bytes
            end
            else begin
                case(pkt_cnt)
                    11'h0 : destin_addr_rx[15:8]  <= macrx_llcrx_data;       //2nd bytes
                    11'h1 : destin_addr_rx[7:0]   <= macrx_llcrx_data;       //1st bytes
                    default : ;
                endcase
            end
        end
    end
end

//pkt source address error
always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        source_addr_rx <= 24'h000000;
    end
    else begin
        if(macrx_llcrx_dval == 1'b1) begin
            case(pkt_cnt)
                11'h2 : source_addr_rx[23:16] <= macrx_llcrx_data;       //3th bytes
                11'h3 : source_addr_rx[15:8]  <= macrx_llcrx_data;       //2nd bytes
                11'h4 : source_addr_rx[7:0]   <= macrx_llcrx_data;       //1st bytes
                default : ;
            endcase
        end
    end
end

//destin_addr_chk[0] for port number check enable
//destin_addr_chk[1] for slot number check enable
//destin_addr_chk[2] for box  number check enable
//destin_addr_chk[3] for station number check enable
always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        pkt_da_error <= 4'b0;
    end
    else if(pkt_cnt == 11'h5) begin

        if(destin_addr_chk[0] == 1'b1) begin
            if(destin_addr_rx[1:0] == destin_addr_cfg[1:0]) begin
                pkt_da_error[0] <= 1'b0;
            end
            else begin
                pkt_da_error[0] <= 1'b1;
            end
        end
        else begin
            pkt_da_error[0] <= 1'b0;
        end

        if(destin_addr_chk[1] == 1'b1) begin
            if(destin_addr_rx[6:2] == destin_addr_cfg[6:2]) begin
                pkt_da_error[1] <= 1'b0;
            end
            else begin
                pkt_da_error[1] <= 1'b1;
            end
        end
        else begin
            pkt_da_error[1] <= 1'b0;
        end

        if(destin_addr_chk[2] == 1'b1) begin
            if(destin_addr_rx[9:7] == destin_addr_cfg[9:7]) begin
                pkt_da_error[2] <= 1'b0;
            end
            else begin
                pkt_da_error[2] <= 1'b1;
            end
        end
        else begin
            pkt_da_error[2] <= 1'b0;
        end

        if(destin_addr_chk[3] == 1'b1) begin
            if(destin_addr_rx[17:10] == destin_addr_cfg[17:10]) begin
                pkt_da_error[3] <= 1'b0;
            end
            else begin
                pkt_da_error[3] <= 1'b1;
            end
        end
        else begin
            pkt_da_error[3] <= 1'b0;
        end
    end
end

always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        pkt_sa_error <= 4'b0;
    end
    else if(pkt_cnt == 11'h5) begin

        if(destin_addr_chk[0] == 1'b1) begin
            if(source_addr_rx[1:0] == source_addr_cfg[1:0]) begin
                pkt_sa_error[0] <= 1'b0;
            end
            else begin
                pkt_sa_error[0] <= 1'b1;
            end
        end
        else begin
            pkt_sa_error[0] <= 1'b0;
        end

        if(destin_addr_chk[1] == 1'b1) begin
            if(source_addr_rx[6:2] == source_addr_cfg[6:2]) begin
                pkt_sa_error[1] <= 1'b0;
            end
            else begin
                pkt_sa_error[1] <= 1'b1;
            end
        end
        else begin
            pkt_sa_error[1] <= 1'b0;
        end

        if(destin_addr_chk[2] == 1'b1) begin
            if(source_addr_rx[9:7] == source_addr_cfg[9:7]) begin
                pkt_sa_error[2] <= 1'b0;
            end
            else begin
                pkt_sa_error[2] <= 1'b1;
            end
        end
        else begin
            pkt_sa_error[2] <= 1'b0;
        end

        if(destin_addr_chk[3] == 1'b1) begin
            if(source_addr_rx[17:10] == source_addr_cfg[17:10]) begin
                pkt_sa_error[3] <= 1'b0;
            end
            else begin
                pkt_sa_error[3] <= 1'b1;
            end
        end
        else begin
            pkt_sa_error[3] <= 1'b0;
        end
    end
end

assign pkt_da_error_tmp = |pkt_da_error;
assign pkt_sa_error_tmp = |pkt_sa_error;

assign slink_addr_error = (pkt_da_error_tmp | pkt_sa_error_tmp);

always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        rxchan_run_cycle <= 16'h0000;
    end
    else begin
        if(slink_addr_error == 1'b0) begin
            if(pkt_cnt == 11'h6 && macrx_llcrx_dval == 1'b1) begin
                rxchan_run_cycle <= {rxchan_run_cycle[15:8],macrx_llcrx_data};
            end
            else if(pkt_cnt == 11'h5 && macrx_llcrx_dval == 1'b1) begin
                rxchan_run_cycle <= {macrx_llcrx_data,rxchan_run_cycle[7:0]};
            end
        end
    end
end

//send pkt head
always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        send_head_flag <= 1'b0;
    end
    else if(send_head_cnt == 3'h5) begin
        send_head_flag <= 1'b0;
    end
    else if(pkt_cnt == 11'h5 && macrx_llcrx_dval_dly[1]) begin
        send_head_flag <= 1'b1;
    end
end

always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        send_head_cnt <= 3'h0;
    end
    else if(send_head_cnt == 3'h5) begin
        send_head_cnt <= 3'h0;
    end
    else if(send_head_flag == 1'b1) begin
        send_head_cnt <= send_head_cnt + 1'b1;
    end
end

always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        llcrx_rxfifo_data <= 8'h00;
    end
    else if(send_head_flag == 1'b1) begin
        case(send_head_cnt)
            3'h0 : llcrx_rxfifo_data <= macrx_llcrx_data_dly[47:40];
            3'h1 : llcrx_rxfifo_data <= macrx_llcrx_data_dly[39:32];
            3'h2 : llcrx_rxfifo_data <= macrx_llcrx_data_dly[31:24];
            3'h3 : llcrx_rxfifo_data <= macrx_llcrx_data_dly[23:16];
            3'h4 : llcrx_rxfifo_data <= macrx_llcrx_data_dly[15:8];
            3'h5 : llcrx_rxfifo_data <= macrx_llcrx_data_dly[7:0];
            default : ;
        endcase
    end
    else begin
        llcrx_rxfifo_data <= macrx_llcrx_data;
    end
end

always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        llcrx_rxfifo_dval <= 1'b0;
    end
    else begin
        if(slink_addr_error == 1'b0) begin
            if(pkt_cnt == 11'h5) begin
                if(send_head_flag == 1'b1 || macrx_llcrx_dval == 1'b1) begin
                    llcrx_rxfifo_dval <= 1'b1;
                end
                else begin
                    llcrx_rxfifo_dval <= 1'b0;
                end
            end
            else if(pkt_cnt >= 11'h6 ) begin
                if(macrx_llcrx_dval == 1'b1) begin
                    llcrx_rxfifo_dval <= 1'b1;
                end
                else begin
                    llcrx_rxfifo_dval <= 1'b0;
                end
            end
        end
        else begin
            llcrx_rxfifo_dval <= 1'b0;
        end
    end
end

always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        llcrx_rxfifo_sop <= 1'b0;
    end
    //else if(macrx_llcrx_dval_dly[0] == 1'b1 && pkt_cnt == 11'hc && slink_addr_error == 1'b0) begin
    else if(send_head_flag == 1'b1 && send_head_cnt == 3'h0 && slink_addr_error == 1'b0) begin
        llcrx_rxfifo_sop <= 1'b1;
    end
    else begin
        llcrx_rxfifo_sop <= 1'b0;
    end
end

always @(posedge clk_125m or negedge rst_125m) begin
    if(rst_125m == 1'b0) begin
        llcrx_rxfifo_eop <= 1'b0;
    end
    else if(slink_addr_error == 1'b0 && pkt_sop_flag == 1'b1) begin
        llcrx_rxfifo_eop <= macrx_llcrx_eop;
    end
    else begin
        llcrx_rxfifo_eop <= 1'b0;
    end
end

endmodule
