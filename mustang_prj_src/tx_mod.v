`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08/23/2017 02:40:18 PM
// Design Name: 
// Module Name: tx_mod
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////
`default_nettype wire

module tx_mod(
    input                           clk_80m                ,
    input                           bus_clk_resetn         ,
    //------------------ mac signal ----------------------
    input                           mpifClk                ,
    
    input                           txReq                  ,
    input          [7:0]            txData                 ,
    input                           macDataValid           ,
    
    output   reg                    txEnd_p                ,
    input                           mpIfTxFifoEmtpy        ,
    output   reg                    phyRdy                 ,
    ------------------------------------
    
    input                           txv_immstop            ,
    
    input                           phy_txstartend_conf    ,
    input                           phy_data_conf          ,
    
    output   reg                    phy_data_req           ,
    output   reg   [7:0]            bup_txdata           ,
    output   reg                    phy_txstartend_req     , 
    output   reg                    phy_ccarst_req         ,
    output   reg                    rxv_macaddr_match      ,       
    output   reg   [3:0]            txv_datarate_reg       ,    
    output   reg   [11:0]           txv_length_reg         ,
    output   reg   [6:0]            txpwr_level_reg        , 
    output   reg   [15:0]           txv_service_reg        
    );
    
// ==================== reg & wire ====================
reg        [3:0]                    txv_datarate            ;    
reg        [11:0]                   txv_length              ;
reg        [6:0]                    txpwr_level             ; 
reg        [15:0]                   txv_service             ;

reg        [15:0]                   counter_tx = 16'd5100      ;

reg           phy_txstartend_conf_d1  ;
reg                                 phy_data_conf_d1        ;
reg        [11:0]                   counter = 12'd0         ;
 
reg                                 fifo_wr_en              ;
reg                                 fifo_rd_en              ; 
wire                                fifo_full               ;
wire                                fifo_empty              ; 
reg                                 fifo_empty_d1           ;
wire       [7:0]                    fifo_dout               ;    

reg        [11:0]                   rddata_counter = 12'd0  ;     
reg        [11:0]                   counter_data = 12'd0    ;

reg                                 empty_state    = 1'b0   ;

wire                                phy_data_req_temp       ;

// ---- receive signal from mac --------------------
reg        [8:0]                    TxVector_cnt    ;
reg        [11:0]                   txData_cnt      ;  
reg        [7:0]                    TxVector_data0  ;
reg        [7:0]                    TxVector_data1  ;
reg        [7:0]                    TxVector_data2  ;
reg        [7:0]                    TxVector_data3  ;
reg        [7:0]                    TxVector_data4  ;
reg        [7:0]                    TxVector_data5  ;
reg        [7:0]                    TxVector_data6  ;
reg        [7:0]                    TxVector_data7  ; 
reg        [7:0]                    TxVector_data8  ;
reg        [7:0]                    TxVector_data9  ;
reg        [7:0]                    TxVector_data10 ;
reg        [7:0]                    TxVector_data11 ;
reg        [7:0]                    TxVector_data12 ;
reg        [7:0]                    TxVector_data13 ;
reg        [7:0]                    TxVector_data14 ;
reg        [7:0]                    TxVector_data15 ;

wire       [7:0]                    txPwrLevel      ;
wire                                sounding        ;
wire                                fecCoding       ;
wire                                reserved1       ;
wire                                smoothing       ;
wire                                continuousTx    ;
wire                                reserved2       ;
wire       [1:0]                    chBW            ;
wire       [7:0]                    antennaSet      ;
wire       [7:0]                    smmIndex        ;
wire       [6:0]                    mcs             ;
wire                                preType         ;
wire       [2:0]                    formatMod       ;
wire       [1:0]                    numExtnSS       ;
wire       [2:0]                    nSTS            ;
wire       [11:0]                   legLength       ;
wire       [3:0]                    legRate         ;
wire       [15:0]                   service         ;
wire       [19:0]                   htLength        ;
wire                                aggregation     ;
wire                                dozeNotAllowed  ;
wire                                shortGI         ;
wire                                diasmbiguityBit ; 
wire       [2:0]                    nTx             ;
wire       [1:0]                    stbc            ;
wire                                BeamFormed      ;
wire       [8:0]                    partialAID      ;
wire       [5:0]                    groupID         ;

reg                                 txReq_d1        ;
reg                                 txReq_d2        ;
reg                                 fifo_reset      ;
reg                                 phy_txstartend_conf_fall;
// ============================================================ //
// --------------------- TxVector signal ---------------------- // 
// ============================================================ //
assign txPwrLevel           = TxVector_data0;
assign sounding             = TxVector_data1[0];
assign fecCoding            = TxVector_data1[1];
assign reserved1            = TxVector_data1[2];
assign smoothing            = TxVector_data1[3];
assign continuousTx         = TxVector_data1[4];
assign reserved2            = TxVector_data1[5];
assign chBW                 = TxVector_data1[7:6];
assign antennaSet           = TxVector_data2;
assign smmIndex             = TxVector_data3;
assign mcs                  = TxVector_data4[6:0];
assign preType              = TxVector_data4[7];
assign formatMod            = TxVector_data5[2:0];
assign numExtnSS            = TxVector_data5[4:3];
assign nSTS                 = TxVector_data5[7:5];
assign legLength[7:0]       = TxVector_data6;
assign legLength[11:8]      = TxVector_data7[3:0];
assign legRate              = TxVector_data7[7:4];
assign service[7:0]         = TxVector_data8;
assign service[15:8]        = TxVector_data9;
assign htLength[7:0]        = TxVector_data10;
assign htLength[15:8]       = TxVector_data11;
assign htLength[19:16]      = TxVector_data12[3:0];
assign aggregation          = TxVector_data12[4];
assign dozeNotAllowed       = TxVector_data12[5];  
assign shortGI              = TxVector_data12[6];
assign diasmbiguityBit      = TxVector_data12[7];  
assign nTx                  = TxVector_data13[2:0];
assign stbc                 = TxVector_data13[5:4];
assign BeamFormed           = TxVector_data13[6];
assign partialAID[7:0]      = TxVector_data14;
assign partialAID[8]        = TxVector_data15[0];
assign groupID[5:0]         = TxVector_data15[6:1];

//-- receive the TxVector data

always @(posedge mpifClk) begin
    if(bus_clk_resetn == 1'b0)
        TxVector_cnt <= 9'd0;
    else
        if(txReq_d2 == 1'b1 && txReq == 1'b0)
            TxVector_cnt <= 9'd0;
        else if(txReq == 1'b1 && TxVector_cnt < 9'd30)
            TxVector_cnt <= TxVector_cnt + 1'b1;
        else
            ;
end  
  
always @(posedge mpifClk) begin
    if(txReq)
        case(TxVector_cnt)
            9'd0  :  TxVector_data0  <= txData ;
            9'd1  :  TxVector_data1  <= txData ;
            9'd2  :  TxVector_data2  <= txData ;
            9'd3  :  TxVector_data3  <= txData ;
            9'd4  :  TxVector_data4  <= txData ;
            9'd5  :  TxVector_data5  <= txData ;
            9'd6  :  TxVector_data6  <= txData ;
            9'd7  :  TxVector_data7  <= txData ;
            9'd8  :  TxVector_data8  <= txData ;
            9'd9  :  TxVector_data9  <= txData ;
            9'd10 :  TxVector_data10 <= txData ;
            9'd11 :  TxVector_data11 <= txData ;
            9'd12 :  TxVector_data12 <= txData ;
            9'd13 :  TxVector_data13 <= txData ;
            9'd14 :  TxVector_data14 <= txData ;
            9'd15 :  TxVector_data15 <= txData ;
            default : ;
        endcase
      else
        ;
end 
  
//-- receive the txData data 
always @(posedge mpifClk) begin
    if(txReq == 1'b1 && macDataValid == 1'b1)
        txData_cnt <= txData_cnt + 1'b1;
    else if(fifo_reset == 1'b1)
        txData_cnt <= 12'd0;
    else
        ;
end   
 
always @(posedge mpifClk) begin
    if(TxVector_cnt > 9'd16 && txData_cnt < legLength - 4)
        phyRdy <= ~fifo_full;
    else 
        phyRdy <= 1'b0;
end  
     


always @(posedge clk_80m) begin
    if(phy_txstartend_conf_d1 == 1'b1 && phy_txstartend_conf == 1'b0)
        phy_txstartend_conf_fall <= 1'b1;
    else if(txReq == 1'b0)
        phy_txstartend_conf_fall <= 1'b0;
    else
        ;
end 

always @(posedge mpifClk) begin
    if(phy_txstartend_conf_fall == 1'b1)
        txEnd_p <= 1'b1;
    else 
        txEnd_p <= 1'b0;
end 

// =========================================================== //
// ----------------------fifo data---------------------------- //  
// =========================================================== //

 tx_mac_data_fifo u_mac_txdata_fifo(
    .rst          ( fifo_reset      ),
 
    .wr_clk       ( mpifClk         ),
    .full         ( fifo_full       ),
    .din          ( txData          ),
    .wr_en        ( macDataValid    ),
    
    .rd_clk       ( clk_80m         ),
    .empty        ( fifo_empty      ),
    .dout         ( fifo_dout       ),
    .rd_en        ( fifo_rd_en      )
);  

always @(posedge mpifClk) begin
    if(TxVector_cnt == 9'd3 || TxVector_cnt == 9'd4)
        fifo_reset <= 1'b1;
    else 
        fifo_reset <= 1'b0;
end 

// =============== read data from fifo to phy=====================
always @(posedge clk_80m) begin
   if(fifo_rd_en == 1'b1 && rddata_counter < txv_length_reg)
       rddata_counter <= rddata_counter + 1'b1;
   else if (phy_txstartend_conf == 1'd0 && phy_txstartend_conf_d1 == 1'b1)
       rddata_counter <= 'd0;
   else
       rddata_counter <= rddata_counter;
end

assign phy_data_req_temp = (counter == txv_length_reg) ? 1'b0 : phy_txstartend_conf_d1^phy_data_conf_d1 ;     


always @(posedge clk_80m) begin
    if(fifo_empty == 1'b0 && phy_txstartend_conf == 1'd1)
        if(phy_txstartend_conf_d1==1'b0 && phy_txstartend_conf==1'b1)begin
            fifo_rd_en        <= 1'b1;
        end
        else if((phy_data_conf_d1!=phy_data_conf) && (rddata_counter < txv_length_reg))begin
            fifo_rd_en <= 1'b1;
        end
        else begin
            fifo_rd_en <= 1'b0;
        end
     else begin
        fifo_rd_en <= 1'b0;
    end
end

  
always@(posedge clk_80m) begin
    if(phy_txstartend_conf == 1'd1)begin
        bup_txdata   <= fifo_dout;  
        phy_data_req   <= phy_data_req_temp ;
    end
    else begin
            bup_txdata   <= 8'h55; 
            phy_data_req   <= 1'b0; 
    end 
end
  
// ======================================================================== //
// -----------------------   tx  signal  to phy    ------------------------ //    
// ======================================================================== //

always@(posedge clk_80m) begin
    phy_txstartend_conf_d1 <= phy_txstartend_conf;
    phy_data_conf_d1       <= phy_data_conf;
    fifo_empty_d1          <= fifo_empty;
end

always@(posedge mpifClk) begin
    txReq_d1               <= txReq;
    txReq_d2               <= txReq_d1;
end

reg          phy_start_en = 1'b0; 

always @(posedge mpifClk) begin
    if(txData_cnt == legLength - 4'd2)
        phy_start_en <= 1'b1;
    else if(phy_txstartend_req == 1'b1)
        phy_start_en <= 1'b0;
    else
        ;
end 

always@(posedge clk_80m) begin
    if(fifo_reset == 1'b1)begin
        phy_txstartend_req      <= 'd0;                                                
        phy_ccarst_req          <= 'd0;
        rxv_macaddr_match       <= 'd0;
    end
    else 
        if(rddata_counter == txv_length_reg)
            phy_txstartend_req      <= 1'd0;
        //else if(txReq == 1'b1 && txData_cnt == legLength - 4'd1)begin  
        else if (txReq == 1'b1 && phy_start_en == 1'b1)begin  
            phy_txstartend_req      <= 'd1; 
            phy_ccarst_req          <= 'd0;
            rxv_macaddr_match       <= 'd1;        
        end
        else ;
end


 
always@(posedge mpifClk) begin
    txv_datarate_reg   <= legRate;     
    txv_length_reg     <= legLength; 
    txpwr_level_reg    <= txPwrLevel;
    txv_service_reg    <= service;
end    
    
    
    
endmodule
