`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08/23/2017 03:19:02 PM
// Design Name: 
// Module Name: rx_mod
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

module rx_mod(
    input                           clk_80m                ,
    input                           bus_clk_resetn         ,
    //------------------ mac signal ----------------------
    input                           mpifClk                ,
    input                           testmode               ,
    input                           rxReq                  ,
    
    output   reg                    rxEndForTiming_p       ,
    output   reg                    rxEnd_p                ,
    output   reg                    phyRdy                 ,
    output   reg   [7:0]            rxData_d1              ,
    
    //---------------  rx data --------------------------------
    input                           phy_data_ind           ,
    input          [7:0]            bup_rxdata             ,
    input          [11:0]           rxv_length             ,
    input          [3:0]            rxv_datarate           ,
    input                           rxv_signal_ind         ,
    input                           EndForRx               ,
    input                           txv_immstop            ,
    
    //------------ reg data for debug --------------------------
    input          [1:0]            chBwInNonHT_reg    ,
    input          [0:0]            dozeNotAllowed_reg ,
    input          [7:0]            antennaSet_reg     ,
    input          [8:0]            partial_AID_reg    ,
    input          [5:0]            group_ID_reg       ,
    input          [31:0]           rssi1_4_reg        ,
    input          [7:0]            rcpi_reg           ,
    input          [31:0]           evm1_4_reg         ,        
 // ---------------------- debug ----------------------------
    output  reg    [3:0]            pr_state           ,
    input                           cp2_detected
    
    );
// ====================  parameter ====================    
parameter                           rxVector1_length = 5'd15  ;
parameter                           rxVector2_length = 5'd8   ;

parameter                           rx_idle_st       = 4'd0   ;
parameter                           rx_Vector1_st    = 4'd1   ;
parameter                           rx_Data_st       = 4'd2   ;
parameter                           rx_Vector2_st    = 4'd3   ;
parameter                           rx_End_st        = 4'd4   ;
// ==================== reg & wire ====================    
reg                                 phy_data_ind_d1  ; 
reg                                 rxv_signal_ind_d1; 
reg                                 rxv_signal_ind_d2;
reg                                 EndForRx_d1      ;
reg                                 EndForRx_d2      ;
    
reg        [7:0]                    RxVector1_data0  ;
reg        [7:0]                    RxVector1_data1  ;
reg        [7:0]                    RxVector1_data2  ;
reg        [7:0]                    RxVector1_data3  ;
reg        [7:0]                    RxVector1_data4  ;
reg        [7:0]                    RxVector1_data5  ;
reg        [7:0]                    RxVector1_data6  ;
reg        [7:0]                    RxVector1_data7  ; 
reg        [7:0]                    RxVector1_data8  ;
reg        [7:0]                    RxVector1_data9  ;
reg        [7:0]                    RxVector1_data10 ;
reg        [7:0]                    RxVector1_data11 ;
reg        [7:0]                    RxVector1_data12 ;
reg        [7:0]                    RxVector1_data13 ;
reg        [7:0]                    RxVector1_data14 ;

reg        [7:0]                    RxVector2_data0  ;
reg        [7:0]                    RxVector2_data1  ;
reg        [7:0]                    RxVector2_data2  ;
reg        [7:0]                    RxVector2_data3  ;
reg        [7:0]                    RxVector2_data4  ;
reg        [7:0]                    RxVector2_data5  ;
reg        [7:0]                    RxVector2_data6  ;
reg        [7:0]                    RxVector2_data7  ;  

reg        [7:0]                    rxData           ;
reg                                 wr_en            ;
wire                                fifo_full        ;
wire                                fifo_empty       ;
wire                                fifo_rd_en       ;
wire       [7:0]                    fifo_dout        ;
reg                                 fifo_rd_en_temp  ;
reg                                 fifo_rd_en_d1    ;

//------------------ txvector signal---------------------
//htLength  : Length of the HT PPDU in bytes
//shortGI   : Short Guard Interval,1?b0: LONG_GI (800 ns) used during the transmission,
//                                 1?b1: SHORT_GI (400 ns) used during the transmission 
//stbc      : Space Time Block Coding,Indicates the difference between the number of space time streams NSTS
//            and the number of spatial streams NSS as indicated by the MCS
//smoothing : Smoothing recommended,1?b1: Smoothing recommended as part of channel estimation,
//                                    1?b0: Smoothing not recommended as part of channel estimation
//mcs       : For HT format:This field represents the MCS.
//            For NON_HT format:The MCS field is reserved and ignored by the PHY
//preType   : Preamble Type,For formatMod = NON-HT and the transmission modulation is DSSS/CCK,
//            1?b:Short Preamble,1?b1:Long Preamble
//formatMod : This field indicates the format and the modulation of the PPDU, and is encoded as follows
//             3?b000: NON-HT, 3?b001: NON-HT-DUP-OFDM, 3?b010: HT-MF, 3?b011: HT-GF, 3?b100: VHT
//chBW      : Channel Bandwidth
//            If formatMod = HT-MF or HT-GF.2?b00: HT_CBW20 - 20 MHz and 40 MHz Upper and 40MHz Lower
//                                          2?b01: HT_CBW40 - 40 MHz
//            If formatMod = VHT            2?b00: VHT_CBW20 - 20 MHz
//                                          2?b01: VHT_CBW40 - 40 MHz
//                                          2?b10: VHT_CBW80 - 80 MHz
//                                          2?b11: VHT_CBW160 or VHT_CBW80p80 - 160 or 80+80 MHz
//            For other values of formatMod 2?b00: NON_HT_CBW20 for all other non-HT modulations
//                                          2?b01: NON_HT_CBW40 for non-HT duplicate
//nSTS      : Indicates the number of space-time streams.
//                                          nSTS = Nss when STBC = 0
//                                          nSTS = 2*Nss when STBC = 1
//lsigValid : L-SIG Valid,This bit is set by the modem when the formatMod = HT-MF and the L-SIG is valid
//sounding  : Indicates whether this PPDU is Sounding.1?b0: NOT_SOUNDING ,1?b1: SOUNDING
//numExtnSS[1:0]/chBWInNonHT[1:0] : For formatMod = NON-HT
//                                  Channel Bandwidth In Non HT used in case of Bandwidth Signalling.
//                                  Otherwise: Number of extension spatial streams received ( 0 ? 3).
//aggregation : MPDU Aggregate,1?b0:PPDU is not an A-MPDU,1?b1:PPDU is an A-MPDU,This field is not used by the PHY
//fecCoding   : FEC Coding,1?b0: Use BCC for this PPDU,1?b1: Use LDPC for this PPDU
//dynBW       : Dynamic Bandwidth,1?b0: Static bandwidth operation,1?b1: Dynamic bandwidth operation
//dozeNotAllowed : TXOP PS Not Allowed,1?b0: Doze mode during a TXOP allowed,1?b1: Doze mode during a TXOP not allowed
//antennaSet  : Indicates which antennas were used for reception. Each bit corresponds,to one antenna
//partialAID  : Received partial AID
//groupID     : Received Group ID
//rssi1_4[7:0]   :Received Signal Strength in dBm for RxChain 1
//rssi1_4[15:8]  :Received Signal Strength in dBm for RxChain 2
//rssi1_4[23:16] :Received Signal Strength in dBm for RxChain 3
//rssi1_4[31:24] :Received Signal Strength in dBm for RxChain 4
//rcpi           :Receive Channel Power Indicator.It is the RF power measured over the data portion of the received frame,
//                averaged over all RX chains. The valid values are 0 to 220.
//                The range of power which can be indicated by this field is from -110 dBm
//                (RCPI = 0) to 0 dBm (RCPI = 220). RCPI is a monotonically increasing function of the power in dBm.
//                The values 221 to 254 are reserved.The value 255 indicates no measurement is available
//evm1_4_reg[7:0]   : Error Vector Magnitude for space time stream 1,EVM is a measure of signal quality
//evm1_4_reg[15:8]  : Error Vector Magnitude for space time stream 2,EVM is a measure of signal quality
//evm1_4_reg[23:16] : Error Vector Magnitude for space time stream 3,EVM is a measure of signal quality
//evm1_4_reg[31:24] : Error Vector Magnitude for space time stream 4,EVM is a measure of signal quality

reg        [19:0]                   htLength         =20'h00000;
reg                                 shortGI          =1'b0;
reg        [1:0]                    stbc             =2'b00;
reg                                 smoothing        =1'b0;
reg        [6:0]                    mcs              =7'h00;
reg                                 preType          =1'b0;
reg        [2:0]                    formatMod        =3'h0;
reg        [1:0]                    chBW             =2'b00;
reg        [2:0]                    nSTS             =3'h1;
reg                                 lsigValid        =1'b0;
reg                                 sounding         =1'b0;
//reg        [1:0]                    numExtnSS        =2'b11;
reg                                 aggregation      =1'b0;
reg                                 fecCoding        =1'b0;
reg                                 dynBW            =1'b0;
//reg                                 dozeNotAllowed   =1'b1;
//reg        [7:0]                    antennaSet       =8'h87;
//reg        [8:0]                    partialAID       =9'h195;
//reg        [5:0]                    groupID          =6'h27;
//reg        [7:0]                    rssi1_4          =32'h01020304;


//reg        [7:0]                    rcpi             =8'h12;
//reg        [7:0]                    evm1_4_reg       =32'h12345678;
reg        [11:0]                   legLength        ;
reg        [3:0]                    nx_state  = 4'd0       ;
reg        [4:0]                    rxVector_cnt     ;
reg        [11:0]                   rx_Data_cnt      ;

wire       [4:0]                    rxcnt_val;

assign  rxcnt_val = (testmode) ? 5'd15 : 5'd14;
reg fifo_rst;
reg  cp2_detected_d1;
reg  cp2_detected_d2;
wire cp2_detected_rise;
 
//=============== cp2_detected_rise ==========================
always @(posedge clk_80m) begin
    if(!bus_clk_resetn ) begin
        cp2_detected_d1 <= 1'b0;
        cp2_detected_d2 <= 1'b0;
    end else begin
        cp2_detected_d1 <=cp2_detected;
        cp2_detected_d2 <=cp2_detected_d1;
    end 
end  
 
assign  cp2_detected_rise = cp2_detected && (!cp2_detected_d2);
  
//=============== write data to fifo ========================== 
always @(posedge clk_80m) begin
    phy_data_ind_d1   <= phy_data_ind;
end 
always@(posedge mpifClk) begin 
     if(!bus_clk_resetn ) begin
         rxv_signal_ind_d1 <= 1'b0;
         rxv_signal_ind_d2 <= 1'b0;
     end else begin
         rxv_signal_ind_d1 <= rxv_signal_ind;
         rxv_signal_ind_d2 <= rxv_signal_ind_d1;
     end 
end 


always @(posedge clk_80m) begin
    if(txv_immstop == 1'b1) begin
        EndForRx_d1       <= EndForRx;
        EndForRx_d2       <= EndForRx_d1;
    end
    else begin
        EndForRx_d1       <= 'd0; 
        EndForRx_d2       <= 'd0;
    end
end 
 
always @(posedge clk_80m) begin
    if((phy_data_ind_d1 == 1'b1 && phy_data_ind == 1'b0) || (phy_data_ind_d1 == 1'b0 && phy_data_ind == 1'b1))
        wr_en <= 1'b1;
    else
        wr_en <= 1'b0;
end 
 
// =========================================================== //
// ----------------------fifo data---------------------------- //  
// =========================================================== //

 rx_mac_data_fifo u_mac_rxdata_fifo(
    .rst          ( !bus_clk_resetn || fifo_rst ),
 
    .wr_clk       ( clk_80m         ),
    .full         ( fifo_full       ),
    .din          ( bup_rxdata      ),
    .wr_en        ( wr_en           ),
    
    .rd_clk       ( mpifClk         ),
    .empty        ( fifo_empty      ),
    .dout         ( fifo_dout       ),
    .rd_en        ( fifo_rd_en      )
);  
 
//============ generate TxVector ============== 
always @(posedge clk_80m) begin
    if(rxv_signal_ind == 1'b1)begin
        legLength        <= rxv_length;
    
        RxVector1_data0  <= rxv_length[7:0];
        RxVector1_data1  <= {rxv_datarate,rxv_length[11:8]};
        RxVector1_data2  <= htLength[7:0];
        RxVector1_data3  <= htLength[15:8];
        RxVector1_data4  <= {smoothing,stbc[1:0],shortGI,htLength[19:16]};
        RxVector1_data5  <= {preType,mcs[6:0]};
        RxVector1_data6  <= {nSTS[2:0],chBW[1:0],formatMod[2:0]};
        RxVector1_data7  <= {dozeNotAllowed_reg,dynBW,fecCoding,aggregation,chBwInNonHT_reg,sounding,lsigValid};
        RxVector1_data8  <= antennaSet_reg;
        RxVector1_data9  <= partial_AID_reg[7:0];
        RxVector1_data10 <= {group_ID_reg[5:0],partial_AID_reg[8]};
        RxVector1_data11 <= rssi1_4_reg[7:0];
        RxVector1_data12 <= rssi1_4_reg[15:8];
        RxVector1_data13 <= rssi1_4_reg[23:16];
        RxVector1_data14 <= rssi1_4_reg[31:24];   
    end
    else 
        ;
end    
    
always @(posedge clk_80m) begin
    if(rxEndForTiming_p == 1'b1)begin
        RxVector2_data0  <= rcpi_reg;
        RxVector2_data1  <= evm1_4_reg[7:0];
        RxVector2_data2  <= evm1_4_reg[15:8];
        RxVector2_data3  <= evm1_4_reg[23:16];
        RxVector2_data4  <= evm1_4_reg[31:24];
        RxVector2_data5  <= 8'h01;
        RxVector2_data6  <= 8'h02;
        RxVector2_data7  <= 8'h03;
    end
    else 
        ;
end     
  
//====== control machine =============  


always@(posedge mpifClk) begin
    if(rx_Data_cnt == legLength - 1'b1)
        rxEndForTiming_p <= 1'b1;
    else
        rxEndForTiming_p <= 1'b0;
end

always@(posedge mpifClk) begin
    if(rxReq == 1'b0 || cp2_detected_rise)
        pr_state <= rx_idle_st;
    else
        pr_state <= nx_state;
end
        
always@(posedge mpifClk) begin
    case(pr_state)
    rx_idle_st    : begin
                        if(rxv_signal_ind_d2 == 1'b1)
                            nx_state <= rx_Vector1_st;
                        else
                            ;
                    end
    rx_Vector1_st : begin
                        if(rxVector_cnt == rxVector1_length)
                            nx_state <= rx_Data_st;
                        else
                            ;
                    end
   rx_Data_st     : begin
                        if(rx_Data_cnt == legLength)
                            nx_state <= rx_Vector2_st;
                        else
                            ;
                    end
   rx_Vector2_st : begin
                         if(rxVector_cnt == rxVector2_length)
                             nx_state <= rx_End_st;
                         else
                            ;
                    end
    rx_End_st     : nx_state <= rx_idle_st;
    
    endcase
end
   
always@(posedge mpifClk) begin
    if((rxv_signal_ind == 1'b1) || (rxEndForTiming_p == 1'b1))
        rxVector_cnt <= 5'd0;
    else if(pr_state == rx_Vector1_st)
        rxVector_cnt <= rxVector_cnt + 1'b1;
    else if(pr_state == rx_Vector2_st)
        rxVector_cnt <= rxVector_cnt + 1'b1;
    else 
        ;
end    
    
always@(posedge mpifClk) begin
    if(pr_state == rx_Vector1_st)begin
        case(rxVector_cnt)
            5'd0   :    rxData <= RxVector1_data0;
            5'd1   :    rxData <= RxVector1_data1;
            5'd2   :    rxData <= RxVector1_data2;
            5'd3   :    rxData <= RxVector1_data3;
            5'd4   :    rxData <= RxVector1_data4;
            5'd5   :    rxData <= RxVector1_data5;
            5'd6   :    rxData <= RxVector1_data6;
            5'd7   :    rxData <= RxVector1_data7;
            5'd8   :    rxData <= RxVector1_data8;
            5'd9   :    rxData <= RxVector1_data9;
            5'd10  :    rxData <= RxVector1_data10;
            5'd11  :    rxData <= RxVector1_data11;
            5'd12  :    rxData <= RxVector1_data12;
            5'd13  :    rxData <= RxVector1_data13;
            5'd14  :    rxData <= RxVector1_data14;
            default :   rxData <= 8'h55;
        endcase
    end
    else if(pr_state == rx_Data_st)
        if(fifo_rd_en_d1 == 1'b1)begin
            rxData <= fifo_dout;
        end
        else begin
            rxData <= 8'h55;
        end
    else if(pr_state == rx_Vector2_st) begin
        case(rxVector_cnt)
            5'd0   :    rxData <= RxVector2_data0;
            5'd1   :    rxData <= RxVector2_data1;
            5'd2   :    rxData <= RxVector2_data2;
            5'd3   :    rxData <= RxVector2_data3;
            5'd4   :    rxData <= RxVector2_data4;
            5'd5   :    rxData <= RxVector2_data5;
            5'd6   :    rxData <= RxVector2_data6;
            5'd7   :    rxData <= RxVector2_data7;
            default :   rxData <= 8'h55;
        endcase
    end
    else begin
        rxData <= 8'h55;
    end    
end

always@(posedge mpifClk) begin
    fifo_rd_en_d1 <= fifo_rd_en;
    rxData_d1     <= rxData;
end

always@(posedge mpifClk) begin
    if(bus_clk_resetn == 1'b0)
        phyRdy <= 1'b0;
    else
        if(pr_state == rx_Vector1_st)
            if(rxVector_cnt > rxcnt_val)
                phyRdy <= 1'b0;
            else
                phyRdy <= 1'b1;
        else if(pr_state == rx_Data_st)
            if(fifo_rd_en_d1 == 1'b1)
                phyRdy <= 1'b1;
            else
                phyRdy <= 1'b0;
        else if(pr_state == rx_Vector2_st)
            if(rxVector_cnt > 5'd7)
                phyRdy <= 1'b0;
            else
                phyRdy <= 1'b1;
end

always@(posedge mpifClk) begin
    if(pr_state == rx_Data_st)
        if(fifo_rd_en == 1'b1)
            rx_Data_cnt <= rx_Data_cnt + 1'b1;
         else
            ;
    else
        rx_Data_cnt <= 12'd0;
end

always@(posedge mpifClk) begin
    if(pr_state == rx_Data_st && fifo_empty == 1'b0)
        fifo_rd_en_temp <= 1'b1;
    else
        fifo_rd_en_temp <= 1'b0;
end

assign fifo_rd_en = fifo_rd_en_temp && !fifo_empty ;
    
always@(posedge mpifClk) begin
    if(pr_state == rx_End_st)
        rxEnd_p <= 1'b1;
    else
        rxEnd_p <= 1'b0;
end    
    

always@(posedge mpifClk) begin
    if(!bus_clk_resetn) begin
        fifo_rst    <= 1'b0;
    end else if(pr_state == rx_Vector1_st && 
           ((rxVector_cnt >=5'd0) && (rxVector_cnt < 5'd3)) ) begin
        fifo_rst    <= 1'b1;
    end else begin
        fifo_rst    <= 1'b0;
    end
end   
    
    
endmodule
