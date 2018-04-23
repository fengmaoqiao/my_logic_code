//**********************************************************
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
module ...
(
  /* clock and reset */
  input                   clk                             ,
  input                   rst_n                           ,                               
  /* user port */
  input     wire          mpIFCLK                         ,
  input     wire          mpIFClkHardRst_n                ,

  /* AHB InterFace */
  input     wire          hready_in                       ,
  input     wire          hsel                            ,
  input     wire  [31:0]  haddr                           ,
  input     wire  [1:0]   htrans                          ,
  input     wire          hwrite                          ,
  output    wire  [31:0]  hrdata                          ,
  input     wire  [31:0]  hwdata                          ,
  output    wire          hready                          ,
  output    wire  [1:0]   hresp                           ,

  input     wire          phyRdy                          ,
  input     wire          mackeepRFOn                     ,//no use
  output    wire          TxkeepRFOn                      ,//no use

  input     wire          txEnd_p                         ,
  output    reg           txReq                           ,
  output    reg           macDataValid_o                  ,

  output    reg           test_tx_wr_en                   ,
  output    reg [4:0]     test_tx_wr_addr                 ,
  output    reg [31:0]    test_tx_wr_data                 ,
  output    reg           test_tx_rd_en                   ,
  output    reg [6:0]     test_tx_rd_addr                 ,

  output    reg           rxReq                           ,
  input     wire          rxEndForTiming_p                ,//no use
  input     wire          rxErr_p                         ,//no use
  input     wire          rxEnd_p                         ,
  input     wire  [11:0]  rxv_length                      ,

  output    reg           test_rx_wr_en                   ,
  output    reg [6:0]     test_rx_wr_addr                 ,
  output    reg           test_rx_rd_en                   ,
  output    reg [4:0]     test_rx_rd_addr                 ,
  input     wire  [31:0]  test_rx_rd_data                 ,

  /* instruct and status lines */
  output    wire          testmode                        ,
  output    wire          txrxmode                        ,//no use

  output    reg [1:0]     txstateCs                       ,
  input     wire          agc_fall              

);

  /**********************************************************
  * Signal Declation
  **********************************************************/
  reg       [  31:0]                   ...               ;
  reg       [  31:0]                   ...               ;
  reg       [  31:0]                   ...               ;

  wire      [  31:0]                   ...               ;
  wire      [  31:0]                   ...               ;    
  wire      [  31:0]                   ...               ;

  /***********************************************************
  * Combinary logic declation
  ***********************************************************/
  assign  hresp = 2'b00;
  
  assign  hsel_reg    = hsel && (haddr[9:0]>=10'h000) && (haddr[9:0]<=10'h003);
  assign  hsel_txdata = hsel && (haddr[9:0]>=10'h004) && (haddr[9:0]<=10'h084);
  assign  hsel_rxdata = hsel && (haddr[9:0]>=10'h088) && (haddr[9:0]<=10'h108);

  assign  testmode    = testmode_status[0];
  assign  txrxmode    = testmode_status[1];
  assign  startTx_p   = testmode_status[2] & (!stopTXstatus);
  assign  stopTx_P    = testmode_status[3] | txEnd_p;
  assign  clr_stopTX  = testmode_status[4];

  wire        test_tx_wr_en_tmp;
  wire  [4:0] test_tx_wr_addr_tmp;

  wire        test_rx_rd_en_tmp;
  reg         test_rx_rd_en_tmp1;
  reg         test_rx_rd_en_tmp2;
  reg         test_rx_rd_en_tmp3;
  reg         test_rx_rd_en_tmp4;
  reg         test_rx_rd_en_tmp5;
  reg [4:0]   test_rx_rd_addr_tmp;
  reg [4:0]   test_rx_rd_addr_tmp1;

  assign  test_tx_wr_en_tmp  = hwrite & hsel_txdata;
  assign  test_rx_rd_addr_tmp = haddr[6:2] - 5'b1;

  wire  stopRx_p;
  wire  startRx;
  wire  enrxreq;
  wire  clr_rxendstatus;
  wire  RXstatus;

  assign  RXstatus  = stopTXstatus;
  assign  exrxreq   = testmode_status[8];
  assign  startRx   = enrxreq & phyRdy & RXstatus;
  assign  stopRx_p  = testmode_status[9];
  assign  clr_rxendstatus = testmode_status[10];

  assign  rd_status = {testmode_status[31],stopTXstatus,rxEnd_p,RXENDStatus,agc_fall,testmode_status[26:0]};

  reg     rxEnd_p1;


  localparam  
                IDLE        = 2'd0,
                TX_VECTOR   = 2'd1,
                TX_DATA     = 2'd2,
                TX_END      = 2'd3;

  reg [1:0] txstateNs;
  reg [4:0] txVectorCnt;

  /***********************************************************
  * txEnd output register
  ***********************************************************/
  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)begin
      txEnd_p1  <= 0;
      rxEnd_p1  <= 0;
    end
    else begin
      txEnd_p1  <= txEnd_p;
      rxEnd_p1  <= rxEnd_p
    end
  end


  /***********************************************************
  * When this state is txEnd,stopTXstatus valid 
  ***********************************************************/
  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)
      stopTXstatus  <= 1'b0;
    else if(!txEnd_p1 && txEnd_p)
      stopTXstatus  <= 1'b1;
    else if(clr_stopTX)
      stopTXstatus  <= 1'b0;
    else
      ;
  end


  /***********************************************************
  * when this state is rxEnd,RXENDStatus valid
  ***********************************************************/
  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)
      RXENDStatus <= 1'b0;    
    else if(!rxEnd_p1 && rxEnd_p)
      RXENDStatus <= 1'b1;
    else if(clr_rxendstatus)
      RXENDStatus <= 1'b0;
    else
      ;
  end

  /***********************************************************
  * Delay the htrans one clock
  ***********************************************************/
  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)
      htrans_dly  <= 0;
    else
      htrans_dly  <= htrans;
  end

  reg hsel_rxdata_d1;
  reg hsel_rxdata_d2;
  
  /***********************************************************
  * 
  ***********************************************************/
  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)begin
      hsel_rxdata_d1  <= 0;
      hsel_rxdata_d1  <= 0;
    end
    else begin
      hsel_rxdata_d1  <= hsel_rxdata;
      hsel_rxdata_d2  <= hsel_rxdata_d1;
    end
  end

  assign  hready  = (hsel==1'b1 && htrans_dly[1] == 1'b1 && hwrite  == 1'b0) ? 1'b0 : 1'b1;

  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)begin
      testmode_status <= 32'b0;
      write_pending   <= 1'b0;
      test_tx_wr_data <= 0;
      test_tx_wr_en   <= 0;
      test_tx_wr_addr <= 0;
    end
    else begin
      if(hready_in  ==  1'b1)
      begin
        if(write_pending==1'b1)begin
          write_pending <= 1'b0;
          case(haddr[9:0])
            10'b0000_0000_00:testmode_status  <=  hwdata[31:0];
            default:;
          endcase
        if(hsel_txdata == 1'b1)begin
          test_tx_wr_data <= hwdata;
          test_tx_wr_en   <= test_tx_wr_en_tmp;
          test_tx_wr_addr <= test_tx_wr_addr_tmp;
        end
        else begin
          test_tx_wr_data <= 0;
          test_tx_wr_en   <= 0;
          test_tx_wr_addr <= 0;
        end
      end
      if(hsel == 1'b1 && htrans[1]  ==  1'b1)
      begin
        if(hwrite == 1'b0 && hsel_reg == 1'b1)
        begin
        end
        else if(hwrite == 1'b0 && hsel_rxdata_d2 == 1'b1)
        begin
        end
        else begin
          write_pending <= 1'b1;
          addr          <= haddr[9:2];
        end
      end
    end
  end

  assign hrdata = hsel ? (haddr[9:2] == 8'b0000_0000_00 ? rd_status : test_rx_rd_data) : 32'h0;


  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)
      txstateCs <= IDLE;
    else
      txstateCs <= txstateNs;
  end

  always @*
  begin
    case(txstateCs)
      IDLE:
        if(startTx_p)
          txstateNs = TX_VECTOR;
        else
          txstateNs = txstateCs;

      TX_VECTOR:
        if(txVectorCnt  ==  5'd16)
        begin
          if(stopTx_p)
            txstateNs = TX_END;
          else
            txstateNs = TX_DATA;
        end
        else
          txstateNs = txstateCs;

      TX_DATA:
        if(txEnd_p == 1'b1)
          txstateNs = IDLE;
        else if(stopTx_p)
          txstateNs = TX_END;
        else
          txstateNs = txstateCs;

      TX_END:
        if(txEnd_p)
          txstateNs = IDLE;
        else
          txstateNs = txstateCs;
      default:
        txstateNs = IDLE;
    endcase
  end


  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)
      txVectorCnt <= 5'b0000;
    else if(txstateCs == TX_VECTOR)
      txVectorCnt <= txVectorCnt  + 5'd1;
    else
      txVectorCnt <= 5'b0000;
  end


  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)
      phyRdy_reg  <= 1'b0;
    else
      phyRdy_reg  <= phyRdy;
  end

  
  always @(*)
  begin
    if(txstateCs  == TX_DATA)
    begin
      if(phyRdy_reg)
        mpIfFifoReadEn  =  1'b1;
      else
        mpIfFifoReadEn  =  1'b0;
    end
    else
    begin
      mpIfFifoReadEn    = 1'b0;
    end
  end


  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)begin
      macDataValid  <= 1'b0;
      TxkeepRFOn    <= 1'b0;
    end
    else begin
      if(txReq)
        TxkeepRFOn  <= mackeepRFOn;
      if(txstateCs  ==  TX_DATA)
      begin
        if(mpIfFifoReadEn == 1'b1)
          macDataValid  <= 1'b1;
        else
          macDataValid  <= 1'b0;
      end
      else
      begin
        macDataValid    <= 1'b0;
      end      
    end
  end

  
  always @(posedge mpIFClk or negedge rst_n)
  begin
    if(!rst_n)begin
      test_tx_rd_en <= 1'b0;
    end
    else if((txstateCs  ==  TX_END) || (txstateCs ==  IDLE))
      test_tx_rd_en <= 1'b0;
    else if((txstateCs  ==  TX_VECTOR) || macDataValdi)begin
      test_tx_rd_en <= 1'b1;
    end
    else begin
      test_tx_rd_en <= 1'b0;
    end
  end


  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)begin
      test_tx_rd_addr <= 7'h000;
    end
    else if(test_tx_rd_en)
      test_tx_rd_addr <= test_tx_rd_addr  + 1;
    else if((txstateCs  ==  TX_END) || (txstateCs ==  IDLE))
      test_tx_rd_addr <= 7'h000;
    else
      test_tx_rd_addr <= test_tx_rd_addr;
  end


  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)begin
      tx_req1 <= 0;
      tx_req2 <= 0;
      tx_req3 <= 0;
      tx_req4 <= 0;
      txReq   <= 0;
      macDataValid1 <= 0;
      macDataValid2 <= 0;
    end
    else begin
      tx_req1 <= startTx_p;
      tx_req2 <= tx_req1;
      tx_req3 <= tx_req2;
      txReq   <= tx_req3;
      macDataValid1   <= macDataValid;
      macDataValid2   <= macDataValid1;
      macDataValid_o  <= macDataValid2;
    end
  end

  /***********************************************************
  * RX PATH Logic 
  ***********************************************************/
  localparam
              RXIDLE    = 3'd0,
              RXVECTOR  = 3'd1,
              RXDATA    = 3'd2,
              RXEND     = 3'd3,
              RXERROR   = 3'd4;

  reg [2:0] rxstateCs;
  reg [4:0] rx_vector_cnt;


  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)
      test_rx_wr_en <= 0;
    else if(startRx)
      test_rx_wr_en <= 1;
    else
      test_rx_wr_en <= 0;
  end


  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)begin
      test_rx_wr_addr <= 7'h000;
    else if(test_rx_wr_en)
      test_rx_wr_addr <= test_rx_wr_addr + 1;
    else if((rxstateCs == RXEND) || (rxstateCs == RXIDLE))
      test_rx_wr_addr <= 7'h000;
    else
      test_rx_wr_addr <= test_rx_wr_addr;
  end
  
  assign test_rx_rd_en_tmp  = (~hwrite) && hsel_rxdata;


  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)
      test_rx_rd_addr <= 5'h0;
    else if(test_rx_rd_en_tmp)
      test_rx_rd_addr <= haddr[6:2] - 5'h2;
    else
      test_rx_rd_addr <= test_rx_rd_addr;
  end
  
  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)begin
      test_rx_rd_en_tmp1  <= 0;
      test_rx_rd_en_tmp2  <= 0;
      test_rx_rd_en       <= 0;
    end
    else begin
      test_rx_rd_en         <= test_rx_rd_en_tmp;
      test_rx_rd_en_tmp1    <= test_rx_rd_en_tmp;
      test_rx_rd_en_tmp2    <= test_rx_rd_en_tmp1;
    end
  end


  /***********************************************************
  * FSM for RX 
  ***********************************************************/
  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)
      rxstateCs <= RXIDLE;
    else
      rxstateCs <= rxstateNs;
  end

  always @*
  begin
    case(rxstateCs)
      RXIDLE:
        if(stopRx_p)
          rxstateNs = RXEND;
        else if(startRx)
          rxstateNs = RXVECTOR;
        else
          rxstateNs = rxstateCs;

      RXVECTOR:
        if(rx_vector_cnt  == 5'd16)
          rxstateNs = RXDATA;
        else if(stopRx_p)
          rxstateNs = RXEND;
        else
          rxstateNs = rxstateCs;

      RXDATA:
        if(rxEnd_p)
          rxstateNs = RXIDLE;
        else if(stopRx_p)
          rxstateNs = RXEND;
        else
          rxstateNs = rxstateCs;

      RXEND:
        if(rxEnd_p)
          rxstateNs = RXIDLE;
        else
          rxstateNs = rxstateCs;
      default:
        rxstateNs = RXIDLE;

    endcase
  end

  
  /***********************************************************
  * RX_VECTOR counter
  ***********************************************************/
  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)
      rx_vector_cnt <= 5'b0000;
    else if(rxstateCs ==  RXVECTOR)
    begin
      if(phyRdy)
        rx_vector_cnt <= rx_vector_cnt + 5'd1;
    end
    else
      rx_vector_cnt <= 5'b0000;
  end


  /***********************************************************
  * RX_REQ 
  ***********************************************************/
  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)
      rxReq   <= 1'b0;
    else begin
      if(enrxreq && RXstatus)
        rxReq   <= 1'b1;
      else if(startRx)
        rxReq   <= 1'b1;
      else if(rxEnd_p || (rxstateCs == RXEND))
        rxReq   <= 1'b0;
      else
        rxReq   <= 1'b0;
    end
  end

 endmodule



