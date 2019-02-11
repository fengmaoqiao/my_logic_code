//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author          : $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: $
// $Date: $
// ---------------------------------------------------------------------------
// Dependencies     : None
// Description      : Top level of deaggregator module
//
// Simulation Notes : 
//    For simulation, two defines are available
//
//    RW_SIMU_ON   : which creates string signals to display the FSM states on  
//                the waveform viewer.
//
//    RW_ASSERT_ON : which enables System Verilog Assertions.
//
// Synthesis Notes  :
//
// Application Note : 
//
// Simulator        :
//     For simulation with RW_ASSERT_ON, the simulator must support System 
//     Verilog Assertions
//
// Parameters       :
// Terms & concepts :
// Bugs             :
// Open issues and future enhancements :
// References       :
// Revision History :
// ---------------------------------------------------------------------------
//
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////


module deaggregator( 
            ///////////////////////////////////////////////
            //$port_g Clock and reset
            ///////////////////////////////////////////////
            input wire         macCoreRxClk,            // MAC Core Receive Clock
            input wire         macCoreClkHardRst_n,     // Hard Reset of the MAC Core Clock domain 
                                                        // active low
            input wire         macCoreClkSoftRst_n,     // Soft Reset of the MAC Core Clock domain
                                                        // active low
            ///////////////////////////////////////////////
            //$port_g MAC Controller
            ///////////////////////////////////////////////
            input wire         startRx,                 // Start Rx
            input wire         stopRx_p,                // Stop Rx
            
            output wire        rxVector1Start_p,        // Indicate that the first byte of RX Vector has been received
            output reg         rxVector1Valid_p,        // Rx vector 1 is available
            output wire        rxEndOfFrame_p,          // End of frame information
            output wire        deaggregatorCsIsIdle,    // Indicate that the deaggregator is waiting for a reception

            output reg         ampduCorrectRcved_p,     // A-MPDU received correctly
            output reg         ampduIncorrectRcved_p,   // A-MPDU not received correctly
            output reg         rxSingleVHTMPDU,         // Detect EOF bit in delimiter in VHT Single MPDU

            output reg [5:0]   rxMPDUCnt,               // Count the number of MPDU detected
            output reg [7:0]   incorrectDelCnt,         // Count the number of incorrect delimiter

            ///////////////////////////////////////////////
            //$port_g RX Controller
            ///////////////////////////////////////////////
            input wire         correctRcved_p,          // Frame received correctly
            
            input wire         rxCntrlReady,            // Rx controller ready to receive data
            
            output wire [11:0] rxLegLength,             // Legacy length
            output wire [ 3:0] rxLegRate,               // Legacy rate
            output wire [19:0] rxHTLength,              // HT length
            output wire [ 6:0] rxMCS,                   // MCS
            output wire        rxPreType,               // Preamble type
            output wire [ 2:0] rxFormatMod,             // Format and modulation
            output wire [ 1:0] rxChBW,                  // Channel bandwidth
            output wire        rxShortGI,               // Short Guard Interval
            output wire        rxSmoothing,             // Smoothing
            output wire        rxLSIGValid,             // L-SIG Valid of received frame
            output wire [ 1:0] rxSTBC,                  // Space Time Block Coding
            output wire        rxSounding,              // Sounding
            output wire [ 1:0] rxNumExtnSS,             // Number of Extension Spatial Streams
            output wire [ 1:0] rxChBWInNonHT,           // Channel bandwidth in Non-HT extracted from the scrambler initialization sequence
            output wire        rxAggregation,           // MPDU aggregate
            output wire        rxFecCoding,             // FEC Coding
            output wire [ 2:0] rxReserved1,             // Reserved
            output wire [ 7:0] rxAntennaSet,            // Antenna set
            output wire [ 2:0] rxnSTS,                  // Number of STS
            output wire        rxDynBW,                 // Dynamique Bandwidth
            output wire        rxDozeNotAllowed,        // TXOP PS not allowed
            output wire [ 8:0] rxPartialAID,            // Partial AID
            output wire [ 5:0] rxGroupID,               // Group ID
            output wire [ 7:0] rxRSSI1,                 // RSSI for RxChain 1
            output wire [ 7:0] rxRSSI2,                 // RSSI for RxChain 2
            output wire [ 7:0] rxRSSI3,                 // RSSI for RxChain 3
            output wire [ 7:0] rxRSSI4,                 // RSSI for RxChain 4
            output wire [ 7:0] rxReserved2,             // Reserved
            output wire [ 7:0] rxRCPI,                  // Receive Channel Power Indicator
            output wire [ 7:0] rxEVM1,                  // Error Vector Magnitude for space time stream 1
            output wire [ 7:0] rxEVM2,                  // Error Vector Magnitude for space time stream 2
            output wire [ 7:0] rxEVM3,                  // Error Vector Magnitude for space time stream 3
            output wire [ 7:0] rxEVM4,                  // Error Vector Magnitude for space time stream 4
            output wire [ 7:0] rxReserved3,             // Reserved
            output wire [ 7:0] rxReserved4,             // Reserved
            output wire [ 7:0] rxReserved5,             // Reserved
            output wire        rxVector2Valid_p,        // Rx vector 2 is available
            
            output wire [ 7:0] rxData,                  // Rx data extracted from MAC-PHY interface FIFO
            output wire        rxDataValid,             // Rx data is valid
            output reg         rxDataStart_p,           // Start of data flow
            output wire        rxDataEnd_p,             // End of data flow
            output wire        rxDataError_p,           // Rx Data error (length null)
            
            output reg  [15:0] rxByteCnt,               // Rx byte counter
 
            output wire [15:0] rxMpduLength,            // Full Rx MPDU Length
            output reg         rxNDP,                   // Indicate that the received frame is a Null Data Packet
            output wire        correctDelimiter,        // Indicate the correct Delimiter is found
            output reg  [1:0]  rxAMPDUCnt,              // Counter incremented at each A-MPDU reception


            ///////////////////////////////////////////////
            //$port_g MAC-PHY interface
            ///////////////////////////////////////////////
            input wire         macPhyIfRxFifoEmpty,     // MAC-PHY interface FIFO is empty
            input wire  [ 7:0] macPhyIfRxFifoData,      // MAC-PHY interface FIFO data
            
            input wire         macPhyIfRxErr_p,         // Rx error from MAC-PHY interface resynchronized
            input wire         macPhyIfRxEnd_p,         // Rx end from MAC-PHY interface resynchronized
            
            output reg         macPhyIfRxFifoReadEn,    // Read command to MAC-PHY interface FIFO

            ///////////////////////////////////////////////
            //$port_g Register interface
            ///////////////////////////////////////////////
            input wire  [19:0] maxAllowedLength,        // Filter frames whose length is greater than this length

            ///////////////////////////////////////////////
            //$port_g Debug ports
            ///////////////////////////////////////////////
            output wire [15:0] debugPortDeaggregator,   // Debug port for validation
            output wire [15:0] debugPortDeaggregator2,   // Debug port for validation2
            output wire [ 3:0] debugPortDeaggregatorFsm // Deaggregator FSM for validation
            );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// deaggregator FSM states definition
//$fsm_sd deaggregator
localparam 
                 IDLE =  4'd0,
    COMP_FIFO_LATENCY =  4'd1,
      READ_RX_VECTOR1 =  4'd2,
         TRIG_RX_CTRL =  4'd3,
       RX_AMPDU_DELIM =  4'd4,
   WAIT_RX_CTRL_READY =  4'd5,
         READ_MP_FIFO =  4'd6,
      READ_RX_VECTOR2 =  4'd7,
        VECTOR2_VALID =  4'd8,
         WAIT_PHY_END =  4'd9,
            RX_ERROR  =  4'd10;


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
  // deaggregator FSM signals definition
  reg [3:0] deaggregatorCs;  // deaggregator FSM Current State
  reg [3:0] deaggregatorNs;  // deaggregator FSM Next State

`ifdef RW_SIMU_ON
  // String definition to dislpay deaggregator current state
  reg [19*8:0] deaggregatorCs_str;
`endif // RW_SIMU_ON

  // Byte counter signals
  reg         byteCntEnd;
  
  // Read enable delayed signals
  reg         rxFifoReadEnDel1;
  
  // macPhyIfRxEnd_p sampled
  reg         macPhyIfRxEndSamp;
  
  // One clk cycle data valid after WAIT_RX_CTRL_READY
  reg         rxDataValidAfterReady;
  
  // Length signals
  wire [19:0] muxRxLength;
  reg  [19:0] htRxLength;
  reg  [15:0] mpduLength;
  wire [15:0] rxLength;  // Rx length of individual frame

  // RX Vectors
  reg [127:0] rxVector1;
  reg  [63:0] rxVector2;
  
  // A-MPDU signals
  wire        signatureFound;
  reg [19:0]  ampduByteCnt;
  reg         ampduByteCntEnd;
//  wire        correctDelimiter;

  // CRC signals
  wire        crcOk;
  reg  [1:0]  crcByteCnt;
  reg  [7:0]  crcCalc;
  wire [7:0]  crcCalcInv;
  
  // Data hold signals for CRC calculation
  reg [7:0]   rxDataHold1;
  reg [7:0]   rxDataHold2;

  // MAC Controller flag signals
  reg         frameRcvedFlag;
 
  // Frame abort due to max. length has occured
  wire        maxLengthExceeded_p;

  // detect and remember the first correct delimiter
  reg         rxFirstDelimiterDone;

  // detect EOF bit in the AMPDU delimiter
  reg         rxEOF;
  
  reg         incDelFound; // The flag incDelFound is used to detect the first incorrect delimiter
  reg         inDelimiter; // Flag indicating when the deaggregatopr is receiving a AMPDU delimiter
  
  wire [6:0]  debugMCS;

    
//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


///////////////////////////////////////
// deaggregator FSM Current State Logic 
///////////////////////////////////////
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    deaggregatorCs <= IDLE; 
  else if(macCoreClkSoftRst_n == 1'b0) // Soft reset
    deaggregatorCs <= IDLE; 
  else
    deaggregatorCs <= deaggregatorNs; 
end

assign deaggregatorCsIsIdle = (deaggregatorCs == IDLE) ? 1'b1 : 1'b0;

///////////////////////////////////////
// deaggregator FSM Next State Logic.
///////////////////////////////////////
always @* 
begin
  if (stopRx_p || (macPhyIfRxErr_p && macPhyIfRxEnd_p))
    //$fsm_t When stopRx_p or macPhyIfRxErr_p and macPhyIfRxEnd_p are true,
    // fsm goes to IDLE state
    deaggregatorNs = IDLE;
    
  else if (macPhyIfRxErr_p && !macPhyIfRxEnd_p)
    //$fsm_t When macPhyIfRxErr_p is true and not macPhyIfRxEnd_p , fsm goes to WAIT_PHY_END state
    deaggregatorNs = WAIT_PHY_END; 
  
  else if ((deaggregatorCs != IDLE) && (deaggregatorCs != VECTOR2_VALID) &&
    (deaggregatorCs != WAIT_PHY_END) && (deaggregatorCs != RX_ERROR) &&
    macPhyIfRxFifoEmpty && macPhyIfRxEndSamp && !rxNDP &&
    !((deaggregatorCs == READ_RX_VECTOR2) && byteCntEnd))
    //$fsm_t When macPhyIfRxFifoEmpty is true and macPhyIfRxEndSamp and not rxNDP, fsm goes to RX_ERROR state
    deaggregatorNs = RX_ERROR; 
  
  else
  begin
  case(deaggregatorCs)

    IDLE:
      //$fsm_s In IDLE state, fsm waits MAC Controller to request RX start.
      if (startRx && !macPhyIfRxFifoEmpty)
        //$fsm_t When startRx is true, fsm goes to COMP_FIFO_LATENCY state
        deaggregatorNs = COMP_FIFO_LATENCY; 
      else
        //$fsm_t When startRx is false, fsm stays to IDLE state
        deaggregatorNs = IDLE;

    COMP_FIFO_LATENCY:
      //$fsm_s In COMP_FIFO_LATENCY state, fsm waits MAC PHY IF FIFO to be not empty.
      if (!macPhyIfRxFifoEmpty)
        //$fsm_t When macPhyIfRxFifoEmpty is false, fsm goes to READ_RX_VECTOR1 state
        deaggregatorNs = READ_RX_VECTOR1; 
      else
        //$fsm_t When macPhyIfRxFifoEmpty is true, fsm stays to COMP_FIFO_LATENCY state
        deaggregatorNs = COMP_FIFO_LATENCY;

    READ_RX_VECTOR1:
      //$fsm_s In READ_RX_VECTOR1 state, fsm waits byteCntEnd active.
      if (byteCntEnd && rxFifoReadEnDel1)
      begin
        if (rxNDP)
          //$fsm_t When Null Data Packet, fsm goes to TRIG_RX_CTRL state
          deaggregatorNs = TRIG_RX_CTRL;
        else if (!rxAggregation && (muxRxLength > maxAllowedLength))
          //$fsm_t When length is null, fsm goes to RX_ERROR state
          deaggregatorNs = RX_ERROR;
        else if (rxAggregation)
          //$fsm_t When frame is a A-MPDU, fsm goes to RX_AMPDU_DELIM state
          deaggregatorNs = RX_AMPDU_DELIM; 
        else
          //$fsm_t When length is not null, fsm goes to TRIG_RX_CTRL state
          deaggregatorNs = TRIG_RX_CTRL; 
      end
      else
        //$fsm_t While byteCntEnd is not asserted, fsm stays to READ_RX_VECTOR1 state
        deaggregatorNs = READ_RX_VECTOR1;

    TRIG_RX_CTRL:
      //$fsm_s In TRIG_RX_CTRL state, fsm triggers RX Controller.
      if (rxNDP)
        //$fsm_t When Null Data Packet, fsm goes to TRIG_RX_CTRL state
        deaggregatorNs = READ_RX_VECTOR2;
      else if (rxCntrlReady)
        //$fsm_t When rxCntrlReady is true, fsm goes to WAIT_RX_CTRL_READY state
        deaggregatorNs = WAIT_RX_CTRL_READY; 
      else
        //$fsm_t When rxCntrlReady is false, fsm stays to TRIG_RX_CTRL state
        deaggregatorNs = TRIG_RX_CTRL;
      
    RX_AMPDU_DELIM:
      //$fsm_s In RX_AMPDU_DELIM state, fsm waits delimitor to be found.
      if (correctDelimiter)
        //$fsm_t When correctDelimiter is true, fsm goes to TRIG_RX_CTRL state
        deaggregatorNs = TRIG_RX_CTRL;
      else if (rxFifoReadEnDel1 && ampduByteCntEnd)
        //$fsm_t When ampduByteCntEnd is true, fsm goes to READ_RX_VECTOR2 state
        deaggregatorNs = READ_RX_VECTOR2;
      else
        //$fsm_t When correctDelimiter and ampduByteCntEnd are false,
        // fsm stays to RX_AMPDU_DELIM state
        deaggregatorNs = RX_AMPDU_DELIM;

    RX_ERROR:
      //$fsm_s In RX_ERROR state, fsm checks if macPhyIfRxEnd_p has been received.
      if (macPhyIfRxEndSamp && macPhyIfRxFifoEmpty)
        //$fsm_t When macPhyIfRxEndSamp is true, fsm goes to IDLE state
        deaggregatorNs = IDLE; 
      else
        //$fsm_t When macPhyIfRxEndSamp is not true, fsm goes to WAIT_PHY_END state
        deaggregatorNs = WAIT_PHY_END;

    WAIT_RX_CTRL_READY:
      //$fsm_s In WAIT_RX_CTRL_READY state, fsm waits rxCntrlReady active.
      if (rxCntrlReady || (frameRcvedFlag && !rxAggregation))
        //$fsm_t When rxCntrlReady is true, fsm goes to READ_MP_FIFO state
        deaggregatorNs = READ_MP_FIFO; 
      else
        //$fsm_t When rxCntrlReady is false, fsm stays to WAIT_RX_CTRL_READY state
        deaggregatorNs = WAIT_RX_CTRL_READY;

    READ_MP_FIFO:
      //$fsm_s In READ_MP_FIFO state, fsm waits until end of the frame is reached.
      if (rxDataValid && byteCntEnd && rxAggregation && !ampduByteCntEnd)
        //$fsm_t When byteCntEnd is true and frame is an A-MPDU and this is not 
        // the last A-MPDU, fsm goes to RX_AMPDU_DELIM state
        deaggregatorNs = RX_AMPDU_DELIM; 
      else if (rxDataValid && (ampduByteCntEnd || byteCntEnd && !rxAggregation))
        //$fsm_t When byteCntEnd is true and frame is an A-MPDU and this is  
        // the last A-MPDU packet, fsm goes to READ_RX_VECTOR2 state
        deaggregatorNs = READ_RX_VECTOR2;
      else if (frameRcvedFlag && !rxAggregation)
        //$fsm_t When a frame of a singleton MPDU has been received, fsm stays in 
        //READ_MP_FIFO state to pops additional bytes in case of lenght error
        deaggregatorNs = READ_MP_FIFO;
      else if (!rxCntrlReady)
        //$fsm_t When rxCntrlReady is false, fsm goes to WAIT_RX_CTRL_READY state
        deaggregatorNs = WAIT_RX_CTRL_READY;
      else
        //$fsm_t When rxCntrlReady is true, fsm stays to READ_MP_FIFO state
        deaggregatorNs = READ_MP_FIFO;

    READ_RX_VECTOR2:
      //$fsm_s In READ_RX_VECTOR2 state, fsm waits byteCntEnd is active.
      if (byteCntEnd && rxFifoReadEnDel1)
        //$fsm_t When byteCntEnd is true, fsm goes to VECTOR2_VALID state
        deaggregatorNs = VECTOR2_VALID; 
      else
        //$fsm_t When byteCntEnd is false, fsm stays
        // to READ_RX_VECTOR2 state
        deaggregatorNs = READ_RX_VECTOR2;

    VECTOR2_VALID:
      //$fsm_s In VECTOR2_VALID state, fsm goes to WAIT_PHY_END.

        //$fsm_t After one clock cycle, fsm goes to WAIT_PHY_END
        deaggregatorNs = WAIT_PHY_END;

    WAIT_PHY_END:
      //$fsm_s In WAIT_PHY_END state, fsm waits macPhyIfRxEnd_p active.
      if (macPhyIfRxEnd_p || macPhyIfRxEndSamp)
        //$fsm_t When macPhyIfRxEnd_p is true, fsm goes to IDLE state
        deaggregatorNs = IDLE; 
      else
        //$fsm_t When macPhyIfRxEnd_p is false, fsm stays to WAIT_PHY_END state
        deaggregatorNs = WAIT_PHY_END;
      
      // Disable case default state for block coverage
      // pragma coverage block = off
     default:   
        deaggregatorNs = IDLE;
      // pragma coverage block = on
        
  endcase
  end
end


///////////////////////////////////////
// Byte Counter control
///////////////////////////////////////
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    rxByteCnt  <= 16'b0;
    byteCntEnd <= 1'b0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    rxByteCnt  <= 16'b0;
    byteCntEnd <= 1'b0;
  end
  else
  begin
    // Clear counter
    if ((deaggregatorCs == IDLE) || (deaggregatorCs == WAIT_PHY_END))
    begin
      rxByteCnt  <= 16'b0;
      byteCntEnd <= 1'b0;
    end
    else
    begin
      // Set counter
      if (deaggregatorCs == COMP_FIFO_LATENCY)
        // Set counter for RX Vector 1
        rxByteCnt <= 16'h000e;
      else if (deaggregatorCs == TRIG_RX_CTRL)
      begin
        // Set counter for RX data
        if (rxLength != 16'd0)
          rxByteCnt <= rxLength - 16'h0001;
      end
      else if ((rxFifoReadEnDel1 && ampduByteCntEnd) ||
            ((deaggregatorCs == READ_MP_FIFO) && rxDataValid &&
              byteCntEnd && !rxAggregation))
          // Set counter for RX Vector 2
          rxByteCnt <= 16'h0007;
      else if ((deaggregatorCs == READ_RX_VECTOR1) && byteCntEnd && rxNDP)
        // Set counter for RX Vector 2
        rxByteCnt <= 16'h0007;
         
      
      // Decrement counter
      if (rxFifoReadEnDel1)
      begin
        // Rx Vector 1
        if (deaggregatorCs == READ_RX_VECTOR1)
        begin
          // Byte counter control
          if (rxByteCnt != 16'h0000)
            rxByteCnt <= rxByteCnt - 16'h0001;
          // Byte counter end control
          if (rxByteCnt == 16'h0001)
            byteCntEnd <= 1'b1;
          else if (byteCntEnd)
            byteCntEnd <= 1'b0;
        end
        // RX Vector 2
        else if (deaggregatorCs == READ_RX_VECTOR2)
        begin
          // Byte counter control
          if (rxByteCnt != 16'h0000)
            rxByteCnt <= rxByteCnt - 16'h0001;
          // Byte counter end control
          if (rxByteCnt == 16'h0001)
            byteCntEnd <= 1'b1;
          else if (byteCntEnd)
            byteCntEnd <= 1'b0;
        end
      end
      // RX data
      if (rxDataValid && ((deaggregatorCs == READ_MP_FIFO)))
      begin
        // Byte counter control
        if ((rxByteCnt != 16'h0000) && !(byteCntEnd || ampduByteCntEnd))
          rxByteCnt <= rxByteCnt - 16'h0001;
        // Byte counter end control
        if (rxByteCnt == 16'h0001)
          byteCntEnd <= 1'b1;
        else if (byteCntEnd || ampduByteCntEnd)
          byteCntEnd <= 1'b0;
      end
    end
  end
end

// macPhyIfRxFifoReadEn delayed by 1 cc due to MAC PHY IF FIFO latency
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    rxFifoReadEnDel1 <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxFifoReadEnDel1 <= 1'b0;
  else
    rxFifoReadEnDel1 <= macPhyIfRxFifoReadEn;
end


///////////////////////////////////////
// RX Vectors
///////////////////////////////////////
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    rxVector1  <= 128'b0;
    rxVector2  <= 64'b0;
    htRxLength <= 20'b0;
    mpduLength <= 16'b0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    rxVector1  <= 128'b0;
    rxVector2  <= 64'b0;
    htRxLength <= 20'b0;
    mpduLength <= 16'b0;
  end
  else if ((deaggregatorCs == COMP_FIFO_LATENCY) && (deaggregatorNs == READ_RX_VECTOR1))
  begin
    rxVector1  <= 128'b0;
    rxVector2  <= 64'b0;
    htRxLength <= 20'b0;
    mpduLength <= 16'b0;
  end
  else
  begin
    // Update rxVector1 length with individual A-MPDU length
    if (rxAggregation)
    begin
      if ((crcByteCnt == 2'h2) && (deaggregatorCs == RX_AMPDU_DELIM))
        mpduLength <= (rxFormatMod == 3'b100) ? {2'b0,rxDataHold2[3:2],rxDataHold1,rxDataHold2[7:4]} : {4'b0, rxDataHold1, rxDataHold2[7:4]};
//        mpduLength <= (rxFormatMod == 3'b100) ? {2'b0, rxDataHold1, rxDataHold2[7:2]} : {4'b0, rxDataHold1, rxDataHold2[7:4]};
    end
    else
      mpduLength <= htRxLength[15:0];
    
    if (rxFifoReadEnDel1)
    begin
      // RX_VECTOR1
      if (deaggregatorCs == READ_RX_VECTOR1)
      begin
        case (rxByteCnt[3:0])
          4'd14: rxVector1[7:0]    <= macPhyIfRxFifoData;
          4'd13: rxVector1[15:8]   <= macPhyIfRxFifoData;
          4'd12: rxVector1[23:16]  <= macPhyIfRxFifoData;
          4'd11: rxVector1[31:24]  <= macPhyIfRxFifoData;
          4'd10: rxVector1[39:32]  <= macPhyIfRxFifoData;
          4'd9 : rxVector1[47:40]  <= macPhyIfRxFifoData;
          4'd8 : rxVector1[55:48]  <= macPhyIfRxFifoData;
          4'd7 : rxVector1[63:56]  <= macPhyIfRxFifoData;
          4'd6 : rxVector1[71:64]  <= macPhyIfRxFifoData;
          4'd5 : rxVector1[79:72]  <= macPhyIfRxFifoData;
          4'd4 : rxVector1[87:80]  <= macPhyIfRxFifoData;
          4'd3 : rxVector1[95:88]  <= macPhyIfRxFifoData;
          4'd2 : rxVector1[103:96] <= macPhyIfRxFifoData;
          4'd1 : rxVector1[111:104] <= macPhyIfRxFifoData;
          4'd0 : rxVector1[119:112] <= macPhyIfRxFifoData;
          // Disable case default state for block coverage
          // pragma coverage block = off
          default : rxVector1     <= rxVector1;
          // pragma coverage block = on
        endcase
          htRxLength <= rxVector1[35:16];
      end
      // RX_VECTOR2
      else if (deaggregatorCs == READ_RX_VECTOR2)
      begin
        case (rxByteCnt[3:0])
          4'h7: rxVector2[7:0]    <= macPhyIfRxFifoData;
          4'h6: rxVector2[15:8]   <= macPhyIfRxFifoData;
          4'h5: rxVector2[23:16]  <= macPhyIfRxFifoData;
          4'h4: rxVector2[31:24]  <= macPhyIfRxFifoData;
          4'h3: rxVector2[39:32]  <= macPhyIfRxFifoData;
          4'h2: rxVector2[47:40]  <= macPhyIfRxFifoData;
          4'h1: rxVector2[55:48]  <= macPhyIfRxFifoData;
          4'h0: rxVector2[63:56]  <= macPhyIfRxFifoData;
          // Disable case default state for block coverage
          // pragma coverage block = off
          default : rxVector2     <= rxVector2;
          // pragma coverage block = on
        endcase
      end
    end
  end
end


///////////////////////////////////////
// Parameter extraction from Rx Vectors
///////////////////////////////////////
// For future use
assign rxReserved2      = 8'h0;

assign rxLegLength      = rxVector1[11:0];
assign rxLegRate        = rxVector1[15:12];
assign rxHTLength       = rxVector1[35:16];
assign rxShortGI        = rxVector1[36];
assign rxSTBC           = rxVector1[38:37];
assign rxSmoothing      = rxVector1[39];
assign rxMCS            = rxVector1[46:40];
assign rxPreType        = rxVector1[47];
assign rxFormatMod      = rxVector1[50:48];
assign rxChBW           = rxVector1[52:51];
assign rxnSTS           = rxVector1[55:53];
assign rxLSIGValid      = rxVector1[56];
assign rxSounding       = rxVector1[57];
assign rxNumExtnSS      = rxVector1[59:58];
assign rxChBWInNonHT    = (rxFormatMod[2:1] == 2'b00) ? rxVector1[59:58] : 2'b0;
assign rxAggregation    = rxVector1[60] || (rxFormatMod == 3'b100);
assign rxFecCoding      = rxVector1[61];
assign rxDynBW          = rxVector1[62];
assign rxDozeNotAllowed = rxVector1[63];
assign rxAntennaSet     = rxVector1[71:64];
assign rxPartialAID     = rxVector1[80:72];
assign rxGroupID        = rxVector1[86:81];


assign rxRSSI1          = rxVector1[95:88];
assign rxRSSI2          = rxVector1[103:96];
assign rxRSSI3          = rxVector1[111:104];
assign rxRSSI4          = rxVector1[119:112];

assign rxReserved1      = 3'h0;


assign rxRCPI        = rxVector2[7:0];
assign rxEVM1        = rxVector2[15:8];
assign rxEVM2        = rxVector2[23:16];
assign rxEVM3        = rxVector2[31:24];

assign rxEVM4        = rxVector2[39:32];
assign rxReserved3   = rxVector2[47:40];
assign rxReserved4   = rxVector2[55:48];
assign rxReserved5   = rxVector2[63:56];


///////////////////////////////////////
// Length selection
///////////////////////////////////////
// RX length mux between HT value and Legacy value
assign muxRxLength = (rxFormatMod >= 3'd2) ? htRxLength : {8'b0, rxLegLength};
// RX length mux between A-MPDU value and muxRxLength value
assign rxLength = (rxAggregation) ? mpduLength : muxRxLength[15:0];
assign rxMpduLength = rxLength;



// detection of NDP 
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    rxNDP <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (deaggregatorCs == IDLE))
    rxNDP <= 1'b0;
  else if (deaggregatorCs == READ_RX_VECTOR1)
  begin
    // Null Data Packet exists only in HT or VHT 
    if ((muxRxLength == 20'b0) && (rxFormatMod >= 3'b010))
      rxNDP <= 1'b1;
    else  
      rxNDP <= 1'b0;
  end
end


///////////////////////////////////////
// Trigger to RX Controller
///////////////////////////////////////
// Inform RX Controller to start reception procedure
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    rxDataStart_p <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (deaggregatorCs == IDLE))
    rxDataStart_p <= 1'b0;
  else
    rxDataStart_p <= (rxCntrlReady && (deaggregatorCs == TRIG_RX_CTRL));
end


// Inform RX Controller to stop reception procedure
assign rxDataEnd_p      = ((deaggregatorCs == READ_MP_FIFO) && 
                             rxDataValid && byteCntEnd) ? 1'b1 : 1'b0;

// Inform RX Controller of length error
assign rxDataError_p    = (deaggregatorCs == RX_ERROR) ? 1'b1 : 1'b0;

// Inform RX Controller that RX Vectors 2 are available
assign rxVector2Valid_p = (deaggregatorCs == VECTOR2_VALID) ? 1'b1 : 1'b0;

// RX data from MAC PHY IF FIFO
assign rxData = macPhyIfRxFifoData;

// Inform RX Controller that data is available
assign rxDataValid = ((deaggregatorCs == READ_MP_FIFO) && 
                     (rxFifoReadEnDel1 || rxDataValidAfterReady)) ? 1'b1 : 1'b0;

// One clk cycle rxDataValid after RX Controller is ready
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    rxDataValidAfterReady <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxDataValidAfterReady <= 1'b0;
  else if (((deaggregatorCs == WAIT_RX_CTRL_READY) ||
            (deaggregatorCs == TRIG_RX_CTRL)) && rxFifoReadEnDel1)
    rxDataValidAfterReady <= 1'b1;
  else if (deaggregatorCs == READ_MP_FIFO)
    rxDataValidAfterReady <= 1'b0;
end

// macPhyIfRxEnd_p sampled for FSM information
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    macPhyIfRxEndSamp <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    macPhyIfRxEndSamp <= 1'b0;
  else if (deaggregatorCs == IDLE)
    macPhyIfRxEndSamp <= 1'b0;
  else if (macPhyIfRxEnd_p)
    macPhyIfRxEndSamp <= 1'b1;
end

// Read enable to MAC PHY IF FIFO
always @* 
begin
  // When MAC PHY IF FIFO is empty release macPhyIfRxFifoReadEn !
  if (macPhyIfRxFifoEmpty == 1'b1)
    macPhyIfRxFifoReadEn = 1'b0;
  else
  begin
    case(deaggregatorCs)

      COMP_FIFO_LATENCY, RX_AMPDU_DELIM, READ_MP_FIFO, WAIT_PHY_END:
        // Read
        macPhyIfRxFifoReadEn = 1'b1;

      READ_RX_VECTOR1:
        // Conditional read
        if (rxByteCnt == 16'h0000)
        begin
          if (rxFifoReadEnDel1)
            macPhyIfRxFifoReadEn = 1'b0;
          else
            macPhyIfRxFifoReadEn = 1'b1;
        end
        else
          macPhyIfRxFifoReadEn = 1'b1;

      READ_RX_VECTOR2:
        // Conditional read
        if (rxByteCnt == 16'h0000)
        begin
          if (rxFifoReadEnDel1)
            macPhyIfRxFifoReadEn = 1'b0;
          else
            macPhyIfRxFifoReadEn = 1'b1;
        end
        else
          macPhyIfRxFifoReadEn = 1'b1;

      default:
        macPhyIfRxFifoReadEn = 1'b0;
          
    endcase
  end
end


///////////////////////////////////////
// Triggers to MAC Controller
///////////////////////////////////////
// Inform MAC Controller to send ACK after A-MPDU end
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    frameRcvedFlag        <= 1'b0;
    ampduIncorrectRcved_p <= 1'b0;
    ampduCorrectRcved_p   <= 1'b0;
    rxSingleVHTMPDU       <= 1'b0;
    rxFirstDelimiterDone   <= 1'b0;
    rxEOF                 <= 1'b0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    frameRcvedFlag        <= 1'b0;
    ampduIncorrectRcved_p <= 1'b0;
    ampduCorrectRcved_p   <= 1'b0;
    rxSingleVHTMPDU       <= 1'b0;
    rxFirstDelimiterDone   <= 1'b0;
    rxEOF                 <= 1'b0;
  end
  else
  begin
    // A-MPDU received pulse generation
    if ((deaggregatorCs == VECTOR2_VALID) && rxAggregation)
    begin
      ampduIncorrectRcved_p <= !frameRcvedFlag;
      ampduCorrectRcved_p   <= frameRcvedFlag;
      frameRcvedFlag        <= 1'b0;
    end
    else if ((deaggregatorCs == RX_ERROR) && rxAggregation)
    begin
      ampduIncorrectRcved_p <= 1'b1;
      ampduCorrectRcved_p   <= 1'b0;
    end
    else
    begin
      ampduIncorrectRcved_p <= 1'b0;
      ampduCorrectRcved_p   <= 1'b0;
    end

    // Detection of bit EOF
    if ((deaggregatorCs == RX_AMPDU_DELIM) && (crcByteCnt == 2'b00) && (rxFormatMod == 3'b100) && rxAggregation)
    begin
      rxEOF <= rxData[0];
    end
    else if((deaggregatorCs != IDLE) && (deaggregatorNs == IDLE))
    begin
      rxEOF <= 1'b0;
    end


    // Set the rxSingleVHTMPDU if the delimiter has length not null and if it is first delimiter 
    // and VHT mode and crcOk
    if ((deaggregatorCs == RX_AMPDU_DELIM) && (correctDelimiter == 1'b1) && (crcByteCnt == 2'b11) && (rxFormatMod == 3'b100) && 
        rxAggregation && crcOk && (mpduLength != 16'h0))
    begin
      rxFirstDelimiterDone <=  1'b1;
      rxSingleVHTMPDU     <= !rxFirstDelimiterDone && rxEOF;
    end
    // Clear the flag if the state is going idle
    else if ((deaggregatorCs != IDLE) && (deaggregatorNs == IDLE))
    begin
      rxSingleVHTMPDU     <= 1'b0;
      rxFirstDelimiterDone <= 1'b0;
    end

    if (deaggregatorCs == IDLE)
      // Clear flags
      frameRcvedFlag <= 1'b0;
    else if (correctRcved_p)
      // Generates flag
      frameRcvedFlag <= 1'b1;
  end
end

// Inform MAC Controller that RX Vectors 1 are available
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    rxVector1Valid_p <= 1'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    rxVector1Valid_p <= 1'b0;
  else 
  begin
    // Pulse generation
    rxVector1Valid_p <= 1'b0;
    if ((deaggregatorCs == READ_RX_VECTOR1) && (deaggregatorNs != READ_RX_VECTOR1))
      rxVector1Valid_p <= 1'b1;
  end
end

// Inform MAC Controller about RX frame ending
assign rxEndOfFrame_p = rxDataError_p || ((deaggregatorCs == WAIT_PHY_END) && (macPhyIfRxEnd_p || macPhyIfRxEndSamp));

// Inform MAC Controller about the reception of the first byte of rxVector1
assign rxVector1Start_p = (deaggregatorCs == COMP_FIFO_LATENCY) && !macPhyIfRxFifoEmpty;


///////////////////////////////////////
// A-MPDU logic
///////////////////////////////////////
// Signature found generation
assign signatureFound = ((deaggregatorCs == RX_AMPDU_DELIM) &&
                         (macPhyIfRxFifoData == 8'h4e)) ? 1'b1 : 1'b0;

// Correct delimiter generation
assign correctDelimiter = (deaggregatorCs == RX_AMPDU_DELIM) &&
                           signatureFound && 
                           (crcByteCnt == 2'd3) &&
                           crcOk && 
                           rxFifoReadEnDel1 && 
                           (mpduLength != 16'b0) &&
                           ({4'b0,mpduLength} <= ampduByteCnt) &&
                           ({4'b0,mpduLength} < muxRxLength) &&
                           ({4'b0,mpduLength} <= maxAllowedLength);

// Data hold for CRC checking
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    rxDataHold1 <= 8'b0;
    rxDataHold2 <= 8'b0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    rxDataHold1 <= 8'b0;
    rxDataHold2 <= 8'b0;
  end
  // Hold data in RX_AMPDU_DELIM state
//   else if ((deaggregatorCs == RX_AMPDU_DELIM) && rxFifoReadEnDel1 &&
//             !signatureFound)
  else if ((deaggregatorCs == RX_AMPDU_DELIM) && rxFifoReadEnDel1)
  begin
    rxDataHold1 <= macPhyIfRxFifoData;
    rxDataHold2 <= rxDataHold1;
  end
end

// CRC byte counter
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    crcByteCnt <= 2'b0;
  else if(macCoreClkSoftRst_n == 1'b0)
    crcByteCnt <= 2'b0;
  // Clear counter in IDLE state
  else if ((deaggregatorCs == IDLE) || 
          ((crcByteCnt == 2'h3) && rxFifoReadEnDel1))
    crcByteCnt <= 2'b0;
  // Increment counter in RX_AMPDU_DELIM state
  else if (((deaggregatorCs == RX_AMPDU_DELIM) ||
            (deaggregatorCs == READ_MP_FIFO) ||
            (deaggregatorCs == WAIT_RX_CTRL_READY) ||
            (deaggregatorCs == TRIG_RX_CTRL)) && 
           rxFifoReadEnDel1 && rxAggregation)
    crcByteCnt <= crcByteCnt + 2'h1;
end

// CRC 8-bit with polynomial x8+x2+x1+1
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    crcCalc <= 8'hff;
  else if(macCoreClkSoftRst_n == 1'b0)
    crcCalc <= 8'hff;
  // Re-initialyse CRC in IDLE state and when crcByteCnt = 3
  else if ((deaggregatorCs == IDLE) ||
          ((crcByteCnt == 2'h3) && rxFifoReadEnDel1))
    crcCalc <= 8'hff;
  else if ((deaggregatorCs == RX_AMPDU_DELIM) && rxFifoReadEnDel1 &&
           (crcByteCnt < 2'h2))
  begin
    // CRC generation
    crcCalc[0] <= macPhyIfRxFifoData[0] ^ macPhyIfRxFifoData[1] ^ macPhyIfRxFifoData[7] ^ 
                  crcCalc[0] ^ crcCalc[6] ^ crcCalc[7];
    crcCalc[1] <= macPhyIfRxFifoData[1] ^ macPhyIfRxFifoData[6] ^ macPhyIfRxFifoData[7] ^ 
                  crcCalc[0] ^ crcCalc[1] ^ crcCalc[6];
    crcCalc[2] <= macPhyIfRxFifoData[1] ^ macPhyIfRxFifoData[5] ^ macPhyIfRxFifoData[6] ^ 
                  macPhyIfRxFifoData[7] ^ crcCalc[0] ^ crcCalc[1] ^ crcCalc[2]  ^
                  crcCalc[6];
    crcCalc[3] <= macPhyIfRxFifoData[0] ^ macPhyIfRxFifoData[4] ^ macPhyIfRxFifoData[5] ^
                  macPhyIfRxFifoData[6] ^ crcCalc[1] ^ crcCalc[2] ^ crcCalc[3]  ^ 
                  crcCalc[7];
    crcCalc[4] <= macPhyIfRxFifoData[3] ^ macPhyIfRxFifoData[4] ^ macPhyIfRxFifoData[5] ^
                  crcCalc[2] ^ crcCalc[3] ^ crcCalc[4];
    crcCalc[5] <= macPhyIfRxFifoData[2] ^ macPhyIfRxFifoData[3] ^ macPhyIfRxFifoData[4] ^
                  crcCalc[3] ^ crcCalc[4] ^ crcCalc[5];
    crcCalc[6] <= macPhyIfRxFifoData[1] ^ macPhyIfRxFifoData[2] ^ macPhyIfRxFifoData[3] ^
                  crcCalc[4] ^ crcCalc[5] ^ crcCalc[6];
    crcCalc[7] <= macPhyIfRxFifoData[0] ^ macPhyIfRxFifoData[1] ^ macPhyIfRxFifoData[2] ^
                  crcCalc[5] ^ crcCalc[6] ^ crcCalc[7];
  end
end


assign crcCalcInv = {~crcCalc[0],~crcCalc[1],~crcCalc[2],~crcCalc[3],~crcCalc[4],~crcCalc[5],~crcCalc[6],~crcCalc[7]};

// CRC Ok generation
assign crcOk = ((deaggregatorCs == RX_AMPDU_DELIM) && 
                (crcCalcInv == rxDataHold1)) ? 1'b1 : 1'b0;

// A-MPDU Byte Counter control
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    ampduByteCnt    <= 20'b0;
    ampduByteCntEnd <= 1'b0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    ampduByteCnt    <= 20'b0;
    ampduByteCntEnd <= 1'b0;
  end
  else
  begin
    // Clear counter in IDLE or WAIT_PHY_END state
    if ((deaggregatorCs == IDLE) || (deaggregatorCs == WAIT_PHY_END))
    begin
      ampduByteCnt    <= 20'b0;
      ampduByteCntEnd <= 1'b0;
    end
    // If frame is an A-MPDU, then control counter
    else if (rxAggregation)
    begin
      if ((deaggregatorCs == READ_RX_VECTOR1) && byteCntEnd)
        // Set counter
          ampduByteCnt <= muxRxLength - 20'h001;
      // READ_MP_FIFO || RX_AMPDU_DELIM || WAIT_RX_CTRL_READY
      else if ((rxFifoReadEnDel1 && (deaggregatorCs == RX_AMPDU_DELIM)) ||
               (rxDataValid && ((deaggregatorCs == READ_MP_FIFO))))
      begin
        // Byte counter control
        if (ampduByteCnt != 20'h000)
          // Decrement counter
          ampduByteCnt <= ampduByteCnt - 20'h001;
        // Byte counter end control
        if (ampduByteCnt == 20'h001)
          ampduByteCntEnd <= 1'b1;
        else if (ampduByteCntEnd)
          ampduByteCntEnd <= 1'b0;
      end
    end
  end
end


// Statistics
//////////////////////////////////////////////////////////////////////////////

// received MPDU counter
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    rxMPDUCnt <= 6'h3F;
  else if (deaggregatorCs == IDLE)
    rxMPDUCnt <= 6'h3F;
  // Increment counter every MPDU detected
  else if (rxDataStart_p)
    rxMPDUCnt <= rxMPDUCnt + 6'd1;
end

// received MPDU counter
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    rxAMPDUCnt <= 2'd0;
  else if (macCoreClkSoftRst_n == 1'b0)
    rxAMPDUCnt <= 2'd0;
  // Increment counter every A-MPDU detected
  else if (rxVector1Valid_p && rxAggregation)
    rxAMPDUCnt <= rxAMPDUCnt + 2'd1;
end




// Flag indicating the end of the AMPDU delimiter
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
    inDelimiter       <= 1'b0;
  else if (deaggregatorCs != RX_AMPDU_DELIM)
    inDelimiter       <= 1'b0;
  else if ((deaggregatorCs == RX_AMPDU_DELIM) && rxFifoReadEnDel1 && (crcByteCnt == 2'd0))
    inDelimiter       <= 1'b1;
end  

// incorrect Delimiter counter
// An immediately repeated CRC error within an A-MPDU is not counted.
always @(posedge macCoreRxClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    incorrectDelCnt <= 8'd0;
    incDelFound     <= 1'b0;
  end  
  else if (deaggregatorCs == IDLE)
  begin
    incorrectDelCnt <= 8'd0;
    incDelFound     <= 1'b0;
  end  
  // Each time a delimiter is received check if it is correct or not
  else if (inDelimiter)
  begin
    // If the delimiter is correct, reset the incDelFound flag. 
    if (correctDelimiter) 
      incDelFound     <= 1'b0;
    // If the delimiter is not correct, the delimiter is not a blank delimiter (mpduLength != 16'b0) 
    // and the incDelFound flag is not set
    // The flag incDelFound is used to detect the first incorrect delimiter
    else if (!incDelFound && (mpduLength != 16'b0) && (crcByteCnt == 2'd3))
    begin
      incorrectDelCnt <= incorrectDelCnt + 8'd1;
      incDelFound     <= 1'b1;
    end
  end  
end  

// Useful for MIB counters. This will be a pulse of 1 macCoreRxClk duration
// Note: This specifically sees READ_RX_VECTOR1 state for current state, 
// instead of (current state != next state). This is due to an stopRx_p 
// issue causing a double abort. As a result of this fix, the double 
// abort will  occur, but this signal will not be generated for the second
// incorrect abort 
assign maxLengthExceeded_p = (deaggregatorNs != deaggregatorCs) &&
                             (deaggregatorNs == RX_ERROR) && 
                             (deaggregatorCs == READ_RX_VECTOR1) &&
                             (muxRxLength > maxAllowedLength);
 

// Debug port
//////////////////////////////////////////////////////////////////////////////
assign debugPortDeaggregator = {maxLengthExceeded_p,
                                rxFormatMod[1],
                                rxFormatMod[0],
                                rxAggregation,
                                macPhyIfRxFifoEmpty,
                                macPhyIfRxFifoReadEn,
                                startRx,
                                stopRx_p,
                                ampduCorrectRcved_p,
                                ampduIncorrectRcved_p,
                                correctRcved_p,
                                rxCntrlReady,
                                rxVector2Valid_p,
                                rxDataError_p,
                                rxDataEnd_p,
                                rxDataStart_p
                                };

assign debugMCS = (rxFormatMod < 3'd2) ? {3'd0,rxLegRate}: rxMCS;

assign debugPortDeaggregator2 = {rxFormatMod,  // 3
                                 debugMCS,     // 7
                                 rxChBW,       // 2
                                 rxShortGI,    // 1
                                 rxAggregation,// 1
                                 rxSTBC};

assign debugPortDeaggregatorFsm = deaggregatorCs;

//////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////
// Display FSM State in string for RTL simulation waveform
//////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
// deaggregator FSM states displayed in a string to ease simulation and debug
always @*
begin
  case (deaggregatorCs)
                 IDLE  :  deaggregatorCs_str = {"IDLE"};
    COMP_FIFO_LATENCY  :  deaggregatorCs_str = {"COMP_FIFO_LATENCY"};
      READ_RX_VECTOR1  :  deaggregatorCs_str = {"READ_RX_VECTOR1"};
         TRIG_RX_CTRL  :  deaggregatorCs_str = {"TRIG_RX_CTRL"};
       RX_AMPDU_DELIM  :  deaggregatorCs_str = {"RX_AMPDU_DELIM"};
         WAIT_PHY_END  :  deaggregatorCs_str = {"WAIT_PHY_END"};
   WAIT_RX_CTRL_READY  :  deaggregatorCs_str = {"WAIT_RX_CTRL_READY"};
         READ_MP_FIFO  :  deaggregatorCs_str = {"READ_MP_FIFO"};
      READ_RX_VECTOR2  :  deaggregatorCs_str = {"READ_RX_VECTOR2"};
        VECTOR2_VALID  :  deaggregatorCs_str = {"VECTOR2_VALID"};
             RX_ERROR  :  deaggregatorCs_str = {"RX_ERROR"};
   endcase
end
`endif // RW_SIMU_ON


///////////////////////////////////////
// System Verilog Assertions
///////////////////////////////////////
`ifdef RW_ASSERT_ON
default clocking cb @(posedge macCoreRxClk); endclocking

//$rw_sva Checks if Deaggregator doesn't request data when MAC IF FIFO is empty.
property noReadWhenFifoEmpty_prop;
@(posedge macCoreRxClk)
    macPhyIfRxFifoEmpty |-> !macPhyIfRxFifoReadEn;
endproperty
noReadWhenFifoEmpty: assert property (disable iff (!macCoreClkHardRst_n) noReadWhenFifoEmpty_prop);

//$rw_sva Checks if Deaggregator doesn't trigger RX Controller with data valid.
property noDataWhenTrigger_prop;
@(posedge macCoreRxClk)
    rxDataStart_p |-> !rxDataValid;
endproperty
noDataWhenTrigger: assert property (disable iff (!macCoreClkHardRst_n) noDataWhenTrigger_prop);

//$rw_sva Checks if macPhyIfRxEnd_p is always generated after macPhyIfRxErr_p.
property macPhyIfEndAftermacPhyIfError_prop;
@(posedge macCoreRxClk)
    (macPhyIfRxErr_p ##1 !macPhyIfRxErr_p) |-> (macPhyIfRxEnd_p [*0:10] ##1 !macPhyIfRxEnd_p);
endproperty
macPhyIfEndAftermacPhyIfError: assert property (disable iff (!macCoreClkHardRst_n) macPhyIfEndAftermacPhyIfError_prop);

//$rw_sva Checks if macPhyIfRxEnd_p is always generated after rxDataError_p.
property macPhyIfEndAfterRxDataError_prop;
@(posedge macCoreRxClk)
    (rxDataError_p ##1 !rxDataError_p) |-> (macPhyIfRxEnd_p [*0:10] ##1 !macPhyIfRxEnd_p);
endproperty
macPhyIfEndAfterRxDataError: assert property (disable iff (!macCoreClkHardRst_n) macPhyIfEndAfterRxDataError_prop);

`endif // RW_ASSERT_ON


endmodule
