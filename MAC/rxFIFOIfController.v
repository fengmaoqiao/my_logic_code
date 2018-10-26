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
// Description      : RX FIFO Interface of rxController module
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
// Application Note :                                                       
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

 
module rxFIFOIfController( 
            ///////////////////////////////////////////////
            //$port_g Clock and reset
            ///////////////////////////////////////////////
            input wire         macCoreRxClk,            // MAC Core Receive Clock
            input wire         macCoreClkHardRst_n,     // Hard Reset of the MAC Core Clock domain 
                                                        // active low
            input wire         macCoreClkSoftRst_n,     // Soft Reset of the MAC Core Clock domain
                                                        // active low
            ///////////////////////////////////////////////
            //$port_g Timer unit
            ///////////////////////////////////////////////
            input wire [63:0]  tsf,                     // TSF

            ///////////////////////////////////////////////
            //$port_g Encryption Engine
            ///////////////////////////////////////////////
            input wire [7:0]   plainDataOut,            // Decrypted data for writing into RX FIFO
            input wire         plainOutDataValid,       // Decrypted data valid
            
            ///////////////////////////////////////////////
            //$port_g Key Search Engine
            ///////////////////////////////////////////////
            input wire         keyStorageValid_p,       // Key Storage Index Valid
            input wire [9:0]   rxKeyIndexReturn,        // Key Storage RAM Index

            ///////////////////////////////////////////////
            //$port_g Decryption FSM
            ///////////////////////////////////////////////
            input wire         rxDataSelect,            // Select data from Encryption Engine
            input wire         encrPadding4BytesFIFOEn, // Encryption padding 4 bytes enable
            input wire         encrPadding4BytesWriteEn,// Encryption padding 4 bytes write enable
            input wire         encrPadding2BytesFIFOEn, // Encryption padding 2 bytes enable
            
            ///////////////////////////////////////////////
            //$port_g MAC-PHY interface
            ///////////////////////////////////////////////
            input wire         macPhyIfRxEndForTiming_p,// Rx end for timing from MAC-PHY if. resynchronized
            input wire         macPhyIfRxErr_p,         // Rx error from MAC-PHY if. resynchronized

            ///////////////////////////////////////////////
            //$port_g A-MPDU Deaggregator
            ///////////////////////////////////////////////
            input wire         correctDelimiter,        // Indicate the correct Delimiter is found
            input wire         rxNDP,                   // Null Data Packet
            input wire [11:0]  rxLegLength,             // Legacy length
            input wire [ 3:0]  rxLegRate,               // Legacy rate
            input wire [19:0]  rxHTLength,              // HT length
            input wire [ 6:0]  rxMCS,                   // MCS
            input wire         rxPreType,               // Preamble type
            //
            input wire [ 2:0]  rxFormatMod,             // Format and modulation
            input wire [ 1:0]  rxChBW,                  // Channel bandwidth
            input wire         rxShortGI,               // Short Guard Interval
            input wire         rxSmoothing,             // Smoothing
            input wire         rxLSIGValid,             // L-SIG Valid
            input wire [ 1:0]  rxSTBC,                  // Space Time Block Coding
            input wire         rxSounding,              // Sounding
            input wire [ 1:0]  rxNumExtnSS,             // Number of Extension Spatial Streams
            input wire         rxAggregation,           // MPDU aggregate
            input wire         rxFecCoding,             // FEC Coding
            input wire [ 2:0]  rxReserved1,             // Reserved
            input wire [ 7:0]  rxAntennaSet,            // Antenna set
            input wire [ 2:0]  rxnSTS,                  // Number of STS       
            input wire         rxDynBW,                 // Dynamique Bandwidth 
            input wire         rxDozeNotAllowed,        // TXOP PS not allowed 
            input wire [ 8:0]  rxPartialAID,            // Partial AID         
            input wire [ 5:0]  rxGroupID,               // Group ID            
            input wire [ 7:0]  rxRSSI1,                 // RSSI for RxChain 1
            //
            input wire [ 7:0]  rxRSSI2,                 // RSSI for RxChain 2
            input wire [ 7:0]  rxRSSI3,                 // RSSI for RxChain 3
            input wire [ 7:0]  rxRSSI4,                 // RSSI for RxChain 4
            input wire [ 7:0]  rxReserved2,             // Reserved
            //
            input wire [ 7:0]  rxRCPI,                  // Receive Channel Power Indicator
            input wire [ 7:0]  rxEVM1,                  // Error Vector Magnitude for space time stream 1
            input wire [ 7:0]  rxEVM2,                  // Error Vector Magnitude for space time stream 2
            input wire [ 7:0]  rxEVM3,                  // Error Vector Magnitude for space time stream 3
            //
            input wire [ 7:0]  rxEVM4,                  // Error Vector Magnitude for space time stream 4
            input wire [ 7:0]  rxReserved3,             // Reserved
            input wire [ 7:0]  rxReserved4,             // Reserved
            input wire [ 7:0]  rxReserved5,             // Reserved
            input wire         rxVector1Valid_p,        // Rx vector 1 is available
            input wire         rxVector2Valid_p,        // Rx vector 2 is available
            
            input wire [ 7:0]  rxData,                  // Rx data read from MAC-PHY interface FIFO
            input wire         rxDataValid,             // Rx data is valid
            input wire         rxDataStart_p,           // Start of data flow
            input wire         rxDataEnd_p,             // End of data flow
            input wire         rxDataError_p,           // Rx data error (incorrect length)
            input wire         rxEndOfFrame_p,          // End of frame information
            input wire  [1:0]  rxAMPDUCnt,              // Counter incremented at each A-MPDU reception
            input wire  [5:0]  rxMPDUCnt,               // Count the number of MPDU detected

            ///////////////////////////////////////////////
            //$port_g RX Controller FSM
            ///////////////////////////////////////////////
            input wire         rxControlIdle,           // FSM in idle
            input wire [15:0]  rxMpduLength,            // Rx MPDU full length

            `ifdef RW_MPDU_AC
            input wire [15:0]  rxLengthSub,             // sub value according to encryption or not for the full rx pkt
            `else
            input wire [15:0]  payloadBufferLength,     // Payload length in buffers (frame body only)
            `endif
            input wire         frmSuccessfulRcved,      // Frame successful for RX DMA
            input wire         fcsErrorRcved,           // FCS Error
            input wire         phyErrorRcved,           // PHY Error
            input wire         undefErrorRcved,         // Undefined Error
            input wire         rxFIFOOverFlowError,     // RX FIFO overflow
            input wire [2:0]   decrStatus,              // Decryption status
            input wire         frmBody,                 // Frame body completion
            
            input wire         startMacHdr,             // Start of the MAC Header
            input wire         endPayload,              // End of the Payload
            input wire         discardFrm,              // End of frame with discard command
            input wire         acceptError_p,           // Pulse to indicate that writeTrailer to accept Error frame (others than FCS error)
            input wire         writeTrailer,            // Write trailer info

            input wire         padding4BytesFIFOEn,     // Padding 4 bytes enable
            input wire         padding4BytesWriteEn,    // Padding 4 bytes write enable
            input wire         padding2BytesFIFOEn,     // Padding 2 bytes enable
            
            output wire        rxFIFODone_p,            // RX FIFO status done
            output reg [3:0]   macHeaderCnt,            // MAC header counter
            output wire        endHeader,               // End Header
            output reg         endHeaderDone,           // End of the Header done
            output reg         rxEndOfFrame,            // RX end of frame holded
            output reg         txInProgressDly,         // Capture txInProgress on rxVector 1 valid pulse
            
            ///////////////////////////////////////////////
            //$port_g Frame decoder
            ///////////////////////////////////////////////
            input  wire [3:0]  subTypeFrame,            // Subtype
            input  wire [1:0]  typeFrame,               // Type
            input  wire        ctrlFrame,               // Control frame
            input  wire        addr1Match,              // ADDR1 match
            input  wire        acceptRcved,             // Accept current frame
            input  wire        bcMcRcved,               // Broadcast/Multicast
            output reg         rxBADly,                // Capture of rxBA

            ///////////////////////////////////////////////
            //$port_g Decrypt FSM
            ///////////////////////////////////////////////
            input wire         keyIndexCapture_p,       // Key Index returned by keySearch capture pulse

            ///////////////////////////////////////////////
            //$port_g RX FIFO
            ///////////////////////////////////////////////
            input wire         rxFIFOAlmostFull,        // RX FIFO is almost full
            
            output reg [3:0]   rxFIFOWrTag,             // RX Tag FIFO write data
            output reg [31:0]  rxFIFOWrData,            // RX FIFO write data
            output wire        rxFIFOWrite,             // RX FIFO write enable

            ///////////////////////////////////////////////
            //$port_g MacController
            ///////////////////////////////////////////////
            input wire         txInProgress,            // Tx is ongoing
            input wire         rxBA,                    // Indicate current tx frame is a single VHT Mpdu

            ///////////////////////////////////////////////
            //$port_g Backoff
            ///////////////////////////////////////////////
            input wire [2:0]   activeAC,                // Indicates which AC is currently selected.

            ///////////////////////////////////////////////
            //$port_g Control and Status Register
            ///////////////////////////////////////////////
            input wire         acceptErrorFrames,       // Accept error frames

            ///////////////////////////////////////////////
            //$port_g Interrupt Controller
            ///////////////////////////////////////////////
            output reg         rxFIFOOverFlow,          // RX FIFO overflow

            output reg  [15:0] debugPortrxFIFOCntrl     // Port for debug purpose
            );


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// MPDU Status information concatenation
wire [31:0] mpduStatusInfo;
wire        descriptorDoneRHMask;
reg         keySRamIndexV;
reg  [9:0]  rxKeyIndexReturnCapt;

// RX FIFO overflow condition
wire        rxFIFOOverFlowCond;

// RX Vector2 valid holded
reg         rxVector2Valid;

// correctDelimiter holded
reg         correctDelimiterDly;

// macPhyIfRxErrHold
reg         macPhyIfRxErrHold;

// acceptErrorHold
reg         acceptErrorHold;

// rxDataErrorHold
reg         rxDataErrorHold;

// TSF holded
reg [63:0]  tsfHold;

`ifndef RW_MPDU_AC
// End Header write pulse
wire        endHeaderWrite_p;
`endif

// 4 bytes counter
reg [3:0]   quadletCnt;
reg         quadletWrite;
reg         discardFrmHold_p;
reg         writeTrailer_ff1;
reg         writeTrailer_ff2;
reg         stopWrite;

// Mux data between Deaggregator or Encryption Engine
wire [7:0]  rxDataMux;
wire        rxDataValidMux;

// wire to caluclate rxFifo length in Quadlet for DMA
wire [15:0] rxMPDUFifoLength;
wire [15:0] rxMPDUFifoQuadletExtra;
wire [15:0] rxMPDUFifoQuadletLength;

reg [19:0]  rxHTLengthCapt; // HT length Captured on rxDataStart_p for the full size of ampdu in rxVector 1

reg         rxNDPInt; // Capture rxNDP when writeTrailler is high

`ifdef RW_MPDU_AC
reg [15:0]  rxMPDULengthCapt;   // length captured for each MPDU inside an ampdu
`endif

`ifdef RW_SIMU_ON
// String definition to display rxControl current state
reg [50*8:0] rxDataRate_str;
`endif // RW_SIMU_ON

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    debugPortrxFIFOCntrl <= 16'd0;
  else
  begin
    if(writeTrailer_ff1)
    begin
      debugPortrxFIFOCntrl <= {writeTrailer_ff1,
                               keySRamIndexV,
                               rxKeyIndexReturn,
                               rxFIFOWrTag};
    end
    else
    begin
      debugPortrxFIFOCntrl <= 16'h7FFF;
    end
  end
end

// TSF holded
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    tsfHold <= 64'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    tsfHold <= 64'b0;
  else if (macPhyIfRxEndForTiming_p)
    tsfHold <= tsf;
  else if (rxVector1Valid_p && rxAggregation)
    // Clear tsfHold on rxVector1Valid_p
    tsfHold <= 64'b0;
end

// Capture of rxHTLength  for the full size of ampdu
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxHTLengthCapt <= 20'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    rxHTLengthCapt <= 20'b0;
  else if (rxVector1Valid_p)
    // Captured rxHTLength on rxDataStart_p
    rxHTLengthCapt <= rxHTLength;
end

`ifdef RW_MPDU_AC
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxMPDULengthCapt <= 16'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    rxMPDULengthCapt <= 16'b0;
  else if (rxFIFOWrTag == 4'b0001) // start of header
  begin
    if(rxFormatMod >= 3'd2)
      // Captured rxHTLength
      rxMPDULengthCapt <= rxMpduLength;
    else
      // Captured  rxLegLength
      rxMPDULengthCapt <= {4'b0000,rxLegLength[11:0]};
  end
end
`endif


// rxVector2Valid holded
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxVector2Valid <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    rxVector2Valid <= 1'b0;
  else if (rxVector2Valid_p)
    rxVector2Valid <=  1'b1;
end

// macPhyIfRxErr_p holded when not rxVector2Valid : avoid stucking in WRITE_STATUS state.
// if rxVector2Valid  then ignore macPhyIfRxErr_p and finish the writeTrailer
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macPhyIfRxErrHold <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    macPhyIfRxErrHold <= 1'b0;
  else if (macPhyIfRxErr_p && !rxVector2Valid)
    macPhyIfRxErrHold <=  1'b1;
end

// acceptError_p holded when not rxVector2Valid : avoid stucking in WRITE_STATUS state.
// if rxVector2Valid  then ignore acceptError_p and finish the writeTrailer
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    acceptErrorHold <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    acceptErrorHold <= 1'b0;
  else if (acceptError_p && !rxVector2Valid)
    acceptErrorHold <=  1'b1;
end

// rxDataErro_p holded when not rxVector2Valid : avoid stucking in WRITE_STATUS state.
// if rxVector2Valid  then ignore rxDataErro_p and finish the writeTrailer
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxDataErrorHold <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    rxDataErrorHold <= 1'b0;
  else if (rxDataError_p && !rxVector2Valid)
    rxDataErrorHold <=  1'b1;
end

// correctDelimiterDly holded
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    correctDelimiterDly <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxFIFODone_p == 1'b1) || (rxControlIdle == 1'b1))
    correctDelimiterDly <= 1'b0;
  else if ((correctDelimiterDly == 1'b0) && (rxControlIdle == 1'b0)) 
    correctDelimiterDly <=  correctDelimiter;
end


// rxEndOfFrame holded
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxEndOfFrame <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    rxEndOfFrame <= 1'b0;
  else if (rxEndOfFrame_p)
    rxEndOfFrame <=  1'b1;
end


always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxNDPInt <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    rxNDPInt <= 1'b0;
  else if (writeTrailer && !writeTrailer_ff1)
    rxNDPInt <=  rxNDP;
end

// writeTrailer delayed
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    writeTrailer_ff1 <= 1'b0;
    writeTrailer_ff2 <= 1'b0;
  end
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxFIFODone_p == 1'b1) || (rxControlIdle == 1'b1))
  begin
    writeTrailer_ff1 <= 1'b0;
    writeTrailer_ff2 <= 1'b0;
  end
  else
  begin
    writeTrailer_ff1 <= (writeTrailer && (correctDelimiterDly || rxVector2Valid || macPhyIfRxErrHold || acceptErrorHold || rxDataErrorHold));
    writeTrailer_ff2 <= writeTrailer_ff1;
  end
end


// macHeaderCnt for end Header Tag
// with rx FLow: start counting only after transmiting rxMPDUFifoQuadletLength
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macHeaderCnt <= 4'h0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    macHeaderCnt <= 4'h0;
  else if ((macHeaderCnt < 4'hb) && rxFIFOWrite && !rxFIFOOverFlow && (rxFIFOWrTag != 4'b1010))
    macHeaderCnt <= macHeaderCnt + 4'h1;
end


// end Header control
`ifdef RW_MPDU_AC
always @(*)
begin
  endHeaderDone = !startMacHdr;
end
`else
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    endHeaderDone <= 1'b0;
  else if ((macCoreClkSoftRst_n == 1'b0) || (rxControlIdle == 1'b1))
    endHeaderDone <= 1'b0;
  else if (endHeaderWrite_p)
    endHeaderDone <= 1'b1;
end
`endif

// End of Header:
// frame accepted  : set on 12th quadlets
// frame discarded : set on 4th quadlets or on 12th quadlets for correct DMA behavior
`ifdef RW_MPDU_AC
assign endHeader = 1'b1; 
`else
assign endHeader = ((acceptRcved || acceptErrorFrames) && (((macHeaderCnt == 4'ha) && rxFIFOWrite)    || 
                                    ((macHeaderCnt == 4'hb) && !endHeaderDone && !endHeaderWrite_p))) ||
                   (!acceptRcved && (macHeaderCnt == 4'ha) && !endHeaderDone     && 
                                    (quadletCnt == 4'h3) && rxDataValid)         ||
                   ((macHeaderCnt == 4'h3) && !acceptRcved && ctrlFrame);

assign endHeaderWrite_p = (rxFIFOWrTag == 4'b0010) && rxFIFOWrite;
`endif

// rxFIFOWrTag control
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxFIFOWrTag <= 4'b1100;
  else if (macCoreClkSoftRst_n == 1'b0)
    rxFIFOWrTag <= 4'b1100;
  else if (rxDataStart_p)
    // MPDU Lenght
    rxFIFOWrTag <= 4'b1010;
  else if (discardFrm || discardFrmHold_p || rxFIFOOverFlowCond)
    // End of frame with discard pattern
    rxFIFOWrTag <= 4'b1111;
  else if (startMacHdr && !rxFIFOWrite && (macHeaderCnt == 4'h0))
    // Start of Header
    rxFIFOWrTag <= 4'b0001;
  `ifndef RW_MPDU_AC
  else if (endHeader)
    // End of Header
    rxFIFOWrTag <= 4'b0010;
  `endif
  else if (endPayload)
    // End of payload
    rxFIFOWrTag <= 4'b0101;
  else if ((writeTrailer_ff1 && (quadletCnt == 4'h9)) || rxFIFODone_p)
    // End of frame with save pattern
    rxFIFOWrTag <= 4'b0000;
  else
    // Intermediate Header or payload
    rxFIFOWrTag <= 4'b1100;
end


// Mux data between Deaggregator or Encryption Engine
assign rxDataMux      = 
`ifdef ENCRYPTION
                        (rxDataSelect) ? plainDataOut : 
`endif
                        rxData;
assign rxDataValidMux = 
`ifdef ENCRYPTION
                        (rxDataSelect) ? plainOutDataValid : 
`endif
                        rxDataValid;

// Convert MPDU length + trailler into FIFO Quadtlet Length
assign rxMPDUFifoLength        = (rxFormatMod >= 3'd2) ? rxMpduLength : {4'b0000,rxLegLength[11:0]};
assign rxMPDUFifoQuadletExtra  = (rxMPDUFifoLength[1:0] != 2'd0) ? 16'd11 : 16'd10;
assign rxMPDUFifoQuadletLength = {2'd0,rxMPDUFifoLength[15:2]} + rxMPDUFifoQuadletExtra;

// rxFIFOWrData control
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxFIFOWrData <= 32'h0;
  else if (macCoreClkSoftRst_n == 1'b0)
    rxFIFOWrData <= 32'h0;
  else
  begin
    // FSM in idle
    if (rxControlIdle && !rxDataStart_p)
      rxFIFOWrData <= 32'h0;
    // Captured rxMPDUFifoQuadletLength
    else if(rxDataStart_p)
      rxFIFOWrData <= {16'h0,rxMPDUFifoQuadletLength[15:0]};
    // RX FIFO Overflow condition
    else if (rxFIFOOverFlowCond)
      rxFIFOWrData <= mpduStatusInfo;
    // 4 bytes padding or frame discard
    else if (padding4BytesFIFOEn || (discardFrm && (quadletCnt == 4'h0)))
      rxFIFOWrData <= 32'h0;
    `ifdef ENCRYPTION
    // 4 bytes encryption padding
    else if (encrPadding4BytesFIFOEn)
      rxFIFOWrData <= 32'h0;
    `endif
    // Trailer information
    else if (writeTrailer_ff1)
    begin
      case (quadletCnt)
        4'h0:
        begin
        `ifdef RW_MPDU_AC
          rxFIFOWrData[15:0] <= rxMPDULengthCapt - rxLengthSub;
          if (rxAggregation)
            rxFIFOWrData[31:16] <= {rxAMPDUCnt,rxMPDUCnt,8'b0};
          else
            rxFIFOWrData[31:16] <= 16'b0;
        `else
          rxFIFOWrData <= {16'b0, payloadBufferLength};
        `endif
        end
        4'h1: rxFIFOWrData <= tsfHold[31:0];
        4'h2: rxFIFOWrData <= tsfHold[63:32];
           4'h3: rxFIFOWrData <= {rxHTLengthCapt[15:0], rxLegRate, rxLegLength};
           4'h4: rxFIFOWrData <= {rxDozeNotAllowed, rxDynBW, rxFecCoding, rxAggregation, 
                                  rxNumExtnSS, rxSounding, rxLSIGValid, rxnSTS,
                                  rxChBW, rxFormatMod, rxPreType, rxMCS, rxSmoothing, 
                                  rxSTBC, rxShortGI, rxHTLengthCapt[19:16]};
           4'h5: rxFIFOWrData <= {rxRSSI1, 1'b0, rxGroupID, rxPartialAID, rxAntennaSet};
           4'h6: rxFIFOWrData <= {8'b0, rxRSSI4, rxRSSI3, rxRSSI2};
           4'h7: rxFIFOWrData <= {rxEVM3, rxEVM2, rxEVM1, rxRCPI};
           4'h8: rxFIFOWrData <= {24'b0, rxEVM4};
           4'h9: rxFIFOWrData <= mpduStatusInfo;
        
        // Disable case default state for block coverage
        // pragma coverage block = off
        default : rxFIFOWrData <= rxFIFOWrData;
        // pragma coverage block = on
      endcase
    end
    // Normal operation
    if (rxDataValidMux && !writeTrailer_ff1 && !rxFIFOOverFlowCond)
    begin
      case (quadletCnt[1:0])
        2'h0    : rxFIFOWrData        <= {24'b0, rxDataMux};
        2'h1    : rxFIFOWrData[15:8]  <= rxDataMux;
        2'h2    : rxFIFOWrData[23:16] <= rxDataMux;
        default : rxFIFOWrData[31:24] <= rxDataMux;
      endcase
      `ifndef RW_MPDU_AC
      // Patching the Old MPDU format with the new rxMPDUFifoQuadletLength sending at the begining of a reception
      if(startMacHdr && !rxFIFOWrite && (macHeaderCnt == 4'h0))
      begin
        rxFIFOWrData[15:0] <= 16'h0;
      end
      `endif
    end
  end
end

// rxFIFOWrite control
assign rxFIFOWrite = rxFIFOOverFlow || (writeTrailer_ff2 && (acceptErrorHold || macPhyIfRxErrHold || rxDataErrorHold)) ||
                     (!rxFIFOOverFlowError && !stopWrite &&
                     (writeTrailer_ff2 || quadletWrite || 
`ifdef ENCRYPTION
                      encrPadding4BytesWriteEn ||
`endif
                      padding4BytesWriteEn || discardFrmHold_p));


// quadletCnt control
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    quadletCnt <= 4'h0;
  else if (macCoreClkSoftRst_n == 1'b0)
    quadletCnt <= 4'h0;
  // Initialization phase
  else if (rxDataStart_p)
    `ifdef RW_MPDU_AC
    quadletCnt <= 4'h0;
    `else
    quadletCnt <= 4'h2;
    `endif
  // Set counter when padding2BytesFIFOEn is active
  else if (padding2BytesFIFOEn)
  begin
    if (!frmBody)
    begin
      if (quadletCnt == 4'h0)
        quadletCnt <= 4'h2;
      else
        quadletCnt <= 4'h0;
    end
    else
      quadletCnt <= 4'h0;
  end
  // Clear counter
  else if (padding4BytesFIFOEn || rxControlIdle || (quadletCnt == 4'hA))
    quadletCnt <= 4'h0;
  `ifdef ENCRYPTION
  else if (encrPadding4BytesFIFOEn || encrPadding2BytesFIFOEn)
    quadletCnt <= 4'h0;
  `endif
  // Trailer phase -> increment until end of writing
  else if (writeTrailer_ff1 &&
    (rxAggregation || phyErrorRcved || rxFIFOOverFlowError || acceptErrorHold || macPhyIfRxErrHold || rxDataErrorHold ||
    (!rxAggregation && ((quadletCnt < 4'h6) || rxEndOfFrame || rxEndOfFrame_p))))
    quadletCnt <= quadletCnt + 4'h1;
  // Normal operation
  else if (rxDataValidMux && !writeTrailer_ff1)
  begin
    if (quadletCnt == 4'h3)
      quadletCnt <= 4'h0;
    else
      quadletCnt <= quadletCnt + 4'h1;
  end
end

// quadletWrite is generated :
//   when quadletCnt=3 meaning that 4 data has been sampled or 
//   when padding2BytesFIFOEn is active during frmBody step
//   when encrPadding2BytesFIFOEn is active
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    quadletWrite <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    quadletWrite <= 1'b0;
  else if(rxDataStart_p)
    quadletWrite <= 1'b1;
  else
    quadletWrite <= rxDataValidMux && ((quadletCnt == 4'h3) || 
`ifdef ENCRYPTION
                    encrPadding2BytesFIFOEn ||
`endif
                    (padding2BytesFIFOEn && ((quadletCnt == 4'h1) || frmBody)));
end

// stopWrite is generated when quadletCnt=6 during write trailer step
// until rxEndOfFrame_p is received
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    stopWrite <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    stopWrite <= 1'b0;
  else if (!(phyErrorRcved || rxFIFOOverFlowError) &&
    (!rxAggregation && (quadletCnt == 4'h6) && rxFIFOWrite) &&
    !(rxEndOfFrame || rxEndOfFrame_p))
    stopWrite <= 1'b1;
  else if (rxControlIdle || rxEndOfFrame_p)
    stopWrite <= 1'b0;
end


// discardFrmHold generation
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    discardFrmHold_p <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    discardFrmHold_p <= 1'b0;
  else if (discardFrmHold_p && rxFIFOWrite)
    discardFrmHold_p <= 1'b0;
  else if (discardFrm && (rxFIFOWrTag != 4'hF))
    discardFrmHold_p <= 1'b1;
end

// rxFIFODone_p control
assign rxFIFODone_p   = (quadletCnt == 4'hA) ||
                        (discardFrmHold_p && rxFIFOWrite);
// MPDU Status information
assign mpduStatusInfo = {(rxNDPInt ? 4'h0:subTypeFrame), (rxNDPInt ? 2'h0 : typeFrame), (keySRamIndexV && !rxNDPInt), rxKeyIndexReturnCapt,
                         descriptorDoneRHMask, rxNDPInt || frmSuccessfulRcved, activeAC[1:0], bcMcRcved,
                         !addr1Match, fcsErrorRcved, phyErrorRcved, undefErrorRcved,
                         (rxFIFOOverFlowError || rxFIFOOverFlowCond),
                         decrStatus, 
                         (frmSuccessfulRcved && txInProgressDly),
                         rxVector2Valid || rxVector2Valid_p};

assign descriptorDoneRHMask = (rxFIFOWrTag == 4'b1111) ? 1'b0 : 1'b1;

always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    keySRamIndexV        <= 1'b0;
    rxKeyIndexReturnCapt <= 10'b0;
  end
  else if ((macCoreClkSoftRst_n == 1'b0) || rxControlIdle)
  begin
    keySRamIndexV        <= 1'b0;
    rxKeyIndexReturnCapt <= 10'b0;
  end
  else if (keyIndexCapture_p)
  begin
    keySRamIndexV        <= keyStorageValid_p;
    rxKeyIndexReturnCapt <= rxKeyIndexReturn;
  end
end

// txInProgressDly and rxBADly generation
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    txInProgressDly    <= 1'b0;
    rxBADly <= 1'b0;
  end
  else if (macCoreClkSoftRst_n == 1'b0)
  begin
    txInProgressDly    <= 1'b0;
    rxBADly <= 1'b0;
  end
  else if (rxVector1Valid_p)
  begin
    txInProgressDly    <= txInProgress;
    if (txInProgress)
    begin
      rxBADly <= rxBA;
    end
  end
  else if(rxFIFODone_p)
  begin
    txInProgressDly    <= 1'b0;
    rxBADly            <= 1'b0;
  end
end

// rxFIFOOverFlow generation
always @ (posedge macCoreRxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxFIFOOverFlow <= 1'b0;
  else if (macCoreClkSoftRst_n == 1'b0)
    rxFIFOOverFlow <= 1'b0;
  else
    rxFIFOOverFlow <= rxFIFOOverFlowCond;
end

// rxFIFOOverFlow condition when FIFO will be full and we are not writing 
// last qualet of the trailer
assign rxFIFOOverFlowCond = rxFIFOWrite && rxFIFOAlmostFull && !quadletCnt[3];


`ifdef RW_SIMU_ON
// String definition to display rxRate

always @(*)
begin
  if ((rxFormatMod == 3'd2) || (rxFormatMod == 3'd3))
  begin
    if(rxChBW == 0)
    begin
      if(rxShortGI)
      begin
        case (rxMCS)
               0  : rxDataRate_str = "HT 7.2 Mbps"   ;
               1  : rxDataRate_str = "HT 14.4 Mbps"  ;
               2  : rxDataRate_str = "HT 21.7 Mbps"  ;
               3  : rxDataRate_str = "HT 28.9 Mbps"  ;
               4  : rxDataRate_str = "HT 43.3 Mbps"  ;
               5  : rxDataRate_str = "HT 57.8 Mbps"  ;
               6  : rxDataRate_str = "HT 65 Mbps"    ;
               7  : rxDataRate_str = "HT 72.2 Mbps"  ;
               8  : rxDataRate_str = "HT 14.4 Mbps"  ;
               9  : rxDataRate_str = "HT 28.9 Mbps"  ;
               10 : rxDataRate_str = "HT 43.3 Mbps"  ;
               11 : rxDataRate_str = "HT 57.8 Mbps"  ;
               12 : rxDataRate_str = "HT 86.7 Mbps"  ;
               13 : rxDataRate_str = "HT 115.6 Mbps" ;
               14 : rxDataRate_str = "HT 130 Mbps"   ;
               15 : rxDataRate_str = "HT 144.4 Mbps" ;
               16 : rxDataRate_str = "HT 21.7 Mbps"  ;
               17 : rxDataRate_str = "HT 43.3 Mbps"  ;
               18 : rxDataRate_str = "HT 65 Mbps"    ;
               19 : rxDataRate_str = "HT 86.7 Mbps"  ;
               20 : rxDataRate_str = "HT 130 Mbps"   ;
               21 : rxDataRate_str = "HT 173.3 Mbps" ;
               22 : rxDataRate_str = "HT 195 Mbps"   ;
               23 : rxDataRate_str = "HT 216.7 Mbps" ;
               24 : rxDataRate_str = "HT 28.9  Mbps" ;
               25 : rxDataRate_str = "HT 57.8 Mbps"  ;
               26 : rxDataRate_str = "HT 86.7 Mbps"  ;
               27 : rxDataRate_str = "HT 115.6 Mbps" ;
               28 : rxDataRate_str = "HT 173.3 Mbps" ;
               29 : rxDataRate_str = "HT 231.1 Mbps" ;
               30 : rxDataRate_str = "HT 260 Mbps"   ;
               31 : rxDataRate_str = "HT 288.9 Mbps" ;
               32 : rxDataRate_str = "HT 6.7 Mbps"   ;
               33 : rxDataRate_str = "HT 43.3 Mbps"  ;
               34 : rxDataRate_str = "HT 57.8 Mbps"  ;
               35 : rxDataRate_str = "HT 72.2 Mbps"  ;
               36 : rxDataRate_str = "HT 65 Mbps"    ;
               37 : rxDataRate_str = "HT 86.7 Mbps"  ;
               38 : rxDataRate_str = "HT 108.3 Mbps" ;
               39 : rxDataRate_str = "HT 57.8 Mbps"  ;
               40 : rxDataRate_str = "HT 72.2 Mbps"  ;
               41 : rxDataRate_str = "HT 72.2 Mbps"  ;
               42 : rxDataRate_str = "HT 86.7 Mbps"  ;
               43 : rxDataRate_str = "HT 101.1 Mbps" ;
               44 : rxDataRate_str = "HT 101.1 Mbps" ;
               45 : rxDataRate_str = "HT 115.6 Mbps" ;
               46 : rxDataRate_str = "HT 86.7 Mbps"  ;
               47 : rxDataRate_str = "HT 108.3 Mbps" ;
               48 : rxDataRate_str = "HT 108.3 Mbps" ;
               49 : rxDataRate_str = "HT 130 Mbps"   ;
               50 : rxDataRate_str = "HT 151.7 Mbps" ;
               51 : rxDataRate_str = "HT 151.7 Mbps" ;
               52 : rxDataRate_str = "HT 173.3 Mbps" ;
               53 : rxDataRate_str = "HT 72.2 Mbps"  ;
               54 : rxDataRate_str = "HT 86.7 Mbps"  ;
               55 : rxDataRate_str = "HT 101.1 Mbps" ;
               56 : rxDataRate_str = "HT 86.7 Mbps"  ;
               57 : rxDataRate_str = "HT 101.1 Mbps" ;
               58 : rxDataRate_str = "HT 115.6 Mbps" ;
               59 : rxDataRate_str = "HT 130 Mbps"   ;
               60 : rxDataRate_str = "HT 115.5 Mbps" ;
               61 : rxDataRate_str = "HT 130 Mbps"   ;
               62 : rxDataRate_str = "HT 144.4 Mbps" ;
               63 : rxDataRate_str = "HT 144.4 Mbps" ;
               64 : rxDataRate_str = "HT 158.9 Mbps" ;
               65 : rxDataRate_str = "HT 108.3 Mbps" ;
               66 : rxDataRate_str = "HT 130 Mbps"   ;
               67 : rxDataRate_str = "HT 151.7 Mbps" ;
               68 : rxDataRate_str = "HT 130 Mbps"   ;
               69 : rxDataRate_str = "HT 151.7 Mbps" ;
               70 : rxDataRate_str = "HT 173.3 Mbps" ;
               71 : rxDataRate_str = "HT 195 Mbps"   ;
               72 : rxDataRate_str = "HT 173.3 Mbps" ;
               73 : rxDataRate_str = "HT 195 Mbps"   ;
               74 : rxDataRate_str = "HT 216.7 Mbps" ;
               75 : rxDataRate_str = "HT 216.7 Mbps" ;
               76 : rxDataRate_str = "HT 238.3 Mbps" ;
          default : rxDataRate_str = "Error 666"     ;
        endcase
      end
      else
      begin
        case (rxMCS)
               0  : rxDataRate_str = "HT 6.5 Mbps"   ;         
               1  : rxDataRate_str = "HT 13 Mbps"    ;         
               2  : rxDataRate_str = "HT 19.5 Mbps"  ;         
               3  : rxDataRate_str = "HT 26 Mbps"    ;         
               4  : rxDataRate_str = "HT 39 Mbps"    ;         
               5  : rxDataRate_str = "HT 52 Mbps"    ;         
               6  : rxDataRate_str = "HT 58.5 Mbps"  ;         
               7  : rxDataRate_str = "HT 65 Mbps"    ;         
               8  : rxDataRate_str = "HT 13 Mbps"    ;         
               9  : rxDataRate_str = "HT 26 Mbps"    ;         
               10 : rxDataRate_str = "HT 39 Mbps"    ;         
               11 : rxDataRate_str = "HT 52 Mbps"    ;         
               12 : rxDataRate_str = "HT 78 Mbps"    ;         
               13 : rxDataRate_str = "HT 104 Mbps"   ;         
               14 : rxDataRate_str = "HT 117 Mbps"   ;         
               15 : rxDataRate_str = "HT 130 Mbps"   ;         
               16 : rxDataRate_str = "HT 19.5 Mbps"  ;         
               17 : rxDataRate_str = "HT 39 Mbps"    ;         
               18 : rxDataRate_str = "HT 58.5 Mbps"  ;         
               19 : rxDataRate_str = "HT 78 Mbps"    ;         
               20 : rxDataRate_str = "HT 117 Mbps"   ;         
               21 : rxDataRate_str = "HT 156 Mbps"   ;         
               22 : rxDataRate_str = "HT 175.5 Mbps" ;         
               23 : rxDataRate_str = "HT 195 Mbps"   ;         
               24 : rxDataRate_str = "HT 26 Mbps"    ;         
               25 : rxDataRate_str = "HT 52 Mbps"    ;         
               26 : rxDataRate_str = "HT 78 Mbps"    ;         
               27 : rxDataRate_str = "HT 104 Mbps"   ;         
               28 : rxDataRate_str = "HT 156 Mbps"   ;         
               29 : rxDataRate_str = "HT 208 Mbps"   ;         
               30 : rxDataRate_str = "HT 234 Mbps"   ;         
               31 : rxDataRate_str = "HT 260 Mbps"   ;         
               32 : rxDataRate_str = "HT 6   Mbps"   ;         
               33 : rxDataRate_str = "HT 39 Mbps"    ;         
               34 : rxDataRate_str = "HT 52 Mbps"    ;         
               35 : rxDataRate_str = "HT 65 Mbps"    ;         
               36 : rxDataRate_str = "HT 58.5 Mbps"  ;         
               37 : rxDataRate_str = "HT 78 Mbps"    ;         
               38 : rxDataRate_str = "HT 97.5 Mbps"  ;         
               39 : rxDataRate_str = "HT 52 Mbps"    ;         
               40 : rxDataRate_str = "HT 65 Mbps"    ;         
               41 : rxDataRate_str = "HT 65 Mbps"    ;         
               42 : rxDataRate_str = "HT 78 Mbps"    ;         
               43 : rxDataRate_str = "HT 91 Mbps"    ;         
               44 : rxDataRate_str = "HT 91 Mbps"    ;         
               45 : rxDataRate_str = "HT 104 Mbps"   ;            
               46 : rxDataRate_str = "HT 78 Mbps"    ;         
               47 : rxDataRate_str = "HT 97.5 Mbps"  ;         
               48 : rxDataRate_str = "HT 97.5 Mbps"  ;         
               49 : rxDataRate_str = "HT 117 Mbps"   ;         
               50 : rxDataRate_str = "HT 136.5 Mbps" ;         
               51 : rxDataRate_str = "HT 136.5 Mbps" ;         
               52 : rxDataRate_str = "HT 156 Mbps"   ;         
               53 : rxDataRate_str = "HT 65 Mbps"    ;         
               54 : rxDataRate_str = "HT 78 Mbps"    ;         
               55 : rxDataRate_str = "HT 91 Mbps"    ;         
               56 : rxDataRate_str = "HT 78 Mbps"    ;         
               57 : rxDataRate_str = "HT 91 Mbps"    ;         
               58 : rxDataRate_str = "HT 104 Mbps"   ;         
               59 : rxDataRate_str = "HT 117 Mbps"   ;         
               60 : rxDataRate_str = "HT 104 Mbps"   ;         
               61 : rxDataRate_str = "HT 117 Mbps"   ;         
               62 : rxDataRate_str = "HT 130 Mbps"   ;         
               63 : rxDataRate_str = "HT 130 Mbps"   ;         
               64 : rxDataRate_str = "HT 143 Mbps"   ;         
               65 : rxDataRate_str = "HT 97.5 Mbps"  ;         
               66 : rxDataRate_str = "HT 117 Mbps"   ;         
               67 : rxDataRate_str = "HT 136.5 Mbps" ;         
               68 : rxDataRate_str = "HT 117 Mbps"   ;         
               69 : rxDataRate_str = "HT 136.5 Mbps" ;         
               70 : rxDataRate_str = "HT 156 Mbps"   ;         
               71 : rxDataRate_str = "HT 175.5 Mbps" ;         
               72 : rxDataRate_str = "HT 156 Mbps"   ;         
               73 : rxDataRate_str = "HT 175.5 Mbps" ;         
               74 : rxDataRate_str = "HT 195 Mbps"   ;         
               75 : rxDataRate_str = "HT 195 Mbps"   ;         
               76 : rxDataRate_str = "HT 214.5 Mbps" ;         
          default : rxDataRate_str = "Error 666"     ;
        endcase
      end
    end
    else
    begin
      if(rxShortGI)
      begin
        case (rxMCS)
               0  : rxDataRate_str = "40MHz HT 15 Mbps"    ;
               1  : rxDataRate_str = "40MHz HT 30 Mbps"    ;
               2  : rxDataRate_str = "40MHz HT 45 Mbps"    ;
               3  : rxDataRate_str = "40MHz HT 60 Mbps"    ;
               4  : rxDataRate_str = "40MHz HT 90 Mbps"    ;
               5  : rxDataRate_str = "40MHz HT 120 Mbps"   ; 
               6  : rxDataRate_str = "40MHz HT 135 Mbps"   ; 
               7  : rxDataRate_str = "40MHz HT 150 Mbps"   ; 
               8  : rxDataRate_str = "40MHz HT 30 Mbps"    ;
               9  : rxDataRate_str = "40MHz HT 60 Mbps"    ;
               10 : rxDataRate_str = "40MHz HT 90 Mbps"    ;
               11 : rxDataRate_str = "40MHz HT 120 Mbps"   ; 
               12 : rxDataRate_str = "40MHz HT 180 Mbps"   ; 
               13 : rxDataRate_str = "40MHz HT 240 Mbps"   ; 
               14 : rxDataRate_str = "40MHz HT 270 Mbps"   ; 
               15 : rxDataRate_str = "40MHz HT 300 Mbps"   ; 
               16 : rxDataRate_str = "40MHz HT 45 Mbps"    ;
               17 : rxDataRate_str = "40MHz HT 90 Mbps"    ;
               18 : rxDataRate_str = "40MHz HT 135 Mbps"   ; 
               19 : rxDataRate_str = "40MHz HT 180 Mbps"   ; 
               20 : rxDataRate_str = "40MHz HT 270 Mbps"   ; 
               21 : rxDataRate_str = "40MHz HT 360 Mbps"   ; 
               22 : rxDataRate_str = "40MHz HT 405 Mbps"   ; 
               23 : rxDataRate_str = "40MHz HT 450 Mbps"   ; 
               24 : rxDataRate_str = "40MHz HT 60 Mbps"    ; 
               25 : rxDataRate_str = "40MHz HT 120 Mbps"   ; 
               26 : rxDataRate_str = "40MHz HT 180 Mbps"   ; 
               27 : rxDataRate_str = "40MHz HT 240 Mbps"   ; 
               28 : rxDataRate_str = "40MHz HT 360 Mbps"   ; 
               29 : rxDataRate_str = "40MHz HT 480 Mbps"   ; 
               30 : rxDataRate_str = "40MHz HT 540 Mbps"   ; 
               31 : rxDataRate_str = "40MHz HT 600 Mbps"   ; 
               32 : rxDataRate_str = "40MHz HT 6.7 Mbps"   ; 
               33 : rxDataRate_str = "40MHz HT 90  Mbps"   ;
               34 : rxDataRate_str = "40MHz HT 120 Mbps"   ;
               35 : rxDataRate_str = "40MHz HT 150 Mbps"   ;
               36 : rxDataRate_str = "40MHz HT 135 Mbps"   ;
               37 : rxDataRate_str = "40MHz HT 180 Mbps"   ;
               38 : rxDataRate_str = "40MHz HT 225 Mbps"   ;
               39 : rxDataRate_str = "40MHz HT 120 Mbps"   ;
               40 : rxDataRate_str = "40MHz HT 150 Mbps"   ;
               41 : rxDataRate_str = "40MHz HT 150 Mbps"   ;
               42 : rxDataRate_str = "40MHz HT 180 Mbps"   ;
               43 : rxDataRate_str = "40MHz HT 210 Mbps"   ;
               44 : rxDataRate_str = "40MHz HT 210 Mbps"   ;
               45 : rxDataRate_str = "40MHz HT 240 Mbps"   ;
               46 : rxDataRate_str = "40MHz HT 180 Mbps"   ;
               47 : rxDataRate_str = "40MHz HT 225 Mbps"   ;
               48 : rxDataRate_str = "40MHz HT 225 Mbps"   ;
               49 : rxDataRate_str = "40MHz HT 270 Mbps"   ;
               50 : rxDataRate_str = "40MHz HT 315 Mbps"   ;
               51 : rxDataRate_str = "40MHz HT 315 Mbps"   ;
               52 : rxDataRate_str = "40MHz HT 360 Mbps"   ;
               53 : rxDataRate_str = "40MHz HT 150 Mbps"   ;
               54 : rxDataRate_str = "40MHz HT 180 Mbps"   ;
               55 : rxDataRate_str = "40MHz HT 210 Mbps"   ;
               56 : rxDataRate_str = "40MHz HT 180 Mbps"   ;
               57 : rxDataRate_str = "40MHz HT 210 Mbps"   ;
               58 : rxDataRate_str = "40MHz HT 240 Mbps"   ;
               59 : rxDataRate_str = "40MHz HT 270 Mbps"   ;
               60 : rxDataRate_str = "40MHz HT 240 Mbps"   ;
               61 : rxDataRate_str = "40MHz HT 270 Mbps"   ;
               62 : rxDataRate_str = "40MHz HT 300 Mbps"   ;
               63 : rxDataRate_str = "40MHz HT 300 Mbps"   ;
               64 : rxDataRate_str = "40MHz HT 330 Mbps"   ;
               65 : rxDataRate_str = "40MHz HT 225 Mbps"   ;
               66 : rxDataRate_str = "40MHz HT 270 Mbps"   ;
               67 : rxDataRate_str = "40MHz HT 315 Mbps"   ;
               68 : rxDataRate_str = "40MHz HT 270 Mbps"   ;
               69 : rxDataRate_str = "40MHz HT 315 Mbps"   ;
               70 : rxDataRate_str = "40MHz HT 360 Mbps"   ;
               71 : rxDataRate_str = "40MHz HT 405 Mbps"   ;
               72 : rxDataRate_str = "40MHz HT 360 Mbps"   ;
               73 : rxDataRate_str = "40MHz HT 405 Mbps"   ;
               74 : rxDataRate_str = "40MHz HT 450 Mbps"   ;
               75 : rxDataRate_str = "40MHz HT 450 Mbps"   ;
               76 : rxDataRate_str = "40MHz HT 495 Mbps"   ;
          default : rxDataRate_str = "Error 666"           ;
        endcase
      end
      else
      begin
        case (rxMCS)
               0  : rxDataRate_str = "40MHz HT 13.5 Mbps"  ;
               1  : rxDataRate_str = "40MHz HT 27 Mbps"    ;
               2  : rxDataRate_str = "40MHz HT 40.5 Mbps"  ;
               3  : rxDataRate_str = "40MHz HT 54 Mbps"    ;
               4  : rxDataRate_str = "40MHz HT 81 Mbps"    ;
               5  : rxDataRate_str = "40MHz HT 108 Mbps"   ;
               6  : rxDataRate_str = "40MHz HT 121.5 Mbps" ;
               7  : rxDataRate_str = "40MHz HT 135 Mbps"   ;
               8  : rxDataRate_str = "40MHz HT 27 Mbps"    ;
               9  : rxDataRate_str = "40MHz HT 54 Mbps"    ;
               10 : rxDataRate_str = "40MHz HT 81 Mbps"    ;
               11 : rxDataRate_str = "40MHz HT 108 Mbps"   ;
               12 : rxDataRate_str = "40MHz HT 162 Mbps"   ;
               13 : rxDataRate_str = "40MHz HT 216 Mbps"   ;
               14 : rxDataRate_str = "40MHz HT 243 Mbps"   ;
               15 : rxDataRate_str = "40MHz HT 270 Mbps"   ;
               16 : rxDataRate_str = "40MHz HT 40.5 Mbps"  ;
               17 : rxDataRate_str = "40MHz HT 81 Mbps"    ;
               18 : rxDataRate_str = "40MHz HT 121.5 Mbps" ;
               19 : rxDataRate_str = "40MHz HT 162 Mbps"   ;
               20 : rxDataRate_str = "40MHz HT 243 Mbps"   ;
               21 : rxDataRate_str = "40MHz HT 324 Mbps"   ;
               22 : rxDataRate_str = "40MHz HT 364.5 Mbps" ;
               23 : rxDataRate_str = "40MHz HT 405 Mbps"   ;
               24 : rxDataRate_str = "40MHz HT 54 Mbps"    ;
               25 : rxDataRate_str = "40MHz HT 108 Mbps"   ;
               26 : rxDataRate_str = "40MHz HT 162 Mbps"   ;
               27 : rxDataRate_str = "40MHz HT 216 Mbps"   ;
               28 : rxDataRate_str = "40MHz HT 324 Mbps"   ;
               29 : rxDataRate_str = "40MHz HT 432 Mbps"   ;
               30 : rxDataRate_str = "40MHz HT 486 Mbps"   ;
               31 : rxDataRate_str = "40MHz HT 540 Mbps"   ;
               32 : rxDataRate_str = "40MHz HT 6 Mbps"     ;
               33 : rxDataRate_str = "40MHz HT 81 Mbps"    ;    
               34 : rxDataRate_str = "40MHz HT 108 Mbps"   ;   
               35 : rxDataRate_str = "40MHz HT 135 Mbps"   ;   
               36 : rxDataRate_str = "40MHz HT 121.5 Mbps" ; 
               37 : rxDataRate_str = "40MHz HT 162 Mbps"   ;   
               38 : rxDataRate_str = "40MHz HT 202.5 Mbps" ; 
               39 : rxDataRate_str = "40MHz HT 108 Mbps"   ;   
               40 : rxDataRate_str = "40MHz HT 135 Mbps"   ;  
               41 : rxDataRate_str = "40MHz HT 135 Mbps"   ;  
               42 : rxDataRate_str = "40MHz HT 162 Mbps"   ;   
               43 : rxDataRate_str = "40MHz HT 189 Mbps"   ;   
               44 : rxDataRate_str = "40MHz HT 189 Mbps"   ;   
               45 : rxDataRate_str = "40MHz HT 216 Mbps"   ;   
               46 : rxDataRate_str = "40MHz HT 162 Mbps"   ;   
               47 : rxDataRate_str = "40MHz HT 202.5 Mbps" ; 
               48 : rxDataRate_str = "40MHz HT 202.5 Mbps" ; 
               49 : rxDataRate_str = "40MHz HT 243 Mbps"   ;   
               50 : rxDataRate_str = "40MHz HT 283.5 Mbps" ; 
               51 : rxDataRate_str = "40MHz HT 283.5 Mbps" ;
               52 : rxDataRate_str = "40MHz HT 324 Mbps"   ;   
               53 : rxDataRate_str = "40MHz HT 135 Mbps"   ;   
               54 : rxDataRate_str = "40MHz HT 162 Mbps"   ;   
               55 : rxDataRate_str = "40MHz HT 189 Mbps"   ;   
               56 : rxDataRate_str = "40MHz HT 162 Mbps"   ;   
               57 : rxDataRate_str = "40MHz HT 189 Mbps"   ;   
               58 : rxDataRate_str = "40MHz HT 216 Mbps"   ;   
               59 : rxDataRate_str = "40MHz HT 243 Mbps"   ;   
               60 : rxDataRate_str = "40MHz HT 216 Mbps"   ;   
               61 : rxDataRate_str = "40MHz HT 243 Mbps"   ;   
               62 : rxDataRate_str = "40MHz HT 270 Mbps"   ;   
               63 : rxDataRate_str = "40MHz HT 270 Mbps"   ;   
               64 : rxDataRate_str = "40MHz HT 297 Mbps"   ;   
               65 : rxDataRate_str = "40MHz HT 202.5 Mbps" ; 
               66 : rxDataRate_str = "40MHz HT 243 Mbps"   ;   
               67 : rxDataRate_str = "40MHz HT 283.5 Mbps" ; 
               68 : rxDataRate_str = "40MHz HT 243 Mbps"   ;   
               69 : rxDataRate_str = "40MHz HT 283.5 Mbps" ; 
               70 : rxDataRate_str = "40MHz HT 324 Mbps"   ;   
               71 : rxDataRate_str = "40MHz HT 364.5 Mbps" ; 
               72 : rxDataRate_str = "40MHz HT 324 Mbps"   ;   
               73 : rxDataRate_str = "40MHz HT 364.5 Mbps" ; 
               74 : rxDataRate_str = "40MHz HT 405 Mbps"   ;   
               75 : rxDataRate_str = "40MHz HT 405 Mbps"   ;   
               76 : rxDataRate_str = "40MHz HT 445.5 Mbps" ;                  
          default : rxDataRate_str = "Error 666"           ;
        endcase
      end
    end
  end
  else
  begin
    case (rxLegRate)
           0  : rxDataRate_str = "Leg 1 Mbps"   ;          
           1  : rxDataRate_str = "Leg 2 Mbps"   ;          
           2  : rxDataRate_str = "Leg 5.5 Mbps" ;          
           3  : rxDataRate_str = "Leg 11 Mbps"  ;          
           11 : rxDataRate_str = "Leg 6 Mbps"   ;          
           15 : rxDataRate_str = "Leg 9 Mbps"   ;          
           10 : rxDataRate_str = "Leg 12 Mbps"  ;          
           14 : rxDataRate_str = "Leg 18 Mbps"  ;          
           9  : rxDataRate_str = "Leg 24 Mbps"  ;          
           13 : rxDataRate_str = "Leg 36 Mbps"  ;          
           8  : rxDataRate_str = "Leg 48 Mbps"  ;          
           12 : rxDataRate_str = "Leg 54 Mbps"  ;          
      default : rxDataRate_str = "Error 666"    ;
    endcase
  end
end

`endif // RW_SIMU_ON

endmodule
