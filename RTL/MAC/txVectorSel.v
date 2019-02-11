//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author: $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: $
// $Date: $
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : This module selects the fields which are provided to the 
//                    MAC-PHY IF for the TX Vector generation from different 
//                    sources based on the type of tranmitted frame
//                    
// Simulation Notes : 
// Synthesis Notes  :
// Application Note :                                                       
// Simulator        :                                                       
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

module txVectorSel (
          //$port_g Clock and Reset interface
          input  wire        macCoreTxClk,          // MAC Core Transmit Clock
          input  wire        macCoreClkHardRst_n,   // Hard Reset of the MAC Core Clock domain 
                                                    // active low
          //$port_g MAC Controller interface
          input  wire        startTx_p,             // Start the transmission
          input  wire  [6:0] txMCS,                 // MCS (Only used for HT frame)
          input  wire [11:0] txLegLength,           // Legacy Length of the PPDU         
          input  wire [ 3:0] txLegRate,             // Legacy Rate of the PPDU.         

          input  wire  [1:0] txChBW,                // Transmit a Frame with Channel Bandwidth 40MHz       
          input  wire        txDynBW,               // Transmit a Frame with dynamic bandwidth
          input  wire        txBWSignaling,         // Transmit a Frame with BW signaling 
          input  wire [19:0] txHTLength,            // Length of the HT PPDU         
          input  wire        txResp,                // Transmit a Response Frame
          input  wire        txFromReg,             // Transmit a HW generated frame based on Register
          input  wire        txFromHD,              // Transmit a HW generated frame based on THD
          input  wire        txCFEND,               // Transmit a HW generated CFEND frame
          input  wire  [1:0] txSTBC,                // Transmit a Frame with Space Time Block Coding
          input  wire        txDisambiguityBit,     // Transmit a Frame with disambiguityBit
          input  wire        txFromFifo,            // Transmit a Frame from Tx FIFO

          //$port_g Tx Parameters Cache interface
          input  wire        preTypeProtTx,         // Preamble Type of Protection frame for Transmission
                                                    // 1'b0: SHORT
                                                    // 1'b1: LONG
          input  wire        preTypeTx,             // Preamble Type of PPDU for Transmission
                                                    // Same coding than preTypeTx
          input  wire  [2:0] formatModProtTx,       // Format and Modulation of Protection frame for Transmission
                                                    // 3'b000: NON-HT
                                                    // 3'b001: NON-HT-DUP-OFDM
                                                    // 3'b010: HT-MF
                                                    // 3'b011: HT-GF
                                                    // 3'b100: VHT
          input  wire  [2:0] formatModTx,           // Format and Modulation of PPDU for Transmission
                                                    // Same coding than formatModProtTx

          input  wire  [7:0] txPwrLevelPT,          // Transmit Power Level
          input  wire  [7:0] txPwrLevelProtPT,      // Transmit Power Level for Protection Frame

          input  wire  [8:0] partialAIDTx,          // Partial AID
          input  wire  [5:0] groupIDTx,             // Group ID
          input  wire        dozeNotAllowedTx,      // TXOP PS is not allowed
          input  wire        smoothingProtTx,       // Smoothing of Protection frame for Transmission
          input  wire        smoothingTx,           // Smoothing of PPDU for Transmission
          input  wire        soundingTx,            // Sounding Protection frame for Transmission
          input  wire  [2:0] nTxProtPT,             // Number of Transmit Chains for Protection Frame
          input  wire  [2:0] nTxPT,                 // Number of Transmit Chains for PPDU
          input  wire        txShortGI,             // Short Guard Interval for Transmission
                                                    // When High, it indicates whether a short Guard Interval
          input  wire  [1:0] stbcPT,                // Space Time Block Coding
          input  wire        txFecCoding,           // FEC Coding
          input  wire  [1:0] numExtnSSPT,           // Number of Extension Spatial Streams
          input  wire        beamFormedPT,          // BeamFormed frame
          input  wire  [7:0] smmIndexPT,            // Spatial Map Matrix Index
          input  wire  [7:0] antennaSetPT,          // Antenna Set
          input  wire        aMPDU,                 // Indicates whether this Transmit Header Descriptor belong to an A-MPDU

          //$port_g CSReg Block interface
          input  wire  [7:0] dsssMaxPwrLevel,       // Maximum Power Level for DSSS/CCK frames
          input  wire  [7:0] ofdmMaxPwrLevel,       // Maximum Power Level for OFDM frames
          input  wire        startTxSmoothing,      // Start Transmission with Smoothing
          input  wire  [7:0] startTxAntennaSet,     // Start Transmission with Antenna Set
          input  wire  [7:0] startTxSMMIndex,       // Start Transmission with Spatial Map Matrix Index

          input  wire        startTxPreType,        // Start Transmission with Preamble Type
                                                    // 1'b0: SHORT
                                                    // 1'b1: LONG

          input  wire  [2:0] startTxFormatMod,      // Start Transmission with Format and Modulation
                                                    // 3'b000: NON-HT
                                                    // 3'b001: NON-HT-DUP-OFDM
                                                    // 3'b010: HT-MF
                                                    // 3'b011: HT-GF
                                                    // 3'b100: VHT
          input  wire  [1:0] startTxNumExtnSS,      // Start Transmission with Number of Extension Spatial Streams
          input  wire  [2:0] pRandom,               // Pseudo random value for bbbServiceA
          input  wire [15:0] bbServiceA,            // Service field when the modulation is OFDM.
          input  wire [ 7:0] bbServiceB,            // Service field when the modulation is DSSS/CCK.
          input  wire [ 2:0] startTxNTx,            // Start Transmission with Number of Transmit Chains for PPDU        

          //$port_g RX Controller interface
          input  wire  [7:0] respTxAntennaSet,      // Response Transmission with Antenna Set
          input  wire  [7:0] respTxSMMIndex,        // Response Transmission with Spatial Map Matrix Index

          input  wire        respTxPreType,         // Response Transmission with Preamble Type
                                                    // 1'b0: SHORT
                                                    // 1'b1: LONG

          input  wire  [2:0] respTxFormatMod,       // Response Transmission with Format and Modulation
                                                    // 3'b000: NON-HT
                                                    // 3'b001: NON-HT-DUP-OFDM
                                                    // 3'b010: HT-MF
                                                    // 3'b011: HT-GF
                                                    // 3'b100: VHT
          input  wire  [1:0] respTxNumExtnSS,       // Response Transmission with Number of Extension Spatial Streams
          input  wire        respTxFECCoding,       // Response Transmission with FEC Coding      
          input  wire [ 2:0] respTxNTx,             // Response Transmission with Number of Transmit Chains for PPDU        
          input  wire        respTxShortGI,         // Response Transmission with Short Guard Interval

          //$port_g MAC-PHY-IF Block interface
          output reg   [7:0] txPwrLevel,            // Transmit power Level
          output reg   [1:0] chBW,                  // Channel Bandwidth        
          output reg   [1:0] chOffset,              // Channel Offset
                                                    //	0 - CH_OFF_20 - 20 MHz channel
                                                    //	1 - CH_OFF_40 - The entire 40 MHz channel
                                                    //	2 - CH_OFF_20U - Upper 20 MHz in 40 MHz
                                                    //	3 - CH_OFF_20L - Lower 20 MHz in 40 MHz
          output reg         smoothing,             // Smoothing Recommended or Not
          output reg   [7:0] antennaSet,            // Antenna Set
          output reg         beamFormed,            // BeamFormed frame
          output reg   [7:0] smmIndex,              // Spatial Map Matrix Index
          output reg   [6:0] mcs,                   // MCS (Only used for HT frame)
          output reg   [2:0] nSTS,                  // nSTS
          output reg         preType,               // Preamble Type
                                                    // 1'b0: SHORT
                                                    // 1'b1: LONG
          output reg   [2:0] formatMod,             // Format and Modulation         
                                                    // 3'b000: NON-HT
                                                    // 3'b001: NON-HT-DUP-OFDM
                                                    // 3'b010: HT-MF
                                                    // 3'b011: HT-GF
                                                    // 3'b100: VHT
          output reg   [1:0] numExtnSS,             // Number of Extension Spatial Streams         
          output reg   [1:0] stbc,                  // Space Time Block Coding         
          output reg         disambiguityBit,       // Transmit a Frame with disambiguityBit

          output reg   [8:0] partialAID,            // Partial AID
          output reg   [5:0] groupID,               // Group ID
          output reg         dozeNotAllowed,        // TXOP PS is not allowed
          output reg         fecCoding,             // Low Density Parity Check code         
          output reg         sounding,              // Indicates whether this PPDU is Sounding         
          output reg  [11:0] legLength,             // Legacy Length of the PPDU         
          output reg  [ 3:0] legRate,               // Legacy Rate of the PPDU.         
          output reg  [15:0] service,               // Scrambler initialization
          output reg  [19:0] htLength,              // Length of the HT PPDU         
          output reg  [ 2:0] nTx,                   // Number of Transmit Chains         
          output reg         shortGI,               // Short Guard Interval         
          output reg         aggreation             // MPDU Aggregate         
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
// String definition to display rxControl current state
reg [50*8:0] txDataRate_str;
`endif // RW_SIMU_ON

wire [2:0] nSSInt; // umber of spatial stream in VHT
  
  
reg   [7:0] txPwrLevelInt;            // Transmit power Level
wire  [1:0] chBWInt;                  // Channel Bandwidth        
wire  [1:0] chOffsetInt;              // Channel Offset
                                   //  0 - CH_OFF_20 - 20 MHz channel
                                   //  1 - CH_OFF_40 - The entire 40 MHz channel
                                   //  2 - CH_OFF_20U - Upper 20 MHz in 40 MHz
                                   //  3 - CH_OFF_20L - Lower 20 MHz in 40 MHz
reg         smoothingInt;             // Smoothing Recommended or Not
reg   [7:0] antennaSetInt;            // Antenna Set
wire        beamFormedInt;            // BeamFormed frame
reg   [7:0] smmIndexInt;              // Spatial Map Matrix Index
wire  [6:0] mcsInt;                   // MCS (Only used for HT frame)
wire  [2:0] nSTSInt;                  // nSTS
reg         preTypeInt;               // Preamble Type
                                   // 1'b0: SHORT
                                   // 1'b1: LONG
wire [2:0] formatModInt;             // Format and Modulation         
reg  [2:0] formatModTxInt;             // Format and Modulation         
                                   // 3'b000: NON-HT
                                   // 3'b001: NON-HT-DUP-OFDM
                                   // 3'b010: HT-MF
                                   // 3'b011: HT-GF
                                   // 3'b100: VHT
reg   [1:0] numExtnSSInt;             // Number of Extension Spatial Streams         
reg   [1:0] stbcInt;                  // Space Time Block Coding         
reg         disambiguityBitInt;       // Transmit a Frame with disambiguityBit

wire  [8:0] partialAIDInt;            // Partial AID
wire  [5:0] groupIDInt;               // Group ID
wire        dozeNotAllowedInt;        // TXOP PS is not allowed
reg         fecCodingInt;             // Low Density Parity Check code         
wire        soundingInt;              // Indicates whether this PPDU is Sounding         
wire [11:0] legLengthInt;             // Legacy Length of the PPDU         
reg  [ 3:0] legRateInt;               // Legacy Rate of the PPDU.         
reg  [15:0] serviceInt;               // Scrambler initialization
wire [19:0] htLengthInt;              // Length of the HT PPDU         
reg  [ 2:0] nTxInt;                   // Number of Transmit Chains         
reg         shortGIInt;               // Short Guard Interval         
wire        aggreationInt;             // MPDU Aggregate         

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// txControlMainFSM FSM Current State Logic 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    txPwrLevel         <= 8'b0;
    chBW               <= 2'b0;        
    chOffset           <= 2'b0;
    smoothing          <= 1'b0;
    antennaSet         <= 8'b0;
    beamFormed         <= 1'b0;
    smmIndex           <= 8'b0;
    mcs                <= 7'b0;
    nSTS               <= 3'b0;
    preType            <= 1'b0;
    formatMod          <= 3'b0;
    numExtnSS          <= 2'b0;         
    stbc               <= 2'b0;         
    disambiguityBit    <= 1'b0;
    partialAID         <= 9'b0;
    groupID            <= 6'b0;
    dozeNotAllowed     <= 1'b0;
    fecCoding          <= 1'b0;         
    sounding           <= 1'b0;         
    legLength          <= 12'b0;         
    legRate            <= 4'b0;         
    service            <= 16'b0;
    htLength           <= 20'b0;         
    nTx                <= 3'b0;         
    shortGI            <= 1'b0;         
    aggreation         <= 1'b0;         
  end
  else if (startTx_p)  // Synchronous Reset
  begin
    txPwrLevel      <= txPwrLevelInt;
    chBW            <= chBWInt;
    chOffset        <= chOffsetInt;
    smoothing       <= smoothingInt;
    antennaSet      <= antennaSetInt;
    beamFormed      <= beamFormedInt;
    smmIndex        <= smmIndexInt;
    mcs             <= mcsInt;
    nSTS            <= nSTSInt;
    preType         <= preTypeInt;
    formatMod       <= formatModInt;
    numExtnSS       <= numExtnSSInt;       
    stbc            <= stbcInt;
    disambiguityBit <= disambiguityBitInt;
    partialAID      <= partialAIDInt;
    groupID         <= groupIDInt;
    dozeNotAllowed  <= dozeNotAllowedInt;
    fecCoding       <= fecCodingInt;     
    sounding        <= soundingInt; 
    legLength       <= legLengthInt;     
    legRate         <= legRateInt;
    service         <= serviceInt;
    htLength        <= htLengthInt;
    nTx             <= nTxInt;
    shortGI         <= shortGIInt; 
    aggreation      <= aggreationInt;         
  end
end

//






// Transmit Vector Preparation


// Channel bandwidth
// Additional check to guaranty a channel BW of 20MHz in case of formatMod legacy
assign chBWInt = (formatModInt != 3'b0) ? txChBW : 2'b0;


// Channel Offset
//
assign  chOffsetInt = 2'b0;

// Smoothing
//
always @*
begin
  if (formatModInt >= 3'd2)
  begin
    case ({txCFEND, txResp, txFromReg, txFromHD, txFromFifo})
      5'b00001 :
        smoothingInt = smoothingTx;
      5'b00010 :
        smoothingInt = smoothingProtTx;
      5'b00100 :
        smoothingInt = startTxSmoothing;
      5'b01000 :
        smoothingInt = ~soundingInt;  // For response frame, the smoothing is enabled when sounding is not requested
      5'b10000 :
        smoothingInt = smoothingProtTx;
      default :
        smoothingInt = startTxSmoothing;
    endcase
  end
  else
  begin
    smoothingInt = 1'b0;
  end
end


// AntennaSet
//
always @*
begin
  case ({txCFEND, txResp, txFromReg, txFromHD, txFromFifo})
    5'b00001 :
      antennaSetInt = antennaSetPT;
    5'b00010 :
      antennaSetInt = antennaSetPT;
    5'b00100 :
      antennaSetInt = startTxAntennaSet;
    5'b01000 :
      antennaSetInt = respTxAntennaSet;
    5'b10000 :
      antennaSetInt = antennaSetPT;
    default :
      antennaSetInt = startTxAntennaSet;
  endcase
end

assign beamFormedInt = (txFromFifo) ? beamFormedPT : 1'b0;

// SMM
//
always @*
begin
  case ({txCFEND, txResp, txFromReg, txFromHD, txFromFifo})
    5'b00001 :
      smmIndexInt = smmIndexPT;
    5'b00010 :
      smmIndexInt = smmIndexPT;
    5'b00100 :
      smmIndexInt = startTxSMMIndex;
    5'b01000 :
      smmIndexInt = respTxSMMIndex;
    5'b10000 :
      smmIndexInt = smmIndexPT;
    default :
      smmIndexInt = startTxSMMIndex;
  endcase
end


// Preamble Type
//
// If the received frame is of a modulation class other than HT and the control response frame is carried
// in a non-HT PPDU, the control response frame shall be transmitted using the same modulation class
// as the received frame. In addition, the control response frame shall be sent using the same value for
// the TXVECTOR parameter PREAMBLE_TYPE as the received frame.
// 
// If the selected rate for the transmission is legRate = 0 only a long preamble is allowed. 
// Note that in case on HT frame, the legRate is forced to 4 (6Mbps)
always @*
begin
  if (legRateInt == 4'b0)
    preTypeInt = 1'b1;
  else
  begin
    case ({txCFEND, txResp, txFromReg, txFromHD, txFromFifo})
      5'b00001 :
        preTypeInt = preTypeTx;
      5'b00010 :
        preTypeInt = preTypeProtTx;
      5'b00100 :
        preTypeInt = startTxPreType;
      5'b01000 :
        preTypeInt = respTxPreType;
      5'b10000 :
        preTypeInt = preTypeProtTx;
      default :
        preTypeInt = startTxPreType;
    endcase
  end
end

// Format Modulation selection
// 3'b000: NON-HT
// 3'b001: NON-HT-DUP-OFDM
// 3'b010: HT-MF
// 3'b011: HT-GF
// 3'b100: VHT
//
always @*
begin
  case ({txCFEND, txResp, txFromReg, txFromHD, txFromFifo})
    5'b00001 :
      formatModTxInt = formatModTx;
    5'b00010 :
      formatModTxInt = formatModProtTx;
    5'b00100 :
      formatModTxInt = startTxFormatMod;
    5'b01000 :
      formatModTxInt = respTxFormatMod;
    5'b10000 :
      formatModTxInt = formatModProtTx;
    default :
      formatModTxInt = startTxFormatMod;
  endcase
end

// If the SW programmed an NON HT Duplicate with txChBW 40 MHz 
// but the macController changed the BW to 20MHz then force the formatmod to NON HT.
// In case of NON_HT_DUP with DSSS (legRate < 4), the formatMod is forced to 0 as the PHY does not support NON_HT_DUP with DSSS/CCK modulation
assign formatModInt = ((formatModTxInt == 3'b001) && ((txChBW == 2'b00) || (legRateInt < 4'd4))) ? 3'b000 : formatModTxInt;

// Number of extension spacial stream selection
//
always @*
begin
  case ({txCFEND, txResp, txFromReg, txFromHD, txFromFifo})
    5'b00001 :
      numExtnSSInt = numExtnSSPT;
    5'b00010 :
      numExtnSSInt = numExtnSSPT;
    5'b00100 :
      numExtnSSInt = startTxNumExtnSS;
    5'b01000 :
      numExtnSSInt = respTxNumExtnSS;
    5'b10000 :
      numExtnSSInt = numExtnSSPT;
    default :
      numExtnSSInt = startTxNumExtnSS;
  endcase
end

// STBC
//
always @*
begin
  case ({txCFEND, txResp, txFromReg, txFromHD, txFromFifo})
    5'b00001 :
      stbcInt = stbcPT;
    5'b00010 :
      stbcInt = txSTBC;
    5'b00100 :
      stbcInt = txSTBC;
    5'b01000 :
      stbcInt = txSTBC;
    5'b10000 :
      stbcInt = txSTBC;
    default :
      stbcInt = txSTBC;
  endcase
end

// disambiguityBit
//
always @*
begin
  case ({txResp, txFromHD, txFromFifo})
    3'b001 :
      disambiguityBitInt = txDisambiguityBit;
    3'b010 :
      disambiguityBitInt = txDisambiguityBit;
    3'b100 :
      disambiguityBitInt = txDisambiguityBit;
    default :
      disambiguityBitInt = 1'b0;
  endcase
end



// A STA shall not transmit a control frame that initiates a TXOP with the TXVECTOR parameter
// FEC_CODING set to a value of LDPC.
// A STA shall not transmit a control response frame with TXVECTOR parameter FEC_CODING set to
// LDPC unless it is in response to a reception of a frame with the RXVECTOR parameter
// FEC_CODING set to LDPC.
always @*
begin
  case ({txCFEND, txResp, txFromReg, txFromHD, txFromFifo})
    5'b00001 :
      fecCodingInt = txFecCoding;
    5'b00010 :
      fecCodingInt = 1'b0;
    5'b00100 :
      fecCodingInt = 1'b0;
    5'b01000 :
      fecCodingInt = respTxFECCoding;
    5'b10000 :
      fecCodingInt = 1'b0;
    default :
      fecCodingInt = 1'b0;
  endcase
end


// nTx Selection.
//
always @*
begin
  case ({txCFEND, txResp, txFromReg, txFromHD, txFromFifo})
    5'b00001 :
      nTxInt = nTxPT;
    5'b00010 :
      nTxInt = nTxProtPT;
    5'b00100 :
      nTxInt = startTxNTx;
    5'b01000 :
      nTxInt = respTxNTx;
    5'b10000 :
      nTxInt = nTxProtPT;
    default :
      nTxInt = startTxNTx;
  endcase
end

// A STA shall not transmit a control frame that initiates a TXOP with the TXVECTOR parameter GI_TYPE
// set to a value of SHORT_GI.
// A STA shall not transmit a control response frame with TXVECTOR parameter GI_TYPE set to SHORT_GI
// unless it is in response to a reception of a frame with the RXVECTOR parameter GI_TYPE set to
// SHORT_GI.
always @*
begin
  case ({txCFEND, txResp, txFromReg, txFromHD, txFromFifo})
    5'b00001 :
      if (formatModInt >= 3'd2)
        shortGIInt = txShortGI;
      else  
        shortGIInt = 1'b0;
    5'b00010 :
      shortGIInt = 1'b0;
    5'b00100 :
      shortGIInt = 1'b0;
    5'b01000 :
      if (formatModInt >= 3'd2)
        shortGIInt = respTxShortGI;
      else  
        shortGIInt = 1'b0;
    5'b10000 :
      shortGIInt = 1'b0;
    default :
      shortGIInt = 1'b0;
  endcase
end

assign soundingInt   = (txFromFifo) ? soundingTx : 1'b0;

// Selection of the Transmit Power
always @*
begin
  case ({txCFEND, txResp, txFromReg, txFromHD, txFromFifo})
    5'b00001 :
      txPwrLevelInt = txPwrLevelPT;
    5'b00010 :
      txPwrLevelInt = txPwrLevelProtPT;
    5'b00100 ,
    5'b01000 ,
    5'b10000 :
      txPwrLevelInt = (legRateInt <= 4'd3) ? dsssMaxPwrLevel : ofdmMaxPwrLevel;
    default :
      txPwrLevelInt = txPwrLevelPT;
  endcase
end


// Assign the service field.
// In case of Bandwidth signaling, the requested/available bandwidth is provided 
// using the service field.
always @*
begin
	if (txBWSignaling && ((formatModInt == 3'b0) || (formatModInt == 3'b1)))
    serviceInt = {bbServiceA[15:7],chBWInt,txDynBW,1'b1,pRandom};
	else if (legRate <= 4'd7)  
	  serviceInt = {8'b0,bbServiceB};
	else
	  serviceInt = bbServiceA;
end

assign dozeNotAllowedInt = (formatModInt == 3'd4) ? (txFromFifo) ? dozeNotAllowedTx : 1'b1 : 1'b0;

assign partialAIDInt = ((txFromFifo) && (formatModInt == 3'd4)) ? partialAIDTx : 9'b0;

assign groupIDInt = ((txFromFifo) && (formatModInt == 3'd4)) ? groupIDTx : 6'b0;


assign aggreationInt = (txFromFifo) ? aMPDU : 1'b0;
assign legLengthInt  = txLegLength;
// assign legRate    = txLegRate;

assign htLengthInt   = txHTLength;


assign mcsInt        = (formatModInt == 3'd4) ? {3'b0,txMCS[3:0]} : txMCS;
assign nSSInt        = (formatModInt == 3'd4) ? txMCS[6:4] : 3'd0;
assign nSTSInt       = (stbcInt != 2'b0) ? ((nSSInt != 3'b0) ? {nSSInt[1:0],1'b0} : 3'd1) : nSSInt[2:0];



// conversion between MCS Index and legay Rate at the MAC PHY Interface
//  txLegRate is the legacy rate based on MCS Index
//  legRate is the legacy rate following the MAC-PHY If convention
//
// The following table provides the conversion rule.
//       +-----+---------+------+
//       | MCS | LegRate | Mbps |
//       +-----+---------+------+
//       |  0  | 4'b0000 |   1  |
//       |  1  | 4'b0001 |   2  |
//       |  2  | 4'b0010 | 5.5  |
//       |  3  | 4'b0011 |  11  |
//       |  4  | 4'b1011 |   6  |
//       |  5  | 4'b1111 |   9  |
//       |  6  | 4'b1010 |  12  |
//       |  7  | 4'b1110 |  18  |
//       |  8  | 4'b1001 |  24  |
//       |  9  | 4'b1101 |  36  |
//       | 10  | 4'b1000 |  48  |
//       | 11  | 4'b1100 |  54  |
//       +-----+---------+------+

always @ *
begin
  case (txLegRate)
        4'd0 : legRateInt = 4'b0000; //   1 Mpbs
        4'd1 : legRateInt = 4'b0001; //   2 Mpbs
        4'd2 : legRateInt = 4'b0010; // 5.5 Mpbs
        4'd3 : legRateInt = 4'b0011; //  11 Mpbs
        4'd4 : legRateInt = 4'b1011; //   6 Mpbs
        4'd5 : legRateInt = 4'b1111; //   9 Mpbs
        4'd6 : legRateInt = 4'b1010; //  12 Mpbs
        4'd7 : legRateInt = 4'b1110; //  18 Mpbs
        4'd8 : legRateInt = 4'b1001; //  24 Mpbs
        4'd9 : legRateInt = 4'b1101; //  36 Mpbs
       4'd10 : legRateInt = 4'b1000; //  48 Mpbs
       4'd11 : legRateInt = 4'b1100; //  54 Mpbs
     default : legRateInt = 4'b1011; //   6 Mpbs
  endcase
end


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
// String definition to display rxControl current state

always @(*)
begin
  if(formatMod>=3'd2)
  begin
    if(chBW == 0) //$todo
    begin
      if(shortGI)
      begin
        case (mcs)
               0  : txDataRate_str = "HT 7.2 Mbps"   ;
               1  : txDataRate_str = "HT 14.4 Mbps"  ;
               2  : txDataRate_str = "HT 21.7 Mbps"  ;
               3  : txDataRate_str = "HT 28.9 Mbps"  ;
               4  : txDataRate_str = "HT 43.3 Mbps"  ;
               5  : txDataRate_str = "HT 57.8 Mbps"  ;
               6  : txDataRate_str = "HT 65 Mbps"    ;
               7  : txDataRate_str = "HT 72.2 Mbps"  ;
               8  : txDataRate_str = "HT 14.4 Mbps"  ;
               9  : txDataRate_str = "HT 28.9 Mbps"  ;
               10 : txDataRate_str = "HT 43.3 Mbps"  ;
               11 : txDataRate_str = "HT 57.8 Mbps"  ;
               12 : txDataRate_str = "HT 86.7 Mbps"  ;
               13 : txDataRate_str = "HT 115.6 Mbps" ;
               14 : txDataRate_str = "HT 130 Mbps"   ;
               15 : txDataRate_str = "HT 144.4 Mbps" ;
               16 : txDataRate_str = "HT 21.7 Mbps"  ;
               17 : txDataRate_str = "HT 43.3 Mbps"  ;
               18 : txDataRate_str = "HT 65 Mbps"    ;
               19 : txDataRate_str = "HT 86.7 Mbps"  ;
               20 : txDataRate_str = "HT 130 Mbps"   ;
               21 : txDataRate_str = "HT 173.3 Mbps" ;
               22 : txDataRate_str = "HT 195 Mbps"   ;
               23 : txDataRate_str = "HT 216.7 Mbps" ;
               24 : txDataRate_str = "HT 28.9  Mbps" ;
               25 : txDataRate_str = "HT 57.8 Mbps"  ;
               26 : txDataRate_str = "HT 86.7 Mbps"  ;
               27 : txDataRate_str = "HT 115.6 Mbps" ;
               28 : txDataRate_str = "HT 173.3 Mbps" ;
               29 : txDataRate_str = "HT 231.1 Mbps" ;
               30 : txDataRate_str = "HT 260 Mbps"   ;
               31 : txDataRate_str = "HT 288.9 Mbps" ;
               32 : txDataRate_str = "HT 6.7 Mbps"   ;
               33 : txDataRate_str = "HT 43.3 Mbps"  ;
               34 : txDataRate_str = "HT 57.8 Mbps"  ;
               35 : txDataRate_str = "HT 72.2 Mbps"  ;
               36 : txDataRate_str = "HT 65 Mbps"    ;
               37 : txDataRate_str = "HT 86.7 Mbps"  ;
               38 : txDataRate_str = "HT 108.3 Mbps" ;
               39 : txDataRate_str = "HT 57.8 Mbps"  ;
               40 : txDataRate_str = "HT 72.2 Mbps"  ;
               41 : txDataRate_str = "HT 72.2 Mbps"  ;
               42 : txDataRate_str = "HT 86.7 Mbps"  ;
               43 : txDataRate_str = "HT 101.1 Mbps" ;
               44 : txDataRate_str = "HT 101.1 Mbps" ;
               45 : txDataRate_str = "HT 115.6 Mbps" ;
               46 : txDataRate_str = "HT 86.7 Mbps"  ;
               47 : txDataRate_str = "HT 108.3 Mbps" ;
               48 : txDataRate_str = "HT 108.3 Mbps" ;
               49 : txDataRate_str = "HT 130 Mbps"   ;
               50 : txDataRate_str = "HT 151.7 Mbps" ;
               51 : txDataRate_str = "HT 151.7 Mbps" ;
               52 : txDataRate_str = "HT 173.3 Mbps" ;
               53 : txDataRate_str = "HT 72.2 Mbps"  ;
               54 : txDataRate_str = "HT 86.7 Mbps"  ;
               55 : txDataRate_str = "HT 101.1 Mbps" ;
               56 : txDataRate_str = "HT 86.7 Mbps"  ;
               57 : txDataRate_str = "HT 101.1 Mbps" ;
               58 : txDataRate_str = "HT 115.6 Mbps" ;
               59 : txDataRate_str = "HT 130 Mbps"   ;
               60 : txDataRate_str = "HT 115.5 Mbps" ;
               61 : txDataRate_str = "HT 130 Mbps"   ;
               62 : txDataRate_str = "HT 144.4 Mbps" ;
               63 : txDataRate_str = "HT 144.4 Mbps" ;
               64 : txDataRate_str = "HT 158.9 Mbps" ;
               65 : txDataRate_str = "HT 108.3 Mbps" ;
               66 : txDataRate_str = "HT 130 Mbps"   ;
               67 : txDataRate_str = "HT 151.7 Mbps" ;
               68 : txDataRate_str = "HT 130 Mbps"   ;
               69 : txDataRate_str = "HT 151.7 Mbps" ;
               70 : txDataRate_str = "HT 173.3 Mbps" ;
               71 : txDataRate_str = "HT 195 Mbps"   ;
               72 : txDataRate_str = "HT 173.3 Mbps" ;
               73 : txDataRate_str = "HT 195 Mbps"   ;
               74 : txDataRate_str = "HT 216.7 Mbps" ;
               75 : txDataRate_str = "HT 216.7 Mbps" ;
               76 : txDataRate_str = "HT 238.3 Mbps" ;
          default : txDataRate_str = "HT Error 666"  ;
        endcase
      end
      else
      begin
        case (mcs)
               0  : txDataRate_str = "HT 6.5 Mbps"   ;         
               1  : txDataRate_str = "HT 13 Mbps"    ;         
               2  : txDataRate_str = "HT 19.5 Mbps"  ;         
               3  : txDataRate_str = "HT 26 Mbps"    ;         
               4  : txDataRate_str = "HT 39 Mbps"    ;         
               5  : txDataRate_str = "HT 52 Mbps"    ;         
               6  : txDataRate_str = "HT 58.5 Mbps"  ;         
               7  : txDataRate_str = "HT 65 Mbps"    ;         
               8  : txDataRate_str = "HT 13 Mbps"    ;         
               9  : txDataRate_str = "HT 26 Mbps"    ;         
               10 : txDataRate_str = "HT 39 Mbps"    ;         
               11 : txDataRate_str = "HT 52 Mbps"    ;         
               12 : txDataRate_str = "HT 78 Mbps"    ;         
               13 : txDataRate_str = "HT 104 Mbps"   ;         
               14 : txDataRate_str = "HT 117 Mbps"   ;         
               15 : txDataRate_str = "HT 130 Mbps"   ;         
               16 : txDataRate_str = "HT 19.5 Mbps"  ;         
               17 : txDataRate_str = "HT 39 Mbps"    ;         
               18 : txDataRate_str = "HT 58.5 Mbps"  ;         
               19 : txDataRate_str = "HT 78 Mbps"    ;         
               20 : txDataRate_str = "HT 117 Mbps"   ;         
               21 : txDataRate_str = "HT 156 Mbps"   ;         
               22 : txDataRate_str = "HT 175.5 Mbps" ;         
               23 : txDataRate_str = "HT 195 Mbps"   ;         
               24 : txDataRate_str = "HT 26 Mbps"    ;         
               25 : txDataRate_str = "HT 52 Mbps"    ;         
               26 : txDataRate_str = "HT 78 Mbps"    ;         
               27 : txDataRate_str = "HT 104 Mbps"   ;         
               28 : txDataRate_str = "HT 156 Mbps"   ;         
               29 : txDataRate_str = "HT 208 Mbps"   ;         
               30 : txDataRate_str = "HT 234 Mbps"   ;         
               31 : txDataRate_str = "HT 260 Mbps"   ;         
               32 : txDataRate_str = "HT 6   Mbps"   ;         
               33 : txDataRate_str = "HT 39 Mbps"    ;         
               34 : txDataRate_str = "HT 52 Mbps"    ;         
               35 : txDataRate_str = "HT 65 Mbps"    ;         
               36 : txDataRate_str = "HT 58.5 Mbps"  ;         
               37 : txDataRate_str = "HT 78 Mbps"    ;         
               38 : txDataRate_str = "HT 97.5 Mbps"  ;         
               39 : txDataRate_str = "HT 52 Mbps"    ;         
               40 : txDataRate_str = "HT 65 Mbps"    ;         
               41 : txDataRate_str = "HT 65 Mbps"    ;         
               42 : txDataRate_str = "HT 78 Mbps"    ;         
               43 : txDataRate_str = "HT 91 Mbps"    ;         
               44 : txDataRate_str = "HT 91 Mbps"    ;         
               45 : txDataRate_str = "HT 104 Mbps"   ;            
               46 : txDataRate_str = "HT 78 Mbps"    ;         
               47 : txDataRate_str = "HT 97.5 Mbps"  ;         
               48 : txDataRate_str = "HT 97.5 Mbps"  ;         
               49 : txDataRate_str = "HT 117 Mbps"   ;         
               50 : txDataRate_str = "HT 136.5 Mbps" ;         
               51 : txDataRate_str = "HT 136.5 Mbps" ;         
               52 : txDataRate_str = "HT 156 Mbps"   ;         
               53 : txDataRate_str = "HT 65 Mbps"    ;         
               54 : txDataRate_str = "HT 78 Mbps"    ;         
               55 : txDataRate_str = "HT 91 Mbps"    ;         
               56 : txDataRate_str = "HT 78 Mbps"    ;         
               57 : txDataRate_str = "HT 91 Mbps"    ;         
               58 : txDataRate_str = "HT 104 Mbps"   ;         
               59 : txDataRate_str = "HT 117 Mbps"   ;         
               60 : txDataRate_str = "HT 104 Mbps"   ;         
               61 : txDataRate_str = "HT 117 Mbps"   ;         
               62 : txDataRate_str = "HT 130 Mbps"   ;         
               63 : txDataRate_str = "HT 130 Mbps"   ;         
               64 : txDataRate_str = "HT 143 Mbps"   ;         
               65 : txDataRate_str = "HT 97.5 Mbps"  ;         
               66 : txDataRate_str = "HT 117 Mbps"   ;         
               67 : txDataRate_str = "HT 136.5 Mbps" ;         
               68 : txDataRate_str = "HT 117 Mbps"   ;         
               69 : txDataRate_str = "HT 136.5 Mbps" ;         
               70 : txDataRate_str = "HT 156 Mbps"   ;         
               71 : txDataRate_str = "HT 175.5 Mbps" ;         
               72 : txDataRate_str = "HT 156 Mbps"   ;         
               73 : txDataRate_str = "HT 175.5 Mbps" ;         
               74 : txDataRate_str = "HT 195 Mbps"   ;         
               75 : txDataRate_str = "HT 195 Mbps"   ;         
               76 : txDataRate_str = "HT 214.5 Mbps" ;         
          default : txDataRate_str = "HT Error 666"  ;
        endcase
      end
    end
    else
    begin
      if(txShortGI)
      begin
        case (mcs)
               0  : txDataRate_str = "40MHz HT 15 Mbps"    ;
               1  : txDataRate_str = "40MHz HT 30 Mbps"    ;
               2  : txDataRate_str = "40MHz HT 45 Mbps"    ;
               3  : txDataRate_str = "40MHz HT 60 Mbps"    ;
               4  : txDataRate_str = "40MHz HT 90 Mbps"    ;
               5  : txDataRate_str = "40MHz HT 120 Mbps"   ; 
               6  : txDataRate_str = "40MHz HT 135 Mbps"   ; 
               7  : txDataRate_str = "40MHz HT 150 Mbps"   ; 
               8  : txDataRate_str = "40MHz HT 30 Mbps"    ;
               9  : txDataRate_str = "40MHz HT 60 Mbps"    ;
               10 : txDataRate_str = "40MHz HT 90 Mbps"    ;
               11 : txDataRate_str = "40MHz HT 120 Mbps"   ; 
               12 : txDataRate_str = "40MHz HT 180 Mbps"   ; 
               13 : txDataRate_str = "40MHz HT 240 Mbps"   ; 
               14 : txDataRate_str = "40MHz HT 270 Mbps"   ; 
               15 : txDataRate_str = "40MHz HT 300 Mbps"   ; 
               16 : txDataRate_str = "40MHz HT 45 Mbps"    ;
               17 : txDataRate_str = "40MHz HT 90 Mbps"    ;
               18 : txDataRate_str = "40MHz HT 135 Mbps"   ; 
               19 : txDataRate_str = "40MHz HT 180 Mbps"   ; 
               20 : txDataRate_str = "40MHz HT 270 Mbps"   ; 
               21 : txDataRate_str = "40MHz HT 360 Mbps"   ; 
               22 : txDataRate_str = "40MHz HT 405 Mbps"   ; 
               23 : txDataRate_str = "40MHz HT 450 Mbps"   ; 
               24 : txDataRate_str = "40MHz HT 60 Mbps"    ; 
               25 : txDataRate_str = "40MHz HT 120 Mbps"   ; 
               26 : txDataRate_str = "40MHz HT 180 Mbps"   ; 
               27 : txDataRate_str = "40MHz HT 240 Mbps"   ; 
               28 : txDataRate_str = "40MHz HT 360 Mbps"   ; 
               29 : txDataRate_str = "40MHz HT 480 Mbps"   ; 
               30 : txDataRate_str = "40MHz HT 540 Mbps"   ; 
               31 : txDataRate_str = "40MHz HT 600 Mbps"   ; 
               33 : txDataRate_str = "40MHz HT 90  Mbps"   ;
               34 : txDataRate_str = "40MHz HT 120 Mbps"   ;
               35 : txDataRate_str = "40MHz HT 150 Mbps"   ;
               36 : txDataRate_str = "40MHz HT 135 Mbps"   ;
               37 : txDataRate_str = "40MHz HT 180 Mbps"   ;
               38 : txDataRate_str = "40MHz HT 225 Mbps"   ;
               39 : txDataRate_str = "40MHz HT 120 Mbps"   ;
               40 : txDataRate_str = "40MHz HT 150 Mbps"   ;
               41 : txDataRate_str = "40MHz HT 150 Mbps"   ;
               42 : txDataRate_str = "40MHz HT 180 Mbps"   ;
               43 : txDataRate_str = "40MHz HT 210 Mbps"   ;
               44 : txDataRate_str = "40MHz HT 210 Mbps"   ;
               45 : txDataRate_str = "40MHz HT 240 Mbps"   ;
               46 : txDataRate_str = "40MHz HT 180 Mbps"   ;
               47 : txDataRate_str = "40MHz HT 225 Mbps"   ;
               48 : txDataRate_str = "40MHz HT 225 Mbps"   ;
               49 : txDataRate_str = "40MHz HT 270 Mbps"   ;
               50 : txDataRate_str = "40MHz HT 315 Mbps"   ;
               51 : txDataRate_str = "40MHz HT 315 Mbps"   ;
               52 : txDataRate_str = "40MHz HT 360 Mbps"   ;
               53 : txDataRate_str = "40MHz HT 150 Mbps"   ;
               54 : txDataRate_str = "40MHz HT 180 Mbps"   ;
               55 : txDataRate_str = "40MHz HT 210 Mbps"   ;
               56 : txDataRate_str = "40MHz HT 180 Mbps"   ;
               57 : txDataRate_str = "40MHz HT 210 Mbps"   ;
               58 : txDataRate_str = "40MHz HT 240 Mbps"   ;
               59 : txDataRate_str = "40MHz HT 270 Mbps"   ;
               60 : txDataRate_str = "40MHz HT 240 Mbps"   ;
               61 : txDataRate_str = "40MHz HT 270 Mbps"   ;
               62 : txDataRate_str = "40MHz HT 300 Mbps"   ;
               63 : txDataRate_str = "40MHz HT 300 Mbps"   ;
               64 : txDataRate_str = "40MHz HT 330 Mbps"   ;
               65 : txDataRate_str = "40MHz HT 225 Mbps"   ;
               66 : txDataRate_str = "40MHz HT 270 Mbps"   ;
               67 : txDataRate_str = "40MHz HT 315 Mbps"   ;
               68 : txDataRate_str = "40MHz HT 270 Mbps"   ;
               69 : txDataRate_str = "40MHz HT 315 Mbps"   ;
               70 : txDataRate_str = "40MHz HT 360 Mbps"   ;
               71 : txDataRate_str = "40MHz HT 405 Mbps"   ;
               72 : txDataRate_str = "40MHz HT 360 Mbps"   ;
               73 : txDataRate_str = "40MHz HT 405 Mbps"   ;
               74 : txDataRate_str = "40MHz HT 450 Mbps"   ;
               75 : txDataRate_str = "40MHz HT 450 Mbps"   ;
               76 : txDataRate_str = "40MHz HT 495 Mbps"   ;
          default : txDataRate_str = "40MHz HT Error 666"  ;
        endcase
      end
      else
      begin
        case (mcs)
               0  : txDataRate_str = "40MHz HT 13.5 Mbps"  ;
               1  : txDataRate_str = "40MHz HT 27 Mbps"    ;
               2  : txDataRate_str = "40MHz HT 40.5 Mbps"  ;
               3  : txDataRate_str = "40MHz HT 54 Mbps"    ;
               4  : txDataRate_str = "40MHz HT 81 Mbps"    ;
               5  : txDataRate_str = "40MHz HT 108 Mbps"   ;
               6  : txDataRate_str = "40MHz HT 121.5 Mbps" ;
               7  : txDataRate_str = "40MHz HT 135 Mbps"   ;
               8  : txDataRate_str = "40MHz HT 27 Mbps"    ;
               9  : txDataRate_str = "40MHz HT 54 Mbps"    ;
               10 : txDataRate_str = "40MHz HT 81 Mbps"    ;
               11 : txDataRate_str = "40MHz HT 108 Mbps"   ;
               12 : txDataRate_str = "40MHz HT 162 Mbps"   ;
               13 : txDataRate_str = "40MHz HT 216 Mbps"   ;
               14 : txDataRate_str = "40MHz HT 243 Mbps"   ;
               15 : txDataRate_str = "40MHz HT 270 Mbps"   ;
               16 : txDataRate_str = "40MHz HT 40.5 Mbps"  ;
               17 : txDataRate_str = "40MHz HT 81 Mbps"    ;
               18 : txDataRate_str = "40MHz HT 121.5 Mbps" ;
               19 : txDataRate_str = "40MHz HT 162 Mbps"   ;
               20 : txDataRate_str = "40MHz HT 243 Mbps"   ;
               21 : txDataRate_str = "40MHz HT 324 Mbps"   ;
               22 : txDataRate_str = "40MHz HT 364.5 Mbps" ;
               23 : txDataRate_str = "40MHz HT 405 Mbps"   ;
               24 : txDataRate_str = "40MHz HT 54 Mbps"    ;
               25 : txDataRate_str = "40MHz HT 108 Mbps"   ;
               26 : txDataRate_str = "40MHz HT 162 Mbps"   ;
               27 : txDataRate_str = "40MHz HT 216 Mbps"   ;
               28 : txDataRate_str = "40MHz HT 324 Mbps"   ;
               29 : txDataRate_str = "40MHz HT 432 Mbps"   ;
               30 : txDataRate_str = "40MHz HT 486 Mbps"   ;
               31 : txDataRate_str = "40MHz HT 540 Mbps"   ;
               33 : txDataRate_str = "40MHz HT 81 Mbps"    ;    
               34 : txDataRate_str = "40MHz HT 108 Mbps"   ;   
               35 : txDataRate_str = "40MHz HT 135 Mbps"   ;   
               36 : txDataRate_str = "40MHz HT 121.5 Mbps" ; 
               37 : txDataRate_str = "40MHz HT 162 Mbps"   ;   
               38 : txDataRate_str = "40MHz HT 202.5 Mbps" ; 
               39 : txDataRate_str = "40MHz HT 108 Mbps"   ;   
               40 : txDataRate_str = "40MHz HT 135 Mbps"   ;  
               41 : txDataRate_str = "40MHz HT 135 Mbps"   ;  
               42 : txDataRate_str = "40MHz HT 162 Mbps"   ;   
               43 : txDataRate_str = "40MHz HT 189 Mbps"   ;   
               44 : txDataRate_str = "40MHz HT 189 Mbps"   ;   
               45 : txDataRate_str = "40MHz HT 216 Mbps"   ;   
               46 : txDataRate_str = "40MHz HT 162 Mbps"   ;   
               47 : txDataRate_str = "40MHz HT 202.5 Mbps" ; 
               48 : txDataRate_str = "40MHz HT 202.5 Mbps" ; 
               49 : txDataRate_str = "40MHz HT 243 Mbps"   ;   
               50 : txDataRate_str = "40MHz HT 283.5 Mbps" ; 
               51 : txDataRate_str = "40MHz HT 283.5 Mbps" ;
               52 : txDataRate_str = "40MHz HT 324 Mbps"   ;   
               53 : txDataRate_str = "40MHz HT 135 Mbps"   ;   
               54 : txDataRate_str = "40MHz HT 162 Mbps"   ;   
               55 : txDataRate_str = "40MHz HT 189 Mbps"   ;   
               56 : txDataRate_str = "40MHz HT 162 Mbps"   ;   
               57 : txDataRate_str = "40MHz HT 189 Mbps"   ;   
               58 : txDataRate_str = "40MHz HT 216 Mbps"   ;   
               59 : txDataRate_str = "40MHz HT 243 Mbps"   ;   
               60 : txDataRate_str = "40MHz HT 216 Mbps"   ;   
               61 : txDataRate_str = "40MHz HT 243 Mbps"   ;   
               62 : txDataRate_str = "40MHz HT 270 Mbps"   ;   
               63 : txDataRate_str = "40MHz HT 270 Mbps"   ;   
               64 : txDataRate_str = "40MHz HT 297 Mbps"   ;   
               65 : txDataRate_str = "40MHz HT 202.5 Mbps" ; 
               66 : txDataRate_str = "40MHz HT 243 Mbps"   ;   
               67 : txDataRate_str = "40MHz HT 283.5 Mbps" ; 
               68 : txDataRate_str = "40MHz HT 243 Mbps"   ;   
               69 : txDataRate_str = "40MHz HT 283.5 Mbps" ; 
               70 : txDataRate_str = "40MHz HT 324 Mbps"   ;   
               71 : txDataRate_str = "40MHz HT 364.5 Mbps" ; 
               72 : txDataRate_str = "40MHz HT 324 Mbps"   ;   
               73 : txDataRate_str = "40MHz HT 364.5 Mbps" ; 
               74 : txDataRate_str = "40MHz HT 405 Mbps"   ;   
               75 : txDataRate_str = "40MHz HT 405 Mbps"   ;   
               76 : txDataRate_str = "40MHz HT 445.5 Mbps" ;                  
          default : txDataRate_str = "40MHz HT Error 666"  ;
        endcase
      end
    end
  end
  else
  begin
    case (legRate)
        4'h0  : txDataRate_str = "Leg 1 Mbps"   ;          
        4'h1  : txDataRate_str = "Leg 2 Mbps"   ;          
        4'h2  : txDataRate_str = "Leg 5.5 Mbps" ;          
        4'h3  : txDataRate_str = "Leg 11 Mbps"  ;          
        4'hb  : txDataRate_str = "Leg 6 Mbps"   ;          
        4'hf  : txDataRate_str = "Leg 9 Mbps"   ;          
        4'ha  : txDataRate_str = "Leg 12 Mbps"  ;          
        4'he  : txDataRate_str = "Leg 18 Mbps"  ;          
        4'h9  : txDataRate_str = "Leg 24 Mbps"  ;          
        4'hd  : txDataRate_str = "Leg 36 Mbps"  ;          
        4'h8  : txDataRate_str = "Leg 48 Mbps"  ;          
        4'hc  : txDataRate_str = "Leg 54 Mbps"  ;          
      default : txDataRate_str = "Leg Error 666";
    endcase
  end
end
`endif // RW_SIMU_ON


`ifdef RW_ASSERT_ON

// Assertion Definitions
///////////////////////////

//$rw_sva Checks if the transmission with a 20MHz BW is never done using a Not Valid MCS.
property notValidMCS20MHzCheck_prop;
@(posedge mcs)
    ((formatMod == 3'd4) && (chBW == 2'd0) && mcs == 9) |->  (nSSInt != 1) && (nSSInt != 2) && (nSSInt != 4);
endproperty
notValidMCS20MHzCheck: assert property (notValidMCS20MHzCheck_prop); 

//$rw_sva Checks if the transmission with a 80MHz BW is never done using a Not Valid MCS.
property notValidMCS80MHzCheck_prop;
@(posedge mcs)
    ((formatMod == 3'd4) && (chBW == 2'd2) && mcs == 6) |->  (nSSInt != 3);
endproperty
notValidMCS80MHzCheck: assert property (notValidMCS80MHzCheck_prop); 

//$rw_sva Checks if the transmission with a 160MHz or 80+80MHz BW is never done using a Not Valid MCS.
property notValidMCS160MHzCheck_prop;
@(posedge mcs)
    ((formatMod == 3'd4) && (chBW == 2'd3) && mcs == 9) |->  (nSSInt != 3);
endproperty
notValidMCS160MHzCheck: assert property (notValidMCS160MHzCheck_prop); 

`endif // RW_ASSERT_ON

endmodule
