//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author: jvanthou $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: 17297 $
// $Date: 2014-12-08 12:18:17 +0100 (Mon, 08 Dec 2014) $
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : Top level of txTimeCalculator module
//                    
// Simulation Notes : 
// Synthesis Notes  : 
//   This design contains two fully asynchronuous clock domains 
//   (macPIClk and macCoreClk). The clock domain crossing is handled in two
//   different ways. 
//     1- All the triggers signals are resynchronized using the 
//        risingEdgeDetector module (resynchronization ff are named _resync).
//     2- All the others signals are not resynchronized because are as per 
//        design, static and can be safely captured when the signals 
//        resynchronized by risingEdgeDetector are high.
//  
//  As a consequence of that, a flash path can be fined between the two clock 
//  domain.
//
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

module txTimeCalculatorAC ( 
          //$port_g Clock and Reset interface
          input  wire        macPIClk,                // MAC Platform Interface Transmit Clock
          input  wire        macPIClkHardRst_n,       // Hard Reset of the MAC Platform Interface Clock domain 
                                                      // active low

          input  wire        macCoreClk,              // MAC Platform Interface Transmit Clock
          input  wire        macCoreClkHardRst_n,     // Hard Reset of the MAC Platform Interface Clock domain 
                                                      // active low

          //$port_g Tx Controller interface
          output  reg        disambiguityMC,          // If VHT and the nSymb modulo 10 is 9 then the flag is high

          //$port_g MAC Controller interface
          input  wire [19:0] ppduLengthMC,            // PPDU Length from MAC Controller
                                                      // This field gives the length of the PPDU for computing time on air.
          input  wire  [2:0] ppduPreTypeMC,           // PPDU Preamble Type from MAC Controller
                                                      // This field indicates what type of preamble is transmitted for the frame.
                                                      // The encoding is as follows:
                                                      // 3'b000: Non-HT-Short
                                                      // 3'b001: Non-HT-Long
                                                      // 3'b010: HT-MF
                                                      // 3'b011: HT-GF
                                                      // 3'b100: VHT
          input  wire  [6:0] ppduMCSIndexMC,          // PPDU LegRate or MCS Index from MAC Controller
                                                      // This field indicates the rate at which this PPDU is transmitted.
          input  wire  [1:0] ppduChBwMC,              // This field indicates the channel bandwidth
          input  wire  [1:0] ppduNumExtnSSMC,         // Number of Extension Spatial Streams      
          input  wire  [1:0] ppduSTBCMC,              // Enable Space Time Block Coding          
          input  wire        ppduShortGIMC,           // PPDU Short Guard Interval from MAC Controller
                                                      // Indicates that the frame should be transmitted with Short GI.
 
          input  wire        woPreambleMC,            // Indicates that total duration should not include the preamble duration 
          input  wire        startComputationMC_p,    // Start Time on Air computation from MAC Controller

          output  reg [15:0] timeOnAirMC,             // Time On Air result to MAC Controller
                                                      // This field gives the time taken for frame transmission in microseconds (us)
                                                      // computed from parameters given by the MAC Controller.
          output  reg        timeOnAirValidMC,        // Time On Air Valid to MAC Controller
                                                      // This field is set when the air time computation is completed.

          //$port_g CSReg interface
          input  wire [19:0] ppduLength,              // PPDU Length
                                                      // This field gives the length of the PPDU for computing time on air.
          input  wire  [1:0] ppduChBw,                // This field indicates the channel bandwidth
          input  wire  [2:0] ppduPreType,             // PPDU Preamble Type
                                                      // This field indicates what type of preamble is transmitted for the frame.
                                                      // The encoding is as follows:
                                                      // 3'b00: Non-HT-Short
                                                      // 3'b01: Non-HT-Long
                                                      // 3'b10: HT-MF
                                                      // 3'b11: HT-GF
                                                      // 3'b11: VHT
          input  wire  [1:0] ppduNumExtnSS,           // Start Transmission with Number of Extension Spatial Streams      
          input  wire  [1:0] ppduSTBC,                // Start Transmission with Space Time Block Coding          
          input  wire        ppduShortGI,             // PPDU Short Guard Interval
                                                      // Indicates that the frame should be transmitted with Short GI.
          input  wire  [6:0] ppduMCSIndex,            // PPDU LegRate or MCS Index
                                                      // This field indicates the rate at which this PPDU is transmitted. 

          input  wire        computeDuration,         // Request to perform a Time on Air computation
          output wire        computeDurationIn,       // Clear the computeDuration
          output wire        computeDurationInValid,  // Clear the computeDuration valid

          output  reg [15:0] timeOnAir,               // Time On Air
          output  reg        timeOnAirValid           // Time on Air is valid
                                                      // This field gives the time taken for frame transmission in microseconds (us)
                                                      // computed from parameters programmed in timeOnAirParamReg register.
  );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

localparam DCCK_SHORT_PREAMBLE  = 16'd96; // Duration of DSSS/CCK Short preamble
localparam DCCK_LONG_PREAMBLE   = 16'd192;// Duration of DSSS/CCK Long preamble
localparam NON_HT_OFDM_PREAMBLE = 16'd20; // Duration of NON-HT OFDM preamble
localparam MM_PREAMBLE          = 16'd32; // Duration of Mixed-Mode preamble
localparam GF_PREAMBLE          = 16'd24; // Duration of GreenField preamble
localparam VHT_PREAMBLE         = 16'd36; // Duration of VHT preamble

// dividerControlFSM FSM states definition
//$fsm_sd dividerControlFSM
localparam
                 IDLE  =  2'd0,  
        COMPUTE_NSYMB  =  2'd1,  
      COMPUTE_SHORTGI  =  2'd2;  


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// dividerControlFSM FSM signals definition
reg   [1:0] dividerControlFSMCs;  // dividerControlFSM FSM Current State
reg   [1:0] dividerControlFSMNs;  // dividerControlFSM FSM Next State

reg   [6:0] mcsIndex_ff1;              // Indicates the rate at which this PPDU is transmitted.
reg         swProcessing;              // Indicates that a SW request is being processed.

reg         startDiv_p;                // Pulse to launch the divider
reg         startDivDly_p;             // Pulse to launch the divider

reg  [14:0] nBitPSymb_comb;            // Combinational number of bits per symbole
reg   [3:0] nSS_comb;                  // Combination number of spacial stream
reg         busy;                      // Busy indication
reg         busyDly;                   // Busy indication
reg         quickDivStart_p;           // Indicates the start of the computation when the divider is not used
reg         quickDivDone_p;            // Indicates the end of the computation when the divider is not used
reg         quickDivDoneDly_p;         // Indicates the end of the computation when the divider is not used (Delay of 1cc)
reg         startComputationMC;        // Indicates that a computation is pending for the MC 
reg         startComputation;          // Indicates that a computation is pending for the Register 
reg  [15:0] preambleDuration;          // Computed preamble duration
reg  [15:0] data14Duration;            // Computed duration for DATA of 14 bytes
reg  [15:0] data20Duration;            // Computed duration for DATA of 20 bytes
reg  [14:0] nBitPSymb;                 // Stored number of bits per symbol
wire [14:0] divisor;                   // Divisor of the divider
wire [23:0] dividend;                  // Dividend of the divider
wire        roundUp;                   // Round Up the result of the division
reg         computeDurationInValidInt; // computeDurationInValid signal coming from the macCoreClk domain

wire  [2:0] preambleType;              // Indicates what type of preamble is transmitted for the frame.
wire        shortGI;                   // Indicates that the frame should be transmitted with Short GI.
wire  [1:0] chBw;                      // Channel Bandwidth
wire  [6:0] mcsIndex;                  // Indicates the rate at which this PPDU is transmitted.
wire [19:0] length;                    // Indicates the length of the PPDU for computing time on air.
wire  [1:0] numExtnSS;                 // Number of extended spacial stream
wire  [1:0] stbc;                      // Indicates that STBC has been selected.

wire [23:0] nBit;                      // Number of bits in ppdu
reg  [23:0] nES;                       // Number of bits in ppdu
wire [23:0] computednSymb;             // Number of Symb computed by the divider
reg  [13:0] computednSymbCapt;         // Number of Symb computed by the divider
reg  [15:0] dataDuration;              // Computed Data Duration
wire [15:0] totalDuration;             // Total duration (preamble + ppdu)
wire        divDone_p;                 // Indicates the end of the computation when the divider is used

wire  [3:0] ndltf;                     // Number of DLTFs required for data space-time streams          
wire  [3:0] neltf;                     // Number of ELTFs required for extension spatial streams
wire  [3:0] vhtltf;                     // Number of VHT-LTFs required for space-time streams

wire  [3:0] nltf;                      // Number of LTFs required for extension spatial streams
wire        isDCCK;                    // Indicates that the modulation is DSSS/CCK
wire  [3:0] initCnt;                   // Initial value of the divider step.
wire        startComputation_p;        // Pulse generated in macCoreClk domain when a rising edge of computeDuration is detected

wire        isLegacy;
//wire        isHT;
wire        isVHT;
wire        is40MHz;
wire        is80MHz;
wire        is160MHz;

wire  [3:0] remainderOut;              // Remainder from divider (oonly used for disambiguity)
reg   [3:0] remainderOutExtraSGIus;    // Convertion of remainderOut into us
wire        endOfProcessing;
`ifdef RW_SIMU_ON
// String definition to display dividerControlFSMCs current state
reg [15*8-1:0] dividerControlFSMCs_str;
`endif // RW_SIMU_ON

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
// Resynchronization with macPIClk for register interface
//////////////////////////////////////////////////////////////////////////////

// Instanciation of risingEdgeDetector
// Name of the instance : U_computeDurationRisingEdgeDetector
// Name of the file containing this module : risingEdgeDetector.v
risingEdgeDetector U_computeDurationRisingEdgeDetector (
    .dstclk       (macCoreClk),
    .dstresetn    (macCoreClkHardRst_n),
    .srcdata      (computeDuration),
    .dstdata      (startComputation_p)
    );

// Instanciation of risingEdgeDetector
// Name of the instance : U_computeDurationInValidRisingEdgeDetector
// Name of the file containing this module : risingEdgeDetector.v
risingEdgeDetector U_computeDurationInValidRisingEdgeDetector (
    .dstclk       (macPIClk),
    .dstresetn    (macPIClkHardRst_n),
    .srcdata      (computeDurationInValidInt),
    .dstdata      (computeDurationInValid)
    );


// Generate the timeOnAirValid indication for register interface
always @ (posedge macPIClk or negedge macPIClkHardRst_n) 
begin
  if (macPIClkHardRst_n == 1'b0)  // Asynchronous Reset
    timeOnAirValid     <= 1'b0;
  else
  begin
    if (computeDurationInValid)
      timeOnAirValid   <= 1'b1;
    else if (computeDuration)
      timeOnAirValid   <= 1'b0;
  end
end

//////////////////////////////////////////////////////////////////////////////
// Control from MAC Controller interface
//////////////////////////////////////////////////////////////////////////////
assign endOfProcessing = (divDone_p && ((!shortGI && (dividerControlFSMCs == COMPUTE_NSYMB)) || 
                                        (dividerControlFSMCs == COMPUTE_SHORTGI)));

// Generate of the startComputationMC signal which indicates
// a pending request from the MAC Controller
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    startComputationMC <= 1'b0;
  else
    if (startComputationMC_p)
      startComputationMC <= 1'b1;
    else if (!swProcessing && (quickDivDoneDly_p || endOfProcessing))
      startComputationMC <= 1'b0;
end 
      
// Generate of the startComputation signal which indicates
// a pending request from the Registers
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    startComputation <= 1'b0;
  else
    if (startComputation_p)
      startComputation <= 1'b1;
    else if (swProcessing && (quickDivDoneDly_p || endOfProcessing))
      startComputation <= 1'b0;
end 

// Capture the computed timeOnAir duration requested by the MAC Controller.
// This value is stable when timeOnAirValidMC is set.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    timeOnAirMC <= 16'b0;
    timeOnAirValidMC <= 1'b0;
  end
  else
  begin
    if (startComputationMC_p)
      timeOnAirValidMC <= 1'b0;
    else
    begin
      if (!swProcessing && (quickDivDoneDly_p || endOfProcessing))
      begin
        timeOnAirMC      <= totalDuration;
        timeOnAirValidMC <= 1'b1;
      end  
    end  
  end
end

      
// Capture the computed timeOnAir duration requested by the registers.
// This value is stable until the next request from the registers.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    timeOnAir <= 16'b0;
    computeDurationInValidInt <= 1'b0;
  end
  else
  begin
    computeDurationInValidInt <= 1'b0;
    if (swProcessing && (quickDivDoneDly_p || endOfProcessing))
    begin
      timeOnAir                 <= totalDuration;
      computeDurationInValidInt <= 1'b1;
    end  
  end
end

// Logic to clear the startComputation bit in the CSReg.
assign computeDurationIn = 1'b0;

// Indicate if the on-going computing has been requested by the MAC Controller
// (swProcessing = 0) or the register (swProcessing = 1)
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    swProcessing <= 1'b0;
  else
  begin
    if (!busy)
    begin
      if (startComputationMC || startComputationMC_p)
        swProcessing <= 1'b0;
      else if (startComputation || startComputation_p)
        swProcessing <= 1'b1;
    end    
  end    
end

// dividerControlFSM FSM Current State Logic 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    dividerControlFSMCs <= IDLE; 
  else
    dividerControlFSMCs <= dividerControlFSMNs; 
end


// dividerControlFSM FSM Next State Logic.
always @* 
begin
  case(dividerControlFSMCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits for a trigger.
      if (startDiv_p) 
        //$fsm_t When startDiv_p is received, the state machine goes to COMPUTE_NSYMB state.
        dividerControlFSMNs = COMPUTE_NSYMB; 
      else
        //$fsm_t While startDiv_p is not received, the state machine stays in IDLE state.
        dividerControlFSMNs = IDLE;

    COMPUTE_NSYMB:
      //$fsm_s In COMPUTE_NSYMB state, the state machine controls the divider to compute the number of Symbol.
      if (divDone_p && shortGI) 
        //$fsm_t When divDone_p is received and shortGI is set, the state machine goes to COMPUTE_SHORTGI state.
        dividerControlFSMNs = COMPUTE_SHORTGI; 
      else if (divDone_p && !shortGI) 
        //$fsm_t When divDone_p is received and shortGI is not set, the state machine goes back to IDLE state.
        dividerControlFSMNs = IDLE; 
      else
        //$fsm_t While divDone_p is not received, the state machine stays in COMPUTE_NSYMB state.
        dividerControlFSMNs = COMPUTE_NSYMB;

    COMPUTE_SHORTGI:
      //$fsm_s In COMPUTE_SHORTGI state, the state machine controls the divider to divide the number of Symbol by 10.
      if (divDone_p) 
        //$fsm_t When startDiv_p is received, the state machine goes back to IDLE state.
        dividerControlFSMNs = IDLE; 
      else
        //$fsm_t While divDone_p is not received, the state machine stays in COMPUTE_SHORTGI state.
        dividerControlFSMNs = COMPUTE_SHORTGI;

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
     default:   
        dividerControlFSMNs = IDLE; 
    // pragma coverage block = on 
  endcase
end


// Generation of the startDiv_p pulse which trigs the divider.
// The divider is used for all the ppdu length value except 14 and 20.
// For those values, the computing has been speed up.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    startDiv_p    <= 1'b0;
    startDivDly_p <= 1'b0;
  end
  else
  begin
    startDivDly_p <= startDiv_p;
    if (!busyDly)
    begin
      if (!swProcessing && startComputationMC  && (ppduMCSIndexMC > 7'd1 || ppduPreTypeMC[2:1] != 2'd0) && (ppduLengthMC != 20'd0) && (ppduLengthMC != 20'd14) && (ppduLengthMC != 20'd20)) 
        startDiv_p <= 1'b1;
      else if (swProcessing && startComputation && (ppduMCSIndex > 7'd1 || ppduPreType[2:1] != 2'd0) && (ppduLength != 20'd0) && (ppduLength != 20'd14) && (ppduLength != 20'd20)) 
        startDiv_p <= 1'b1;
      else    
        startDiv_p <= 1'b0;
    end
    else if (divDone_p && (dividerControlFSMCs == COMPUTE_NSYMB) && shortGI)
      startDiv_p <= 1'b1;
    else
      startDiv_p <= 1'b0;
  end
end

// Generate the quickDivDone_p pulse. This pulse indicates the completion of a 
// duration computing which did not used the divider.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    quickDivStart_p   <= 1'b0;
    quickDivDone_p    <= 1'b0;
    quickDivDoneDly_p <= 1'b0;
  end
  else
  begin
    quickDivDoneDly_p <= quickDivDone_p;
    quickDivDone_p    <= quickDivStart_p;
    if (!busyDly)
    begin
      if (!swProcessing && startComputationMC  && ((ppduMCSIndexMC <= 7'd1 && ppduPreTypeMC[2:1] == 2'b0) || (ppduLengthMC == 20'd0) || (ppduLengthMC == 20'd14) || (ppduLengthMC == 20'd20))) 
        quickDivStart_p <= 1'b1;
      else if (swProcessing && startComputation && ((ppduMCSIndex <= 7'd1 && ppduPreType[2:1] == 2'b0) || (ppduLength == 20'd0) || (ppduLength == 20'd14) || (ppduLength == 20'd20))) 
        quickDivStart_p <= 1'b1;
      else    
        quickDivStart_p <= 1'b0;
    end
    else    
      quickDivStart_p <= 1'b0;
  end    
end

// Generation of the busy signal which indicates an on-going processing
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    busy    <= 1'b0;
    busyDly <= 1'b0;
  end
  else
  begin
    busyDly <= busy;
    if (!busy && (startComputation || startComputationMC || startComputation_p || startComputationMC_p))
      busy <= 1'b1;
    if (endOfProcessing || quickDivDoneDly_p || computeDurationInValidInt)
      busy <= 1'b0;
  end    
end

// totalDuration = preambleDuration + dataDuration.
// In case of MCS 0 or 1 (1Mpbs or 2Mbps), the dataDuration is the length 
// multiplied by 8 (1Mbps) or by 4 (2Mbps)
assign totalDuration = (!swProcessing && woPreambleMC) ? dataDuration[15:0] : preambleDuration + dataDuration[15:0];


// Assign the different parameter depending of the source of the request 
//(MAC Controller or Registers)
assign mcsIndex     = (swProcessing) ? ppduMCSIndex   : ppduMCSIndexMC;
assign length       = (swProcessing) ? ppduLength     : ppduLengthMC;
assign preambleType = (swProcessing) ? ppduPreType    : ppduPreTypeMC;

assign isLegacy     = (preambleType[2:1] == 2'b00);
//assign isHT         = (preambleType[2:1] == 2'b01);
assign isVHT        = (preambleType      == 3'b100);

assign stbc         = (isLegacy) ? 2'b0 : (swProcessing) ? ppduSTBC       : ppduSTBCMC;
assign shortGI      = (isLegacy) ? 1'b0 : (swProcessing) ? ppduShortGI    : ppduShortGIMC;
assign chBw         = (isLegacy) ? 2'b0 : (swProcessing) ? ppduChBw       : ppduChBwMC;

assign numExtnSS    = (isLegacy || isVHT) ? 2'b0 : (swProcessing) ? ppduNumExtnSS  : ppduNumExtnSSMC;

assign is40MHz      = (chBw == 2'd1);
assign is80MHz      = (chBw == 2'd2);
assign is160MHz     = (chBw == 2'd3);

// Indicates if the modulation is DSSS/CCK or not.
assign isDCCK = ((mcsIndex<7'd4) && (preambleType[2:1] == 2'b00)) ? 1'b1 : 1'b0;


// For DSSS/CCK modulation (MCSIndex < 4 and PreType < 2)
// 
// duration = preambleduration + length*8/dataRate
// If preambleType = 0 (Short preamble), preambleduration = 96
// If preambleType = 1 (Long preamble),  preambleduration = 192
//
// If MCSIndex = 0, datarate = 1
// If MCSIndex = 1, datarate = 2
// If MCSIndex = 2, datarate = 5.5
// If MCSIndex = 3, datarate = 11
//
//
// For OFDM modulation (Legacy and HT and VHT)
// 
// duration = preambleduration + dataduration
//
// preambleduration = If LEGACY then 20us
//                    If HT MixMode then 32us + NLTF*4
//                    If HT GreendField then 24us + (NLTF-1)*4
//                    If VHT then 36us + NLTF*4
//
// NLTF             = depends on HT or VHT NSS, and extNSS for HT only
//
// dataduration     = ceil( NumberOfSymbols * SymbolDuration)
//
// SymbolDuration   = is 4 us for Normal Guard Interval and 3.6 for Short Guard Interval
//
// NumberOfSymbols  = If no STBC then  ceil((length*8+22)/NDBPS) else 2*ceil((length*8+22)/NDBPS)
//
// NDBPS            = Number of data bits per symbol (it is defined according to the MCSINDEX and the operating mode LEGACY or HT or VHT)
// Note: The 22 bits in the formula come from the 16 bits of service field and 6 tail bits.


// Instanciation of divider
// Name of the instance : U_divider
// Name of the file containing this module : divider.v
divider #(.NBIT_WIDTH(24),.NBITPSYMB_WIDTH(15)) U_divider (
    .macCoreClk             (macCoreClk),
    .macCoreClkHardRst_n    (macCoreClkHardRst_n),
    .startDiv_p             (startDivDly_p),
    .roundUp                (roundUp),
    .nBit                   (dividend),
    .nBitPSymb              (divisor),
    .initCnt                (initCnt),
    .nSymb                  (computednSymb),
    .remainderOut           (remainderOut),
    .divDone_p              (divDone_p)
    );

assign divisor  = (dividerControlFSMNs == COMPUTE_SHORTGI) ? 15'ha : nBitPSymb;
assign dividend = (dividerControlFSMNs == COMPUTE_SHORTGI) ? ((stbc > 2'd0) ? computednSymb<<24'd1 : computednSymb<<24'd0) : nBit;
assign roundUp  = (dividerControlFSMCs == COMPUTE_NSYMB) ? 1'b1 : 1'b0;

// Generation of the disambiguity
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    disambiguityMC <= 1'b0;
  else if (startDiv_p)
    disambiguityMC <= 1'b0;
  else if (divDone_p && (dividerControlFSMCs == COMPUTE_SHORTGI) && (remainderOut == 4'd9) && (preambleType == 3'b100) && !swProcessing)
    disambiguityMC <= 1'b1;
end

// Generation of the busy signal which indicates an on-going processing
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    computednSymbCapt <= 14'b0;
  else
    if (divDone_p && (dividerControlFSMCs == COMPUTE_NSYMB))
    begin
      if (stbc > 2'd0)
        computednSymbCapt <= {computednSymb[12:0],1'b0};
      else  
        computednSymbCapt <= computednSymb[13:0];
    end    
end

//
always @(*)
begin
  if(shortGI)
  begin
    case(remainderOut)
      4'd3: remainderOutExtraSGIus = 4'd1; // (3*4)/10 = 1.2
      4'd4: remainderOutExtraSGIus = 4'd1; // (4*4)/10 = 1.6
      4'd5: remainderOutExtraSGIus = 4'd2; // (5*4)/10 = 2.0
      4'd6: remainderOutExtraSGIus = 4'd2; // (6*4)/10 = 2.4
      4'd7: remainderOutExtraSGIus = 4'd2; // (7*4)/10 = 2.8
      4'd8: remainderOutExtraSGIus = 4'd3; // (8*4)/10 = 3.2
      4'd9: remainderOutExtraSGIus = 4'd3; // (9*4)/10 = 3.6
      default: remainderOutExtraSGIus = 4'd0; // Others remainder value is not modulo 10 or less than 3
    endcase
  end
  else
  begin
    remainderOutExtraSGIus = 4'd0;
  end
end


// assign dataDuration with the computed duration 
always @ *
begin
  if (length == 20'd0)
    dataDuration = 16'd0;
  else if (length == 20'd14)
    dataDuration = data14Duration;
  else if (length == 20'd20)
    dataDuration = data20Duration;
  else if(isLegacy)
  begin
    if (mcsIndex_ff1 == 7'd0) // 1 Mbps
      dataDuration = {length[12:0],3'b0};
    else if (mcsIndex_ff1 == 7'd1) // 2 Mbps
      dataDuration = {length[13:0],2'b0};
    else if (isDCCK)
      dataDuration = computednSymb[15:0];
    else
      dataDuration = {computednSymb[13:0],2'b0};
  end
  else // isHT or VHT
  begin
    if (shortGI)
      dataDuration = {computednSymbCapt[13:0],2'b00} - {computednSymb[13:0],2'b00} - {12'b0,remainderOutExtraSGIus};
    else
    begin
      if (stbc > 2'd0) 
        dataDuration = {computednSymb[12:0],3'b0};
      else 
        dataDuration = {computednSymb[13:0],2'b0};
    end
  end
end

// Set the number of steps done by the divider.
// As the divider does 5 steps per clock cycle, this number must be a multiple of 5.
// The max value is 15.
assign initCnt = (nBit < 24'd256) ? 4'd5 : 4'd15;
//assign initCnt = 15;


////    Table 20-11 -- Determining the number of space time streams
////      +---------------------+------------+-----------------+
////      |  Number of Spatial  | STBC field | Number of space |
////      |  Streams (from MCS) |            | time streams    |
////      +---------------------+------------+-----------------+
////      |          1          |      0     |        1        | 
////      |          1          |      1     |        2        | 
////      |          2          |      0     |        2        | 
////      |          2          |      1     |        3        | 
////      |          2          |      2     |        4        | 
////      |          3          |      0     |        3        | 
////      |          3          |      1     |        4        | 
////      |          4          |      0     |        4        | 
////      +---------------------+------------+-----------------+
////
////    Table 20-12 -- Number of DLTFs required for data space-time streams
////      +-------+-------+
////      |  NSTS | NDLTF |
////      +-------+-------+
////      |  1    |   1   | 
////      |  2    |   2   | 
////      |  3    |   4   | 
////      |  4    |   4   |
////      +-------+-------+
assign ndltf = ((nSS_comb + {2'b00,stbc}) == 4'd3) ? 4'd4 : (nSS_comb+{2'b00,stbc});

////assign ndltf = nSS_comb;
////assign ndltf = nSS_comb+stbc;
//
////    Table 20-13 -- Number of ELTFs required for extension spatial streams
////      +-------+-------+
////      |  NESS | NELTF |
////      +-------+-------+
////      |  0    |   0   | 
////      |  1    |   1   | 
////      |  2    |   2   | 
////      |  3    |   4   |
////      +-------+-------+
assign neltf = (numExtnSS == 2'd3) ? 4'd4 : {2'b00,numExtnSS};

////    Table 22-13 -- Number of VHT LTFs required for differents number of spatial streams
////      +-------+---------+
////      |  NSTS | NVHTLTF |
////      +-------+---------+
////      |  1    |   1     |
////      |  2    |   2     |
////      |  3    |   4     |
////      |  4    |   4     |
////      |  5    |   6     |
////      |  6    |   6     |
////      |  7    |   8     |
////      |  8    |   8     |
////      +-------+---------+
// if stbc == 1 then NSTS = NSS * 2 else NSTS = NSS
assign vhtltf  = (stbc == 2'd1)     ? {nSS_comb[2:0],1'b0} : 
                 (nSS_comb == 4'd1) ? 4'd1                 : 
                 (nSS_comb[0])      ? nSS_comb + 4'd1      : 
                                      nSS_comb;



// For DSSS/CCK modulation (MCSIndex < 4)
//
// If preambleType = 0 (Short preamble), preambleduration = 96
// If preambleType = 1 (Long preamble),  preambleduration = 192
//
// For non-HT OFDM modulation (4 <= MCSIndex <= 11)
// 
// preambleduration = 20
//
// For HT OFDM modulation
//
// If preambleType = 2 (HT MixedMode)
// If preambleType = 3 (HT GreenField)
// 
// duration = preambleduration + dataduration
// preambleduration :
//    If Greenfield mode :
//        preambleduration = 8+8+8+(NLTF-1)*4
//        preambleduration = 24+(NLTF-1)*4
//    If MixedMode mode :
//        preambleduration = 8+8+4+8+4+(NLTF)*4
//        preambleduration = 32+(NLTF)*4
//
// The total number of HT-LTFs is:
// NLTF = NDLTF + NELTF       (20-22)
// The number of Data HT-LTFs is denoted NDLTF. The number of extension HT-LTFs is denoted NELTF. 
// NLTF shall not exceed 5. 
// Table 20-11 shows the determination of the number of space time streams from the
// MCS and STBC fields in the HT-SIG. Table 20-12 shows the number of Data HT-LTFs as a function of the
// number of space time streams (NSTS). Table 20-13 shows the number of extension HT-LTFs as a function of
// the number of extension spatial streams (NESS).NSTS plus NESS is less than or equal to 4. In the case where
// NSTS equals 3, NESS cannot exceed one; if NESS equals one in this case then NLTF equals 5.

assign nltf = (preambleType == 3'b010) ? ndltf+neltf       :
              (preambleType == 3'b011) ? ndltf+neltf-4'd1  :
                                         vhtltf            ;

// Set the preambleDuration depending on the MCS and the preamble type.
always @*
begin
  if ((mcsIndex_ff1 < 7'd4) && (preambleType == 3'b001)) 
    preambleDuration = DCCK_LONG_PREAMBLE;
  else if ((mcsIndex_ff1 < 7'd4) && (preambleType == 3'b000))
    preambleDuration = DCCK_SHORT_PREAMBLE;
  else if (preambleType[2:1] == 2'b00)
    preambleDuration = NON_HT_OFDM_PREAMBLE;
  else
  begin
    if (preambleType == 3'b010) // MixedMode
      preambleDuration = MM_PREAMBLE+{10'b0,nltf,2'b0};
    else if(preambleType == 3'b011) // GreenField
      preambleDuration = GF_PREAMBLE+{10'b0,nltf,2'b0};
    else // VHT
      preambleDuration = VHT_PREAMBLE+{10'b0,vhtltf,2'b0};
  end
end    

// Set nBitPSymb_comb with the number of bits per symbole.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    nBitPSymb_comb <= 15'd0;
  else if (preambleType[2:1] == 2'b00)
  begin
    case (mcsIndex[3:0])
             4'd0 : nBitPSymb_comb <= 15'd2;   // This value have been muplitplied by 2
             4'd1 : nBitPSymb_comb <= 15'd4;   // This value have been muplitplied by 2
             4'd2 : nBitPSymb_comb <= 15'd11;  // This value have been muplitplied by 2
             4'd3 : nBitPSymb_comb <= 15'd22;  // This value have been muplitplied by 2
             4'd4 : nBitPSymb_comb <= 15'd24;  //  6Mbps
             4'd5 : nBitPSymb_comb <= 15'd36;  //  9Mbps
             4'd6 : nBitPSymb_comb <= 15'd48;  // 12Mbps 
             4'd7 : nBitPSymb_comb <= 15'd72;  // 18Mbps 
             4'd8 : nBitPSymb_comb <= 15'd96;  // 24Mbps 
             4'd9 : nBitPSymb_comb <= 15'd144; // 36Mbps 
            4'd10 : nBitPSymb_comb <= 15'd192; // 48Mbps 
            4'd11 : nBitPSymb_comb <= 15'd216; // 54Mbps 
    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
       default : nBitPSymb_comb <= 15'd1;    
    // pragma coverage block = on
    endcase                           
  end
  else if(preambleType[2:1] == 2'b01)
  // In case of HT rate.
  begin
    case (mcsIndex[6:0])
             7'd0 : nBitPSymb_comb <= (is40MHz) ? 15'd54    : 15'd26   ;
             7'd1 : nBitPSymb_comb <= (is40MHz) ? 15'd108   : 15'd52   ;
             7'd2 : nBitPSymb_comb <= (is40MHz) ? 15'd162   : 15'd78   ;
             7'd3 : nBitPSymb_comb <= (is40MHz) ? 15'd216   : 15'd104  ;
             7'd4 : nBitPSymb_comb <= (is40MHz) ? 15'd324   : 15'd156  ;
             7'd5 : nBitPSymb_comb <= (is40MHz) ? 15'd432   : 15'd208  ;
             7'd6 : nBitPSymb_comb <= (is40MHz) ? 15'd486   : 15'd234  ;
             7'd7 : nBitPSymb_comb <= (is40MHz) ? 15'd540   : 15'd260  ;
             7'd8 : nBitPSymb_comb <= (is40MHz) ? 15'd108   : 15'd52   ;
             7'd9 : nBitPSymb_comb <= (is40MHz) ? 15'd216   : 15'd104  ;
            7'd10 : nBitPSymb_comb <= (is40MHz) ? 15'd324   : 15'd156  ;
            7'd11 : nBitPSymb_comb <= (is40MHz) ? 15'd432   : 15'd208  ;
            7'd12 : nBitPSymb_comb <= (is40MHz) ? 15'd648   : 15'd312  ;
            7'd13 : nBitPSymb_comb <= (is40MHz) ? 15'd864   : 15'd416  ;
            7'd14 : nBitPSymb_comb <= (is40MHz) ? 15'd972   : 15'd468  ;
            7'd15 : nBitPSymb_comb <= (is40MHz) ? 15'd1080  : 15'd520  ;
            7'd16 : nBitPSymb_comb <= (is40MHz) ? 15'd162   : 15'd78   ;
            7'd17 : nBitPSymb_comb <= (is40MHz) ? 15'd324   : 15'd156  ;
            7'd18 : nBitPSymb_comb <= (is40MHz) ? 15'd486   : 15'd234  ;
            7'd19 : nBitPSymb_comb <= (is40MHz) ? 15'd648   : 15'd312  ;
            7'd20 : nBitPSymb_comb <= (is40MHz) ? 15'd972   : 15'd468  ;
            7'd21 : nBitPSymb_comb <= (is40MHz) ? 15'd1296  : 15'd624  ;
            7'd22 : nBitPSymb_comb <= (is40MHz) ? 15'd1458  : 15'd702  ;
            7'd23 : nBitPSymb_comb <= (is40MHz) ? 15'd1620  : 15'd780  ;
            7'd24 : nBitPSymb_comb <= (is40MHz) ? 15'd216   : 15'd104  ;
            7'd25 : nBitPSymb_comb <= (is40MHz) ? 15'd432   : 15'd208  ;
            7'd26 : nBitPSymb_comb <= (is40MHz) ? 15'd648   : 15'd312  ;
            7'd27 : nBitPSymb_comb <= (is40MHz) ? 15'd864   : 15'd416  ;
            7'd28 : nBitPSymb_comb <= (is40MHz) ? 15'd1296  : 15'd624  ;
            7'd29 : nBitPSymb_comb <= (is40MHz) ? 15'd1728  : 15'd832  ;
            7'd30 : nBitPSymb_comb <= (is40MHz) ? 15'd1944  : 15'd936  ;
            7'd31 : nBitPSymb_comb <= (is40MHz) ? 15'd2160  : 15'd1040 ;
            7'd32 : nBitPSymb_comb <=                         15'd24   ;
            7'd33 : nBitPSymb_comb <= (is40MHz) ? 15'd324   : 15'd156  ;
            7'd34 : nBitPSymb_comb <= (is40MHz) ? 15'd432   : 15'd208  ;
            7'd35 : nBitPSymb_comb <= (is40MHz) ? 15'd540   : 15'd260  ;
            7'd36 : nBitPSymb_comb <= (is40MHz) ? 15'd486   : 15'd234  ;
            7'd37 : nBitPSymb_comb <= (is40MHz) ? 15'd648   : 15'd312  ;
            7'd38 : nBitPSymb_comb <= (is40MHz) ? 15'd810   : 15'd390  ;
            7'd39 : nBitPSymb_comb <= (is40MHz) ? 15'd432   : 15'd208  ;
            7'd40 : nBitPSymb_comb <= (is40MHz) ? 15'd540   : 15'd260  ;
            7'd41 : nBitPSymb_comb <= (is40MHz) ? 15'd540   : 15'd260  ;
            7'd42 : nBitPSymb_comb <= (is40MHz) ? 15'd648   : 15'd312  ;
            7'd43 : nBitPSymb_comb <= (is40MHz) ? 15'd756   : 15'd364  ;
            7'd44 : nBitPSymb_comb <= (is40MHz) ? 15'd756   : 15'd364  ;
            7'd45 : nBitPSymb_comb <= (is40MHz) ? 15'd864   : 15'd416  ;
            7'd46 : nBitPSymb_comb <= (is40MHz) ? 15'd648   : 15'd312  ;
            7'd47 : nBitPSymb_comb <= (is40MHz) ? 15'd810   : 15'd390  ;
            7'd48 : nBitPSymb_comb <= (is40MHz) ? 15'd810   : 15'd390  ;
            7'd49 : nBitPSymb_comb <= (is40MHz) ? 15'd972   : 15'd468  ;
            7'd50 : nBitPSymb_comb <= (is40MHz) ? 15'd1134  : 15'd546  ;
            7'd51 : nBitPSymb_comb <= (is40MHz) ? 15'd1134  : 15'd546  ;
            7'd52 : nBitPSymb_comb <= (is40MHz) ? 15'd1296  : 15'd624  ;
            7'd53 : nBitPSymb_comb <= (is40MHz) ? 15'd540   : 15'd260  ;
            7'd54 : nBitPSymb_comb <= (is40MHz) ? 15'd648   : 15'd312  ;
            7'd55 : nBitPSymb_comb <= (is40MHz) ? 15'd756   : 15'd364  ;
            7'd56 : nBitPSymb_comb <= (is40MHz) ? 15'd648   : 15'd312  ;
            7'd57 : nBitPSymb_comb <= (is40MHz) ? 15'd756   : 15'd364  ;
            7'd58 : nBitPSymb_comb <= (is40MHz) ? 15'd864   : 15'd416  ;
            7'd59 : nBitPSymb_comb <= (is40MHz) ? 15'd972   : 15'd468  ;
            7'd60 : nBitPSymb_comb <= (is40MHz) ? 15'd864   : 15'd416  ;
            7'd61 : nBitPSymb_comb <= (is40MHz) ? 15'd972   : 15'd468  ;
            7'd62 : nBitPSymb_comb <= (is40MHz) ? 15'd1080  : 15'd520  ;
            7'd63 : nBitPSymb_comb <= (is40MHz) ? 15'd1080  : 15'd520  ;
            7'd64 : nBitPSymb_comb <= (is40MHz) ? 15'd1188  : 15'd572  ;
            7'd65 : nBitPSymb_comb <= (is40MHz) ? 15'd810   : 15'd390  ;
            7'd66 : nBitPSymb_comb <= (is40MHz) ? 15'd972   : 15'd468  ;
            7'd67 : nBitPSymb_comb <= (is40MHz) ? 15'd1134  : 15'd546  ;
            7'd68 : nBitPSymb_comb <= (is40MHz) ? 15'd972   : 15'd468  ;
            7'd69 : nBitPSymb_comb <= (is40MHz) ? 15'd1134  : 15'd546  ;
            7'd70 : nBitPSymb_comb <= (is40MHz) ? 15'd1296  : 15'd624  ;
            7'd71 : nBitPSymb_comb <= (is40MHz) ? 15'd1458  : 15'd702  ;
            7'd72 : nBitPSymb_comb <= (is40MHz) ? 15'd1296  : 15'd624  ;
            7'd73 : nBitPSymb_comb <= (is40MHz) ? 15'd1458  : 15'd702  ;
            7'd74 : nBitPSymb_comb <= (is40MHz) ? 15'd1620  : 15'd780  ;
            7'd75 : nBitPSymb_comb <= (is40MHz) ? 15'd1620  : 15'd780  ;
            7'd76 : nBitPSymb_comb <= (is40MHz) ? 15'd1782  : 15'd858  ;
    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
       default : nBitPSymb_comb <= 15'd1;
    // pragma coverage block = on 
    endcase
  end
  else if(preambleType[2:0] == 3'b100)
  // VHT - Table 22-30 to 22-61
  begin
    case(nSS_comb)
      4'd1:
      begin
        case(mcsIndex[3:0])
          4'd0: nBitPSymb_comb <= (is160MHz) ? 15'd234 : (is80MHz) ? 15'd117 : (is40MHz) ? 15'd54 : 15'd26  ;
          4'd1: nBitPSymb_comb <= (is160MHz) ? 15'd468 : (is80MHz) ? 15'd234 : (is40MHz) ? 15'd108: 15'd52  ;
          4'd2: nBitPSymb_comb <= (is160MHz) ? 15'd702 : (is80MHz) ? 15'd351 : (is40MHz) ? 15'd162: 15'd78  ;
          4'd3: nBitPSymb_comb <= (is160MHz) ? 15'd936 : (is80MHz) ? 15'd468 : (is40MHz) ? 15'd216: 15'd104 ;
          4'd4: nBitPSymb_comb <= (is160MHz) ? 15'd1404: (is80MHz) ? 15'd702 : (is40MHz) ? 15'd324: 15'd156 ;
          4'd5: nBitPSymb_comb <= (is160MHz) ? 15'd1872: (is80MHz) ? 15'd936 : (is40MHz) ? 15'd432: 15'd208 ;
          4'd6: nBitPSymb_comb <= (is160MHz) ? 15'd2106: (is80MHz) ? 15'd1053: (is40MHz) ? 15'd486: 15'd234 ;
          4'd7: nBitPSymb_comb <= (is160MHz) ? 15'd2340: (is80MHz) ? 15'd1170: (is40MHz) ? 15'd540: 15'd260 ;
          4'd8: nBitPSymb_comb <= (is160MHz) ? 15'd2808: (is80MHz) ? 15'd1404: (is40MHz) ? 15'd648: 15'd312 ;
          4'd9: nBitPSymb_comb <= (is160MHz) ? 15'd3120: (is80MHz) ? 15'd1560: (is40MHz) ? 15'd720: 15'd1   ;
          // Disable coverage on the default state because it cannot be reached.
          // pragma coverage block = off 
          default: nBitPSymb_comb <= 15'd1;
          // pragma coverage block = on
        endcase
      end
      4'd2:
      begin
        case(mcsIndex[3:0])
          4'd0: nBitPSymb_comb <= (is160MHz) ? 15'd468 : (is80MHz) ? 15'd234 : (is40MHz) ? 15'd108 : 15'd52   ;
          4'd1: nBitPSymb_comb <= (is160MHz) ? 15'd936 : (is80MHz) ? 15'd468 : (is40MHz) ? 15'd216 : 15'd104  ;
          4'd2: nBitPSymb_comb <= (is160MHz) ? 15'd1404: (is80MHz) ? 15'd702 : (is40MHz) ? 15'd324 : 15'd156  ;
          4'd3: nBitPSymb_comb <= (is160MHz) ? 15'd1872: (is80MHz) ? 15'd936 : (is40MHz) ? 15'd432 : 15'd208  ;
          4'd4: nBitPSymb_comb <= (is160MHz) ? 15'd2808: (is80MHz) ? 15'd1404: (is40MHz) ? 15'd648 : 15'd312  ;
          4'd5: nBitPSymb_comb <= (is160MHz) ? 15'd3744: (is80MHz) ? 15'd1872: (is40MHz) ? 15'd864 : 15'd416  ;
          4'd6: nBitPSymb_comb <= (is160MHz) ? 15'd4212: (is80MHz) ? 15'd2106: (is40MHz) ? 15'd972 : 15'd468  ;
          4'd7: nBitPSymb_comb <= (is160MHz) ? 15'd4680: (is80MHz) ? 15'd2340: (is40MHz) ? 15'd1080: 15'd520  ;
          4'd8: nBitPSymb_comb <= (is160MHz) ? 15'd5616: (is80MHz) ? 15'd2808: (is40MHz) ? 15'd1296: 15'd624  ;
          4'd9: nBitPSymb_comb <= (is160MHz) ? 15'd6240: (is80MHz) ? 15'd3120: (is40MHz) ? 15'd1440: 15'd1    ;
          // Disable coverage on the default state because it cannot be reached.
          // pragma coverage block = off 
          default: nBitPSymb_comb <= 15'd1;
          // pragma coverage block = on
        endcase
      end
      4'd3:
      begin
        case(mcsIndex[3:0])
          4'd0: nBitPSymb_comb <= (is160MHz) ? 15'd702 : (is80MHz) ? 15'd351 : (is40MHz) ? 15'd162 : 15'd78   ;
          4'd1: nBitPSymb_comb <= (is160MHz) ? 15'd1404: (is80MHz) ? 15'd702 : (is40MHz) ? 15'd324 : 15'd156  ;
          4'd2: nBitPSymb_comb <= (is160MHz) ? 15'd2106: (is80MHz) ? 15'd1053: (is40MHz) ? 15'd486 : 15'd234  ;
          4'd3: nBitPSymb_comb <= (is160MHz) ? 15'd2808: (is80MHz) ? 15'd1404: (is40MHz) ? 15'd648 : 15'd312  ;
          4'd4: nBitPSymb_comb <= (is160MHz) ? 15'd4212: (is80MHz) ? 15'd2106: (is40MHz) ? 15'd972 : 15'd468  ;
          4'd5: nBitPSymb_comb <= (is160MHz) ? 15'd5616: (is80MHz) ? 15'd2808: (is40MHz) ? 15'd1296: 15'd624  ;
          4'd6: nBitPSymb_comb <= (is160MHz) ? 15'd6318: (is80MHz) ? 15'd1   : (is40MHz) ? 15'd1458: 15'd702  ;
          4'd7: nBitPSymb_comb <= (is160MHz) ? 15'd7020: (is80MHz) ? 15'd3510: (is40MHz) ? 15'd1620: 15'd780  ;
          4'd8: nBitPSymb_comb <= (is160MHz) ? 15'd8424: (is80MHz) ? 15'd4212: (is40MHz) ? 15'd1944: 15'd936  ;
          4'd9: nBitPSymb_comb <= (is160MHz) ? 15'd1   : (is80MHz) ? 15'd4680: (is40MHz) ? 15'd2160: 15'd1040 ;
          // Disable coverage on the default state because it cannot be reached.
          // pragma coverage block = off 
          default: nBitPSymb_comb <= 15'd1;
          // pragma coverage block = on
        endcase
      end
      4'd4:
      begin
        case(mcsIndex[3:0])
          4'd0: nBitPSymb_comb <= (is160MHz) ? 15'd936  : (is80MHz) ? 15'd468 : (is40MHz) ? 15'd216 : 15'd104  ;
          4'd1: nBitPSymb_comb <= (is160MHz) ? 15'd1872 : (is80MHz) ? 15'd936 : (is40MHz) ? 15'd432 : 15'd208  ;
          4'd2: nBitPSymb_comb <= (is160MHz) ? 15'd2808 : (is80MHz) ? 15'd1404: (is40MHz) ? 15'd648 : 15'd312  ;
          4'd3: nBitPSymb_comb <= (is160MHz) ? 15'd3744 : (is80MHz) ? 15'd1872: (is40MHz) ? 15'd864 : 15'd416  ;
          4'd4: nBitPSymb_comb <= (is160MHz) ? 15'd5616 : (is80MHz) ? 15'd2808: (is40MHz) ? 15'd1296: 15'd624  ;
          4'd5: nBitPSymb_comb <= (is160MHz) ? 15'd7488 : (is80MHz) ? 15'd3744: (is40MHz) ? 15'd1728: 15'd832  ;
          4'd6: nBitPSymb_comb <= (is160MHz) ? 15'd8424 : (is80MHz) ? 15'd4212: (is40MHz) ? 15'd1944: 15'd936  ;
          4'd7: nBitPSymb_comb <= (is160MHz) ? 15'd9360 : (is80MHz) ? 15'd4680: (is40MHz) ? 15'd2160: 15'd1040 ;
          4'd8: nBitPSymb_comb <= (is160MHz) ? 15'd11232: (is80MHz) ? 15'd5616: (is40MHz) ? 15'd2592: 15'd1248 ;
          4'd9: nBitPSymb_comb <= (is160MHz) ? 15'd12480: (is80MHz) ? 15'd6240: (is40MHz) ? 15'd2880: 15'd1    ;
          // Disable coverage on the default state because it cannot be reached.
          // pragma coverage block = off 
          default: nBitPSymb_comb <= 15'd1;
          // pragma coverage block = on
        endcase
      end
      4'd5:
      begin
        case(mcsIndex[3:0])
          4'd0: nBitPSymb_comb <= (is160MHz) ? 15'd1170 : (is80MHz) ? 15'd585 : (is40MHz) ? 15'd270 : 15'd130  ;
          4'd1: nBitPSymb_comb <= (is160MHz) ? 15'd2340 : (is80MHz) ? 15'd1170: (is40MHz) ? 15'd540 : 15'd260  ;
          4'd2: nBitPSymb_comb <= (is160MHz) ? 15'd3510 : (is80MHz) ? 15'd1755: (is40MHz) ? 15'd810 : 15'd390  ;
          4'd3: nBitPSymb_comb <= (is160MHz) ? 15'd4680 : (is80MHz) ? 15'd2340: (is40MHz) ? 15'd1080: 15'd520  ;
          4'd4: nBitPSymb_comb <= (is160MHz) ? 15'd7020 : (is80MHz) ? 15'd3510: (is40MHz) ? 15'd1620: 15'd780  ;
          4'd5: nBitPSymb_comb <= (is160MHz) ? 15'd9360 : (is80MHz) ? 15'd4680: (is40MHz) ? 15'd2160: 15'd1040 ;
          4'd6: nBitPSymb_comb <= (is160MHz) ? 15'd10530: (is80MHz) ? 15'd5265: (is40MHz) ? 15'd2430: 15'd1170 ;
          4'd7: nBitPSymb_comb <= (is160MHz) ? 15'd11700: (is80MHz) ? 15'd5850: (is40MHz) ? 15'd2700: 15'd1300 ;
          4'd8: nBitPSymb_comb <= (is160MHz) ? 15'd14040: (is80MHz) ? 15'd7020: (is40MHz) ? 15'd3240: 15'd1560 ;
          4'd9: nBitPSymb_comb <= (is160MHz) ? 15'd15600: (is80MHz) ? 15'd7800: (is40MHz) ? 15'd3600: 15'd1    ;
          // Disable coverage on the default state because it cannot be reached.
          // pragma coverage block = off 
          default: nBitPSymb_comb <= 15'd1;
          // pragma coverage block = on
        endcase
      end
      4'd6:
      begin
        case(mcsIndex[3:0])
          4'd0: nBitPSymb_comb <= (is160MHz) ? 15'd1404 : (is80MHz) ? 15'd702 : (is40MHz) ? 15'd324 : 15'd156  ;
          4'd1: nBitPSymb_comb <= (is160MHz) ? 15'd2808 : (is80MHz) ? 15'd1404: (is40MHz) ? 15'd648 : 15'd312  ;
          4'd2: nBitPSymb_comb <= (is160MHz) ? 15'd4212 : (is80MHz) ? 15'd2106: (is40MHz) ? 15'd972 : 15'd468  ;
          4'd3: nBitPSymb_comb <= (is160MHz) ? 15'd5616 : (is80MHz) ? 15'd2808: (is40MHz) ? 15'd1296: 15'd624  ;
          4'd4: nBitPSymb_comb <= (is160MHz) ? 15'd8424 : (is80MHz) ? 15'd4212: (is40MHz) ? 15'd1944: 15'd936  ;
          4'd5: nBitPSymb_comb <= (is160MHz) ? 15'd11232: (is80MHz) ? 15'd5616: (is40MHz) ? 15'd2592: 15'd1248 ;
          4'd6: nBitPSymb_comb <= (is160MHz) ? 15'd12636: (is80MHz) ? 15'd6318: (is40MHz) ? 15'd2916: 15'd1404 ;
          4'd7: nBitPSymb_comb <= (is160MHz) ? 15'd14040: (is80MHz) ? 15'd7020: (is40MHz) ? 15'd3240: 15'd1560 ;
          4'd8: nBitPSymb_comb <= (is160MHz) ? 15'd16848: (is80MHz) ? 15'd8424: (is40MHz) ? 15'd3888: 15'd1872 ;
          4'd9: nBitPSymb_comb <= (is160MHz) ? 15'd18720: (is80MHz) ? 15'd1   : (is40MHz) ? 15'd4320: 15'd2080 ;
          // Disable coverage on the default state because it cannot be reached.
          // pragma coverage block = off 
          default: nBitPSymb_comb <= 15'd1;
          // pragma coverage block = on
        endcase
      end
      4'd7:
      begin
        case(mcsIndex[3:0])
          4'd0: nBitPSymb_comb <= (is160MHz) ? 15'd1638 : (is80MHz) ? 15'd819  : (is40MHz) ? 15'd378 : 15'd182  ;
          4'd1: nBitPSymb_comb <= (is160MHz) ? 15'd3276 : (is80MHz) ? 15'd1638 : (is40MHz) ? 15'd756 : 15'd364  ;
          4'd2: nBitPSymb_comb <= (is160MHz) ? 15'd4914 : (is80MHz) ? 15'd2457 : (is40MHz) ? 15'd1134: 15'd546  ;
          4'd3: nBitPSymb_comb <= (is160MHz) ? 15'd6552 : (is80MHz) ? 15'd3276 : (is40MHz) ? 15'd1512: 15'd728  ;
          4'd4: nBitPSymb_comb <= (is160MHz) ? 15'd9828 : (is80MHz) ? 15'd4914 : (is40MHz) ? 15'd2268: 15'd1092 ;
          4'd5: nBitPSymb_comb <= (is160MHz) ? 15'd13104: (is80MHz) ? 15'd6552 : (is40MHz) ? 15'd3024: 15'd1456 ;
          4'd6: nBitPSymb_comb <= (is160MHz) ? 15'd14742: (is80MHz) ? 15'd1    : (is40MHz) ? 15'd3402: 15'd1638 ;
          4'd7: nBitPSymb_comb <= (is160MHz) ? 15'd16380: (is80MHz) ? 15'd8190 : (is40MHz) ? 15'd3780: 15'd1820 ;
          4'd8: nBitPSymb_comb <= (is160MHz) ? 15'd19656: (is80MHz) ? 15'd9828 : (is40MHz) ? 15'd4536: 15'd2184 ;
          4'd9: nBitPSymb_comb <= (is160MHz) ? 15'd21840: (is80MHz) ? 15'd10920: (is40MHz) ? 15'd5040: 15'd1    ;
          // Disable coverage on the default state because it cannot be reached.
          // pragma coverage block = off 
          default: nBitPSymb_comb <= 15'd1;
          // pragma coverage block = on
        endcase
      end
      4'd8:
      begin
        case(mcsIndex[3:0])
          4'd0: nBitPSymb_comb <= (is160MHz) ? 15'd1872 : (is80MHz) ? 15'd936  : (is40MHz) ? 15'd432 : 15'd208  ;
          4'd1: nBitPSymb_comb <= (is160MHz) ? 15'd3744 : (is80MHz) ? 15'd1872 : (is40MHz) ? 15'd864 : 15'd416  ;
          4'd2: nBitPSymb_comb <= (is160MHz) ? 15'd5616 : (is80MHz) ? 15'd2808 : (is40MHz) ? 15'd1296: 15'd624  ;
          4'd3: nBitPSymb_comb <= (is160MHz) ? 15'd7488 : (is80MHz) ? 15'd3744 : (is40MHz) ? 15'd1728: 15'd832  ;
          4'd4: nBitPSymb_comb <= (is160MHz) ? 15'd11232: (is80MHz) ? 15'd5616 : (is40MHz) ? 15'd2592: 15'd1248 ;
          4'd5: nBitPSymb_comb <= (is160MHz) ? 15'd14976: (is80MHz) ? 15'd7488 : (is40MHz) ? 15'd3456: 15'd1664 ;
          4'd6: nBitPSymb_comb <= (is160MHz) ? 15'd16848: (is80MHz) ? 15'd8424 : (is40MHz) ? 15'd3888: 15'd1872 ;
          4'd7: nBitPSymb_comb <= (is160MHz) ? 15'd18720: (is80MHz) ? 15'd9360 : (is40MHz) ? 15'd4320: 15'd2080 ;
          4'd8: nBitPSymb_comb <= (is160MHz) ? 15'd22464: (is80MHz) ? 15'd11232: (is40MHz) ? 15'd5184: 15'd2496 ;
          4'd9: nBitPSymb_comb <= (is160MHz) ? 15'd24960: (is80MHz) ? 15'd12480: (is40MHz) ? 15'd5760: 15'd1    ;
          // Disable coverage on the default state because it cannot be reached.
          // pragma coverage block = off 
          default: nBitPSymb_comb <= 15'd1;
          // pragma coverage block = on
        endcase
      end
      // Disable coverage on the default state because it cannot be reached.
      // pragma coverage block = off 
      default: nBitPSymb_comb <= 15'd1;
      // pragma coverage block = on
    endcase
  end
end

//  NSS : Number of Spacial Stream
//      +-------+-----+
//      |  MCS  | NSS |
//      +-------+-----+
//      |  0-7  |  1  |
//      +-------+-----+
//      |  8-15 |  2  |
//      +-------+-----+
//      | 16-20 |  3  |
//      +-------+-----+
//      | 21-23 |  3  |
//      +-------+-----+
//      | 23-27 |  4  |
//      +-------+-----+
//      | 28-31 |  4  |
//      +-------+-----+
//      |  32   |  1  |
//      +-------+-----+
//      | 33-38 |  2  |
//      +-------+-----+
//      | 39-52 |  3  |
//      +-------+-----+
//      | 53-76 |  4  |
//      +-------+-----+
always @*
begin
  if ((preambleType == 3'b010) || (preambleType == 3'b011))
  // In case of HT rate.
  begin
    case (mcsIndex[6:0])
      7'd0,7'd1,7'd2,7'd3,7'd4,7'd5,7'd6,7'd7          : nSS_comb = 4'd1;
      7'd8,7'd9,7'd10,7'd11,7'd12,7'd13,7'd14,7'd15    : nSS_comb = 4'd2;
      7'd16,7'd17,7'd18,7'd19,7'd20,7'd21,7'd22,7'd23  : nSS_comb = 4'd3;
      7'd24,7'd25,7'd26,7'd27,7'd28,7'd29,7'd30,7'd31  : nSS_comb = 4'd4;
      7'd32                                            : nSS_comb = 4'd1;
      7'd33,7'd34,7'd35,7'd36,7'd37,7'd38              : nSS_comb = 4'd2;
      7'd39,7'd40,7'd41,7'd42,7'd43,7'd44,7'd45,7'd46,
      7'd47,7'd48,7'd49,7'd50,7'd51,7'd52              : nSS_comb = 4'd3;
      7'd53,7'd54,7'd55,7'd56,7'd57,7'd58,7'd59,7'd60,
      7'd61,7'd62,7'd63,7'd64,7'd65,7'd66,7'd67,7'd68,
      7'd69,7'd70,7'd71,7'd72,7'd73,7'd74,7'd75,7'd76  : nSS_comb = 4'd4;
    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
      default                                          : nSS_comb = 4'd1;
    // pragma coverage block = on 
    endcase
  end
  else if(preambleType == 3'b100)
    // VHT Rate
    nSS_comb = {1'b0,mcsIndex[6:4]} + 4'd1; // nSS is set from 0 to 7 in mcsIndex[6:4] (where 0 means 1 nSS)
  else
    nSS_comb = 4'd1;
end

// 6*NES selection for nBit calculcation
always @*
begin
  if((preambleType == 3'b010) || (preambleType == 3'b011))
  // HT case
  begin
    nES = (nBitPSymb_comb < 15'd1296) ? 24'd6 : 24'd12;
  end
  else if(preambleType == 3'b100)
  begin
    // 20MHz and  40MHz Bandwidth
    if(chBw < 2'd2)
    begin
      nES = (nBitPSymb_comb <= 15'd2160) ? 24'd6 : (nBitPSymb_comb <= 15'd4320) ? 24'd12 : 24'd18;
    end
    // 80MHz Bandwidth
    else if(chBw == 2'd2)
    begin
      if((nSS_comb == 4'd7) && (nBitPSymb_comb == 15'd8190))
      begin
        nES = 24'd36;
      end
      else if((nSS_comb == 4'd7) && (nBitPSymb_comb == 15'd2457))
      begin
        nES = 24'd18;
      end
      else
      begin
        nES = (nBitPSymb_comb <= 15'd2106) ? 24'd6 : (nBitPSymb_comb <= 15'd4212) ? 24'd12 : (nBitPSymb_comb <= 15'd6318) ? 24'd18 : (nBitPSymb_comb <= 15'd8424) ? 24'd24 : 24'd36;
      end
    end
    // 160MHz Bandwidth
    else if(chBw == 2'd3)
    begin
      if( ((nSS_comb == 4'd4) && (nBitPSymb_comb == 15'd9360)) || ((nSS_comb == 4'd7) && (nBitPSymb_comb == 15'd9828)) )
      begin
        nES = 24'd36;
      end
      else if((nBitPSymb_comb == 15'd14040) && ((nSS_comb == 4'd5) || (nSS_comb == 4'd6)) )
      begin
        nES = 24'd48;
      end
      else if((nSS_comb == 4'd7) && (nBitPSymb_comb == 15'd16380))
      begin
        nES = 24'd54;
      end
      else
      begin
        nES = (nBitPSymb_comb <= 15'd2106)  ? 24'd6  :
              (nBitPSymb_comb <= 15'd4212)  ? 24'd12 :
              (nBitPSymb_comb <= 15'd6318)  ? 24'd18 :
              (nBitPSymb_comb <= 15'd8424)  ? 24'd24 :
              (nBitPSymb_comb <= 15'd10530) ? 24'd30 :
              (nBitPSymb_comb <= 15'd12636) ? 24'd36 :
              (nBitPSymb_comb <= 15'd14742) ? 24'd42 :
              (nBitPSymb_comb <= 15'd16848) ? 24'd48 :
              (nBitPSymb_comb <= 15'd18720) ? 24'd54 :
                                              24'd72 ;
      end
    end
    else
    begin
      nES = 24'd6; // 6*1
    end
  end
  else
  begin
    nES = 24'd6; // 6*1
  end
end

// Set nBit with the total number of bit of the ppdu. Note that for OFDM frame,
// 22 bits have to be added (16 for service field and 6 for tails)
assign nBit = ((mcsIndex_ff1 < 7'd4) && (preambleType[2:1] == 2'b00)) ? {length,4'b0} : {1'b0,length,3'b0}+24'd16+nES;


always @ *
begin
  if (stbc > 2'd0)
    nBitPSymb  = {nBitPSymb_comb[13:0],1'd0};
  else  
    nBitPSymb  = nBitPSymb_comb;
end

// Delay mcsIndex of one clock cycle.
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    mcsIndex_ff1  <= 7'b0;
  else
    mcsIndex_ff1  <= mcsIndex[6:0];
end


// Set data14Duration with the duration of a 14bytes PPDU based on the rate
// Set data14Duration with the duration of a 14bytes PPDU based on the rate
always @ *
begin
  // In case of legacy rate.
  if (isLegacy)
  begin
    case (mcsIndex_ff1[3:0])
             4'd0 : data14Duration = 16'd112; //  1Mbps
             4'd1 : data14Duration =  16'd56; //  2Mbps
             4'd2 : data14Duration =  16'd21; //5.5Mbps
             4'd3 : data14Duration =  16'd11; // 11Mbps
             4'd4 : data14Duration =  16'd24; //  6Mbps
             4'd5 : data14Duration =  16'd16; //  9Mbps
             4'd6 : data14Duration =  16'd12; // 12Mbps
             4'd7 : data14Duration =   16'd8; // 18Mbps
             4'd8 : data14Duration =   16'd8; // 24Mbps
             4'd9 : data14Duration =   16'd4; // 36Mbps
            4'd10 : data14Duration =   16'd4; // 48Mbps
            4'd11 : data14Duration =   16'd4; // 54Mbps
       // Disable coverage on the default state because it cannot be reached.
       // pragma coverage block = off 
       default : data14Duration = 16'd112;    
       // pragma coverage block = on 
    endcase                           
  end
  else
  // In case of HT or VHT rate.
  begin
    // only one symbol since 14*8 + 22 = 134 bits
    if(nBitPSymb_comb >= 15'd134)
    begin
      // If STBC then the SYMBOL is transmitted twice
      // Short Guard interval does not matter since 3.6 or 7.2 is round up to 4 or 8
      data14Duration = (stbc != 2'd0) ? 16'd8 : 16'd4;
    end
    // If two symbols 134/2 = 67
    // HT  NDBPS(78 104 108)
    // VHT NDBPS(78 104 108 117)
    else if(nBitPSymb_comb >= 15'd67)
    begin
      // STBC does not matter since both symbol are send twice in parrallel
      // Short GI does not matter since 3.6*2 = 7.4 = 8
      data14Duration = 16'd8;
    end
    // If three symbols 134/3 = 44.6 = 45
    // HT  NDBPS(52 54)
    // VHT NDBPS(52 54)
    else if(nBitPSymb_comb >= 15'd45)
    begin
      // STBC add 1 more symbol
      // Short GI is taken in the calculation
      data14Duration = (stbc != 2'd0) ? ( (shortGI) ? 16'd15 : 16'd16) : ( (shortGI) ? 16'd11 : 16'd12);
    end
    // If four symbols 134/4 = 33.5 = 34 : Ignored since there is no nBitPSymb_comb between 34 and 45
    // If five symbols 134/5 = 26.8 = 27 : Ignored since there is no nBitPSymb_comb between 27 and 34
    // If six  symbols 134/6 = 22.3 = 23
    // HT  NDBPS(26 24)
    // VHT NDBPS(26)
    else if(nBitPSymb_comb > 15'd23)
    begin
      // STBC does not matter
      // Short GI is taken in the calculation
      data14Duration = (shortGI) ? 16'd22 : 16'd24;
    end
    else
    begin
      data14Duration = 16'd4; // 1 symbol
    end
  end
end


// Set data20Duration with the duration of a 20bytes PPDU based on the rate
always @ *
begin
  // In case of legacy rate.
  if (isLegacy)
  begin
    case (mcsIndex_ff1[3:0])
             4'd0 : data20Duration = 16'd160; //  1Mbps
             4'd1 : data20Duration =  16'd80; //  2Mbps
             4'd2 : data20Duration =  16'd30; //5.5Mbps
             4'd3 : data20Duration =  16'd15; // 11Mbps
             4'd4 : data20Duration =  16'd32; //  6Mbps
             4'd5 : data20Duration =  16'd24; //  9Mbps
             4'd6 : data20Duration =  16'd16; // 12Mbps
             4'd7 : data20Duration =  16'd12; // 18Mbps
             4'd8 : data20Duration =   16'd8; // 24Mbps
             4'd9 : data20Duration =   16'd8; // 36Mbps
            4'd10 : data20Duration =   16'd4; // 48Mbps
            4'd11 : data20Duration =   16'd4; // 54Mbps
       // Disable coverage on the default state because it cannot be reached.
       // pragma coverage block = off 
       default : data20Duration = 16'd128;    
       // pragma coverage block = on 
    endcase
  end
  // HT and VHT mode
  else
  begin
    // Test if it has only 1 symbol (20*8 + 22) = 182
    if(nBitPSymb_comb >= 15'd182)
    begin
      // If STBC then the SYMBOL is transmitted twice
      // Short Guard interval does not matter since 3.6 or 7.2 is round up to 4 or 8
      data20Duration = (stbc != 2'd0) ? 16'd8 : 16'd4;
    end
    // If 2 symbols 182/2 = 91
    // HT  NDBPS(104 156 108 162)
    // VHT NDBPS(104 156 130 108 162 117)
    else if(nBitPSymb_comb >= 15'd91)  
    begin
      // STBC does not matter since both symbol are send twice in parrallel
      // Short GI does not matter since 3.6*2 = 7.4 = 8
      data20Duration = 16'd8;
    end
    // If 3 symbols 182/3 = 60.66 = 61
    // HT  NDBPS(78)
    // VHT NDBPS(78)
    else if(nBitPSymb_comb >= 15'd61)  
    begin
      // STBC add 1 more symbol
      // Short GI is taken in the calculation
      data20Duration = (stbc != 2'd0) ? ( (shortGI) ? 16'd15 : 16'd16) : ( (shortGI) ? 16'd11 : 16'd12);
    end
    // If 4 symbols 182/4 = 45.5 = 46
    // HT  NDBPS(52 54)
    // VHT NDBPS(52 54)
    else if(nBitPSymb_comb >= 15'd46)
    begin
      // STBC does not matter
      // Short GI is taken in the calculation
      data20Duration = (shortGI) ? 16'd15 : 16'd16;
    end
    // If 5 symbols 182/5 = 36.4 = 37 : Ignored since there is no nBitPSymb_comb between 37 and 46
    // If 6 symbols 182/6 = 30.3 = 31 : Ignored since there is no nBitPSymb_comb between 31 and 37
    // If 7 symbols 182/7 = 26
    // HT  NDBPS(26)
    // VHT NDBPS(26)
    else if(nBitPSymb_comb >= 15'd26)
    begin
      // STBC add 1 more symbol
      // Short GI is taken in the calculation
      data20Duration = (stbc != 2'd0) ? ( (shortGI) ? 16'd29 : 16'd32) : ( (shortGI) ? 16'd26 : 16'd28);
    end
    // If 8 symbols 182/7 = 22.75 = 23
    // HT  NDBPS(24)
    else if(nBitPSymb_comb >= 15'd23)
    begin
      // STBC does not matter
      // Short GI is taken in the calculation
      data20Duration = (shortGI) ? 16'd29 : 16'd32;
    end
    else
    begin
      data20Duration = 16'd4;  // 1 symbol
    end
  end
end

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////



`ifdef RW_SIMU_ON
// Disable coverage on the default state because it cannot be reached.
// pragma coverage block = off 


// dividerControlFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (dividerControlFSMCs)
                 IDLE  :  dividerControlFSMCs_str = {"IDLE           "};
        COMPUTE_NSYMB  :  dividerControlFSMCs_str = {"COMPUTE_NSYMB  "};
      COMPUTE_SHORTGI  :  dividerControlFSMCs_str = {"COMPUTE_SHORTGI"};
              default  :  dividerControlFSMCs_str = {"XXX            "};
   endcase
end
// pragma coverage block = on

`endif // RW_SIMU_ON


// System Verilog Assertions
////////////////////////////
`ifdef RW_ASSERT_ON

// The number of Data HT-LTFs is denoted NDLTF. The number of extension HT-LTFs is denoted NELTF. The
// total number of HT-LTFs is:
// NLTF = NDLTF + NELTF       (20-22)
// shall not exceed 5. Table 20-11 shows the determination of the number of space time streams from the
// MCS and STBC fields in the HT-SIG. Table 20-12 shows the number of Data HT-LTFs as a function of the
// number of space time streams (NSTS). Table 20-13 shows the number of extension HT-LTFs as a function of
// the number of extension spatial streams (NESS).NSTS plus NESS is less than or equal to 4. In the case where
// NSTS equals 3, NESS cannot exceed one; if NESS equals one in this case then NLTF equals 5.

// assertion (nSS_comb+stbc+numExtnSS) <= 5 $todo



// $rw_sva Checks if the short preamble is not selection with legRate = 1Mbps
// property noShortPreambleWith1Mbps_prop;
// @(posedge macCoreClk)
//   disable iff(!macCoreClkHardRst_n)
//     !woPreambleMC && (mcsIndex == 0) && (busy) |-> (preambleType == 2'b01);
// endproperty
// noShortPreambleWith1Mbps: assert property (noShortPreambleWith1Mbps_prop); 

// $rw_sva Checks if the short Guard Interval is not selected with legacy rate
// property noShortGIWithLegRate_prop;
// @(posedge macCoreClk)
//   disable iff(!macCoreClkHardRst_n)
//     !woPreambleMC && (mcsIndex <128) && (busy) |-> (shortGI == 1'b0);
// endproperty
// noShortGIWithLegRate: assert property (noShortGIWithLegRate_pr

// $rw_sva Checks if the preamble type is compatible with legRate
// property noHTPreambleWithLegRate_prop;
// @(posedge macCoreClk)
//   disable iff(!macCoreClkHardRst_n)
//     !woPreambleMC && (mcsIndex <128) && (busy) |-> (preambleType < 2);
// endproperty
// noHTPreambleWithLegRate: assert property (noHTPreambleWithLegRate_prop); 

// $rw_sva Checks if the preamble type is compatible with HT-Rate
property noLegPreambleWithHTRate_prop;
@(posedge macCoreClk)
  disable iff(!macCoreClkHardRst_n)
    !woPreambleMC && (mcsIndex >=128) && (busy) |-> (preambleType >= 2);
endproperty
noLegPreambleWithHTRate: assert property (noLegPreambleWithHTRate_prop); 

`endif // RW_ASSERT_ON

endmodule