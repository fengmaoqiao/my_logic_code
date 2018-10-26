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
// Description      : 
//   This module converts a 8/16/19 byte seed into a arbitarily long sequence
//   of pseudo random bytes. It uses RSA RC4 algorithm to generate the pseudo 
//   random bytes. It generates one pseudo random byte every 3 clocks. The cipher 
//   strength is selected on the basis of signal currCipherLen.
//   The initialisation (init) process takes 128 clocks to complete, after which 
//   the state machine waits for seedValid to be asserted. The transformation
//   process takes 768 clocks to complete, after which the state machine waits for
//   prnStrobe_p to be asserted. For every prnStrobe_p, one pseudo random byte is 
//   output with prnOutValid_p being asserted.
//   The state machine returns to init when initPRNG_p is asserted, and immediately
//   starts its init process.
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

module prng(

  //$port_g Input ports
  input  wire         hardRstBbClk_n,     // reset signal from hardware
  input  wire         softRstBbClk_p,     // reset signal from software
  input  wire         bbClk,              // baseband clock signal
  input  wire         currCipherLen,      // signal to select encryption strength
  input  wire [151:0] seed,               // signal indicating validity of seed
  input  wire         seedValid,          // 152/ 128/ 64 bit seed used by PRNG
  input  wire         initPRNG_p,         // init signal, used to start init process
  input  wire         prnStrobe_p,        // strobe for pseudo random bytes to be generated
  input  wire   [7:0] sBoxAReadData,      // data bus from internal RAM, port A
  input  wire   [7:0] sBoxBReadData,      // data bus from internal RAM, port B
  input  wire         rxError_p,          // signal to indicate error in reception 

  //$port_g Output ports 
  output reg         initDone_p,          // signal indicating end of init process
  output reg         initSBoxIndexDone_p, // signal indicating end of SBOX Index init process
  output wire        prngIsIdle,          // signal indicating that the FSM is in IDLE state
  output reg   [7:0] prnOut,              // output lines
  output reg         prnOutValid_p,       // indicates validity of the pseudo random byte on prnOut
  output reg   [7:0] sBoxAAddr,           // address bus to internal RAM, port A
  output reg   [7:0] sBoxBAddr,           // address bus to internal RAM, port B
  output reg         sBoxAEn,             // enable signal for internal RAM, port A
  output reg         sBoxBEn,             // enable signal for internal RAM, port B
  output reg         sBoxAWriteEn,        // write enable signal for internal RAM, port A
  output reg         sBoxBWriteEn,        // write enable signal for internal RAM, port B
  output reg   [7:0] sBoxAWriteData,      // data bus to internal RAM, port A
  output reg   [7:0] sBoxBWriteData,      // data bus to internal RAM, port B
`ifdef SBOX_RDATA_CAPT
  output reg   [4:0] prngCs 
`else
  output reg   [3:0] prngCs 
`endif
);



//--------------------- internal registers -------------------

`ifdef SBOX_RDATA_CAPT
reg [4:0] prngNs;
`else
reg [3:0] prngNs;
`endif
reg [7:0] i;
reg [7:0] nextI;
reg [7:0] j;
reg [7:0] nextJ;
reg [7:0] sBoxI;
reg [7:0] nextSBoxI;
reg [7:0] sBoxJ;
reg [7:0] nextSBoxJ;
reg       initStatus;
reg       nextInitStatus;
reg [4:0] seedPart;
reg [4:0] nextSeedPart;
reg [2:0] clkCounter1;
reg [2:0] clkCounter2;

`ifdef SBOX_RDATA_CAPT
reg [7:0] sBoxAReadDataCapt;      // Captured data bus from internal RAM, port A
reg [7:0] sBoxBReadDataCapt;      // Captured data bus from internal RAM, port B
`else
wire [7:0] sBoxAReadDataCapt;     // Assigned data bus from internal RAM, port A
wire [7:0] sBoxBReadDataCapt;     // Assigned data bus from internal RAM, port B
`endif

`ifdef RW_SIMU_ON
// String definition to display txControlMainFSM current state
reg [21*8:0] prngCs_str;
`endif // RW_SIMU_ON

wire [2:0] prgnWep2BbClkRatio;

//--------------------- prngCs declarations -------------------
parameter PRGNWEP2BBCLKRATIOINT = 32'd1;
  
`ifdef SBOX_RDATA_CAPT
//$fsm_sd prngCs
localparam
  IDLE                 = 5'd0, // Do nothing
  SBOX_INDEX_INIT      = 5'd1, // Initialise sboxdpram with index values
  WAIT_FOR_SEED_VALID  = 5'd2, // Wait until seedValid signal goes high
  SBOX_TRN_READ_I      = 5'd3, // Generate read signals for var i
  WAIT_SBOX_TRN_READ_I = 5'd13, // Generate read signals for var i
  SBOX_TRN_READ_J      = 5'd4, // Generate read signals for var j
  WAIT_SBOX_TRN_READ_J = 5'd14, // Generate read signals for var i
  SBOX_TRN_WRITE_IJ    = 5'd5, // Generate write signals for vars i and j
  PRN_BYTE_READ_I      = 5'd6, // Generate read signals for var i
  WAIT_PRN_BYTE_READ_I = 5'd15, // Generate read signals for var i
  PRN_BYTE_READ_J      = 5'd7, // Generate read signals for var j
  WAIT_PRN_BYTE_READ_J = 5'd16, // Generate read signals for var i
  PRN_BYTE_WRITE_IJ    = 5'd8, // Generate write signals for vars i and j
  WAIT_FOR_STROBE      = 5'd9, // Wait until strobe pulse comes for data
  DELAY_PRN_OUT1       = 5'd10, // Delay the PRN output by one clock
  DELAY_PRN_OUT2       = 5'd11, // Delay the PRN output by two clocks
  DELAY_PRN_OUT3       = 5'd12; // Delay the PRN output by three clocks
`else
localparam
  IDLE                = 4'd0, // Do nothing
  SBOX_INDEX_INIT     = 4'd1, // Initialise sboxdpram with index values
  WAIT_FOR_SEED_VALID = 4'd2, // Wait until seedValid signal goes high
  SBOX_TRN_READ_I     = 4'd3, // Generate read signals for var i
  SBOX_TRN_READ_J     = 4'd4, // Generate read signals for var j
  SBOX_TRN_WRITE_IJ   = 4'd5, // Generate write signals for vars i and j
  PRN_BYTE_READ_I     = 4'd6, // Generate read signals for var i
  PRN_BYTE_READ_J     = 4'd7, // Generate read signals for var j
  PRN_BYTE_WRITE_IJ   = 4'd8, // Generate write signals for vars i and j
  WAIT_FOR_STROBE     = 4'd9, // Wait until strobe pulse comes for data
  DELAY_PRN_OUT1      = 4'd10, // Delay the PRN output by one clock
  DELAY_PRN_OUT2      = 4'd11, // Delay the PRN output by two clocks
  DELAY_PRN_OUT3      = 4'd12; // Delay the PRN output by three clocks
`endif

assign prgnWep2BbClkRatio = PRGNWEP2BBCLKRATIOINT[2:0];



assign prngIsIdle = (prngCs == IDLE);

// SBOX_INDEX_INIT:
// put index value in other 255 locations of sBox
// after all locations have been covered, check if seedValid signal is high
// if not high enter wait prngCs else do the transformations on sBox.
// use both ports of the RAM to do the init process. this takes 128 clocks
// for the 256 locations.

// WAIT_FOR_SEED_VALID:
// wait until seedValid signal is given before proceeding with transformations 
// on sBox.

// SBOX_TRN_READ_I:
// send read enable to sBox[i] in this prngCs. this is step 1 of transformation.
// the 3 steps are repeated for every location. a total of 256 * 3 = 768 clocks
// are taken for the transformation phase.

// SBOX_TRN_READ_J:
// read sBox[i], calculate value of j, send read enable to sBox[j].
// this is step 2 of transformation.

// SBOX_TRN_WRITE_IJ:
// read sBox[j], swap sBox[i] & sBox[j].
// this is step 3 of transformation. if all locations have not been covered,
// jump to step 1 (SBOX_TRN_READ_I), else jump to PRN_BYTE_READ_I.
// keep one PRN ready. as soon as the first prnStrobe_p is given,
// release it and start calculating the next PRN byte.

// PRN_BYTE_READ_I:
// send read enable to sBox[i]. if initStatus is set, send read enable for
// sBox[i+j], ie do not send read enable the first time this prngCs in entered.

// PRN_BYTE_READ_J:
// read sBox[i], calculate value of j. send read enable to sBox[j].

// PRN_BYTE_WRITE_IJ:
// read sBox[j], swap sBox[i] & sBox[j].
// if prnStrobe_p is asserted, jump to PRN_BYTE_READ_I, else enter wait prngCs.

// WAIT_FOR_STROBE:
// wait until prnStrobe_p is asserted.

// DELAY_PRN_OUT1/2/3:
// wait state to delay generation of the PRN byte

always @(*)
  begin
  case (prngCs)

    IDLE:
      //$fsm_s In IDLE state, the prng waits for 1 clock cycle
      
      //$fsm_t After 1 clock cycle, the state goes to SBOX_INDEX_INIT state
      prngNs = SBOX_INDEX_INIT;

    SBOX_INDEX_INIT:  
      //$fsm_s In SBOX_INDEX_INIT, the prgn is itinializing the SBOX memories from 0 to 255 
      if (i[7:0] == 8'hFE && seedValid == 1'b1)
        //$fsm_t When SBOX is initialized and a seed is valid, the state goes to SBOX_TRN_READ_I state
        prngNs = SBOX_TRN_READ_I;

      else if (i[7:0] == 8'hFE && seedValid == 1'b0)
        //$fsm_t When SBOX is initialized and a seed is not valid, the state goes to WAIT_FOR_SEED_VALID state
        prngNs = WAIT_FOR_SEED_VALID;

      else
        //$fsm_t When SBOX is not initialized, the state stays in SBOX_INDEX_INIT state
        prngNs = SBOX_INDEX_INIT;

    WAIT_FOR_SEED_VALID:
      //$fsm_s In WAIT_FOR_SEED_VALID, the prgn waits until seedValid signal is given before proceeding with transformations on sBox
      if (seedValid == 1'b1)
        //fsm_t If seed is valid, the state goes to SBOX_TRN_READ_I state
        prngNs = SBOX_TRN_READ_I;
      else
        //fsm_t If seed is not valid, the state waits in WAIT_FOR_SEED_VALID state
        prngNs = WAIT_FOR_SEED_VALID;


    SBOX_TRN_READ_I:
      //$fsm_s In SBOX_TRN_READ_I, the prgn read the byte at index I
      
`ifdef SBOX_RDATA_CAPT
      //$fsm_t After one clock cycle, the state goes to WAIT_SBOX_TRN_READ_I state
      prngNs = WAIT_SBOX_TRN_READ_I;

    WAIT_SBOX_TRN_READ_I:
      //$fsm_s In SBOX_TRN_READ_I, the prgn read the byte at index I
`endif

      //$fsm_t After one clock cycle, the state goes to SBOX_TRN_READ_J state
      prngNs = SBOX_TRN_READ_J;

    SBOX_TRN_READ_J:
      //$fsm_s In SBOX_TRN_READ_J, the prgn read the byte at index J

`ifdef SBOX_RDATA_CAPT
      //$fsm_t After one clock cycle, the state goes to WAIT_SBOX_TRN_READ_J state
      prngNs = WAIT_SBOX_TRN_READ_J;

    WAIT_SBOX_TRN_READ_J:
`endif
      //$fsm_s In SBOX_TRN_READ_J, the prgn read the byte at index J

      //$fsm_t After one clock cycle, the state goes to SBOX_TRN_WRITE_IJ state
      prngNs = SBOX_TRN_WRITE_IJ;

    SBOX_TRN_WRITE_IJ:
      //$fsm_s In SBOX_TRN_WRITE_IJ, the prgn swaps sBox[i] & sBox[j]
      if (i[7:0] == 8'hFF)
        //$fsm_t If all SBOX has been swapt, the state goes to PRN_BYTE_READ_I state
        prngNs = PRN_BYTE_READ_I;
      else
        //$fsm_t If not all SBOX has been swapt, the state goes to SBOX_TRN_READ_I state
        prngNs = SBOX_TRN_READ_I;

    PRN_BYTE_READ_I:
      //$fsm_s In PRN_BYTE_READ_I, the prgn read the byte at index I

`ifdef SBOX_RDATA_CAPT
      //$fsm_t After one clock cycle, the state goes to WAIT_PRN_BYTE_READ_I state
      prngNs = WAIT_PRN_BYTE_READ_I;

    WAIT_PRN_BYTE_READ_I:
      //$fsm_s In PRN_BYTE_READ_I, the prgn read the byte at index I
`endif

      //$fsm_t After one clock cycle, the state goes to PRN_BYTE_READ_J state
      prngNs = PRN_BYTE_READ_J;

    PRN_BYTE_READ_J:
      //$fsm_s In PRN_BYTE_READ_I, the prgn read the byte at index J

`ifdef SBOX_RDATA_CAPT
      //$fsm_t After one clock cycle, the state goes to WAIT_PRN_BYTE_READ_J state
      prngNs = WAIT_PRN_BYTE_READ_J;

    WAIT_PRN_BYTE_READ_J:
`endif
      //$fsm_s In PRN_BYTE_READ_I, the prgn read the byte at index J

      //$fsm_t After one clock cycle, the state goes to PRN_BYTE_WRITE_IJ state
      prngNs = PRN_BYTE_WRITE_IJ;

    PRN_BYTE_WRITE_IJ:
      //$fsm_s In SBOX_TRN_WRITE_IJ, the prgn swaps sBox[i] & sBox[j]

      if (prnStrobe_p == 1'b1)
        if ((prgnWep2BbClkRatio == 3'd3) || (prgnWep2BbClkRatio == 3'd4))
          //$fsm_t If the xored data byte is strobed and  the WEP/TKIP clock ratio is 3 or 4, the state goes to DELAY_PRN_OUT1 state
          prngNs = DELAY_PRN_OUT1;
        else
          //$fsm_t If the xored data byte is strobed and  the WEP/TKIP clock ratio is 1 or 2, the state goes to PRN_BYTE_READ_I state
          prngNs = PRN_BYTE_READ_I;
      else
        //$fsm_t If the xored data byte is not strobed, the state goes to WAIT_FOR_STROBE state
        prngNs = WAIT_FOR_STROBE;

    WAIT_FOR_STROBE:
      //$fsm_s In WAIT_FOR_STROBE, the prgn wait for prnStrobe_p
      if (prnStrobe_p == 1'b1)
        if ((prgnWep2BbClkRatio == 3'd3) || (prgnWep2BbClkRatio == 3'd4))
          //$fsm_t If the xored data byte is strobed and  the WEP/TKIP clock ratio is 3 or 4, the state goes to DELAY_PRN_OUT1 state
          prngNs = DELAY_PRN_OUT1;
        else
          //$fsm_t If the xored data byte is strobed and  the WEP/TKIP clock ratio is 1 or 2, the state goes to PRN_BYTE_READ_I state
          prngNs = PRN_BYTE_READ_I;
      else
        //$fsm_t If the xored data byte is not strobed, the state stays in WAIT_FOR_STROBE state
        prngNs = WAIT_FOR_STROBE;

    DELAY_PRN_OUT1:
      //$fsm_s In DELAY_PRN_OUT1, the prgn wait for prgn byte generation
      
      if (prgnWep2BbClkRatio == 3'd4)
        //$fsm_t If the WEP/TKIP clock ratio is 4, the state goes to DELAY_PRN_OUT2 state
        prngNs = DELAY_PRN_OUT2;
      else
        //$fsm_t If the WEP/TKIP clock ratio is 3, the state goes to PRN_BYTE_READ_I state
        prngNs = PRN_BYTE_READ_I;

    DELAY_PRN_OUT2:
      //$fsm_s In DELAY_PRN_OUT2, the prgn wait for prgn byte generation

      //$fsm_t After one clock cycle, the state goes to DELAY_PRN_OUT3 state
      prngNs = DELAY_PRN_OUT3;

    DELAY_PRN_OUT3:
      //$fsm_s In DELAY_PRN_OUT3, the prgn wait for prgn byte generation
     
      //$fsm_t After one clock cycle, the state goes to PRN_BYTE_READ_I state
      prngNs = PRN_BYTE_READ_I;

    default:
      prngNs = IDLE;

    endcase
end

// build the prngCs flip flops

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    prngCs <= IDLE;
  else if (softRstBbClk_p == 1'b1)
    prngCs <= IDLE;
  else if (rxError_p)
    prngCs <= IDLE;
  else if (initPRNG_p == 1'b1)
    prngCs <= IDLE;
  else
    prngCs <= prngNs;


// logic for clkCounter1
// this counter counts the number of bb2Clk edges occuring for every bbClk.
// It is used to make the pulse width of pulses produced in bb2Clk domain
// equal to pulses produced in bbClk domain for correct sampling.

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (!hardRstBbClk_n)
    clkCounter1 <= 3'd0;
  else if (softRstBbClk_p)
    clkCounter1 <= 3'd0;
  else if (prngCs == PRN_BYTE_READ_I && initStatus == 1'b0)
    clkCounter1 <= prgnWep2BbClkRatio;
  else if (clkCounter1 == 3'd0)
    clkCounter1 <= 3'd0;
  else
    clkCounter1 <= clkCounter1 - 3'd1;


// logic for initDone_p
// when transformation phase is over, assert initDone_p. it should be asserted 
// as long as clkCounter is non zero.

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    initDone_p  <= 1'b0;
  else if (softRstBbClk_p == 1'b1)
    initDone_p  <= 1'b0;
`ifdef SBOX_RDATA_CAPT
  else if(prngCs == PRN_BYTE_READ_J && initStatus == 1'b0)
`else
  else if(prngCs == PRN_BYTE_READ_I && initStatus == 1'b0)
`endif
    initDone_p <= 1'b1;
  else
    initDone_p <= 1'b0;

// logic for initSBoxIndexDone_p
// when SBOX Index Initialisation is over, assert initSBoxIndexDone_p. 

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    initSBoxIndexDone_p  <= 1'b0;
  else if (softRstBbClk_p == 1'b1)
    initSBoxIndexDone_p  <= 1'b0;
  else if(prngNs == WAIT_FOR_SEED_VALID)
    initSBoxIndexDone_p <= 1'b1;
  else
    initSBoxIndexDone_p <= 1'b0;


// logic for prnOut
// since the enable to port B of sBox was sent in prngCs PRN_BYTE_READ_I
// data will be available in this prngCs. This is the PRN output.

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    prnOut[7:0] <= 8'b0;
  else if (softRstBbClk_p == 1'b1)
    prnOut[7:0] <= 8'b0;
  else if (initPRNG_p == 1'b1)
    prnOut[7:0] <= 8'b0;
  else if (prngCs == PRN_BYTE_READ_J && initStatus == 1'b1)
    prnOut[7:0] <= sBoxBReadDataCapt[7:0];
  else
    prnOut[7:0] <= prnOut[7:0];


// logic for clkCounter2
// this counter counts the number of bb2Clk edges occuring for every bbClk.
// It is used to make the pulse width of pulses produced in bb2Clk domain
// equal to pulses produced in bbClk domain for correct sampling.

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (!hardRstBbClk_n)
    clkCounter2 <= 3'd0;
  else if (softRstBbClk_p)
    clkCounter2 <= 3'd0;
`ifdef SBOX_RDATA_CAPT
  else if (prngCs == PRN_BYTE_READ_J && initStatus == 1'b1)
`else
  else if (prngCs == PRN_BYTE_READ_I && initStatus == 1'b1)
`endif
    clkCounter2 <= prgnWep2BbClkRatio;
  else if (clkCounter2 == 3'd0)
    clkCounter2 <= 3'd0;
  else
    clkCounter2 <= clkCounter2 - 3'd1;


// logic for prnOutValid_p
// prnOutValid_p needs to be sent when data is available from port B of the 
// sBox RAM. it should be asserted as long as clkCounter is non zero.
 
always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    prnOutValid_p  <= 1'b0;
  else if (softRstBbClk_p == 1'b1)
   prnOutValid_p  <= 1'b0;
  else
    prnOutValid_p  <= (clkCounter2 != 3'd0);

`ifdef SBOX_RDATA_CAPT
always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    sBoxAReadDataCapt  <= 8'b0;
  else if (softRstBbClk_p == 1'b1)
    sBoxAReadDataCapt  <= 8'b0;
  else
    sBoxAReadDataCapt  <= sBoxAReadData;

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    sBoxBReadDataCapt  <= 8'b0;
  else if (softRstBbClk_p == 1'b1)
    sBoxBReadDataCapt  <= 8'b0;
  else
    sBoxBReadDataCapt  <= sBoxBReadData;

`else

assign sBoxAReadDataCapt = sBoxAReadData;
assign sBoxBReadDataCapt = sBoxBReadData;

`endif



// logic for sBoxAAddr
// sBoxAAddr takes the value of i in most prngCss, and takes the value of j
// in SBOX_TRN_READ_J prngCs, for retriving value of sBox[j].

always @(prngCs or i or seedPart or j or sBoxAReadDataCapt or seed)
  case (prngCs)
    IDLE:
      sBoxAAddr[7:0] = 8'b0;
 
    SBOX_INDEX_INIT:
      sBoxAAddr[7:0] = i[7:0];

    SBOX_TRN_READ_I:
      sBoxAAddr[7:0] = i[7:0];

    SBOX_TRN_READ_J:
      case (seedPart[4:0])

      5'd0 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[7:0];
      5'd1 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[15:8];
      5'd2 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[23:16];
      5'd3 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[31:24];
      5'd4 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[39:32];
      5'd5 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[47:40];
      5'd6 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[55:48];
      5'd7 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[63:56];
      5'd8 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[71:64];
      5'd9 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[79:72];
      5'd10 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[87:80];
      5'd11 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[95:88];
      5'd12 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[103:96];
      5'd13 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[111:104];
      5'd14 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[119:112];
      5'd15 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[127:120];
      5'd16 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[135:128];
      5'd17 :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[143:136];
      default :
        sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0] + seed[151:144];

      endcase

    SBOX_TRN_WRITE_IJ:
      sBoxAAddr[7:0] = i[7:0];

    PRN_BYTE_READ_I:
      sBoxAAddr[7:0] = i[7:0];

    PRN_BYTE_READ_J:
      sBoxAAddr[7:0] = j[7:0] + sBoxAReadDataCapt[7:0];

    PRN_BYTE_WRITE_IJ:
      sBoxAAddr[7:0] = i[7:0];

    default:
      sBoxAAddr[7:0] = 8'h0; // for synthesis optimisation
  
  endcase


// logic for sBoxAEn
// sBoxAEn is asserted in most prngCss, it is deasserted when swapping
// needs to be done from the same location ie a particular case of i = j.
// it is asserted evert time a read needs to be performed on port A of RAM.

always @(prngCs or sBoxAAddr or j)
  case (prngCs)
    SBOX_INDEX_INIT:
      sBoxAEn = 1'b1;

    SBOX_TRN_READ_I:
      sBoxAEn = 1'b1;

    SBOX_TRN_READ_J:
      sBoxAEn = 1'b1;

    SBOX_TRN_WRITE_IJ:
      if (sBoxAAddr[7:0] != j[7:0])
        sBoxAEn = 1'b1;
      else
        sBoxAEn = 1'b0;

    PRN_BYTE_READ_I:
      sBoxAEn = 1'b1;

    PRN_BYTE_READ_J:
      sBoxAEn = 1'b1;

    PRN_BYTE_WRITE_IJ:
      if (sBoxAAddr[7:0] != j[7:0])
        sBoxAEn = 1'b1;
      else
        sBoxAEn = 1'b0;
   
    default:
      sBoxAEn = 1'b0;

  endcase


// logic for sBoxAWriteEn
// sBoxAWriteEn is asserted during init when all locations of sBox RAM
// have to be filled with index values.
// it is also asserted when sBox[j] value has to be written into sBox[i] via 
// port A, in prngCs SBOX_TRN_WRITE_IJ and PRN_BYTE_WRITE_IJ.

always @(prngCs or sBoxAAddr or j)
  case (prngCs)
    SBOX_INDEX_INIT:
      sBoxAWriteEn = 1'b1;

    SBOX_TRN_WRITE_IJ:
      if (sBoxAAddr[7:0] != j[7:0])
        sBoxAWriteEn = 1'b1;
      else
        sBoxAWriteEn = 1'b0;

    PRN_BYTE_WRITE_IJ:
      if (sBoxAAddr[7:0] != j[7:0])
        sBoxAWriteEn = 1'b1;
      else
        sBoxAWriteEn = 1'b0;

    default:
      sBoxAWriteEn = 1'b0;

  endcase


// logic for sBoxAWriteData
// during init, data to be written via port A of RAM is the index itself.
// during SBOX_TRN_WRITE_IJ and PRN_BYTE_WRITE_IJ, data to be written via
// port A of RAM is the previously retrived data from port A of RAM, which is 
// sBox[j] to be written to location i.

always @(prngCs or i or sBoxAReadDataCapt)
  case (prngCs)
    SBOX_INDEX_INIT:
      sBoxAWriteData[7:0] = i[7:0];
 
    SBOX_TRN_WRITE_IJ:
      sBoxAWriteData[7:0] = sBoxAReadDataCapt[7:0];

    PRN_BYTE_WRITE_IJ:
      sBoxAWriteData[7:0] = sBoxAReadDataCapt[7:0];

   default:
     sBoxAWriteData[7:0] = 8'h0; // for synthesis optimisation;

  endcase


// logic for sBoxBAddr
// port B of the RAM is used during init for filling all locations of RAM with
// its index value. during init, sBoxBAddr is equal to i + 1.
// during SBOX_TRN_WRITE_IJ and PRN_BYTE_WRITE_IJ, it takes the value of j,
// for writing sBox[i] into location j.
// sBoxBAddr also takes the value of sBox[i] + sBox[j] for retriving a PRN
// in PRN_BYTE_READ_I prngCs from port B of RAM.

always @(prngCs or i or j or sBoxI or sBoxJ or initStatus)
  case (prngCs)
    IDLE:
      sBoxBAddr[7:0] = 8'b0;

    SBOX_INDEX_INIT:
      sBoxBAddr[7:0] = i[7:0] + 8'h1;
    
    SBOX_TRN_WRITE_IJ:
      sBoxBAddr[7:0] = j[7:0];

    PRN_BYTE_READ_I:
      if (initStatus == 1'b1)
        sBoxBAddr[7:0] = sBoxI[7:0] + sBoxJ[7:0];
      else
        sBoxBAddr[7:0] = 8'h0; // for synthesis optimisation; 

    PRN_BYTE_WRITE_IJ:
      sBoxBAddr[7:0] = j[7:0];

   default:
     sBoxBAddr[7:0] = 8'h0; // for synthesis optimisation;
  endcase


// logic for sBoxBEn
// port B is enabled during the init process.
// it is again enabled when sBox[i] is to be written into location j, during
// SBOX_TRN_WRITE_IJ and PRN_BYTE_WRITE_IJ.
// sBoxBEn is also asserted when the value of sBox[sBox[i] + sBox[j]] has
// to be retrived from port B of RAM.

always @(prngCs or sBoxAAddr or j or initStatus)
  case (prngCs)
    SBOX_INDEX_INIT:
      sBoxBEn = 1'b1;
    
    SBOX_TRN_WRITE_IJ:
      if (sBoxAAddr[7:0] != j[7:0])
        sBoxBEn = 1'b1;
      else
        sBoxBEn = 1'b0;

    PRN_BYTE_READ_I:
      if (initStatus == 1'b1)
        sBoxBEn = 1'b1;
      else
        sBoxBEn = 1'b0;
    
    PRN_BYTE_WRITE_IJ:
      if (sBoxAAddr[7:0] != j[7:0])
        sBoxBEn = 1'b1;
      else
        sBoxBEn = 1'b0;
     
    default:
      sBoxBEn = 1'b0;

  endcase


// logic for sBoxBWriteEn
// sBoxBWriteEn is asserted during the init process.
// it is again asserted when sBox[i] is to be written into location j, during
// SBOX_TRN_WRITE_IJ and PRN_BYTE_WRITE_IJ.

always @(prngCs or sBoxAAddr or j)
  case (prngCs)
    SBOX_INDEX_INIT:
      sBoxBWriteEn = 1'b1;

    SBOX_TRN_WRITE_IJ:
      if (sBoxAAddr[7:0] != j[7:0])
        sBoxBWriteEn = 1'b1;
      else
        sBoxBWriteEn = 1'b0;

    PRN_BYTE_WRITE_IJ:
      if (sBoxAAddr[7:0] != j[7:0])
        sBoxBWriteEn = 1'b1;
      else
        sBoxBWriteEn = 1'b0;
    
    default:
      sBoxBWriteEn = 1'b0;

  endcase


// logic for sBoxBWriteData
// during init, data to be written via port B of RAM is the index itself.
// during SBOX_TRN_WRITE_IJ and PRN_BYTE_WRITE_IJ, data to be written via
// port B of RAM is the previously retrived data from port A of RAM, which is 
// sBox[i] to be written to location j.

always @(prngCs or i or sBoxI)
  case (prngCs)
    SBOX_INDEX_INIT:
      sBoxBWriteData[7:0] = i[7:0] + 8'h1;
   
    SBOX_TRN_WRITE_IJ:
      sBoxBWriteData[7:0] = sBoxI[7:0];

    PRN_BYTE_WRITE_IJ:
      sBoxBWriteData[7:0] = sBoxI[7:0];

   default:
     sBoxBWriteData[7:0] = 8'h0; // for synthesis optimisation;

  endcase


// logic for nextI
// i starts with a value of 0.
// i is incremented by 2 during the SBOX_INDEX_INIT prngCs, for referencing
// every alternate location of RAM via port A.
// It is the i counter during the transformation process and later during
// calculation of PR bytes, according to the RC4 algorithm.

always @(prngCs or i)
  case (prngCs)
    IDLE:
      nextI[7:0] = 8'b0;

    SBOX_INDEX_INIT:
      if (i[7:0] == 8'hFE)
        nextI[7:0] = 8'b0;
      else
        nextI[7:0] = i[7:0] + 8'h2;
      
    SBOX_TRN_WRITE_IJ:
      if (i[7:0] == 8'hFF)
        nextI[7:0] = 8'b1;
      else
        nextI[7:0] = i[7:0] + 8'h1;

    PRN_BYTE_WRITE_IJ:
      nextI[7:0] = i[7:0] + 8'h1;

  default:
    nextI[7:0] = i[7:0];

  endcase


// logic for i, registered on clock

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    i[7:0]  <= 8'b0;
  else if (softRstBbClk_p == 1'b1)
    i[7:0]  <= 8'b0;
  else
    i[7:0]  <= nextI[7:0];


// logic for nextJ
// j starts with a value of 0.
// j is calculated according to the RC4 algorithm in prngCs SBOX_TRN_READ_J,
// for writing sBox[i] to location j via port B or RAM.
// in prngCs PRN_BYTE_READ_J, it takes a value of sBox[i] + sBox[j] for 
// generation of a PR byte.  

always @(prngCs or seedPart or j or sBoxAReadDataCapt or seed or i) 
  case (prngCs)
    IDLE:
      nextJ[7:0] = 8'b0;

    SBOX_TRN_READ_J:
     case (seedPart[4:0])

      5'd0 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[7:0];
      5'd1 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[15:8];
      5'd2 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[23:16];
      5'd3 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[31:24];
      5'd4 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[39:32];
      5'd5 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[47:40];
      5'd6 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[55:48];
      5'd7 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[63:56];
      5'd8 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[71:64];
      5'd9 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[79:72];
      5'd10 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[87:80];
      5'd11 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[95:88];
      5'd12 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[103:96];
      5'd13 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[111:104];
      5'd14 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[119:112];
      5'd15 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[127:120];
      5'd16 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[135:128];
      5'd17 :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[143:136];
      default :
        nextJ[7:0] =  j[7:0] + sBoxAReadDataCapt[7:0] + seed[151:144];

    endcase

    SBOX_TRN_WRITE_IJ:
      if (i[7:0] == 8'hFF)
        nextJ[7:0] = 8'b0;
      else
        nextJ[7:0] = j[7:0];

    PRN_BYTE_READ_J:
      nextJ[7:0] = j[7:0] + sBoxAReadDataCapt[7:0];

   default:
     nextJ[7:0] = j[7:0];

  endcase


// logic for j, registered on clock

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    j[7:0]  <= 8'b0;
  else if (softRstBbClk_p == 1'b1)
    j[7:0]  <= 8'b0;
  else
    j[7:0]  <= nextJ[7:0];


// logic for sBoxI
// sBoxI starts with an initial value of zero.
// it stores the value of sBox[i] retrived from port A of RAM temorarily
// for internal calculations.

always @(prngCs or sBoxAReadDataCapt or sBoxI)
  case (prngCs)
    IDLE:
      nextSBoxI[7:0] = 8'b0;

   SBOX_TRN_READ_J:
     nextSBoxI[7:0] = sBoxAReadDataCapt[7:0];

   PRN_BYTE_READ_J:
     nextSBoxI[7:0] = sBoxAReadDataCapt[7:0];

  default:
    nextSBoxI[7:0] = sBoxI[7:0];

  endcase


// logic for sBoxI, registered on clock

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    sBoxI[7:0]  <= 8'b0;
  else if (softRstBbClk_p == 1'b1)
    sBoxI[7:0]  <= 8'b0;
  else
    sBoxI[7:0]  <= nextSBoxI[7:0];


// logic for sBoxJ
// sBoxJ starts with an initial value of zero.
// it stores the value of sBox[j] retrived from port A of RAM temorarily
// for internal calculations.

always @(prngCs or sBoxAReadDataCapt or sBoxJ)
  case (prngCs)
    IDLE:
      nextSBoxJ[7:0] = 8'b0;

    PRN_BYTE_WRITE_IJ:
      nextSBoxJ[7:0] = sBoxAReadDataCapt[7:0];

    default:
      nextSBoxJ[7:0] = sBoxJ[7:0];

  endcase


// logic for j, registered on clock

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    sBoxJ[7:0]  <= 8'b0;
  else if (softRstBbClk_p == 1'b1)
    sBoxJ[7:0]  <= 8'b0;
  else
    sBoxJ[7:0]  <= nextSBoxJ[7:0];


// logic for nextInitStatus
// initStatus is zero at start, it takes a value of 1 the first time it enters
// PRN_BYTE_WRITE_IJ prngCs. It is used to prevent a wrong value of PR byte
// being released, the first time PRN_BYTE_READ_I prngCs is entered.

always @(prngCs or initStatus)
  if (prngCs == IDLE)
    nextInitStatus = 1'b0;

  else if (prngCs == PRN_BYTE_WRITE_IJ)
    nextInitStatus = 1'b1;

  else
    nextInitStatus = initStatus;


// logic for initStatus, registered on clock

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    initStatus  <= 1'b0;
  else if (softRstBbClk_p == 1'b1)
    initStatus  <= 1'b0;
  else
    initStatus  <= nextInitStatus;


// logic for nextSeedPart
// seedPart starts with a value of zero. It is the seed selection index, and
// is used so that the seed value need not be stored internally in this
// module. The seed value held on the input lines can be directly indexed
// by this variable.
// it varies from 0 to 7 for a 64 bit seed.
// it varies from 0 to 15 for a 128 bit seed.

// for currCipherLen as 0, and wep on (in rivierawaves header), the default 64 bit
// encryption is used)

always @(prngCs or currCipherLen or seedPart)
  case (prngCs)
    IDLE:
      nextSeedPart[4:0] = 5'b0;

    SBOX_TRN_WRITE_IJ:
      if (currCipherLen == 1'b0)
      begin
        if (seedPart[4:0] == 5'd7)
          nextSeedPart[4:0] = 5'b0;
        else
          nextSeedPart[4:0] = seedPart[4:0] + 5'h1;
      end
      else if (currCipherLen == 1'b1)
      begin
        if (seedPart[4:0] == 5'd15)
          nextSeedPart[4:0] = 5'b0;
        else
          nextSeedPart[4:0] = seedPart[4:0] + 5'h1;
      end
      else
      begin
        if (seedPart[4:0] == 5'd7)
          nextSeedPart[4:0] = 5'b0;
        else
          nextSeedPart[4:0] = seedPart[4:0] + 5'h1;
      end
    default:
      nextSeedPart[4:0] = seedPart[4:0];
       
  endcase


// logic for seedPart, registered on clock

always @(posedge bbClk or negedge hardRstBbClk_n)
  if (hardRstBbClk_n == 1'b0)
    seedPart  <= 5'b0;
  else if (softRstBbClk_p == 1'b1)
    seedPart  <= 5'b0;
  else
    seedPart[4:0]  <= nextSeedPart[4:0];


`ifdef RW_SIMU_ON
// Disable coverage the RW_SIMU_ON part because this code is not functional but 
// here to ease the simulation
// pragma coverage block = off 

// txControlMainFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (prngCs)
    IDLE                  :  prngCs_str = {"IDLE"};
    SBOX_INDEX_INIT       :  prngCs_str = {"SBOX_INDEX_INIT"};
    WAIT_FOR_SEED_VALID   :  prngCs_str = {"WAIT_FOR_SEED_VALID"};
    SBOX_TRN_READ_I       :  prngCs_str = {"SBOX_TRN_READ_I"};
    SBOX_TRN_READ_J       :  prngCs_str = {"SBOX_TRN_READ_J"};
    SBOX_TRN_WRITE_IJ     :  prngCs_str = {"SBOX_TRN_WRITE_IJ"};
    PRN_BYTE_READ_I       :  prngCs_str = {"PRN_BYTE_READ_I"};
    PRN_BYTE_READ_J       :  prngCs_str = {"PRN_BYTE_READ_J"};
    PRN_BYTE_WRITE_IJ     :  prngCs_str = {"PRN_BYTE_WRITE_IJ"};
`ifdef SBOX_RDATA_CAPT
    WAIT_SBOX_TRN_READ_I  :  prngCs_str = {"WAIT_SBOX_TRN_READ_I"};
    WAIT_SBOX_TRN_READ_J  :  prngCs_str = {"WAIT_SBOX_TRN_READ_J"};
    WAIT_PRN_BYTE_READ_I  :  prngCs_str = {"WAIT_PRN_BYTE_READ_I"};
    WAIT_PRN_BYTE_READ_J  :  prngCs_str = {"WAIT_PRN_BYTE_READ_J"};
`endif
    WAIT_FOR_STROBE       :  prngCs_str = {"WAIT_FOR_STROBE"};
    DELAY_PRN_OUT1        :  prngCs_str = {"DELAY_PRN_OUT1"};
    DELAY_PRN_OUT2        :  prngCs_str = {"DELAY_PRN_OUT2"};
    DELAY_PRN_OUT3        :  prngCs_str = {"DELAY_PRN_OUT3"};
    default               :  prngCs_str = {"XXX"};
  endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

endmodule


//------------------- END OF FILE ----------------//
