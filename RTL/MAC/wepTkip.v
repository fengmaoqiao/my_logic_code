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
//   This is the top level module which instantiates the wep modules listed
//   above. It also changes the active configuration (ie interconnection between
//   the modules) depending on the signal rxCsIsIdle.
// 
//    64/ 128 bit RC4 encryption is supported by the wep module, with on the
//    fly switching between these cipher strengths. Higher cipher strengths can be
//    easily supported when required.
//                    
// Simulation Notes : 
// Synthesis Notes  :
// Application Note :                                                       
// Simulator        :                                                       
// Parameters       :                                                       
// Terms & concepts :                                                       
// Bugs             :                                                       
// Open issues and future enhancements :                                    
//   The PRNG block has been set to at a higher frequency clock (macWTClk), 
//   whose frequency will be tied twice or thrice that of macCoreClk.
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"
module wepTkip(

  //$port_g Input ports
  `ifdef PRNG_FASTER_CLK
  input  wire                 macWTClk,              // Faster clock for WEP-TKIP crypto blocks
  input  wire                 macWTClkHardRst_n,     // Active low hard reset synchronized to macWTClk
  input  wire                 macWTClkSoftRst_p,     // Active low soft reset signal synchronized to the macWTClk
  `endif

  input  wire                 macCoreClk,            // Primary MAC core clock
  input  wire                 hardRstBbClk_n,        // Active low hard reset synchronized to MAC clock

  `ifndef PRNG_FASTER_CLK
  input  wire                 softRstBbClk_p,        // Active high soft reset synchronized to MAC clock
  `endif

  input  wire                 rxCsIsIdle,            // Signal to indicate whether core is in tx or rx
  input  wire                 cipherLen,             // signal to indicate which cipher strength to use
  input  wire           [2:0] cipherType,            // signal to indicate which cipher type
  input  wire                 initPRNG_p,            // init signal to PRNG
  input  wire                 prnStrobe_p,           // strobe pulse for releasing PRN output
  input  wire          [23:0] txWEPIV,               // WEP IV from SW
  input  wire                 txWEPIVValid,          // WEP IV Valid
  input  wire          [47:0] txRxAddress,           // Transmitter address of MPDU (TX or RX)

  input  wire         [127:0] cryptoKey,             // Key corresponding to this MAC Address
  input  wire                 cryptoKeyValid,        // Validating signal for key

  input  wire                 icvStart_p,            // indication to start taking in the data 
  input  wire                 icvSDrain_p,           // indication to start draining tha data
  input  wire                 icvEnable_p,           // enable input to FCS

  input  wire           [7:0] plainText,             // bytes input during tx to the wep block              
  input  wire           [7:0] dataFromBuffer,        // bytes input during rx to the wep block              
  input  wire          [23:0] rxInitVector,          // received IV with the MPDU                           
  input  wire                 rxError_p,             // error signal from rxcontroller                      
  input  wire           [7:0] sBoxAReadData,         // data bus from internal RAM, port A                  
  input  wire           [7:0] sBoxBReadData,         // data bus from internal RAM, port B                  

  `ifdef TKIP
  input  wire                 txTKIP,                // 48-bit TSC value for TKIP
  input  wire          [47:0] tkipSeqCntr,           // Flag indicating that TKIP should be used to
  input  wire          [47:0] macAddr,               // encrypt the current frame
  `endif

  //$port_g Output ports
  output wire                 initDone_p,           // indicated PRNG has finished init and transformation
  output wire                 prnOutValid_p,        // signal to indicate valid PRN output
  output wire                 initSBoxIndexDone_p, // signal indicating end of SBOX Index init process

  output wire          [7:0]  dataFromXor,          // bytes from XOR block
  output wire                 icvCRCOk,             // CRC OK
  output wire          [7:0]  sBoxAAddr,            // address bus to internal RAM, port A 
  output wire          [7:0]  sBoxBAddr,            // address bus to internal RAM, port B
  output wire          [7:0]  sBoxAWriteData,       // data bus to internal RAM, port A  
  output wire          [7:0]  sBoxBWriteData,       // data bus to internal RAM, port B
  output wire                 sBoxAEn,              // enable signal for internal RAM, port A
  output wire                 sBoxBEn,              // enable signal for internal RAM, port B 
  output wire                 sBoxAWriteEn,         // write enable signal for internal RAM, port A
  output wire                 sBoxBWriteEn,         // write enable signal for internal RAM, port B

  `ifdef SBOX_RDATA_CAPT
    output wire           [4:0] prngCs,               // PRNG block current state
  `else  
    output wire           [3:0] prngCs,               // PRNG block current state
  `endif
  output wire                 debug_initDonemacWTClk_p // Debug signal
 
 );

//------------- external connections -----------------

//------------- common inputs ------------

   wire                   prngIsIdle; 
   wire                   seedValid;            // Seed Validating signal
   wire                   rxErrorWtSynch_p;
   
   wire                   icvStartRxError_p;

   assign                 icvStartRxError_p = icvStart_p || rxErrorWtSynch_p;

   //------------- input to TKIP ----------------
   `ifdef TKIP
   wire                   rxTKIP;               // Indication of TKIP being used for encry/decryption

   wire            [47:0] txrAddress;
   // Transmitter address 
   assign                 txrAddress = rxCsIsIdle ? macAddr : txRxAddress;
   `endif // TKIP

   //------------- outputs from PRNG ------------
   wire                   initDonemacWTClk_p;   


//------------- external connections end -----------------

//------------- internal connections ------------

//------------- inputs to PRNG from KLG ------------

   wire [151:0]           seed;

//------------- input to MUX1TOXOR from PRNG ------------

   wire [7:0]             prnOut;

//------------- input to XOR from MUX1TOXOR ------------

   wire [7:0]             data1ToXor;
   assign                 data1ToXor[7:0] = prnOut[7:0];

//------------- input to MUX2TOXOR from ICV ------------

   wire [7:0]             dataFromICV;

//------------- input to XOR from MUX2TOXOR ------------

   wire [7:0]             data2ToXor;

`ifdef SBOX_RDATA_CAPT
   reg [7:0] dataFromBufferCapt;
   
`ifdef PRNG_FASTER_CLK
   always @(posedge macWTClk or negedge hardRstBbClk_n)
`else
   always @(posedge macCoreClk or negedge hardRstBbClk_n)
`endif
     if(hardRstBbClk_n == 1'b0)
       dataFromBufferCapt <= 8'b0;
     else 
       dataFromBufferCapt <= dataFromBuffer;
`endif   
 
 
// when rxCsIsIdle = 1, the core is in transmit mode. dataFromICV should be fed
// to XOR block, together with bytes from PRNG block.
// when rxCsIsIdle = 0, the core is in receive mode. dataFromBuffer should
// be fed to the XOR block, together with bytes from PRNG block.

`ifdef SBOX_RDATA_CAPT
   assign                 data2ToXor = rxCsIsIdle ? dataFromICV : dataFromBufferCapt;
`else
   assign                 data2ToXor = rxCsIsIdle ? dataFromICV : dataFromBuffer;
`endif
//------------- input to ICV from MUXTOICV ------------

   wire [7:0]             dataToICV;

// when rxCsIsIdle = 1, the core is in transmit mode. plainText should be fed
// to ICV block.
// when rxCsIsIdle = 0, the core is in receive mode. dataFromXor should be
// fed to ICV block.

   assign                 dataToICV = rxCsIsIdle ? plainText : dataFromXor;


//----------- inputs to TKIP --------------

   wire [151:0]           klgseed;
   wire                   klgSeedValid;
   wire                   wepProtected;
   wire                   tkipProtected;

  assign  klgSeedValid   = (!rxCsIsIdle)   ?  cryptoKeyValid                :
                                              cryptoKeyValid && txWEPIVValid;


  assign  klgseed[151:0] = (!rxCsIsIdle)   ?  {cryptoKey[127:0],rxInitVector[23:0]}: 
                           (wepProtected)  ?  {cryptoKey[127:0],txWEPIV[23:0]}     : 
                                              152'b0                               ;

   assign                 wepProtected  = (cipherType == 3'b001) ? 1'b1 : 1'b0;
   assign                 tkipProtected = (cipherType == 3'b010) ? 1'b1 : 1'b0;
   

   
`ifdef DOT11I_SUPPORTED
   
`ifdef TKIP

   wire                   txRxTKIP;

   assign                 rxTKIP = ~(rxCsIsIdle) && tkipProtected;

   assign                 txRxTKIP = (rxCsIsIdle) ? txTKIP : rxTKIP;

// ----------- input to PRNG from TKIP ---------------

   wire [127:0]           tkipSeed;
   wire                   tkipSeedValid;

//------------- input to TKIP from KLG -----------------

   wire                   initTKIP_p;
   reg                    initTKIPInt_p;
   
//------------- input to TKIP from tkipsBox ------------

   wire [15:0]            sBoxDataA;
   wire [15:0]            sBoxDataB;

//------------- input to tkipsBox from TKIP -------------

   wire [7:0]             sBoxAddressA;
   wire [7:0]             sBoxAddressB;

   assign                 seed = (txRxTKIP) ? {24'h000000,tkipSeed} : klgseed;

`else

// If TKIP is not supported and only WEP is supported then seed is directly
// assigned klgSeed from klg block.

   assign                 seed = klgseed;

`endif // TKIP

`endif // DOT11I_SUPPORTED
   
`ifdef DOT11I_SUPPORTED
   
// If the cipher suite to be used is TKIP, the seedvalid from the TKIP block
// is passed on to the PRNG block. If wep is to be used, then the seedvalid from klg is passed to the PRNG
// block
assign seedValid = (txRxTKIP) ? tkipSeedValid && tkipProtected :
                                klgSeedValid  && wepProtected;

`endif // DOT11I_SUPPORTED
   
//------------- internal connections end ------------

`ifdef PRNG_FASTER_CLK
   always @(posedge macWTClk or negedge macWTClkHardRst_n)
     if(macWTClkHardRst_n == 1'b0)
       initTKIPInt_p <= 1'b0;
     else if(macWTClkSoftRst_p == 1'b1)
       initTKIPInt_p <= 1'b0;
`else
   always @(posedge macCoreClk or negedge hardRstBbClk_n)
     if(hardRstBbClk_n == 1'b0)
       initTKIPInt_p <= 1'b0;
     else if(softRstBbClk_p == 1'b1)
       initTKIPInt_p <= 1'b0;
`endif
     else if(txRxTKIP == 1'b1)
       initTKIPInt_p <= klgSeedValid & txRxTKIP;
     else
       initTKIPInt_p <= 1'b0;

   assign initTKIP_p = (klgSeedValid & txRxTKIP) & (initTKIPInt_p == 1'b0);
   
prng #(.PRGNWEP2BBCLKRATIOINT(`WEP_2_BB_CLK_RATIO)) U_prng(

//--------------------- input ports ------------------


`ifdef PRNG_FASTER_CLK
  .bbClk (macWTClk),
  .hardRstBbClk_n (macWTClkHardRst_n),
  .softRstBbClk_p (macWTClkSoftRst_p),
`else
  .bbClk (macCoreClk),
  .hardRstBbClk_n (hardRstBbClk_n),
  .softRstBbClk_p (softRstBbClk_p),
`endif

  .currCipherLen (cipherLen),
  .seedValid (seedValid),
  .seed (seed),
  .initPRNG_p (initPRNG_p),
  .prnStrobe_p (prnStrobe_p),
  .sBoxAReadData (sBoxAReadData),
  .sBoxBReadData (sBoxBReadData),
  .rxError_p (rxErrorWtSynch_p),

//--------------------- output ports ------------------

  .initDone_p (initDonemacWTClk_p),
  .initSBoxIndexDone_p (initSBoxIndexDone_p),
  .prngIsIdle (prngIsIdle),
  .prnOut (prnOut),
  .prnOutValid_p (prnOutValid_p),
  .sBoxAAddr (sBoxAAddr),
  .sBoxBAddr (sBoxBAddr),
  .sBoxAEn (sBoxAEn),
  .sBoxBEn (sBoxBEn),
  .sBoxAWriteEn (sBoxAWriteEn),
  .sBoxBWriteEn (sBoxBWriteEn),
  .sBoxAWriteData (sBoxAWriteData),
  .sBoxBWriteData (sBoxBWriteData),
  .prngCs (prngCs)
  );

`ifdef TKIP

tkip U_tkip (

//--------------------- input ports ------------------
`ifdef PRNG_FASTER_CLK
  .bbClk (macWTClk),
  .hardRstBbClk_n (macWTClkHardRst_n),
  .softRstBbClk_p (macWTClkSoftRst_p),
`else
  .bbClk (macCoreClk),
  .hardRstBbClk_n (hardRstBbClk_n),
  .softRstBbClk_p (softRstBbClk_p),
`endif

  .initTKIP_p (initTKIP_p),
  .txRxEnd_p (prngIsIdle),
  .temporalKey (cryptoKey),
  .tkipSeqCntr (tkipSeqCntr),
  .txrAddress (txrAddress),
  .sBoxDataA (sBoxDataA),
  .sBoxDataB (sBoxDataB),
  .rxError_p (rxErrorWtSynch_p),
            
//--------------------- output ports ------------------

  .sBoxAddressA (sBoxAddressA),
  .sBoxAddressB (sBoxAddressB),
  .tkipSeed (tkipSeed),
  .tkipSeedValid (tkipSeedValid)
   );


sBoxTKIP U_sBoxTKIP (

//--------------------- input ports ------------------
`ifdef PRNG_FASTER_CLK
  .bbClk (macWTClk),
  .hardRstBbClk_n (macWTClkHardRst_n),
`else
  .bbClk (macCoreClk),
  .hardRstBbClk_n (hardRstBbClk_n),
`endif

  .sBoxAddressA (sBoxAddressA),
  .sBoxAddressB (sBoxAddressB),

//--------------------- output ports ------------------

  .sBoxDataA (sBoxDataA),
  .sBoxDataB (sBoxDataB)
  );

`endif // TKIP


icv U_icv (

// Inputs

  .bbClk (macCoreClk),
  .hardRstBbClk_n (hardRstBbClk_n),
  .dataToICV (dataToICV),
  .icvStart_p (icvStartRxError_p),
  .icvSDrain_p (icvSDrain_p),
  .icvEnable_p (icvEnable_p), 

// Outputs

  .dataFromICV (dataFromICV),
  .icvCRCOk (icvCRCOk)
  );


asyncXor U_asyncXor(

//--------------------- input ports ------------------

  .data1ToXor (data1ToXor),
  .data2ToXor (data2ToXor),

//--------------------- output ports ------------------

  .dataFromXor (dataFromXor)
  );

// ---------- Synchronizations for output signals --------------
toggleSynch1 U_initDone
(

`ifdef PRNG_FASTER_CLK

  .genClk(macWTClk),
  .hardReset_n(macWTClkHardRst_n),

`else

  .genClk(macCoreClk),
  .hardReset_n(hardRstBbClk_n),

`endif

  .synClk (macCoreClk),
  .dataIn(initDonemacWTClk_p),
  .dataOut(initDone_p)

);

assign debug_initDonemacWTClk_p = initDonemacWTClk_p;


toggleSynch1 U_rxErrorForWepSynch_p
(
  .genClk (macCoreClk),

`ifdef PRNG_FASTER_CLK

  .synClk (macWTClk),
  .hardReset_n (macWTClkHardRst_n),

`else

  .synClk (macCoreClk),
  .hardReset_n (hardRstBbClk_n),

`endif // PRNG_FASTER_CLK

  .dataIn (rxError_p),
  .dataOut (rxErrorWtSynch_p)

);

endmodule

//------------------- END OF FILE ----------------//
