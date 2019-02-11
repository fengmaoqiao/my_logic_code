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
// Description      : Top level of macCSReg module
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
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"


module macCSReg( 

    //$port_g Clocks and Reset
    input  wire macPIClk,              // Platform clock
    input  wire macPIClkHardRst_n,     // Platfrom Reset
    input  wire macPIClkSoftRst_n,     // Platfrom Reset
    input  wire macCoreClk,            // Core clock
    input  wire macCoreClkHardRst_n,   // Core Reset
    input  wire macCoreClkSoftRst_n,   // Core Reset

    // Registers
    //$port_g NEXTTBTTREG register.
    input wire [15 : 0] nextTBTT                     ,// in
    //$port_g GENINTEVENTSETREG register.
    input wire  statussetrxPayloadDMADead          ,// in
    input wire  statussetrxHeaderDMADead           ,// in
    input wire  statussetphyRxStart                ,// in
    input wire  statussetphyErr                    ,// in
    input wire  statussetmacPHYIFUnderRun          ,// in
    input wire  statussethwErr                     ,// in
    input wire  statussetimpSecDTIM                ,// in
    input wire  statussetimpPriDTIM                ,// in
    input wire  statussetbcnTxDMADead              ,// in
    input wire  statussetac3TxDMADead              ,// in
    input wire  statussetac2TxDMADead              ,// in
    input wire  statussetac1TxDMADead              ,// in
    input wire  statussetac0TxDMADead              ,// in
    input wire  statussetptError                   ,// in
    input wire  statussettimSet                    ,// in
    input wire  statussetolbcDSSS                  ,// in
    input wire  statussetolbcOFDM                  ,// in
    input wire  statussetrxFIFOOverFlow            ,// in
    input wire  statussetrxDMAEmpty                ,// in
    input wire  statussetmacPHYIFOverflow          ,// in
    input wire  statusabsGenTimers                 ,// in
    input wire  statussetidleInterrupt             ,// in
    input wire  statussetimpSecTBTT                ,// in
    input wire  statussetimpPriTBTT                ,// in
    //$port_g TXRXINTEVENTSETREG register.
    input wire  statussetbcnTxBufTrigger           ,// in
    input wire  statussetac3TxBufTrigger           ,// in
    input wire  statussetac2TxBufTrigger           ,// in
    input wire  statussetac1TxBufTrigger           ,// in
    input wire  statussetac0TxBufTrigger           ,// in
    input wire  statussetac3BWDropTrigger          ,// in
    input wire  statussetac2BWDropTrigger          ,// in
    input wire  statussetac1BWDropTrigger          ,// in
    input wire  statussetac0BWDropTrigger          ,// in
    input wire  statussetcounterRxTrigger          ,// in
    input wire  statussetbaRxTrigger               ,// in
    input wire  statussettimerRxTrigger            ,// in
    input wire  statussetrxTrigger                 ,// in
    input wire  statussettimerTxTrigger            ,// in
    input wire  statussettxopComplete              ,// in
    input wire  statussetrdTxTrigger               ,// in
    input wire  statussethccaTxTrigger             ,// in
    input wire  statussetbcnTxTrigger              ,// in
    input wire  statussetac3TxTrigger              ,// in
    input wire  statussetac2TxTrigger              ,// in
    input wire  statussetac1TxTrigger              ,// in
    input wire  statussetac0TxTrigger              ,// in
    input wire  statussetrdProtTrigger             ,// in
    input wire  statussethccaProtTrigger           ,// in
    input wire  statussetac3ProtTrigger            ,// in
    input wire  statussetac2ProtTrigger            ,// in
    input wire  statussetac1ProtTrigger            ,// in
    input wire  statussetac0ProtTrigger            ,// in
    //$port_g TIMERSINTEVENTSETREG register.
    input wire  statussetabsTimers9                ,// in
    input wire  statussetabsTimers8                ,// in
    input wire  statussetabsTimers7                ,// in
    input wire  statussetabsTimers6                ,// in
    input wire  statussetabsTimers5                ,// in
    input wire  statussetabsTimers4                ,// in
    input wire  statussetabsTimers3                ,// in
    input wire  statussetabsTimers2                ,// in
    input wire  statussetabsTimers1                ,// in
    input wire  statussetabsTimers0                ,// in
    input wire [31 : 0] tsfTimerLowIn,// in
    input wire  tsfTimerLowInValid,// in
    input wire [31 : 0] tsfTimerHighIn,// in
    input wire  tsfTimerHighInValid,// in
    input wire  computeDurationIn,// in
    input wire  computeDurationInValid,// in
    //$port_g TIMEONAIRVALUEREG register.
    input wire  timeOnAirValid               ,// in
    input wire [15 : 0] timeOnAir                    ,// in
    //$port_g DMACNTRLSETREG register.
    input wire  statussetrxPayloadNewHead          ,// in
    input wire  statussetrxHeaderNewHead           ,// in
    input wire  statussetrxPayloadNewTail          ,// in
    input wire  statussetrxHeaderNewTail           ,// in
    input wire  statussethaltAC3AfterTXOP          ,// in
    input wire  statussethaltAC2AfterTXOP          ,// in
    input wire  statussethaltAC1AfterTXOP          ,// in
    input wire  statussethaltAC0AfterTXOP          ,// in
    input wire  statussethaltBcnAfterTXOP          ,// in
    input wire  statussettxAC3NewHead              ,// in
    input wire  statussettxAC2NewHead              ,// in
    input wire  statussettxAC1NewHead              ,// in
    input wire  statussettxAC0NewHead              ,// in
    input wire  statussettxBcnNewHead              ,// in
    input wire  statussettxAC3NewTail              ,// in
    input wire  statussettxAC2NewTail              ,// in
    input wire  statussettxAC1NewTail              ,// in
    input wire  statussettxAC0NewTail              ,// in
    input wire  statussettxBcnNewTail              ,// in
    //$port_g DMASTATUS1REG register.
    input wire [1 : 0] rxPayloadState               ,// in
    input wire [1 : 0] rxHeaderState                ,// in
    input wire [1 : 0] txAC3State                   ,// in
    input wire [1 : 0] txAC2State                   ,// in
    input wire [1 : 0] txAC1State                   ,// in
    input wire [1 : 0] txAC0State                   ,// in
    input wire [1 : 0] txBcnState                   ,// in
    //$port_g DMASTATUS2REG register.
    input wire  txAC3NewHeadErr              ,// in
    input wire  txAC2NewHeadErr              ,// in
    input wire  txAC1NewHeadErr              ,// in
    input wire  txAC0NewHeadErr              ,// in
    input wire  txBcnNewHeadErr              ,// in
    input wire  txAC3BusErr                  ,// in
    input wire  txAC2BusErr                  ,// in
    input wire  txAC1BusErr                  ,// in
    input wire  txAC0BusErr                  ,// in
    input wire  txBcnBusErr                  ,// in
    input wire  txAC3PTAddressErr            ,// in
    input wire  txAC2PTAddressErr            ,// in
    input wire  txAC1PTAddressErr            ,// in
    input wire  txAC0PTAddressErr            ,// in
    input wire  txBcnPTAddressErr            ,// in
    input wire  txAC3NextPointerErr          ,// in
    input wire  txAC2NextPointerErr          ,// in
    input wire  txAC1NextPointerErr          ,// in
    input wire  txAC0NextPointerErr          ,// in
    input wire  txBcnNextPointerErr          ,// in
    input wire  txAC3UPatternErr             ,// in
    input wire  txAC2UPatternErr             ,// in
    input wire  txAC1UPatternErr             ,// in
    input wire  txAC0UPatternErr             ,// in
    input wire  txBcnUPatternErr             ,// in
    input wire  txAC3LenMismatch             ,// in
    input wire  txAC2LenMismatch             ,// in
    input wire  txAC1LenMismatch             ,// in
    input wire  txAC0LenMismatch             ,// in
    input wire  txBcnLenMismatch             ,// in
    //$port_g DMASTATUS3REG register.
    input wire  rxPayNewHeadErr              ,// in
    input wire  rxHdrNewHeadErr              ,// in
    input wire  rxPayBusErr                  ,// in
    input wire  rxHdrBusErr                  ,// in
    input wire  rxPayNextPointerErr          ,// in
    input wire  rxHdrNextPointerErr          ,// in
    input wire  rxPayUPatternErr             ,// in
    input wire  rxHdrUPatternErr             ,// in
    //$port_g DMASTATUS4REG register.
    input wire  txAC3HaltAfterTXOP           ,// in
    input wire  txAC2HaltAfterTXOP           ,// in
    input wire  txAC1HaltAfterTXOP           ,// in
    input wire  txAC0HaltAfterTXOP           ,// in
    input wire  txBcnHaltAfterTXOP           ,// in
    input wire  txAC3EndQ                    ,// in
    input wire  txAC2EndQ                    ,// in
    input wire  txAC1EndQ                    ,// in
    input wire  txAC0EndQ                    ,// in
    input wire  txBcnEndQ                    ,// in
    input wire  txAC3Startup                 ,// in
    input wire  txAC2Startup                 ,// in
    input wire  txAC1Startup                 ,// in
    input wire  txAC0Startup                 ,// in
    input wire  txBcnStartup                 ,// in
    //$port_g EDCAACHASDATASETREG register.
    input wire  statussetac3HasData                ,// in
    input wire  statussetac2HasData                ,// in
    input wire  statussetac1HasData                ,// in
    input wire  statussetac0HasData                ,// in
    //$port_g MOT1REG register.
    input wire [15 : 0] ac1MOT                       ,// in
    input wire [15 : 0] ac0MOT                       ,// in
    //$port_g MOT2REG register.
    input wire [15 : 0] ac3MOT                       ,// in
    input wire [15 : 0] ac2MOT                       ,// in
    //$port_g MOT3REG register.
    input wire [15 : 0] miscMOT                      ,// in
    input wire [15 : 0] hccaQAPMOT                   ,// in
    //$port_g TXBWDROPINFOREG register.
    input wire [1 : 0] txBWAfterDrop                ,// in
    //$port_g DEBUGBCNSPTRREG register.
    input wire [31 : 0] bcnStatusPointer             ,// in
    //$port_g DEBUGAC0SPTRREG register.
    input wire [31 : 0] ac0StatusPointer             ,// in
    //$port_g DEBUGAC1SPTRREG register.
    input wire [31 : 0] ac1StatusPointer             ,// in
    //$port_g DEBUGAC2SPTRREG register.
    input wire [31 : 0] ac2StatusPointer             ,// in
    //$port_g DEBUGAC3SPTRREG register.
    input wire [31 : 0] ac3StatusPointer             ,// in
    //$port_g DEBUGTXCPTRREG register.
    input wire [31 : 0] txCurrentPointer             ,// in
    //$port_g DEBUGRXPAYSPTRREG register.
    input wire [31 : 0] rxPayStatPointer             ,// in
    //$port_g DEBUGRXHDRCPTRREG register.
    input wire [31 : 0] rxHdrStatPointer             ,// in
    //$port_g DEBUGRXPAYCPTRREG register.
    input wire [31 : 0] rxPayCurrentPointer          ,// in
    input wire  swProf31In,// in
    input wire  swProf31InValid,// in
    input wire  swProf30In,// in
    input wire  swProf30InValid,// in
    input wire  swProf29In,// in
    input wire  swProf29InValid,// in
    input wire  swProf28In,// in
    input wire  swProf28InValid,// in
    input wire  swProf27In,// in
    input wire  swProf27InValid,// in
    input wire  swProf26In,// in
    input wire  swProf26InValid,// in
    input wire  swProf25In,// in
    input wire  swProf25InValid,// in
    input wire  swProf24In,// in
    input wire  swProf24InValid,// in
    input wire  swProf23In,// in
    input wire  swProf23InValid,// in
    input wire  swProf22In,// in
    input wire  swProf22InValid,// in
    input wire  swProf21In,// in
    input wire  swProf21InValid,// in
    input wire  swProf20In,// in
    input wire  swProf20InValid,// in
    input wire  swProf19In,// in
    input wire  swProf19InValid,// in
    input wire  swProf18In,// in
    input wire  swProf18InValid,// in
    input wire  swProf17In,// in
    input wire  swProf17InValid,// in
    input wire  swProf16In,// in
    input wire  swProf16InValid,// in
    input wire  swProf15In,// in
    input wire  swProf15InValid,// in
    input wire  swProf14In,// in
    input wire  swProf14InValid,// in
    input wire  swProf13In,// in
    input wire  swProf13InValid,// in
    input wire  swProf12In,// in
    input wire  swProf12InValid,// in
    input wire  swProf11In,// in
    input wire  swProf11InValid,// in
    input wire  swProf10In,// in
    input wire  swProf10InValid,// in
    input wire  swProf9In,// in
    input wire  swProf9InValid,// in
    input wire  swProf8In,// in
    input wire  swProf8InValid,// in
    input wire  swProf7In,// in
    input wire  swProf7InValid,// in
    input wire  swProf6In,// in
    input wire  swProf6InValid,// in
    input wire  swProf5In,// in
    input wire  swProf5InValid,// in
    input wire  swProf4In,// in
    input wire  swProf4InValid,// in
    input wire  swProf3In,// in
    input wire  swProf3InValid,// in
    input wire  swProf2In,// in
    input wire  swProf2InValid,// in
    input wire  swProf1In,// in
    input wire  swProf1InValid,// in
    input wire  swProf0In,// in
    input wire  swProf0InValid,// in
    //$port_g SWSETPROFILINGREG register.
    input wire  statusswSetProf31                  ,// in
    input wire  statusswSetProf30                  ,// in
    input wire  statusswSetProf29                  ,// in
    input wire  statusswSetProf28                  ,// in
    input wire  statusswSetProf27                  ,// in
    input wire  statusswSetProf26                  ,// in
    input wire  statusswSetProf25                  ,// in
    input wire  statusswSetProf24                  ,// in
    input wire  statusswSetProf23                  ,// in
    input wire  statusswSetProf22                  ,// in
    input wire  statusswSetProf21                  ,// in
    input wire  statusswSetProf20                  ,// in
    input wire  statusswSetProf19                  ,// in
    input wire  statusswSetProf18                  ,// in
    input wire  statusswSetProf17                  ,// in
    input wire  statusswSetProf16                  ,// in
    input wire  statusswSetProf15                  ,// in
    input wire  statusswSetProf14                  ,// in
    input wire  statusswSetProf13                  ,// in
    input wire  statusswSetProf12                  ,// in
    input wire  statusswSetProf11                  ,// in
    input wire  statusswSetProf10                  ,// in
    input wire  statusswSetProf9                   ,// in
    input wire  statusswSetProf8                   ,// in
    input wire  statusswSetProf7                   ,// in
    input wire  statusswSetProf6                   ,// in
    input wire  statusswSetProf5                   ,// in
    input wire  statusswSetProf4                   ,// in
    input wire  statusswSetProf3                   ,// in
    input wire  statusswSetProf2                   ,// in
    input wire  statusswSetProf1                   ,// in
    input wire  statusswSetProf0                   ,// in
    //$port_g SIGNATUREREG register.
    input wire [31 : 0] signature                    ,// in
    //$port_g VERSION1REG register.
    input wire  mac80211MHFormat             ,// in
    input wire  coex                         ,// in
    input wire  wapi                         ,// in
    input wire  tpc                          ,// in
    input wire  vht                          ,// in
    input wire  ht                           ,// in
    input wire  rce                          ,// in
    input wire  ccmp                         ,// in
    input wire  tkip                         ,// in
    input wire  wep                          ,// in
    input wire  security                     ,// in
    input wire  sme                          ,// in
    input wire  hcca                         ,// in
    input wire  edca                         ,// in
    input wire  qos                          ,// in
    //$port_g VERSION2REG register.
    input wire [2 : 0] phaseNumber                  ,// in
    input wire [5 : 0] releaseNumber                ,// in
    input wire  ieRelease                    ,// in
    input wire [6 : 0] umVersion                    ,// in
    //$port_g BITMAPCNTREG register.
    input wire [15 : 0] bitmapCnt                    ,// in
    input wire [3 : 0] nextStateIn,// in
    input wire  nextStateInValid,// in
    //$port_g STATECNTRLREG register.
    input wire [3 : 0] currentState                 ,// in
    input wire  tsfUpdatedBySWIn,// in
    input wire  tsfUpdatedBySWInValid,// in
    input wire  keyStoRAMResetIn,// in
    input wire  keyStoRAMResetInValid,// in
    input wire  mibTableResetIn,// in
    input wire  mibTableResetInValid,// in
    input wire  baPSBitmapResetIn,// in
    input wire  baPSBitmapResetInValid,// in
    input wire  encrRxFIFOResetIn,// in
    input wire  encrRxFIFOResetInValid,// in
    input wire  macPHYIFFIFOResetIn,// in
    input wire  macPHYIFFIFOResetInValid,// in
    input wire  txFIFOResetIn,// in
    input wire  txFIFOResetInValid,// in
    input wire  rxFIFOResetIn,// in
    input wire  rxFIFOResetInValid,// in
    input wire  hwFSMResetIn,// in
    input wire  hwFSMResetInValid,// in
    //$port_g MACERRRECCNTRLREG register.
    input wire  useErrRec                    ,// in
    //$port_g MACERRSETSTATUSREG register.
    input wire  statuserrInHWLevel3                ,// in
    input wire  statuserrInTxRxLevel2              ,// in
    input wire  statuserrInRxLevel1                ,// in
    input wire  statuserrInTxLevel1                ,// in
    //$port_g RXCNTRLREG register.
    input wire  enDuplicateDetection         ,// in
    input wire  dtimUpdatedBySWIn,// in
    input wire  dtimUpdatedBySWInValid,// in
    input wire [7 : 0] cfpPeriodIn,// in
    input wire  cfpPeriodInValid,// in
    input wire [7 : 0] dtimPeriodIn,// in
    input wire  dtimPeriodInValid,// in
    input wire [31 : 0] encrKeyRAMWord0In,// in
    input wire  encrKeyRAMWord0InValid,// in
    input wire [31 : 0] encrKeyRAMWord1In,// in
    input wire  encrKeyRAMWord1InValid,// in
    input wire [31 : 0] encrKeyRAMWord2In,// in
    input wire  encrKeyRAMWord2InValid,// in
    input wire [31 : 0] encrKeyRAMWord3In,// in
    input wire  encrKeyRAMWord3InValid,// in
    input wire [31 : 0] macAddrRAMLowIn,// in
    input wire  macAddrRAMLowInValid,// in
    input wire [15 : 0] macAddrRAMHighIn,// in
    input wire  macAddrRAMHighInValid,// in
    input wire  newReadIn,// in
    input wire  newReadInValid,// in
    input wire  newWriteIn,// in
    input wire  newWriteInValid,// in
    input wire [2 : 0] cTypeRAMIn,// in
    input wire  cTypeRAMInValid,// in
    input wire [3 : 0] vlanIDRAMIn,// in
    input wire  vlanIDRAMInValid,// in
    input wire [1 : 0] sppRAMIn,// in
    input wire  sppRAMInValid,// in
    input wire  useDefKeyRAMIn,// in
    input wire  useDefKeyRAMInValid,// in
    input wire  cLenRAMIn,// in
    input wire  cLenRAMInValid,// in
`ifdef RW_WAPI_EN                     
    input wire [31 : 0] encrIntKeyRAMWord0In,// in
    input wire  encrIntKeyRAMWord0InValid,// in
    input wire [31 : 0] encrIntKeyRAMWord1In,// in
    input wire  encrIntKeyRAMWord1InValid,// in
    input wire [31 : 0] encrIntKeyRAMWord2In,// in
    input wire  encrIntKeyRAMWord2InValid,// in
    input wire [31 : 0] encrIntKeyRAMWord3In,// in
    input wire  encrIntKeyRAMWord3InValid,// in
`endif // RW_WAPI_EN                     
    //$port_g PROTTRIGTIMERREG register.
    input wire [7 : 0] hccaTriggerTimer             ,// in
    input wire  mibWriteIn,// in
    input wire  mibWriteInValid,// in
    //$port_g MONOTONICCOUNTER1REG register.
    input wire [31 : 0] monotonicCounter1            ,// in
    //$port_g MONOTONICCOUNTER2LOREG register.
    input wire [31 : 0] monotonicCounterLow2         ,// in
    //$port_g MONOTONICCOUNTER2HIREG register.
    input wire [15 : 0] monotonicCounterHigh2        ,// in
    input wire [31 : 0] ccaBusyDurIn,// in
    input wire  ccaBusyDurInValid,// in
    input wire  sendCFEndNowIn,// in
    input wire  sendCFEndNowInValid,// in
    input wire [15 : 0] quietDuration1In,// in
    input wire  quietDuration1InValid,// in
    input wire [7 : 0] quietPeriod1In,// in
    input wire  quietPeriod1InValid,// in
    input wire [7 : 0] quietCount1In,// in
    input wire  quietCount1InValid,// in
    input wire [15 : 0] quietOffset1In,// in
    input wire  quietOffset1InValid,// in
    input wire [15 : 0] quietDuration2In,// in
    input wire  quietDuration2InValid,// in
    input wire [7 : 0] quietPeriod2In,// in
    input wire  quietPeriod2InValid,// in
    input wire [7 : 0] quietCount2In,// in
    input wire  quietCount2InValid,// in
    input wire [15 : 0] quietOffset2In,// in
    input wire  quietOffset2InValid,// in
    input wire [31 : 0] ccaBusyDurSec20In,// in
    input wire  ccaBusyDurSec20InValid,// in
    input wire [31 : 0] ccaBusyDurSec40In,// in
    input wire  ccaBusyDurSec40InValid,// in
    input wire [31 : 0] ccaBusyDurSec80In,// in
    input wire  ccaBusyDurSec80InValid,// in
    input wire  startTxFrameExIn,// in
    input wire  startTxFrameExInValid,// in
`ifdef RW_WLAN_COEX_EN                
`endif // RW_WLAN_COEX_EN                
    //$port_g DEBUGHWSM1REG register.
    input wire [7 : 0] macControlLs                 ,// in
    input wire [8 : 0] txControlLs                  ,// in
    input wire [4 : 0] rxControlLs                  ,// in
    //$port_g DEBUGHWSM2REG register.
    input wire [7 : 0] macControlCs                 ,// in
    input wire [8 : 0] txControlCs                  ,// in
    input wire [4 : 0] rxControlCs                  ,// in
    //$port_g DEBUGPORTVALUEREG register.
    input wire [31 : 0] debugPortRead                ,// in
    input wire [25 : 0] navCounterIn,// in
    input wire  navCounterInValid,// in
    //$port_g DEBUGCWREG register.
    input wire [1 : 0] activeAC                     ,// in
    input wire [3 : 0] currentCW3                   ,// in
    input wire [3 : 0] currentCW2                   ,// in
    input wire [3 : 0] currentCW1                   ,// in
    input wire [3 : 0] currentCW0                   ,// in
    //$port_g DEBUGQSRCREG register.
    input wire [7 : 0] ac3QSRC                      ,// in
    input wire [7 : 0] ac2QSRC                      ,// in
    input wire [7 : 0] ac1QSRC                      ,// in
    input wire [7 : 0] ac0QSRC                      ,// in
    //$port_g DEBUGQLRCREG register.
    input wire [7 : 0] ac3QLRC                      ,// in
    input wire [7 : 0] ac2QLRC                      ,// in
    input wire [7 : 0] ac1QLRC                      ,// in
    input wire [7 : 0] ac0QLRC                      ,// in
    //
    //$port_g DOZECNTRL2REG register.
    output wire  wakeUpFromDoze           ,// out
    output wire  wakeUpSW                 ,// out
    //$port_g MACCNTRL2REG register.
    output wire  softReset                ,// out
    //$port_g GENINTEVENTSETREG register.
    output wire  setrxPayloadDMADead      ,// out
    output wire  setrxHeaderDMADead       ,// out
    output wire  setphyRxStart            ,// out
    output wire  setphyErr                ,// out
    output wire  setmacPHYIFUnderRun      ,// out
    output wire  sethwErr                 ,// out
    output wire  setimpSecDTIM            ,// out
    output wire  setimpPriDTIM            ,// out
    output wire  setbcnTxDMADead          ,// out
    output wire  setac3TxDMADead          ,// out
    output wire  setac2TxDMADead          ,// out
    output wire  setac1TxDMADead          ,// out
    output wire  setac0TxDMADead          ,// out
    output wire  setptError               ,// out
    output wire  settimSet                ,// out
    output wire  setolbcDSSS              ,// out
    output wire  setolbcOFDM              ,// out
    output wire  setrxFIFOOverFlow        ,// out
    output wire  setrxDMAEmpty            ,// out
    output wire  setmacPHYIFOverflow      ,// out
    output wire  absGenTimers             ,// out
    output wire  setidleInterrupt         ,// out
    output wire  setimpSecTBTT            ,// out
    output wire  setimpPriTBTT            ,// out
    //$port_g GENINTEVENTCLEARREG register.
    output wire  clearrxPayloadDMADead    ,// out
    output wire  clearrxHeaderDMADead     ,// out
    output wire  clearphyRxStart          ,// out
    output wire  clearphyErr              ,// out
    output wire  clearmacPHYIFUnderRun    ,// out
    output wire  clearhwErr               ,// out
    output wire  clearimpSecDTIM          ,// out
    output wire  clearimpPriDTIM          ,// out
    output wire  clearbcnTxDMADead        ,// out
    output wire  clearac3TxDMADead        ,// out
    output wire  clearac2TxDMADead        ,// out
    output wire  clearac1TxDMADead        ,// out
    output wire  clearac0TxDMADead        ,// out
    output wire  clearptError             ,// out
    output wire  cleartimSet              ,// out
    output wire  clearolbcDSSS            ,// out
    output wire  clearolbcOFDM            ,// out
    output wire  clearrxFIFOOverFlow      ,// out
    output wire  clearrxDMAEmpty          ,// out
    output wire  clearmacPHYIFOverflow    ,// out
    output wire  clearidleInterrupt       ,// out
    output wire  clearimpSecTBTT          ,// out
    output wire  clearimpPriTBTT          ,// out
    //$port_g GENINTUNMASKREG register.
    output wire  masterGenIntEn           ,// out
    output wire  maskrxPayloadDMADead     ,// out
    output wire  maskrxHeaderDMADead      ,// out
    output wire  maskphyRxStart           ,// out
    output wire  maskphyErr               ,// out
    output wire  maskmacPHYIFUnderRun     ,// out
    output wire  maskhwErr                ,// out
    output wire  maskimpSecDTIM           ,// out
    output wire  maskimpPriDTIM           ,// out
    output wire  maskbcnTxDMADead         ,// out
    output wire  maskac3TxDMADead         ,// out
    output wire  maskac2TxDMADead         ,// out
    output wire  maskac1TxDMADead         ,// out
    output wire  maskac0TxDMADead         ,// out
    output wire  maskptError              ,// out
    output wire  masktimSet               ,// out
    output wire  maskolbcDSSS             ,// out
    output wire  maskolbcOFDM             ,// out
    output wire  maskrxFIFOOverFlow       ,// out
    output wire  maskrxDMAEmpty           ,// out
    output wire  maskmacPHYIFOverflow     ,// out
    output wire  maskabsGenTimers         ,// out
    output wire  maskidleInterrupt        ,// out
    output wire  maskimpSecTBTT           ,// out
    output wire  maskimpPriTBTT           ,// out
    //$port_g TXRXINTEVENTSETREG register.
    output wire  setbcnTxBufTrigger       ,// out
    output wire  setac3TxBufTrigger       ,// out
    output wire  setac2TxBufTrigger       ,// out
    output wire  setac1TxBufTrigger       ,// out
    output wire  setac0TxBufTrigger       ,// out
    output wire  setac3BWDropTrigger      ,// out
    output wire  setac2BWDropTrigger      ,// out
    output wire  setac1BWDropTrigger      ,// out
    output wire  setac0BWDropTrigger      ,// out
    output wire  setcounterRxTrigger      ,// out
    output wire  setbaRxTrigger           ,// out
    output wire  settimerRxTrigger        ,// out
    output wire  setrxTrigger             ,// out
    output wire  settimerTxTrigger        ,// out
    output wire  settxopComplete          ,// out
    output wire  setrdTxTrigger           ,// out
    output wire  sethccaTxTrigger         ,// out
    output wire  setbcnTxTrigger          ,// out
    output wire  setac3TxTrigger          ,// out
    output wire  setac2TxTrigger          ,// out
    output wire  setac1TxTrigger          ,// out
    output wire  setac0TxTrigger          ,// out
    output wire  setrdProtTrigger         ,// out
    output wire  sethccaProtTrigger       ,// out
    output wire  setac3ProtTrigger        ,// out
    output wire  setac2ProtTrigger        ,// out
    output wire  setac1ProtTrigger        ,// out
    output wire  setac0ProtTrigger        ,// out
    //$port_g TXRXINTEVENTCLEARREG register.
    output wire  clearbcnTxBufTrigger     ,// out
    output wire  clearac3TxBufTrigger     ,// out
    output wire  clearac2TxBufTrigger     ,// out
    output wire  clearac1TxBufTrigger     ,// out
    output wire  clearac0TxBufTrigger     ,// out
    output wire  clearac3BWDropTrigger    ,// out
    output wire  clearac2BWDropTrigger    ,// out
    output wire  clearac1BWDropTrigger    ,// out
    output wire  clearac0BWDropTrigger    ,// out
    output wire  clearcounterRxTrigger    ,// out
    output wire  clearbaRxTrigger         ,// out
    output wire  cleartimerRxTrigger      ,// out
    output wire  clearrxTrigger           ,// out
    output wire  cleartimerTxTrigger      ,// out
    output wire  cleartxopComplete        ,// out
    output wire  clearrdTxTrigger         ,// out
    output wire  clearhccaTxTrigger       ,// out
    output wire  clearbcnTxTrigger        ,// out
    output wire  clearac3TxTrigger        ,// out
    output wire  clearac2TxTrigger        ,// out
    output wire  clearac1TxTrigger        ,// out
    output wire  clearac0TxTrigger        ,// out
    output wire  clearrdProtTrigger       ,// out
    output wire  clearhccaProtTrigger     ,// out
    output wire  clearac3ProtTrigger      ,// out
    output wire  clearac2ProtTrigger      ,// out
    output wire  clearac1ProtTrigger      ,// out
    output wire  clearac0ProtTrigger      ,// out
    //$port_g TXRXINTUNMASKREG register.
    output wire  masterTxRxIntEn          ,// out
    output wire  maskbcnTxBufTrigger      ,// out
    output wire  maskac3TxBufTrigger      ,// out
    output wire  maskac2TxBufTrigger      ,// out
    output wire  maskac1TxBufTrigger      ,// out
    output wire  maskac0TxBufTrigger      ,// out
    output wire  maskac3BWDropTrigger     ,// out
    output wire  maskac2BWDropTrigger     ,// out
    output wire  maskac1BWDropTrigger     ,// out
    output wire  maskac0BWDropTrigger     ,// out
    output wire  maskcounterRxTrigger     ,// out
    output wire  maskbaRxTrigger          ,// out
    output wire  masktimerRxTrigger       ,// out
    output wire  maskrxTrigger            ,// out
    output wire  masktimerTxTrigger       ,// out
    output wire  masktxopComplete         ,// out
    output wire  maskrdTxTrigger          ,// out
    output wire  maskhccaTxTrigger        ,// out
    output wire  maskbcnTxTrigger         ,// out
    output wire  maskac3TxTrigger         ,// out
    output wire  maskac2TxTrigger         ,// out
    output wire  maskac1TxTrigger         ,// out
    output wire  maskac0TxTrigger         ,// out
    output wire  maskrdProtTrigger        ,// out
    output wire  maskhccaProtTrigger      ,// out
    output wire  maskac3ProtTrigger       ,// out
    output wire  maskac2ProtTrigger       ,// out
    output wire  maskac1ProtTrigger       ,// out
    output wire  maskac0ProtTrigger       ,// out
    //$port_g TIMERSINTEVENTSETREG register.
    output wire  setabsTimers9            ,// out
    output wire  setabsTimers8            ,// out
    output wire  setabsTimers7            ,// out
    output wire  setabsTimers6            ,// out
    output wire  setabsTimers5            ,// out
    output wire  setabsTimers4            ,// out
    output wire  setabsTimers3            ,// out
    output wire  setabsTimers2            ,// out
    output wire  setabsTimers1            ,// out
    output wire  setabsTimers0            ,// out
    //$port_g TIMERSINTEVENTCLEARREG register.
    output wire  clearabsTimers9          ,// out
    output wire  clearabsTimers8          ,// out
    output wire  clearabsTimers7          ,// out
    output wire  clearabsTimers6          ,// out
    output wire  clearabsTimers5          ,// out
    output wire  clearabsTimers4          ,// out
    output wire  clearabsTimers3          ,// out
    output wire  clearabsTimers2          ,// out
    output wire  clearabsTimers1          ,// out
    output wire  clearabsTimers0          ,// out
    //$port_g TIMERSINTUNMASKREG register.
    output wire  maskabsTimers9           ,// out
    output wire  maskabsTimers8           ,// out
    output wire  maskabsTimers7           ,// out
    output wire  maskabsTimers6           ,// out
    output wire  maskabsTimers5           ,// out
    output wire  maskabsTimers4           ,// out
    output wire  maskabsTimers3           ,// out
    output wire  maskabsTimers2           ,// out
    output wire  maskabsTimers1           ,// out
    output wire  maskabsTimers0           ,// out
    //$port_g TSFLOREG register.
    output wire [31 : 0] tsfTimerLow              ,// out
    //$port_g TSFHIREG register.
    output wire [31 : 0] tsfTimerHigh             ,// out
    //$port_g TIMEONAIRPARAM1REG register.
    output wire [1 : 0] ppduSTBC                 ,// out
    output wire [1 : 0] ppduNumExtnSS            ,// out
    output wire  ppduShortGI              ,// out
    output wire [2 : 0] ppduPreType              ,// out
    output wire [1 : 0] ppduBW                   ,// out
    output wire [19 : 0] ppduLength               ,// out
    //$port_g TIMEONAIRPARAM2REG register.
    output wire [6 : 0] ppduMCSIndex             ,// out
    //$port_g TIMEONAIRVALUEREG register.
    output wire  computeDuration          ,// out
    //$port_g DMACNTRLSETREG register.
    output wire  setrxPayloadNewHead      ,// out
    output wire  setrxHeaderNewHead       ,// out
    output wire  setrxPayloadNewTail      ,// out
    output wire  setrxHeaderNewTail       ,// out
    output wire  sethaltAC3AfterTXOP      ,// out
    output wire  sethaltAC2AfterTXOP      ,// out
    output wire  sethaltAC1AfterTXOP      ,// out
    output wire  sethaltAC0AfterTXOP      ,// out
    output wire  sethaltBcnAfterTXOP      ,// out
    output wire  settxAC3NewHead          ,// out
    output wire  settxAC2NewHead          ,// out
    output wire  settxAC1NewHead          ,// out
    output wire  settxAC0NewHead          ,// out
    output wire  settxBcnNewHead          ,// out
    output wire  settxAC3NewTail          ,// out
    output wire  settxAC2NewTail          ,// out
    output wire  settxAC1NewTail          ,// out
    output wire  settxAC0NewTail          ,// out
    output wire  settxBcnNewTail          ,// out
    //$port_g DMACNTRLCLEARREG register.
    output wire  clearrxPayloadNewHead    ,// out
    output wire  clearrxHeaderNewHead     ,// out
    output wire  clearrxPayloadNewTail    ,// out
    output wire  clearrxHeaderNewTail     ,// out
    output wire  clearhaltAC3AfterTXOP    ,// out
    output wire  clearhaltAC2AfterTXOP    ,// out
    output wire  clearhaltAC1AfterTXOP    ,// out
    output wire  clearhaltAC0AfterTXOP    ,// out
    output wire  clearhaltBcnAfterTXOP    ,// out
    output wire  cleartxAC3NewHead        ,// out
    output wire  cleartxAC2NewHead        ,// out
    output wire  cleartxAC1NewHead        ,// out
    output wire  cleartxAC0NewHead        ,// out
    output wire  cleartxBcnNewHead        ,// out
    output wire  cleartxAC3NewTail        ,// out
    output wire  cleartxAC2NewTail        ,// out
    output wire  cleartxAC1NewTail        ,// out
    output wire  cleartxAC0NewTail        ,// out
    output wire  cleartxBcnNewTail        ,// out
    //$port_g TXBCNHEADPTRREG register.
    output wire [31 : 0] txBcnHeadPtr             ,// out
    //$port_g TXAC0HEADPTRREG register.
    output wire [31 : 0] txAC0HeadPtr             ,// out
    //$port_g TXAC1HEADPTRREG register.
    output wire [31 : 0] txAC1HeadPtr             ,// out
    //$port_g TXAC2HEADPTRREG register.
    output wire [31 : 0] txAC2HeadPtr             ,// out
    //$port_g TXAC3HEADPTRREG register.
    output wire [31 : 0] txAC3HeadPtr             ,// out
    //$port_g TXSTRUCTSIZESREG register.
    output wire [5 : 0] dmaRBDSize               ,// out
    output wire [5 : 0] dmaRHDSize               ,// out
    output wire [5 : 0] dmaTBDSize               ,// out
    output wire [5 : 0] dmaTHDSize               ,// out
    output wire [5 : 0] ptEntrySize              ,// out
    //$port_g RXHEADERHEADPTRREG register.
    output wire [29 : 0] rxHeaderHeadPtr          ,// out
    output wire  rxHeaderHeadPtrValid     ,// out
    //$port_g RXPAYLOADHEADPTRREG register.
    output wire [29 : 0] rxPayloadHeadPtr         ,// out
    output wire  rxPayloadHeadPtrValid    ,// out
    //$port_g DMATHRESHOLDREG register.
    output wire [7 : 0] rxFIFOThreshold          ,// out
    output wire [7 : 0] txFIFOThreshold          ,// out
    //$port_g EDCAACHASDATASETREG register.
    output wire  setac3HasData            ,// out
    output wire  setac2HasData            ,// out
    output wire  setac1HasData            ,// out
    output wire  setac0HasData            ,// out
    //$port_g EDCAACHASDATACLEARREG register.
    output wire  clearac3HasData          ,// out
    output wire  clearac2HasData          ,// out
    output wire  clearac1HasData          ,// out
    output wire  clearac0HasData          ,// out
    //$port_g SWPROFILINGREG register.
    output wire  swProf31                 ,// out
    output wire  swProf30                 ,// out
    output wire  swProf29                 ,// out
    output wire  swProf28                 ,// out
    output wire  swProf27                 ,// out
    output wire  swProf26                 ,// out
    output wire  swProf25                 ,// out
    output wire  swProf24                 ,// out
    output wire  swProf23                 ,// out
    output wire  swProf22                 ,// out
    output wire  swProf21                 ,// out
    output wire  swProf20                 ,// out
    output wire  swProf19                 ,// out
    output wire  swProf18                 ,// out
    output wire  swProf17                 ,// out
    output wire  swProf16                 ,// out
    output wire  swProf15                 ,// out
    output wire  swProf14                 ,// out
    output wire  swProf13                 ,// out
    output wire  swProf12                 ,// out
    output wire  swProf11                 ,// out
    output wire  swProf10                 ,// out
    output wire  swProf9                  ,// out
    output wire  swProf8                  ,// out
    output wire  swProf7                  ,// out
    output wire  swProf6                  ,// out
    output wire  swProf5                  ,// out
    output wire  swProf4                  ,// out
    output wire  swProf3                  ,// out
    output wire  swProf2                  ,// out
    output wire  swProf1                  ,// out
    output wire  swProf0                  ,// out
    //$port_g SWSETPROFILINGREG register.
    output wire  swSetProf31              ,// out
    output wire  swSetProf30              ,// out
    output wire  swSetProf29              ,// out
    output wire  swSetProf28              ,// out
    output wire  swSetProf27              ,// out
    output wire  swSetProf26              ,// out
    output wire  swSetProf25              ,// out
    output wire  swSetProf24              ,// out
    output wire  swSetProf23              ,// out
    output wire  swSetProf22              ,// out
    output wire  swSetProf21              ,// out
    output wire  swSetProf20              ,// out
    output wire  swSetProf19              ,// out
    output wire  swSetProf18              ,// out
    output wire  swSetProf17              ,// out
    output wire  swSetProf16              ,// out
    output wire  swSetProf15              ,// out
    output wire  swSetProf14              ,// out
    output wire  swSetProf13              ,// out
    output wire  swSetProf12              ,// out
    output wire  swSetProf11              ,// out
    output wire  swSetProf10              ,// out
    output wire  swSetProf9               ,// out
    output wire  swSetProf8               ,// out
    output wire  swSetProf7               ,// out
    output wire  swSetProf6               ,// out
    output wire  swSetProf5               ,// out
    output wire  swSetProf4               ,// out
    output wire  swSetProf3               ,// out
    output wire  swSetProf2               ,// out
    output wire  swSetProf1               ,// out
    output wire  swSetProf0               ,// out
    //$port_g SWCLEARPROFILINGREG register.
    output wire  swClearProf31            ,// out
    output wire  swClearProf30            ,// out
    output wire  swClearProf29            ,// out
    output wire  swClearProf28            ,// out
    output wire  swClearProf27            ,// out
    output wire  swClearProf26            ,// out
    output wire  swClearProf25            ,// out
    output wire  swClearProf24            ,// out
    output wire  swClearProf23            ,// out
    output wire  swClearProf22            ,// out
    output wire  swClearProf21            ,// out
    output wire  swClearProf20            ,// out
    output wire  swClearProf19            ,// out
    output wire  swClearProf18            ,// out
    output wire  swClearProf17            ,// out
    output wire  swClearProf16            ,// out
    output wire  swClearProf15            ,// out
    output wire  swClearProf14            ,// out
    output wire  swClearProf13            ,// out
    output wire  swClearProf12            ,// out
    output wire  swClearProf11            ,// out
    output wire  swClearProf10            ,// out
    output wire  swClearProf9             ,// out
    output wire  swClearProf8             ,// out
    output wire  swClearProf7             ,// out
    output wire  swClearProf6             ,// out
    output wire  swClearProf5             ,// out
    output wire  swClearProf4             ,// out
    output wire  swClearProf3             ,// out
    output wire  swClearProf2             ,// out
    output wire  swClearProf1             ,// out
    output wire  swClearProf0             ,// out
    //$port_g SIGNATUREREG register.
    //$port_g MACADDRLOWREG register.
    output wire [31 : 0] macAddrLow               ,// out
    //$port_g MACADDRHIREG register.
    output wire [15 : 0] macAddrHigh              ,// out
    //$port_g MACADDRLOWMASKREG register.
    output wire [31 : 0] macAddrLowMask           ,// out
    //$port_g MACADDRHIMASKREG register.
    output wire [15 : 0] macAddrHighMask          ,// out
    //$port_g BSSIDLOWREG register.
    output wire [31 : 0] bssIDLow                 ,// out
    //$port_g BSSIDHIREG register.
    output wire [15 : 0] bssIDHigh                ,// out
    //$port_g BSSIDLOWMASKREG register.
    output wire [31 : 0] bssIDLowMask             ,// out
    //$port_g BSSIDHIMASKREG register.
    output wire [15 : 0] bssIDHighMask            ,// out
    //$port_g STATECNTRLREG register.
    output wire [3 : 0] nextState                ,// out
    //$port_g SCANCNTRLREG register.
    output wire [15 : 0] probeDelay               ,// out
    //$port_g DOZECNTRL1REG register.
    output wire [14 : 0] atimW                    ,// out
    output wire  wakeupDTIM               ,// out
    output wire [15 : 0] listenInterval           ,// out
    //$port_g MACCNTRL1REG register.
    output wire  rxRIFSEn                 ,// out
    output wire  tsfMgtDisable            ,// out
    output wire  tsfUpdatedBySW           ,// out
    output wire [2 : 0] abgnMode                 ,// out
    output wire  keyStoRAMReset           ,// out
    output wire  mibTableReset            ,// out
    output wire  rateControllerMPIF       ,// out
    output wire  disableBAResp            ,// out
    output wire  disableCTSResp           ,// out
    output wire  disableACKResp           ,// out
    output wire  activeClkGating          ,// out
    output wire  enableLPClkSwitch        ,// out
    output wire  cfpAware                 ,// out
    output wire  pwrMgt                   ,// out
    output wire  ap                       ,// out
    output wire  bssType                  ,// out
    //$port_g MACERRRECCNTRLREG register.
    output wire  rxFlowCntrlEn            ,// out
    output wire  baPSBitmapReset          ,// out
    output wire  encrRxFIFOReset          ,// out
    output wire  macPHYIFFIFOReset        ,// out
    output wire  txFIFOReset              ,// out
    output wire  rxFIFOReset              ,// out
    output wire  hwFSMReset               ,// out
    output wire  useErrDet                ,// out
    //$port_g MACERRSETSTATUSREG register.
    output wire  errInHWLevel3            ,// out
    output wire  errInTxRxLevel2          ,// out
    output wire  errInRxLevel1            ,// out
    output wire  errInTxLevel1            ,// out
    //$port_g MACERRCLEARSTATUSREG register.
    output wire  clearErrInHWLevel3       ,// out
    output wire  clearErrInTxRxLevel2     ,// out
    output wire  clearErrInRxLevel1       ,// out
    output wire  clearErrInTxLevel1       ,// out
    //$port_g RXCNTRLREG register.
    output wire  acceptUnknown            ,// out
    output wire  acceptOtherDataFrames    ,// out
    output wire  acceptQoSNull            ,// out
    output wire  acceptQCFWOData          ,// out
    output wire  acceptQData              ,// out
    output wire  acceptCFWOData           ,// out
    output wire  acceptData               ,// out
    output wire  acceptOtherCntrlFrames   ,// out
    output wire  acceptCFEnd              ,// out
    output wire  acceptACK                ,// out
    output wire  acceptCTS                ,// out
    output wire  acceptRTS                ,// out
    output wire  acceptPSPoll             ,// out
    output wire  acceptBA                 ,// out
    output wire  acceptBAR                ,// out
    output wire  acceptOtherMgmtFrames    ,// out
    output wire  acceptAllBeacon          ,// out
    output wire  acceptNotExpectedBA      ,// out
    output wire  acceptDecryptErrorFrames ,// out
    output wire  acceptBeacon             ,// out
    output wire  acceptProbeResp          ,// out
    output wire  acceptProbeReq           ,// out
    output wire  acceptMyUnicast          ,// out
    output wire  acceptUnicast            ,// out
    output wire  acceptErrorFrames        ,// out
    output wire  acceptOtherBSSID         ,// out
    output wire  acceptBroadcast          ,// out
    output wire  acceptMulticast          ,// out
    output wire  dontDecrypt              ,// out
    output wire  excUnencrypted           ,// out
    //$port_g BCNCNTRL1REG register.
    output wire [7 : 0] noBcnTxTime              ,// out
    output wire  impTBTTIn128Us           ,// out
    output wire [6 : 0] impTBTTPeriod            ,// out
    output wire [15 : 0] beaconInt                ,// out
    //$port_g BCNCNTRL2REG register.
    output wire [11 : 0] aid                      ,// out
    output wire [7 : 0] timOffset                ,// out
    output wire [7 : 0] bcnUpdateOffset          ,// out
    //$port_g DTIMCFP1REG register.
    output wire  dtimUpdatedBySW          ,// out
    output wire [7 : 0] cfpPeriod                ,// out
    output wire [7 : 0] dtimPeriod               ,// out
    //$port_g DTIMCFP2REG register.
    output wire [15 : 0] cfpMaxDuration           ,// out
    //$port_g RETRYLIMITSREG register.
    output wire [7 : 0] dot11LongRetryLimit      ,// out
    output wire [7 : 0] dot11ShortRetryLimit     ,// out
    //$port_g BBSERVICEREG register.
    output wire [2 : 0] maxPHYNtx                ,// out
    output wire [7 : 0] bbServiceB               ,// out
    output wire [15 : 0] bbServiceA               ,// out
    //$port_g MAXPOWERLEVELREG register.
    output wire [7 : 0] dsssMaxPwrLevel          ,// out
    output wire [7 : 0] ofdmMaxPwrLevel          ,// out
    //$port_g ENCRKEY0REG register.
    output wire [31 : 0] encrKeyRAMWord0          ,// out
    //$port_g ENCRKEY1REG register.
    output wire [31 : 0] encrKeyRAMWord1          ,// out
    //$port_g ENCRKEY2REG register.
    output wire [31 : 0] encrKeyRAMWord2          ,// out
    //$port_g ENCRKEY3REG register.
    output wire [31 : 0] encrKeyRAMWord3          ,// out
    //$port_g ENCRMACADDRLOWREG register.
    output wire [31 : 0] macAddrRAMLow            ,// out
    //$port_g ENCRMACADDRHIGHREG register.
    output wire [15 : 0] macAddrRAMHigh           ,// out
    //$port_g ENCRCNTRLREG register.
    output wire  newRead                  ,// out
    output wire  newWrite                 ,// out
    output wire [9 : 0] keyIndexRAM              ,// out
    output wire [2 : 0] cTypeRAM                 ,// out
    output wire [3 : 0] vlanIDRAM                ,// out
    output wire [1 : 0] sppRAM                   ,// out
    output wire  useDefKeyRAM             ,// out
    output wire  cLenRAM                  ,// out
`ifdef RW_WAPI_EN                     
    //$port_g ENCRWPIINTKEY0REG register.
    output wire [31 : 0] encrIntKeyRAMWord0       ,// out
    //$port_g ENCRWPIINTKEY1REG register.
    output wire [31 : 0] encrIntKeyRAMWord1       ,// out
    //$port_g ENCRWPIINTKEY2REG register.
    output wire [31 : 0] encrIntKeyRAMWord2       ,// out
    //$port_g ENCRWPIINTKEY3REG register.
    output wire [31 : 0] encrIntKeyRAMWord3       ,// out
`endif // RW_WAPI_EN                     
    //$port_g RATESREG register.
    output wire [11 : 0] bssBasicRateSet          ,// out
    //$port_g OLBCREG register.
    output wire [7 : 0] dsssCount                ,// out
    output wire [7 : 0] ofdmCount                ,// out
    output wire [15 : 0] olbcTimer                ,// out
    //$port_g TIMINGS1REG register.
    output wire [9 : 0] txChainDelayInMACClk     ,// out
    output wire [9 : 0] txRFDelayInMACClk        ,// out
    output wire [7 : 0] macCoreClkFreq           ,// out
    //$port_g TIMINGS2REG register.
    output wire [15 : 0] slotTimeInMACClk         ,// out
    output wire [7 : 0] slotTime                 ,// out
    //$port_g TIMINGS3REG register.
    output wire [9 : 0] rxRFDelayInMACClk        ,// out
    output wire [9 : 0] txDelayRFOnInMACClk      ,// out
    output wire [9 : 0] macProcDelayInMACClk     ,// out
    //$port_g TIMINGS4REG register.
    output wire [9 : 0] radioWakeUpTime          ,// out
    output wire [9 : 0] radioChirpTime           ,// out
    //$port_g TIMINGS5REG register.
    output wire [15 : 0] sifsBInMACClk            ,// out
    output wire [7 : 0] sifsB                    ,// out
    //$port_g TIMINGS6REG register.
    output wire [15 : 0] sifsAInMACClk            ,// out
    output wire [7 : 0] sifsA                    ,// out
    //$port_g TIMINGS7REG register.
    output wire [3 : 0] rxCCADelay               ,// out
    output wire [7 : 0] rifs                     ,// out
    //$port_g TIMINGS8REG register.
    output wire [7 : 0] rxStartDelayMIMO         ,// out
    output wire [7 : 0] rxStartDelayShort        ,// out
    output wire [7 : 0] rxStartDelayLong         ,// out
    output wire [7 : 0] rxStartDelayOFDM         ,// out
    //$port_g TIMINGS9REG register.
    output wire [9 : 0] rifsTOInMACClk           ,// out
    output wire [9 : 0] rifsInMACClk             ,// out
    output wire [9 : 0] txDMAProcDlyInMACClk     ,// out
    //$port_g PROTTRIGTIMERREG register.
    output wire [7 : 0] edcaTriggerTimer         ,// out
    //$port_g TXTRIGGERTIMERREG register.
    output wire [7 : 0] txPacketTimeout          ,// out
    output wire [7 : 0] txAbsoluteTimeout        ,// out
    //$port_g RXTRIGGERTIMERREG register.
    output wire [7 : 0] rxPayloadUsedCount       ,// out
    output wire [7 : 0] rxPacketTimeout          ,// out
    output wire [7 : 0] rxAbsoluteTimeout        ,// out
    //$port_g MIBTABLEWRITEREG register.
    output wire [15 : 0] mibValue                 ,// out
    output wire  mibWrite                 ,// out
    output wire  mibIncrementMode         ,// out
    output wire [9 : 0] mibTableIndex            ,// out
    //$port_g ABSTIMERREG0 register.
    output wire [31 : 0] absTimerValue0           ,// out
    //$port_g ABSTIMERREG1 register.
    output wire [31 : 0] absTimerValue1           ,// out
    //$port_g ABSTIMERREG2 register.
    output wire [31 : 0] absTimerValue2           ,// out
    //$port_g ABSTIMERREG3 register.
    output wire [31 : 0] absTimerValue3           ,// out
    //$port_g ABSTIMERREG4 register.
    output wire [31 : 0] absTimerValue4           ,// out
    //$port_g ABSTIMERREG5 register.
    output wire [31 : 0] absTimerValue5           ,// out
    //$port_g ABSTIMERREG6 register.
    output wire [31 : 0] absTimerValue6           ,// out
    //$port_g ABSTIMERREG7 register.
    output wire [31 : 0] absTimerValue7           ,// out
    //$port_g ABSTIMERREG8 register.
    output wire [31 : 0] absTimerValue8           ,// out
    //$port_g ABSTIMERREG9 register.
    output wire [31 : 0] absTimerValue9           ,// out
    //$port_g MAXRXLENGTHREG register.
    output wire [19 : 0] maxAllowedLength         ,// out
    //$port_g EDCAAC0REG register.
    output wire [15 : 0] txOpLimit0               ,// out
    output wire [3 : 0] cwMax0                   ,// out
    output wire [3 : 0] cwMin0                   ,// out
    output wire [3 : 0] aifsn0                   ,// out
    //$port_g EDCAAC1REG register.
    output wire [15 : 0] txOpLimit1               ,// out
    output wire [3 : 0] cwMax1                   ,// out
    output wire [3 : 0] cwMin1                   ,// out
    output wire [3 : 0] aifsn1                   ,// out
    //$port_g EDCAAC2REG register.
    output wire [15 : 0] txOpLimit2               ,// out
    output wire [3 : 0] cwMax2                   ,// out
    output wire [3 : 0] cwMin2                   ,// out
    output wire [3 : 0] aifsn2                   ,// out
    //$port_g EDCAAC3REG register.
    output wire [15 : 0] txOpLimit3               ,// out
    output wire [3 : 0] cwMax3                   ,// out
    output wire [3 : 0] cwMin3                   ,// out
    output wire [3 : 0] aifsn3                   ,// out
    //$port_g EDCACCABUSYREG register.
    output wire [31 : 0] ccaBusyDur               ,// out
    //$port_g EDCACNTRLREG register.
    output wire  keepTXOPOpen             ,// out
    output wire  remTXOPInDurField        ,// out
    output wire  sendCFEnd                ,// out
    output wire  sendCFEndNow             ,// out
    //$port_g QUIETELEMENT1AREG register.
    output wire [15 : 0] quietDuration1           ,// out
    output wire [7 : 0] quietPeriod1             ,// out
    output wire [7 : 0] quietCount1              ,// out
    //$port_g QUIETELEMENT1BREG register.
    output wire [15 : 0] quietOffset1             ,// out
    //$port_g QUIETELEMENT2AREG register.
    output wire [15 : 0] quietDuration2           ,// out
    output wire [7 : 0] quietPeriod2             ,// out
    output wire [7 : 0] quietCount2              ,// out
    //$port_g QUIETELEMENT2BREG register.
    output wire [15 : 0] quietOffset2             ,// out
    //$port_g ADDCCABUSYSEC20REG register.
    output wire [31 : 0] ccaBusyDurSec20          ,// out
    //$port_g ADDCCABUSYSEC40REG register.
    output wire [31 : 0] ccaBusyDurSec40          ,// out
    //$port_g ADDCCABUSYSEC80REG register.
    output wire [31 : 0] ccaBusyDurSec80          ,// out
    //$port_g STBCCNTRLREG register.
    output wire [6 : 0] basicSTBCMCS             ,// out
    output wire  dualCTSProt              ,// out
    output wire [7 : 0] ctsSTBCDur               ,// out
    output wire [15 : 0] cfEndSTBCDur             ,// out
    //$port_g STARTTX1REG register.
    output wire [1 : 0] startTxBW                ,// out
    output wire  startTxPreType           ,// out
    output wire [2 : 0] startTxFormatMod         ,// out
    output wire [7 : 0] startTxMCSIndex0         ,// out
    output wire [9 : 0] startTxKSRIndex          ,// out
    output wire [1 : 0] startTxAC                ,// out
    output wire [1 : 0] startTxFrmExType         ,// out
    output wire  startTxFrameEx           ,// out
    //$port_g STARTTX2REG register.
    output wire [15 : 0] durControlFrm            ,// out
    //$port_g STARTTX3REG register.
    output wire [7 : 0] startTxSMMIndex          ,// out
    output wire [7 : 0] startTxAntennaSet        ,// out
    output wire  startTxLSTP              ,// out
    output wire  startTxSmoothing         ,// out
    output wire  startTxShortGI           ,// out
    output wire [2 : 0] startTxNTx               ,// out
    output wire  startTxFecCoding         ,// out
    output wire [1 : 0] startTxSTBC              ,// out
    output wire [1 : 0] startTxNumExtnSS         ,// out
    //$port_g TXBWCNTRLREG register.
    output wire [1 : 0] maxSupportedBW           ,// out
    output wire [7 : 0] aPPDUMaxTime             ,// out
    output wire  dynBWEn                  ,// out
    output wire [2 : 0] numTryBWAcquisition      ,// out
    output wire  dropToLowerBW            ,// out
    output wire [1 : 0] defaultBWTXOP            ,// out
    output wire  defaultBWTXOPV           ,// out
    //$port_g HTMCSREG register.
    output wire [5 : 0] bssBasicHTMCSSetUM       ,// out
    output wire [15 : 0] bssBasicHTMCSSetEM       ,// out
    //$port_g VHTMCSREG register.
    output wire [15 : 0] bssBasicVHTMCSSet        ,// out
    //$port_g LSTPREG register.
    output wire  supportLSTP              ,// out
`ifdef RW_WLAN_COEX_EN                
    //$port_g COEXCONTROLREG register.
    output wire [6 : 0] coexWlanChanFreq         ,// out
    output wire  coexWlanChanOffset       ,// out
    output wire  coexEnable               ,// out
    //$port_g COEXPTIREG register.
    output wire [3 : 0] coexPTIBcnData           ,// out
    output wire [3 : 0] coexPTIBKData            ,// out
    output wire [3 : 0] coexPTIBEData            ,// out
    output wire [3 : 0] coexPTIVIData            ,// out
    output wire [3 : 0] coexPTIVOData            ,// out
    output wire [3 : 0] coexPTIMgt               ,// out
    output wire [3 : 0] coexPTICntl              ,// out
    output wire [3 : 0] coexPTIAck               ,// out
`endif // RW_WLAN_COEX_EN                
    //$port_g DEBUGPORTSELREG register.
    output wire [7 : 0] debugPortSel2            ,// out
    output wire [7 : 0] debugPortSel1            ,// out
    //$port_g DEBUGNAVREG register.
    output wire [25 : 0] navCounter               ,// out
    //$port_g DEBUGCWREG register.
    output wire [1 : 0] backoffOffset            ,// out
    //$port_g DEBUGPHYREG register.
    output wire  rxReqForceDeassertion    ,// out
            
    
    output wire latchNextState_p  , // Next state latch
    //$port_g host slave IF
    input  wire                               regWrite,              // Write enable
    input  wire                               regRead,               // Read enable
    input  wire   [(`RW_REG_ADDR_WIDTH-1):0]  regAddr,              // Register address
    input  wire   [(`RW_REG_DATA_WIDTH-1):0]  regWriteData,          // Data to be written to the registers

    output wire                               regReadyIn,            // read data valid or write completed 
    output wire   [(`RW_REG_DATA_WIDTH-1):0]  regReadData            // Data read from registers
    
            
);



  //////////////////////////////////////////////////////////////////////////////
  //host slave IF
  //////////////////////////////////////////////////////////////////////////////

  wire                                      plRegSel;
  reg                                       plRegSelDly;
  wire                                      coreRegSel;
  wire          [(`RW_REG_DATA_WIDTH-1):0]  plReadData;
  reg           [(`RW_REG_DATA_WIDTH-1):0]  plReadDataCapt;
  wire          [(`RW_REG_DATA_WIDTH-1):0]  coreReadData;
  wire                                      coreReadyIn;

  wire                                      postWriteWrite;
  wire                                      postWriteRead;
  wire          [(`RW_REG_DATA_WIDTH-1):0]  postWritewriteData;
  wire          [(`RW_REG_DATA_WIDTH-1):0]  postWritereadData;
  wire          [(`RW_REG_ADDR_WIDTH-2):0]  postWriteregAddr;

  wire                                      postWriteSel;
  
  //////////////////////////////////////////////////////////////////////////////
  //Registers
  //////////////////////////////////////////////////////////////////////////////
 
  //////////////////////////////////////////////////////////////////////////////
  // Ouput linkage
  //////////////////////////////////////////////////////////////////////////////
  assign plRegSel    = (regAddr[(`RW_REG_ADDR_WIDTH-1)]);
  assign coreRegSel  = ( !regAddr[(`RW_REG_ADDR_WIDTH-1)]);
  assign regReadData = plRegSelDly ? plReadDataCapt : coreReadData;
  assign regReadyIn  = coreReadyIn & !regRead;

  // sample data read from registers on macPIClk
  always @(posedge macPIClk or negedge macPIClkHardRst_n)
  begin
    if (macPIClkHardRst_n == 1'b0)
    begin
      plReadDataCapt <= `RW_REG_DATA_WIDTH'b0;
      plRegSelDly    <= 1'b0;       
    end
    else 
    begin
      plRegSelDly    <= plRegSel;       
      if (plRegSel && regRead)
        plReadDataCapt <= plReadData;
    end
  end




`ifdef ASSERT_ON

//$rw_sva Checks no write is fired while read is active
property no_write_while_read_prop; 
@(posedge macPIClk)
  disable iff(macPIClkHardRst_n==0)
  regRead |-> !regWrite;
endproperty
no_write_while_read: assert property (no_write_while_read_prop); 

//$rw_sva Checks no read is fired while write is active
property no_read_while_write_prop; 
@(posedge macPIClk)
  disable iff(macPIClkHardRst_n==0)
  regWrite |-> !regRead;
endproperty
no_read_while_write: assert property (no_write_while_read_prop); 

`endif // ASSERT_ON

// Instanciation of macPlReg
// Name of the instance : u_macPlReg
// Name of the file containing this module : macPlReg.v
macPlReg u_macPlReg (
		.hardRstClk_n                     (macPIClkHardRst_n),
		.softRstClk_n                     (macPIClkSoftRst_n),
		.Clk                              (macPIClk),
		.nextTBTT                         (nextTBTT),
		.statussetrxPayloadDMADead        (statussetrxPayloadDMADead),
		.statussetrxHeaderDMADead         (statussetrxHeaderDMADead),
		.statussetphyRxStart              (statussetphyRxStart),
		.statussetphyErr                  (statussetphyErr),
		.statussetmacPHYIFUnderRun        (statussetmacPHYIFUnderRun),
		.statussethwErr                   (statussethwErr),
		.statussetimpSecDTIM              (statussetimpSecDTIM),
		.statussetimpPriDTIM              (statussetimpPriDTIM),
		.statussetbcnTxDMADead            (statussetbcnTxDMADead),
		.statussetac3TxDMADead            (statussetac3TxDMADead),
		.statussetac2TxDMADead            (statussetac2TxDMADead),
		.statussetac1TxDMADead            (statussetac1TxDMADead),
		.statussetac0TxDMADead            (statussetac0TxDMADead),
		.statussetptError                 (statussetptError),
		.statussettimSet                  (statussettimSet),
		.statussetolbcDSSS                (statussetolbcDSSS),
		.statussetolbcOFDM                (statussetolbcOFDM),
		.statussetrxFIFOOverFlow          (statussetrxFIFOOverFlow),
		.statussetrxDMAEmpty              (statussetrxDMAEmpty),
		.statussetmacPHYIFOverflow        (statussetmacPHYIFOverflow),
		.statusabsGenTimers               (statusabsGenTimers),
		.statussetidleInterrupt           (statussetidleInterrupt),
		.statussetimpSecTBTT              (statussetimpSecTBTT),
.statussetimpPriTBTT              (statussetimpPriTBTT),
                .statussetbcnTxBufTrigger         (statussetbcnTxBufTrigger),
                .statussetac3TxBufTrigger         (statussetac3TxBufTrigger),
                .statussetac2TxBufTrigger         (statussetac2TxBufTrigger),
                .statussetac1TxBufTrigger         (statussetac1TxBufTrigger),
                .statussetac0TxBufTrigger         (statussetac0TxBufTrigger),
                .statussetac3BWDropTrigger        (statussetac3BWDropTrigger),
                .statussetac2BWDropTrigger        (statussetac2BWDropTrigger),
                .statussetac1BWDropTrigger        (statussetac1BWDropTrigger),
                .statussetac0BWDropTrigger        (statussetac0BWDropTrigger),
                .statussetcounterRxTrigger        (statussetcounterRxTrigger),
                .statussetbaRxTrigger             (statussetbaRxTrigger),
                .statussettimerRxTrigger          (statussettimerRxTrigger),
                .statussetrxTrigger               (statussetrxTrigger),
                .statussettimerTxTrigger          (statussettimerTxTrigger),
                .statussettxopComplete            (statussettxopComplete),
                .statussetrdTxTrigger             (statussetrdTxTrigger),
                .statussethccaTxTrigger           (statussethccaTxTrigger),
                .statussetbcnTxTrigger            (statussetbcnTxTrigger),
                .statussetac3TxTrigger            (statussetac3TxTrigger),
                .statussetac2TxTrigger            (statussetac2TxTrigger),
                .statussetac1TxTrigger            (statussetac1TxTrigger),
                .statussetac0TxTrigger            (statussetac0TxTrigger),
                .statussetrdProtTrigger           (statussetrdProtTrigger),
                .statussethccaProtTrigger         (statussethccaProtTrigger),
                .statussetac3ProtTrigger          (statussetac3ProtTrigger),
                .statussetac2ProtTrigger          (statussetac2ProtTrigger),
                .statussetac1ProtTrigger          (statussetac1ProtTrigger),
                .statussetac0ProtTrigger          (statussetac0ProtTrigger),
                .statussetabsTimers9              (statussetabsTimers9),
                .statussetabsTimers8              (statussetabsTimers8),
                .statussetabsTimers7              (statussetabsTimers7),
                .statussetabsTimers6              (statussetabsTimers6),
                .statussetabsTimers5              (statussetabsTimers5),
                .statussetabsTimers4              (statussetabsTimers4),
                .statussetabsTimers3              (statussetabsTimers3),
                .statussetabsTimers2              (statussetabsTimers2),
                .statussetabsTimers1              (statussetabsTimers1),
                .statussetabsTimers0              (statussetabsTimers0),
                .tsfTimerLowIn                    (tsfTimerLowIn),
                .tsfTimerLowInValid               (tsfTimerLowInValid),
                .tsfTimerHighIn                   (tsfTimerHighIn),
                .tsfTimerHighInValid              (tsfTimerHighInValid),
                .computeDurationIn                (computeDurationIn),
                .computeDurationInValid           (computeDurationInValid),
                .timeOnAirValid                   (timeOnAirValid),
                .timeOnAir                        (timeOnAir),
                .statussetrxPayloadNewHead        (statussetrxPayloadNewHead),
                .statussetrxHeaderNewHead         (statussetrxHeaderNewHead),
                .statussetrxPayloadNewTail        (statussetrxPayloadNewTail),
                .statussetrxHeaderNewTail         (statussetrxHeaderNewTail),
                .statussethaltAC3AfterTXOP        (statussethaltAC3AfterTXOP),
                .statussethaltAC2AfterTXOP        (statussethaltAC2AfterTXOP),
                .statussethaltAC1AfterTXOP        (statussethaltAC1AfterTXOP),
                .statussethaltAC0AfterTXOP        (statussethaltAC0AfterTXOP),
                .statussethaltBcnAfterTXOP        (statussethaltBcnAfterTXOP),
                .statussettxAC3NewHead            (statussettxAC3NewHead),
                .statussettxAC2NewHead            (statussettxAC2NewHead),
                .statussettxAC1NewHead            (statussettxAC1NewHead),
                .statussettxAC0NewHead            (statussettxAC0NewHead),
                .statussettxBcnNewHead            (statussettxBcnNewHead),
                .statussettxAC3NewTail            (statussettxAC3NewTail),
                .statussettxAC2NewTail            (statussettxAC2NewTail),
                .statussettxAC1NewTail            (statussettxAC1NewTail),
                .statussettxAC0NewTail            (statussettxAC0NewTail),
                .statussettxBcnNewTail            (statussettxBcnNewTail),
                .rxPayloadState                   (rxPayloadState),
                .rxHeaderState                    (rxHeaderState),
                .txAC3State                       (txAC3State),
                .txAC2State                       (txAC2State),
                .txAC1State                       (txAC1State),
                .txAC0State                       (txAC0State),
                .txBcnState                       (txBcnState),
                .txAC3NewHeadErr                  (txAC3NewHeadErr),
                .txAC2NewHeadErr                  (txAC2NewHeadErr),
                .txAC1NewHeadErr                  (txAC1NewHeadErr),
                .txAC0NewHeadErr                  (txAC0NewHeadErr),
                .txBcnNewHeadErr                  (txBcnNewHeadErr),
                .txAC3BusErr                      (txAC3BusErr),
                .txAC2BusErr                      (txAC2BusErr),
                .txAC1BusErr                      (txAC1BusErr),
                .txAC0BusErr                      (txAC0BusErr),
                .txBcnBusErr                      (txBcnBusErr),
                .txAC3PTAddressErr                (txAC3PTAddressErr),
                .txAC2PTAddressErr                (txAC2PTAddressErr),
                .txAC1PTAddressErr                (txAC1PTAddressErr),
                .txAC0PTAddressErr                (txAC0PTAddressErr),
                .txBcnPTAddressErr                (txBcnPTAddressErr),
                .txAC3NextPointerErr              (txAC3NextPointerErr),
                .txAC2NextPointerErr              (txAC2NextPointerErr),
                .txAC1NextPointerErr              (txAC1NextPointerErr),
                .txAC0NextPointerErr              (txAC0NextPointerErr),
                .txBcnNextPointerErr              (txBcnNextPointerErr),
                .txAC3UPatternErr                 (txAC3UPatternErr),
                .txAC2UPatternErr                 (txAC2UPatternErr),
                .txAC1UPatternErr                 (txAC1UPatternErr),
                .txAC0UPatternErr                 (txAC0UPatternErr),
                .txBcnUPatternErr                 (txBcnUPatternErr),
                .txAC3LenMismatch                 (txAC3LenMismatch),
                .txAC2LenMismatch                 (txAC2LenMismatch),
                .txAC1LenMismatch                 (txAC1LenMismatch),
                .txAC0LenMismatch                 (txAC0LenMismatch),
                .txBcnLenMismatch                 (txBcnLenMismatch),
                .rxPayNewHeadErr                  (rxPayNewHeadErr),
                .rxHdrNewHeadErr                  (rxHdrNewHeadErr),
                .rxPayBusErr                      (rxPayBusErr),
                .rxHdrBusErr                      (rxHdrBusErr),
                .rxPayNextPointerErr              (rxPayNextPointerErr),
                .rxHdrNextPointerErr              (rxHdrNextPointerErr),
                .rxPayUPatternErr                 (rxPayUPatternErr),
                .rxHdrUPatternErr                 (rxHdrUPatternErr),
                .txAC3HaltAfterTXOP               (txAC3HaltAfterTXOP),
                .txAC2HaltAfterTXOP               (txAC2HaltAfterTXOP),
                .txAC1HaltAfterTXOP               (txAC1HaltAfterTXOP),
                .txAC0HaltAfterTXOP               (txAC0HaltAfterTXOP),
                .txBcnHaltAfterTXOP               (txBcnHaltAfterTXOP),
                .txAC3EndQ                        (txAC3EndQ),
                .txAC2EndQ                        (txAC2EndQ),
                .txAC1EndQ                        (txAC1EndQ),
                .txAC0EndQ                        (txAC0EndQ),
                .txBcnEndQ                        (txBcnEndQ),
                .txAC3Startup                     (txAC3Startup),
                .txAC2Startup                     (txAC2Startup),
                .txAC1Startup                     (txAC1Startup),
                .txAC0Startup                     (txAC0Startup),
                .txBcnStartup                     (txBcnStartup),
                .statussetac3HasData              (statussetac3HasData),
                .statussetac2HasData              (statussetac2HasData),
                .statussetac1HasData              (statussetac1HasData),
                .statussetac0HasData              (statussetac0HasData),
                .ac1MOT                           (ac1MOT),
                .ac0MOT                           (ac0MOT),
                .ac3MOT                           (ac3MOT),
                .ac2MOT                           (ac2MOT),
                .miscMOT                          (miscMOT),
                .hccaQAPMOT                       (hccaQAPMOT),
                .txBWAfterDrop                    (txBWAfterDrop),
                .bcnStatusPointer                 (bcnStatusPointer),
                .ac0StatusPointer                 (ac0StatusPointer),
                .ac1StatusPointer                 (ac1StatusPointer),
                .ac2StatusPointer                 (ac2StatusPointer),
                .ac3StatusPointer                 (ac3StatusPointer),
                .txCurrentPointer                 (txCurrentPointer),
                .rxPayStatPointer                 (rxPayStatPointer),
                .rxHdrStatPointer                 (rxHdrStatPointer),
                .rxPayCurrentPointer              (rxPayCurrentPointer),
                .swProf31In                       (swProf31In),
                .swProf31InValid                  (swProf31InValid),
                .swProf30In                       (swProf30In),
                .swProf30InValid                  (swProf30InValid),
                .swProf29In                       (swProf29In),
                .swProf29InValid                  (swProf29InValid),
                .swProf28In                       (swProf28In),
                .swProf28InValid                  (swProf28InValid),
                .swProf27In                       (swProf27In),
                .swProf27InValid                  (swProf27InValid),
                .swProf26In                       (swProf26In),
                .swProf26InValid                  (swProf26InValid),
                .swProf25In                       (swProf25In),
                .swProf25InValid                  (swProf25InValid),
                .swProf24In                       (swProf24In),
                .swProf24InValid                  (swProf24InValid),
                .swProf23In                       (swProf23In),
                .swProf23InValid                  (swProf23InValid),
                .swProf22In                       (swProf22In),
                .swProf22InValid                  (swProf22InValid),
                .swProf21In                       (swProf21In),
                .swProf21InValid                  (swProf21InValid),
                .swProf20In                       (swProf20In),
                .swProf20InValid                  (swProf20InValid),
                .swProf19In                       (swProf19In),
                .swProf19InValid                  (swProf19InValid),
                .swProf18In                       (swProf18In),
                .swProf18InValid                  (swProf18InValid),
                .swProf17In                       (swProf17In),
                .swProf17InValid                  (swProf17InValid),
                .swProf16In                       (swProf16In),
                .swProf16InValid                  (swProf16InValid),
                .swProf15In                       (swProf15In),
                .swProf15InValid                  (swProf15InValid),
                .swProf14In                       (swProf14In),
                .swProf14InValid                  (swProf14InValid),
                .swProf13In                       (swProf13In),
                .swProf13InValid                  (swProf13InValid),
                .swProf12In                       (swProf12In),
                .swProf12InValid                  (swProf12InValid),
                .swProf11In                       (swProf11In),
                .swProf11InValid                  (swProf11InValid),
                .swProf10In                       (swProf10In),
                .swProf10InValid                  (swProf10InValid),
                .swProf9In                        (swProf9In),
                .swProf9InValid                   (swProf9InValid),
                .swProf8In                        (swProf8In),
                .swProf8InValid                   (swProf8InValid),
                .swProf7In                        (swProf7In),
                .swProf7InValid                   (swProf7InValid),
                .swProf6In                        (swProf6In),
                .swProf6InValid                   (swProf6InValid),
                .swProf5In                        (swProf5In),
                .swProf5InValid                   (swProf5InValid),
                .swProf4In                        (swProf4In),
                .swProf4InValid                   (swProf4InValid),
                .swProf3In                        (swProf3In),
                .swProf3InValid                   (swProf3InValid),
                .swProf2In                        (swProf2In),
                .swProf2InValid                   (swProf2InValid),
                .swProf1In                        (swProf1In),
                .swProf1InValid                   (swProf1InValid),
                .swProf0In                        (swProf0In),
                .swProf0InValid                   (swProf0InValid),
                .statusswSetProf31                (statusswSetProf31),
                .statusswSetProf30                (statusswSetProf30),
                .statusswSetProf29                (statusswSetProf29),
                .statusswSetProf28                (statusswSetProf28),
                .statusswSetProf27                (statusswSetProf27),
                .statusswSetProf26                (statusswSetProf26),
                .statusswSetProf25                (statusswSetProf25),
                .statusswSetProf24                (statusswSetProf24),
                .statusswSetProf23                (statusswSetProf23),
                .statusswSetProf22                (statusswSetProf22),
                .statusswSetProf21                (statusswSetProf21),
                .statusswSetProf20                (statusswSetProf20),
                .statusswSetProf19                (statusswSetProf19),
                .statusswSetProf18                (statusswSetProf18),
                .statusswSetProf17                (statusswSetProf17),
                .statusswSetProf16                (statusswSetProf16),
                .statusswSetProf15                (statusswSetProf15),
                .statusswSetProf14                (statusswSetProf14),
                .statusswSetProf13                (statusswSetProf13),
                .statusswSetProf12                (statusswSetProf12),
                .statusswSetProf11                (statusswSetProf11),
                .statusswSetProf10                (statusswSetProf10),
                .statusswSetProf9                 (statusswSetProf9),
                .statusswSetProf8                 (statusswSetProf8),
                .statusswSetProf7                 (statusswSetProf7),
                .statusswSetProf6                 (statusswSetProf6),
                .statusswSetProf5                 (statusswSetProf5),
                .statusswSetProf4                 (statusswSetProf4),
                .statusswSetProf3                 (statusswSetProf3),
                .statusswSetProf2                 (statusswSetProf2),
                .statusswSetProf1                 (statusswSetProf1),
                .statusswSetProf0                 (statusswSetProf0),
                .wakeUpFromDoze                   (wakeUpFromDoze),
                .wakeUpSW                         (wakeUpSW),
                .softReset                        (softReset),
                .setrxPayloadDMADead              (setrxPayloadDMADead),
                .setrxHeaderDMADead               (setrxHeaderDMADead),
                .setphyRxStart                    (setphyRxStart),
                .setphyErr                        (setphyErr),
                .setmacPHYIFUnderRun              (setmacPHYIFUnderRun),
                .sethwErr                         (sethwErr),
                .setimpSecDTIM                    (setimpSecDTIM),
                .setimpPriDTIM                    (setimpPriDTIM),
                .setbcnTxDMADead                  (setbcnTxDMADead),
                .setac3TxDMADead                  (setac3TxDMADead),
                .setac2TxDMADead                  (setac2TxDMADead),
                .setac1TxDMADead                  (setac1TxDMADead),
                .setac0TxDMADead                  (setac0TxDMADead),
                .setptError                       (setptError),
                .settimSet                        (settimSet),
                .setolbcDSSS                      (setolbcDSSS),
                .setolbcOFDM                      (setolbcOFDM),
                .setrxFIFOOverFlow                (setrxFIFOOverFlow),
                .setrxDMAEmpty                    (setrxDMAEmpty),
                .setmacPHYIFOverflow              (setmacPHYIFOverflow),
                .absGenTimers                     (absGenTimers),
                .setidleInterrupt                 (setidleInterrupt),
                .setimpSecTBTT                    (setimpSecTBTT),
                .setimpPriTBTT                    (setimpPriTBTT),
                .clearrxPayloadDMADead            (clearrxPayloadDMADead),
                .clearrxHeaderDMADead             (clearrxHeaderDMADead),
                .clearphyRxStart                  (clearphyRxStart),
                .clearphyErr                      (clearphyErr),
                .clearmacPHYIFUnderRun            (clearmacPHYIFUnderRun),
                .clearhwErr                       (clearhwErr),
                .clearimpSecDTIM                  (clearimpSecDTIM),
                .clearimpPriDTIM                  (clearimpPriDTIM),
                .clearbcnTxDMADead                (clearbcnTxDMADead),
                .clearac3TxDMADead                (clearac3TxDMADead),
                .clearac2TxDMADead                (clearac2TxDMADead),
                .clearac1TxDMADead                (clearac1TxDMADead),
                .clearac0TxDMADead                (clearac0TxDMADead),
                .clearptError                     (clearptError),
                .cleartimSet                      (cleartimSet),
                .clearolbcDSSS                    (clearolbcDSSS),
                .clearolbcOFDM                    (clearolbcOFDM),
                .clearrxFIFOOverFlow              (clearrxFIFOOverFlow),
                .clearrxDMAEmpty                  (clearrxDMAEmpty),
                .clearmacPHYIFOverflow            (clearmacPHYIFOverflow),
                .clearidleInterrupt               (clearidleInterrupt),
                .clearimpSecTBTT                  (clearimpSecTBTT),
                .clearimpPriTBTT                  (clearimpPriTBTT),
                .masterGenIntEn                   (masterGenIntEn),
                .maskrxPayloadDMADead             (maskrxPayloadDMADead),
                .maskrxHeaderDMADead              (maskrxHeaderDMADead),
                .maskphyRxStart                   (maskphyRxStart),
                .maskphyErr                       (maskphyErr),
                .maskmacPHYIFUnderRun             (maskmacPHYIFUnderRun),
                .maskhwErr                        (maskhwErr),
                .maskimpSecDTIM                   (maskimpSecDTIM),
                .maskimpPriDTIM                   (maskimpPriDTIM),
                .maskbcnTxDMADead                 (maskbcnTxDMADead),
                .maskac3TxDMADead                 (maskac3TxDMADead),
                .maskac2TxDMADead                 (maskac2TxDMADead),
                .maskac1TxDMADead                 (maskac1TxDMADead),
                .maskac0TxDMADead                 (maskac0TxDMADead),
                .maskptError                      (maskptError),
                .masktimSet                       (masktimSet),
                .maskolbcDSSS                     (maskolbcDSSS),
                .maskolbcOFDM                     (maskolbcOFDM),
                .maskrxFIFOOverFlow               (maskrxFIFOOverFlow),
                .maskrxDMAEmpty                   (maskrxDMAEmpty),
                .maskmacPHYIFOverflow             (maskmacPHYIFOverflow),
                .maskabsGenTimers                 (maskabsGenTimers),
                .maskidleInterrupt                (maskidleInterrupt),
                .maskimpSecTBTT                   (maskimpSecTBTT),
                .maskimpPriTBTT                   (maskimpPriTBTT),
                .setbcnTxBufTrigger               (setbcnTxBufTrigger),
                .setac3TxBufTrigger               (setac3TxBufTrigger),
                .setac2TxBufTrigger               (setac2TxBufTrigger),
                .setac1TxBufTrigger               (setac1TxBufTrigger),
                .setac0TxBufTrigger               (setac0TxBufTrigger),
                .setac3BWDropTrigger              (setac3BWDropTrigger),
                .setac2BWDropTrigger              (setac2BWDropTrigger),
                .setac1BWDropTrigger              (setac1BWDropTrigger),
                .setac0BWDropTrigger              (setac0BWDropTrigger),
                .setcounterRxTrigger              (setcounterRxTrigger),
                .setbaRxTrigger                   (setbaRxTrigger),
                .settimerRxTrigger                (settimerRxTrigger),
                .setrxTrigger                     (setrxTrigger),
                .settimerTxTrigger                (settimerTxTrigger),
                .settxopComplete                  (settxopComplete),
                .setrdTxTrigger                   (setrdTxTrigger),
                .sethccaTxTrigger                 (sethccaTxTrigger),
                .setbcnTxTrigger                  (setbcnTxTrigger),
                .setac3TxTrigger                  (setac3TxTrigger),
                .setac2TxTrigger                  (setac2TxTrigger),
                .setac1TxTrigger                  (setac1TxTrigger),
                .setac0TxTrigger                  (setac0TxTrigger),
                .setrdProtTrigger                 (setrdProtTrigger),
                .sethccaProtTrigger               (sethccaProtTrigger),
                .setac3ProtTrigger                (setac3ProtTrigger),
                .setac2ProtTrigger                (setac2ProtTrigger),
                .setac1ProtTrigger                (setac1ProtTrigger),
                .setac0ProtTrigger                (setac0ProtTrigger),
                .clearbcnTxBufTrigger             (clearbcnTxBufTrigger),
                .clearac3TxBufTrigger             (clearac3TxBufTrigger),
                .clearac2TxBufTrigger             (clearac2TxBufTrigger),
                .clearac1TxBufTrigger             (clearac1TxBufTrigger),
                .clearac0TxBufTrigger             (clearac0TxBufTrigger),
                .clearac3BWDropTrigger            (clearac3BWDropTrigger),
                .clearac2BWDropTrigger            (clearac2BWDropTrigger),
                .clearac1BWDropTrigger            (clearac1BWDropTrigger),
                .clearac0BWDropTrigger            (clearac0BWDropTrigger),
                .clearcounterRxTrigger            (clearcounterRxTrigger),
                .clearbaRxTrigger                 (clearbaRxTrigger),
                .cleartimerRxTrigger              (cleartimerRxTrigger),
                .clearrxTrigger                   (clearrxTrigger),
                .cleartimerTxTrigger              (cleartimerTxTrigger),
                .cleartxopComplete                (cleartxopComplete),
                .clearrdTxTrigger                 (clearrdTxTrigger),
                .clearhccaTxTrigger               (clearhccaTxTrigger),
                .clearbcnTxTrigger                (clearbcnTxTrigger),
                .clearac3TxTrigger                (clearac3TxTrigger),
                .clearac2TxTrigger                (clearac2TxTrigger),
                .clearac1TxTrigger                (clearac1TxTrigger),
                .clearac0TxTrigger                (clearac0TxTrigger),
                .clearrdProtTrigger               (clearrdProtTrigger),
                .clearhccaProtTrigger             (clearhccaProtTrigger),
                .clearac3ProtTrigger              (clearac3ProtTrigger),
                .clearac2ProtTrigger              (clearac2ProtTrigger),
                .clearac1ProtTrigger              (clearac1ProtTrigger),
                .clearac0ProtTrigger              (clearac0ProtTrigger),
                .masterTxRxIntEn                  (masterTxRxIntEn),
                .maskbcnTxBufTrigger              (maskbcnTxBufTrigger),
                .maskac3TxBufTrigger              (maskac3TxBufTrigger),
                .maskac2TxBufTrigger              (maskac2TxBufTrigger),
                .maskac1TxBufTrigger              (maskac1TxBufTrigger),
                .maskac0TxBufTrigger              (maskac0TxBufTrigger),
                .maskac3BWDropTrigger             (maskac3BWDropTrigger),
                .maskac2BWDropTrigger             (maskac2BWDropTrigger),
                .maskac1BWDropTrigger             (maskac1BWDropTrigger),
                .maskac0BWDropTrigger             (maskac0BWDropTrigger),
                .maskcounterRxTrigger             (maskcounterRxTrigger),
                .maskbaRxTrigger                  (maskbaRxTrigger),
                .masktimerRxTrigger               (masktimerRxTrigger),
                .maskrxTrigger                    (maskrxTrigger),
                .masktimerTxTrigger               (masktimerTxTrigger),
                .masktxopComplete                 (masktxopComplete),
                .maskrdTxTrigger                  (maskrdTxTrigger),
                .maskhccaTxTrigger                (maskhccaTxTrigger),
                .maskbcnTxTrigger                 (maskbcnTxTrigger),
                .maskac3TxTrigger                 (maskac3TxTrigger),
                .maskac2TxTrigger                 (maskac2TxTrigger),
                .maskac1TxTrigger                 (maskac1TxTrigger),
                .maskac0TxTrigger                 (maskac0TxTrigger),
                .maskrdProtTrigger                (maskrdProtTrigger),
                .maskhccaProtTrigger              (maskhccaProtTrigger),
                .maskac3ProtTrigger               (maskac3ProtTrigger),
                .maskac2ProtTrigger               (maskac2ProtTrigger),
                .maskac1ProtTrigger               (maskac1ProtTrigger),
                .maskac0ProtTrigger               (maskac0ProtTrigger),
                .setabsTimers9                    (setabsTimers9),
                .setabsTimers8                    (setabsTimers8),
                .setabsTimers7                    (setabsTimers7),
                .setabsTimers6                    (setabsTimers6),
                .setabsTimers5                    (setabsTimers5),
                .setabsTimers4                    (setabsTimers4),
                .setabsTimers3                    (setabsTimers3),
                .setabsTimers2                    (setabsTimers2),
                .setabsTimers1                    (setabsTimers1),
                .setabsTimers0                    (setabsTimers0),
                .clearabsTimers9                  (clearabsTimers9),
                .clearabsTimers8                  (clearabsTimers8),
                .clearabsTimers7                  (clearabsTimers7),
                .clearabsTimers6                  (clearabsTimers6),
                .clearabsTimers5                  (clearabsTimers5),
                .clearabsTimers4                  (clearabsTimers4),
                .clearabsTimers3                  (clearabsTimers3),
                .clearabsTimers2                  (clearabsTimers2),
                .clearabsTimers1                  (clearabsTimers1),
                .clearabsTimers0                  (clearabsTimers0),
                .maskabsTimers9                   (maskabsTimers9),
                .maskabsTimers8                   (maskabsTimers8),
                .maskabsTimers7                   (maskabsTimers7),
                .maskabsTimers6                   (maskabsTimers6),
                .maskabsTimers5                   (maskabsTimers5),
                .maskabsTimers4                   (maskabsTimers4),
                .maskabsTimers3                   (maskabsTimers3),
                .maskabsTimers2                   (maskabsTimers2),
                .maskabsTimers1                   (maskabsTimers1),
                .maskabsTimers0                   (maskabsTimers0),
                .tsfTimerLow                      (tsfTimerLow),
                .tsfTimerHigh                     (tsfTimerHigh),
                .ppduSTBC                         (ppduSTBC),
                .ppduNumExtnSS                    (ppduNumExtnSS),
                .ppduShortGI                      (ppduShortGI),
                .ppduPreType                      (ppduPreType),
                .ppduBW                           (ppduBW),
                .ppduLength                       (ppduLength),
                .ppduMCSIndex                     (ppduMCSIndex),
                .computeDuration                  (computeDuration),
                .setrxPayloadNewHead              (setrxPayloadNewHead),
                .setrxHeaderNewHead               (setrxHeaderNewHead),
                .setrxPayloadNewTail              (setrxPayloadNewTail),
                .setrxHeaderNewTail               (setrxHeaderNewTail),
                .sethaltAC3AfterTXOP              (sethaltAC3AfterTXOP),
                .sethaltAC2AfterTXOP              (sethaltAC2AfterTXOP),
                .sethaltAC1AfterTXOP              (sethaltAC1AfterTXOP),
                .sethaltAC0AfterTXOP              (sethaltAC0AfterTXOP),
                .sethaltBcnAfterTXOP              (sethaltBcnAfterTXOP),
                .settxAC3NewHead                  (settxAC3NewHead),
                .settxAC2NewHead                  (settxAC2NewHead),
                .settxAC1NewHead                  (settxAC1NewHead),
                .settxAC0NewHead                  (settxAC0NewHead),
                .settxBcnNewHead                  (settxBcnNewHead),
                .settxAC3NewTail                  (settxAC3NewTail),
                .settxAC2NewTail                  (settxAC2NewTail),
                .settxAC1NewTail                  (settxAC1NewTail),
                .settxAC0NewTail                  (settxAC0NewTail),
                .settxBcnNewTail                  (settxBcnNewTail),
                .clearrxPayloadNewHead            (clearrxPayloadNewHead),
                .clearrxHeaderNewHead             (clearrxHeaderNewHead),
                .clearrxPayloadNewTail            (clearrxPayloadNewTail),
                .clearrxHeaderNewTail             (clearrxHeaderNewTail),
                .clearhaltAC3AfterTXOP            (clearhaltAC3AfterTXOP),
                .clearhaltAC2AfterTXOP            (clearhaltAC2AfterTXOP),
                .clearhaltAC1AfterTXOP            (clearhaltAC1AfterTXOP),
                .clearhaltAC0AfterTXOP            (clearhaltAC0AfterTXOP),
                .clearhaltBcnAfterTXOP            (clearhaltBcnAfterTXOP),
                .cleartxAC3NewHead                (cleartxAC3NewHead),
                .cleartxAC2NewHead                (cleartxAC2NewHead),
                .cleartxAC1NewHead                (cleartxAC1NewHead),
                .cleartxAC0NewHead                (cleartxAC0NewHead),
                .cleartxBcnNewHead                (cleartxBcnNewHead),
                .cleartxAC3NewTail                (cleartxAC3NewTail),
                .cleartxAC2NewTail                (cleartxAC2NewTail),
                .cleartxAC1NewTail                (cleartxAC1NewTail),
                .cleartxAC0NewTail                (cleartxAC0NewTail),
                .cleartxBcnNewTail                (cleartxBcnNewTail),
                .txBcnHeadPtr                     (txBcnHeadPtr),
                .txAC0HeadPtr                     (txAC0HeadPtr),
                .txAC1HeadPtr                     (txAC1HeadPtr),
                .txAC2HeadPtr                     (txAC2HeadPtr),
                .txAC3HeadPtr                     (txAC3HeadPtr),
                .dmaRBDSize                       (dmaRBDSize),
                .dmaRHDSize                       (dmaRHDSize),
                .dmaTBDSize                       (dmaTBDSize),
                .dmaTHDSize                       (dmaTHDSize),
                .ptEntrySize                      (ptEntrySize),
                .rxHeaderHeadPtr                  (rxHeaderHeadPtr),
                .rxHeaderHeadPtrValid             (rxHeaderHeadPtrValid),
                .rxPayloadHeadPtr                 (rxPayloadHeadPtr),
                .rxPayloadHeadPtrValid            (rxPayloadHeadPtrValid),
                .rxFIFOThreshold                  (rxFIFOThreshold),
                .txFIFOThreshold                  (txFIFOThreshold),
                .setac3HasData                    (setac3HasData),
                .setac2HasData                    (setac2HasData),
                .setac1HasData                    (setac1HasData),
                .setac0HasData                    (setac0HasData),
                .clearac3HasData                  (clearac3HasData),
                .clearac2HasData                  (clearac2HasData),
                .clearac1HasData                  (clearac1HasData),
                .clearac0HasData                  (clearac0HasData),
                .swProf31                         (swProf31),
                .swProf30                         (swProf30),
                .swProf29                         (swProf29),
                .swProf28                         (swProf28),
                .swProf27                         (swProf27),
                .swProf26                         (swProf26),
                .swProf25                         (swProf25),
                .swProf24                         (swProf24),
                .swProf23                         (swProf23),
                .swProf22                         (swProf22),
                .swProf21                         (swProf21),
                .swProf20                         (swProf20),
                .swProf19                         (swProf19),
                .swProf18                         (swProf18),
                .swProf17                         (swProf17),
                .swProf16                         (swProf16),
                .swProf15                         (swProf15),
                .swProf14                         (swProf14),
                .swProf13                         (swProf13),
                .swProf12                         (swProf12),
                .swProf11                         (swProf11),
                .swProf10                         (swProf10),
                .swProf9                          (swProf9),
                .swProf8                          (swProf8),
                .swProf7                          (swProf7),
                .swProf6                          (swProf6),
                .swProf5                          (swProf5),
                .swProf4                          (swProf4),
                .swProf3                          (swProf3),
                .swProf2                          (swProf2),
                .swProf1                          (swProf1),
                .swProf0                          (swProf0),
                .swSetProf31                      (swSetProf31),
                .swSetProf30                      (swSetProf30),
                .swSetProf29                      (swSetProf29),
                .swSetProf28                      (swSetProf28),
                .swSetProf27                      (swSetProf27),
                .swSetProf26                      (swSetProf26),
                .swSetProf25                      (swSetProf25),
                .swSetProf24                      (swSetProf24),
                .swSetProf23                      (swSetProf23),
                .swSetProf22                      (swSetProf22),
                .swSetProf21                      (swSetProf21),
                .swSetProf20                      (swSetProf20),
                .swSetProf19                      (swSetProf19),
                .swSetProf18                      (swSetProf18),
                .swSetProf17                      (swSetProf17),
                .swSetProf16                      (swSetProf16),
                .swSetProf15                      (swSetProf15),
                .swSetProf14                      (swSetProf14),
                .swSetProf13                      (swSetProf13),
                .swSetProf12                      (swSetProf12),
                .swSetProf11                      (swSetProf11),
                .swSetProf10                      (swSetProf10),
                .swSetProf9                       (swSetProf9),
                .swSetProf8                       (swSetProf8),
                .swSetProf7                       (swSetProf7),
                .swSetProf6                       (swSetProf6),
                .swSetProf5                       (swSetProf5),
                .swSetProf4                       (swSetProf4),
                .swSetProf3                       (swSetProf3),
                .swSetProf2                       (swSetProf2),
                .swSetProf1                       (swSetProf1),
                .swSetProf0                       (swSetProf0),
                .swClearProf31                    (swClearProf31),
                .swClearProf30                    (swClearProf30),
                .swClearProf29                    (swClearProf29),
                .swClearProf28                    (swClearProf28),
                .swClearProf27                    (swClearProf27),
                .swClearProf26                    (swClearProf26),
                .swClearProf25                    (swClearProf25),
                .swClearProf24                    (swClearProf24),
                .swClearProf23                    (swClearProf23),
                .swClearProf22                    (swClearProf22),
                .swClearProf21                    (swClearProf21),
                .swClearProf20                    (swClearProf20),
                .swClearProf19                    (swClearProf19),
                .swClearProf18                    (swClearProf18),
                .swClearProf17                    (swClearProf17),
                .swClearProf16                    (swClearProf16),
                .swClearProf15                    (swClearProf15),
                .swClearProf14                    (swClearProf14),
                .swClearProf13                    (swClearProf13),
                .swClearProf12                    (swClearProf12),
                .swClearProf11                    (swClearProf11),
                .swClearProf10                    (swClearProf10),
                .swClearProf9                     (swClearProf9),
                .swClearProf8                     (swClearProf8),
                .swClearProf7                     (swClearProf7),
                .swClearProf6                     (swClearProf6),
                .swClearProf5                     (swClearProf5),
                .swClearProf4                     (swClearProf4),
                .swClearProf3                     (swClearProf3),
                .swClearProf2                     (swClearProf2),
                .swClearProf1                     (swClearProf1),
                .swClearProf0                     (swClearProf0),
                .regSel                           (plRegSel),
                .regWrite                         (regWrite),
                .regRead                          (regRead),
                .latchNextState_p                 (latchNextState_p),
                .regAddr                          (regAddr[(`RW_REG_ADDR_WIDTH-2):0]),
                .regWriteData                     (regWriteData),
                .regReadData                      (plReadData)
                );
        
        // Instanciation of macCoreReg
        // Name of the instance : u_macCoreReg
        // Name of the file containing this module : macCoreReg.v
        macCoreReg u_macCoreReg (
                .hardRstClk_n                     (macCoreClkHardRst_n),
                .softRstClk_n                     (macCoreClkSoftRst_n),
                .Clk                              (macCoreClk),
                .signature                        (signature),
                .mac80211MHFormat                 (mac80211MHFormat),
                .coex                             (coex),
                .wapi                             (wapi),
                .tpc                              (tpc),
                .vht                              (vht),
                .ht                               (ht),
                .rce                              (rce),
                .ccmp                             (ccmp),
                .tkip                             (tkip),
                .wep                              (wep),
                .security                         (security),
                .sme                              (sme),
                .hcca                             (hcca),
                .edca                             (edca),
                .qos                              (qos),
                .phaseNumber                      (phaseNumber),
                .releaseNumber                    (releaseNumber),
                .ieRelease                        (ieRelease),
                .umVersion                        (umVersion),
                .bitmapCnt                        (bitmapCnt),
                .nextStateIn                      (nextStateIn),
                .nextStateInValid                 (nextStateInValid),
                .currentState                     (currentState),
                .tsfUpdatedBySWIn                 (tsfUpdatedBySWIn),
                .tsfUpdatedBySWInValid            (tsfUpdatedBySWInValid),
                .keyStoRAMResetIn                 (keyStoRAMResetIn),
                .keyStoRAMResetInValid            (keyStoRAMResetInValid),
                .mibTableResetIn                  (mibTableResetIn),
                .mibTableResetInValid             (mibTableResetInValid),
                .baPSBitmapResetIn                (baPSBitmapResetIn),
                .baPSBitmapResetInValid           (baPSBitmapResetInValid),
                .encrRxFIFOResetIn                (encrRxFIFOResetIn),
                .encrRxFIFOResetInValid           (encrRxFIFOResetInValid),
                .macPHYIFFIFOResetIn              (macPHYIFFIFOResetIn),
                .macPHYIFFIFOResetInValid         (macPHYIFFIFOResetInValid),
                .txFIFOResetIn                    (txFIFOResetIn),
                .txFIFOResetInValid               (txFIFOResetInValid),
                .rxFIFOResetIn                    (rxFIFOResetIn),
                .rxFIFOResetInValid               (rxFIFOResetInValid),
                .hwFSMResetIn                     (hwFSMResetIn),
                .hwFSMResetInValid                (hwFSMResetInValid),
                .useErrRec                        (useErrRec),
                .statuserrInHWLevel3              (statuserrInHWLevel3),
                .statuserrInTxRxLevel2            (statuserrInTxRxLevel2),
                .statuserrInRxLevel1              (statuserrInRxLevel1),
                .statuserrInTxLevel1              (statuserrInTxLevel1),
                .enDuplicateDetection             (enDuplicateDetection),
                .dtimUpdatedBySWIn                (dtimUpdatedBySWIn),
                .dtimUpdatedBySWInValid           (dtimUpdatedBySWInValid),
                .cfpPeriodIn                      (cfpPeriodIn),
                .cfpPeriodInValid                 (cfpPeriodInValid),
                .dtimPeriodIn                     (dtimPeriodIn),
                .dtimPeriodInValid                (dtimPeriodInValid),
                .encrKeyRAMWord0In                (encrKeyRAMWord0In),
                .encrKeyRAMWord0InValid           (encrKeyRAMWord0InValid),
                .encrKeyRAMWord1In                (encrKeyRAMWord1In),
                .encrKeyRAMWord1InValid           (encrKeyRAMWord1InValid),
                .encrKeyRAMWord2In                (encrKeyRAMWord2In),
                .encrKeyRAMWord2InValid           (encrKeyRAMWord2InValid),
                .encrKeyRAMWord3In                (encrKeyRAMWord3In),
                .encrKeyRAMWord3InValid           (encrKeyRAMWord3InValid),
                .macAddrRAMLowIn                  (macAddrRAMLowIn),
                .macAddrRAMLowInValid             (macAddrRAMLowInValid),
                .macAddrRAMHighIn                 (macAddrRAMHighIn),
                .macAddrRAMHighInValid            (macAddrRAMHighInValid),
                .newReadIn                        (newReadIn),
                .newReadInValid                   (newReadInValid),
                .newWriteIn                       (newWriteIn),
                .newWriteInValid                  (newWriteInValid),
                .cTypeRAMIn                       (cTypeRAMIn),
                .cTypeRAMInValid                  (cTypeRAMInValid),
                .vlanIDRAMIn                      (vlanIDRAMIn),
                .vlanIDRAMInValid                 (vlanIDRAMInValid),
                .sppRAMIn                         (sppRAMIn),
                .sppRAMInValid                    (sppRAMInValid),
                .useDefKeyRAMIn                   (useDefKeyRAMIn),
                .useDefKeyRAMInValid              (useDefKeyRAMInValid),
                .cLenRAMIn                        (cLenRAMIn),
                .cLenRAMInValid                   (cLenRAMInValid),
            `ifdef RW_WAPI_EN                     
                .encrIntKeyRAMWord0In             (encrIntKeyRAMWord0In),
                .encrIntKeyRAMWord0InValid        (encrIntKeyRAMWord0InValid),
                .encrIntKeyRAMWord1In             (encrIntKeyRAMWord1In),
                .encrIntKeyRAMWord1InValid        (encrIntKeyRAMWord1InValid),
                .encrIntKeyRAMWord2In             (encrIntKeyRAMWord2In),
                .encrIntKeyRAMWord2InValid        (encrIntKeyRAMWord2InValid),
                .encrIntKeyRAMWord3In             (encrIntKeyRAMWord3In),
                .encrIntKeyRAMWord3InValid        (encrIntKeyRAMWord3InValid),
            `endif // RW_WAPI_EN                     
                .hccaTriggerTimer                 (hccaTriggerTimer),
                .mibWriteIn                       (mibWriteIn),
                .mibWriteInValid                  (mibWriteInValid),
                .monotonicCounter1                (monotonicCounter1),
                .monotonicCounterLow2             (monotonicCounterLow2),
                .monotonicCounterHigh2            (monotonicCounterHigh2),
                .ccaBusyDurIn                     (ccaBusyDurIn),
                .ccaBusyDurInValid                (ccaBusyDurInValid),
                .sendCFEndNowIn                   (sendCFEndNowIn),
                .sendCFEndNowInValid              (sendCFEndNowInValid),
                .quietDuration1In                 (quietDuration1In),
                .quietDuration1InValid            (quietDuration1InValid),
                .quietPeriod1In                   (quietPeriod1In),
                .quietPeriod1InValid              (quietPeriod1InValid),
                .quietCount1In                    (quietCount1In),
                .quietCount1InValid               (quietCount1InValid),
                .quietOffset1In                   (quietOffset1In),
                .quietOffset1InValid              (quietOffset1InValid),
                .quietDuration2In                 (quietDuration2In),
                .quietDuration2InValid            (quietDuration2InValid),
                .quietPeriod2In                   (quietPeriod2In),
                .quietPeriod2InValid              (quietPeriod2InValid),
                .quietCount2In                    (quietCount2In),
                .quietCount2InValid               (quietCount2InValid),
                .quietOffset2In                   (quietOffset2In),
                .quietOffset2InValid              (quietOffset2InValid),
                .ccaBusyDurSec20In                (ccaBusyDurSec20In),
                .ccaBusyDurSec20InValid           (ccaBusyDurSec20InValid),
                .ccaBusyDurSec40In                (ccaBusyDurSec40In),
                .ccaBusyDurSec40InValid           (ccaBusyDurSec40InValid),
                .ccaBusyDurSec80In                (ccaBusyDurSec80In),
                .ccaBusyDurSec80InValid           (ccaBusyDurSec80InValid),
                .startTxFrameExIn                 (startTxFrameExIn),
                .startTxFrameExInValid            (startTxFrameExInValid),
            `ifdef RW_WLAN_COEX_EN                
            `endif // RW_WLAN_COEX_EN                
                .macControlLs                     (macControlLs),
                .txControlLs                      (txControlLs),
                .rxControlLs                      (rxControlLs),
                .macControlCs                     (macControlCs),
                .txControlCs                      (txControlCs),
                .rxControlCs                      (rxControlCs),
                .debugPortRead                    (debugPortRead),
                .navCounterIn                     (navCounterIn),
                .navCounterInValid                (navCounterInValid),
                .activeAC                         (activeAC),
                .currentCW3                       (currentCW3),
                .currentCW2                       (currentCW2),
                .currentCW1                       (currentCW1),
                .currentCW0                       (currentCW0),
                .ac3QSRC                          (ac3QSRC),
                .ac2QSRC                          (ac2QSRC),
                .ac1QSRC                          (ac1QSRC),
                .ac0QSRC                          (ac0QSRC),
                .ac3QLRC                          (ac3QLRC),
                .ac2QLRC                          (ac2QLRC),
                .ac1QLRC                          (ac1QLRC),
                .ac0QLRC                          (ac0QLRC),
                .macAddrLow                       (macAddrLow),
                .macAddrHigh                      (macAddrHigh),
                .macAddrLowMask                   (macAddrLowMask),
                .macAddrHighMask                  (macAddrHighMask),
                .bssIDLow                         (bssIDLow),
                .bssIDHigh                        (bssIDHigh),
                .bssIDLowMask                     (bssIDLowMask),
                .bssIDHighMask                    (bssIDHighMask),
                .nextState                        (nextState),
                .probeDelay                       (probeDelay),
                .atimW                            (atimW),
                .wakeupDTIM                       (wakeupDTIM),
                .listenInterval                   (listenInterval),
                .rxRIFSEn                         (rxRIFSEn),
                .tsfMgtDisable                    (tsfMgtDisable),
                .tsfUpdatedBySW                   (tsfUpdatedBySW),
                .abgnMode                         (abgnMode),
                .keyStoRAMReset                   (keyStoRAMReset),
                .mibTableReset                    (mibTableReset),
                .rateControllerMPIF               (rateControllerMPIF),
                .disableBAResp                    (disableBAResp),
                .disableCTSResp                   (disableCTSResp),
                .disableACKResp                   (disableACKResp),
                .activeClkGating                  (activeClkGating),
                .enableLPClkSwitch                (enableLPClkSwitch),
                .cfpAware                         (cfpAware),
                .pwrMgt                           (pwrMgt),
                .ap                               (ap),
                .bssType                          (bssType),
                .rxFlowCntrlEn                    (rxFlowCntrlEn),
                .baPSBitmapReset                  (baPSBitmapReset),
                .encrRxFIFOReset                  (encrRxFIFOReset),
                .macPHYIFFIFOReset                (macPHYIFFIFOReset),
                .txFIFOReset                      (txFIFOReset),
                .rxFIFOReset                      (rxFIFOReset),
                .hwFSMReset                       (hwFSMReset),
                .useErrDet                        (useErrDet),
                .errInHWLevel3                    (errInHWLevel3),
                .errInTxRxLevel2                  (errInTxRxLevel2),
                .errInRxLevel1                    (errInRxLevel1),
                .errInTxLevel1                    (errInTxLevel1),
                .clearErrInHWLevel3               (clearErrInHWLevel3),
                .clearErrInTxRxLevel2             (clearErrInTxRxLevel2),
                .clearErrInRxLevel1               (clearErrInRxLevel1),
                .clearErrInTxLevel1               (clearErrInTxLevel1),
                .acceptUnknown                    (acceptUnknown),
                .acceptOtherDataFrames            (acceptOtherDataFrames),
                .acceptQoSNull                    (acceptQoSNull),
                .acceptQCFWOData                  (acceptQCFWOData),
                .acceptQData                      (acceptQData),
                .acceptCFWOData                   (acceptCFWOData),
                .acceptData                       (acceptData),
                .acceptOtherCntrlFrames           (acceptOtherCntrlFrames),
                .acceptCFEnd                      (acceptCFEnd),
                .acceptACK                        (acceptACK),
                .acceptCTS                        (acceptCTS),
                .acceptRTS                        (acceptRTS),
                .acceptPSPoll                     (acceptPSPoll),
                .acceptBA                         (acceptBA),
                .acceptBAR                        (acceptBAR),
                .acceptOtherMgmtFrames            (acceptOtherMgmtFrames),
                .acceptAllBeacon                  (acceptAllBeacon),
                .acceptNotExpectedBA              (acceptNotExpectedBA),
                .acceptDecryptErrorFrames         (acceptDecryptErrorFrames),
                .acceptBeacon                     (acceptBeacon),
                .acceptProbeResp                  (acceptProbeResp),
                .acceptProbeReq                   (acceptProbeReq),
                .acceptMyUnicast                  (acceptMyUnicast),
                .acceptUnicast                    (acceptUnicast),
                .acceptErrorFrames                (acceptErrorFrames),
                .acceptOtherBSSID                 (acceptOtherBSSID),
                .acceptBroadcast                  (acceptBroadcast),
                .acceptMulticast                  (acceptMulticast),
                .dontDecrypt                      (dontDecrypt),
                .excUnencrypted                   (excUnencrypted),
                .noBcnTxTime                      (noBcnTxTime),
                .impTBTTIn128Us                   (impTBTTIn128Us),
                .impTBTTPeriod                    (impTBTTPeriod),
                .beaconInt                        (beaconInt),
                .aid                              (aid),
                .timOffset                        (timOffset),
                .bcnUpdateOffset                  (bcnUpdateOffset),
                .dtimUpdatedBySW                  (dtimUpdatedBySW),
                .cfpPeriod                        (cfpPeriod),
                .dtimPeriod                       (dtimPeriod),
                .cfpMaxDuration                   (cfpMaxDuration),
                .dot11LongRetryLimit              (dot11LongRetryLimit),
                .dot11ShortRetryLimit             (dot11ShortRetryLimit),
                .maxPHYNtx                        (maxPHYNtx),
                .bbServiceB                       (bbServiceB),
                .bbServiceA                       (bbServiceA),
                .dsssMaxPwrLevel                  (dsssMaxPwrLevel),
                .ofdmMaxPwrLevel                  (ofdmMaxPwrLevel),
                .encrKeyRAMWord0                  (encrKeyRAMWord0),
                .encrKeyRAMWord1                  (encrKeyRAMWord1),
                .encrKeyRAMWord2                  (encrKeyRAMWord2),
                .encrKeyRAMWord3                  (encrKeyRAMWord3),
                .macAddrRAMLow                    (macAddrRAMLow),
                .macAddrRAMHigh                   (macAddrRAMHigh),
                .newRead                          (newRead),
                .newWrite                         (newWrite),
                .keyIndexRAM                      (keyIndexRAM),
                .cTypeRAM                         (cTypeRAM),
                .vlanIDRAM                        (vlanIDRAM),
                .sppRAM                           (sppRAM),
                .useDefKeyRAM                     (useDefKeyRAM),
                .cLenRAM                          (cLenRAM),
            `ifdef RW_WAPI_EN                     
                .encrIntKeyRAMWord0               (encrIntKeyRAMWord0),
                .encrIntKeyRAMWord1               (encrIntKeyRAMWord1),
                .encrIntKeyRAMWord2               (encrIntKeyRAMWord2),
                .encrIntKeyRAMWord3               (encrIntKeyRAMWord3),
            `endif // RW_WAPI_EN                     
                .bssBasicRateSet                  (bssBasicRateSet),
                .dsssCount                        (dsssCount),
                .ofdmCount                        (ofdmCount),
                .olbcTimer                        (olbcTimer),
                .txChainDelayInMACClk             (txChainDelayInMACClk),
                .txRFDelayInMACClk                (txRFDelayInMACClk),
                .macCoreClkFreq                   (macCoreClkFreq),
                .slotTimeInMACClk                 (slotTimeInMACClk),
                .slotTime                         (slotTime),
                .rxRFDelayInMACClk                (rxRFDelayInMACClk),
                .txDelayRFOnInMACClk              (txDelayRFOnInMACClk),
                .macProcDelayInMACClk             (macProcDelayInMACClk),
                .radioWakeUpTime                  (radioWakeUpTime),
                .radioChirpTime                   (radioChirpTime),
                .sifsBInMACClk                    (sifsBInMACClk),
                .sifsB                            (sifsB),
                .sifsAInMACClk                    (sifsAInMACClk),
                .sifsA                            (sifsA),
                .rxCCADelay                       (rxCCADelay),
                .rifs                             (rifs),
                .rxStartDelayMIMO                 (rxStartDelayMIMO),
                .rxStartDelayShort                (rxStartDelayShort),
                .rxStartDelayLong                 (rxStartDelayLong),
                .rxStartDelayOFDM                 (rxStartDelayOFDM),
                .rifsTOInMACClk                   (rifsTOInMACClk),
                .rifsInMACClk                     (rifsInMACClk),
                .txDMAProcDlyInMACClk             (txDMAProcDlyInMACClk),
                .edcaTriggerTimer                 (edcaTriggerTimer),
                .txPacketTimeout                  (txPacketTimeout),
                .txAbsoluteTimeout                (txAbsoluteTimeout),
                .rxPayloadUsedCount               (rxPayloadUsedCount),
                .rxPacketTimeout                  (rxPacketTimeout),
                .rxAbsoluteTimeout                (rxAbsoluteTimeout),
                .mibValue                         (mibValue),
                .mibWrite                         (mibWrite),
                .mibIncrementMode                 (mibIncrementMode),
                .mibTableIndex                    (mibTableIndex),
                .absTimerValue0                   (absTimerValue0),
                .absTimerValue1                   (absTimerValue1),
                .absTimerValue2                   (absTimerValue2),
                .absTimerValue3                   (absTimerValue3),
                .absTimerValue4                   (absTimerValue4),
                .absTimerValue5                   (absTimerValue5),
                .absTimerValue6                   (absTimerValue6),
                .absTimerValue7                   (absTimerValue7),
                .absTimerValue8                   (absTimerValue8),
                .absTimerValue9                   (absTimerValue9),
                .maxAllowedLength                 (maxAllowedLength),
                .txOpLimit0                       (txOpLimit0),
                .cwMax0                           (cwMax0),
                .cwMin0                           (cwMin0),
                .aifsn0                           (aifsn0),
                .txOpLimit1                       (txOpLimit1),
                .cwMax1                           (cwMax1),
                .cwMin1                           (cwMin1),
                .aifsn1                           (aifsn1),
                .txOpLimit2                       (txOpLimit2),
                .cwMax2                           (cwMax2),
                .cwMin2                           (cwMin2),
                .aifsn2                           (aifsn2),
                .txOpLimit3                       (txOpLimit3),
                .cwMax3                           (cwMax3),
                .cwMin3                           (cwMin3),
                .aifsn3                           (aifsn3),
                .ccaBusyDur                       (ccaBusyDur),
                .keepTXOPOpen                     (keepTXOPOpen),
                .remTXOPInDurField                (remTXOPInDurField),
                .sendCFEnd                        (sendCFEnd),
                .sendCFEndNow                     (sendCFEndNow),
                .quietDuration1                   (quietDuration1),
                .quietPeriod1                     (quietPeriod1),
                .quietCount1                      (quietCount1),
                .quietOffset1                     (quietOffset1),
                .quietDuration2                   (quietDuration2),
                .quietPeriod2                     (quietPeriod2),
                .quietCount2                      (quietCount2),
                .quietOffset2                     (quietOffset2),
                .ccaBusyDurSec20                  (ccaBusyDurSec20),
                .ccaBusyDurSec40                  (ccaBusyDurSec40),
                .ccaBusyDurSec80                  (ccaBusyDurSec80),
                .basicSTBCMCS                     (basicSTBCMCS),
                .dualCTSProt                      (dualCTSProt),
                .ctsSTBCDur                       (ctsSTBCDur),
                .cfEndSTBCDur                     (cfEndSTBCDur),
                .startTxBW                        (startTxBW),
                .startTxPreType                   (startTxPreType),
                .startTxFormatMod                 (startTxFormatMod),
                .startTxMCSIndex0                 (startTxMCSIndex0),
                .startTxKSRIndex                  (startTxKSRIndex),
                .startTxAC                        (startTxAC),
                .startTxFrmExType                 (startTxFrmExType),
                .startTxFrameEx                   (startTxFrameEx),
                .durControlFrm                    (durControlFrm),
                .startTxSMMIndex                  (startTxSMMIndex),
                .startTxAntennaSet                (startTxAntennaSet),
                .startTxLSTP                      (startTxLSTP),
                .startTxSmoothing                 (startTxSmoothing),
                .startTxShortGI                   (startTxShortGI),
                .startTxNTx                       (startTxNTx),
                .startTxFecCoding                 (startTxFecCoding),
                .startTxSTBC                      (startTxSTBC),
                .startTxNumExtnSS                 (startTxNumExtnSS),
                .maxSupportedBW                   (maxSupportedBW),
                .aPPDUMaxTime                     (aPPDUMaxTime),
                .dynBWEn                          (dynBWEn),
                .numTryBWAcquisition              (numTryBWAcquisition),
                .dropToLowerBW                    (dropToLowerBW),
                .defaultBWTXOP                    (defaultBWTXOP),
                .defaultBWTXOPV                   (defaultBWTXOPV),
                .bssBasicHTMCSSetUM               (bssBasicHTMCSSetUM),
                .bssBasicHTMCSSetEM               (bssBasicHTMCSSetEM),
                .bssBasicVHTMCSSet                (bssBasicVHTMCSSet),
                .supportLSTP                      (supportLSTP),
            `ifdef RW_WLAN_COEX_EN                
                .coexWlanChanFreq                 (coexWlanChanFreq),
                .coexWlanChanOffset               (coexWlanChanOffset),
                .coexEnable                       (coexEnable),
                .coexPTIBcnData                   (coexPTIBcnData),
                .coexPTIBKData                    (coexPTIBKData),
                .coexPTIBEData                    (coexPTIBEData),
                .coexPTIVIData                    (coexPTIVIData),
                .coexPTIVOData                    (coexPTIVOData),
                .coexPTIMgt                       (coexPTIMgt),
                .coexPTICntl                      (coexPTICntl),
                .coexPTIAck                       (coexPTIAck),
            `endif // RW_WLAN_COEX_EN                
                .debugPortSel2                    (debugPortSel2),
                .debugPortSel1                    (debugPortSel1),
                .navCounter                       (navCounter),
                .backoffOffset                    (backoffOffset),
                .rxReqForceDeassertion            (rxReqForceDeassertion),
                // edit by fengmaoqiao
                .regSel                           (coreRegSel),
                .regWrite                         (regWrite),
                .regRead                          (regRead),
                .regAddr                          (regAddr[(`RW_REG_ADDR_WIDTH-2):0]),
                .regWriteData                     (regWriteData),
                .regReadData                      (coreReadData)
                );
        
        // Instanciation of postWrite
        // Name of the instance : u_postWrite
        // Name of the file containing this module : postWrite.v
        postWrite u_postWrite (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .macCoreClk             (macCoreClk),
                .macCoreClkHardRst_n    (macCoreClkHardRst_n),
                .regSel                 (coreRegSel),
                .regWrite               (regWrite),
                .regRead                (regRead),
                .regAddr                (regAddr[(`RW_REG_ADDR_WIDTH-2):0]),
                .regWriteData           (regWriteData),
                .regReadyIn             (coreReadyIn),
                // edit by fengmaoqiao
                .regReadData            (),
                .postWriteWrite         (postWriteWrite),
                .postWriteRead          (postWriteRead),
                .postWriteSel           (postWriteSel),
                .postWriteregAddr       (postWriteregAddr),
                .postWritewriteData     (postWritewriteData),
                .postWritereadData      (postWritereadData)
                );
        
        endmodule