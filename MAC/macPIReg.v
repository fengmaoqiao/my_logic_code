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
// $Revision: 7258 $
// $Date: 2013-04-04 19:09:08 +0200 (Thu, 04 Apr 2013) $
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : Platform register
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
module macPlReg (
    ////////////////////////////////////////////
    // clock and reset
    ////////////////////////////////////////////
    input wire hardRstClk_n     , // Hard Reset.
    input wire softRstClk_n     , // Soft Reset.
    input wire Clk              , // clock clock.

    ////////////////////////////////////////////
    // Registers
    ////////////////////////////////////////////

    //$port_g NEXTTBTTREG register.
    input wire [15 : 0] nextTBTT                  ,// in

    //$port_g GENINTEVENTSETREG register.
    input wire  statussetrxPayloadDMADead       ,// in
    input wire  statussetrxHeaderDMADead        ,// in
    input wire  statussetphyRxStart             ,// in
    input wire  statussetphyErr                 ,// in
    input wire  statussetmacPHYIFUnderRun       ,// in
    input wire  statussethwErr                  ,// in
    input wire  statussetimpSecDTIM             ,// in
    input wire  statussetimpPriDTIM             ,// in
    input wire  statussetbcnTxDMADead           ,// in
    input wire  statussetac3TxDMADead           ,// in
    input wire  statussetac2TxDMADead           ,// in
    input wire  statussetac1TxDMADead           ,// in
    input wire  statussetac0TxDMADead           ,// in
    input wire  statussetptError                ,// in
    input wire  statussettimSet                 ,// in
    input wire  statussetolbcDSSS               ,// in
    input wire  statussetolbcOFDM               ,// in
    input wire  statussetrxFIFOOverFlow         ,// in
    input wire  statussetrxDMAEmpty             ,// in
    input wire  statussetmacPHYIFOverflow       ,// in
    input wire  statusabsGenTimers              ,// in
    input wire  statussetidleInterrupt          ,// in
    input wire  statussetimpSecTBTT             ,// in
    input wire  statussetimpPriTBTT             ,// in

    //$port_g TXRXINTEVENTSETREG register.

    //$port_g TXRXINTEVENTSETREG register.
    input wire  statussetbcnTxBufTrigger        ,// in
    input wire  statussetac3TxBufTrigger        ,// in
    input wire  statussetac2TxBufTrigger        ,// in
    input wire  statussetac1TxBufTrigger        ,// in
    input wire  statussetac0TxBufTrigger        ,// in
    input wire  statussetac3BWDropTrigger       ,// in
    input wire  statussetac2BWDropTrigger       ,// in
    input wire  statussetac1BWDropTrigger       ,// in
    input wire  statussetac0BWDropTrigger       ,// in
    input wire  statussetcounterRxTrigger       ,// in
    input wire  statussetbaRxTrigger            ,// in
    input wire  statussettimerRxTrigger         ,// in
    input wire  statussetrxTrigger              ,// in
    input wire  statussettimerTxTrigger         ,// in
    input wire  statussettxopComplete           ,// in
    input wire  statussetrdTxTrigger            ,// in
    input wire  statussethccaTxTrigger          ,// in
    input wire  statussetbcnTxTrigger           ,// in
    input wire  statussetac3TxTrigger           ,// in
    input wire  statussetac2TxTrigger           ,// in
    input wire  statussetac1TxTrigger           ,// in
    input wire  statussetac0TxTrigger           ,// in
    input wire  statussetrdProtTrigger          ,// in
    input wire  statussethccaProtTrigger        ,// in
    input wire  statussetac3ProtTrigger         ,// in
    input wire  statussetac2ProtTrigger         ,// in
    input wire  statussetac1ProtTrigger         ,// in
    input wire  statussetac0ProtTrigger         ,// in

    //$port_g TXRXINTEVENTCLEARREG register.

    //$port_g TIMERSINTEVENTSETREG register.

    //$port_g TIMERSINTEVENTSETREG register.
    input wire  statussetabsTimers9             ,// in
    input wire  statussetabsTimers8             ,// in
    input wire  statussetabsTimers7             ,// in
    input wire  statussetabsTimers6             ,// in
    input wire  statussetabsTimers5             ,// in
    input wire  statussetabsTimers4             ,// in
    input wire  statussetabsTimers3             ,// in
    input wire  statussetabsTimers2             ,// in
    input wire  statussetabsTimers1             ,// in
    input wire  statussetabsTimers0             ,// in

    //$port_g TIMERSINTEVENTCLEARREG register.

    //$port_g TSFLOREG register.
    input wire [31 : 0] tsfTimerLowIn,// in
    input wire  tsfTimerLowInValid,// in

    //$port_g TSFHIREG register.
    input wire [31 : 0] tsfTimerHighIn,// in
    input wire  tsfTimerHighInValid,// in
    input wire  computeDurationIn,// in
    input wire  computeDurationInValid,// in
    //$port_g TIMEONAIRVALUEREG register.
    input wire  timeOnAirValid            ,// in
    input wire [15 : 0] timeOnAir                 ,// in

    //$port_g DMACNTRLSETREG register.
    input wire  statussetrxPayloadNewHead       ,// in
    input wire  statussetrxHeaderNewHead        ,// in
    input wire  statussetrxPayloadNewTail       ,// in
    input wire  statussetrxHeaderNewTail        ,// in
    input wire  statussethaltAC3AfterTXOP       ,// in
    input wire  statussethaltAC2AfterTXOP       ,// in
    input wire  statussethaltAC1AfterTXOP       ,// in
    input wire  statussethaltAC0AfterTXOP       ,// in
    input wire  statussethaltBcnAfterTXOP       ,// in
    input wire  statussettxAC3NewHead           ,// in
    input wire  statussettxAC2NewHead           ,// in
    input wire  statussettxAC1NewHead           ,// in
    input wire  statussettxAC0NewHead           ,// in
    input wire  statussettxBcnNewHead           ,// in
    input wire  statussettxAC3NewTail           ,// in
    input wire  statussettxAC2NewTail           ,// in
    input wire  statussettxAC1NewTail           ,// in
    input wire  statussettxAC0NewTail           ,// in
    input wire  statussettxBcnNewTail           ,// in

    //$port_g DMASTATUS1REG register.
    input wire [1 : 0] rxPayloadState            ,// in
    input wire [1 : 0] rxHeaderState             ,// in
    input wire [1 : 0] txAC3State                ,// in
    input wire [1 : 0] txAC2State                ,// in
    input wire [1 : 0] txAC1State                ,// in
    input wire [1 : 0] txAC0State                ,// in
    input wire [1 : 0] txBcnState                ,// in

    //$port_g DMASTATUS2REG register.
    input wire  txAC3NewHeadErr           ,// in
    input wire  txAC2NewHeadErr           ,// in
    input wire  txAC1NewHeadErr           ,// in
    input wire  txAC0NewHeadErr           ,// in
    input wire  txBcnNewHeadErr           ,// in
    input wire  txAC3BusErr               ,// in
    input wire  txAC2BusErr               ,// in
    input wire  txAC1BusErr               ,// in
    input wire  txAC0BusErr               ,// in
    input wire  txBcnBusErr               ,// in
    input wire  txAC3PTAddressErr         ,// in
    input wire  txAC2PTAddressErr         ,// in
    input wire  txAC1PTAddressErr         ,// in
    input wire  txAC0PTAddressErr         ,// in
    input wire  txBcnPTAddressErr         ,// in
    input wire  txAC3NextPointerErr       ,// in
    input wire  txAC2NextPointerErr       ,// in
    input wire  txAC1NextPointerErr       ,// in
    input wire  txAC0NextPointerErr       ,// in
    input wire  txBcnNextPointerErr       ,// in
    input wire  txAC3UPatternErr          ,// in
    input wire  txAC2UPatternErr          ,// in
    input wire  txAC1UPatternErr          ,// in
    input wire  txAC0UPatternErr          ,// in
    input wire  txBcnUPatternErr          ,// in
    input wire  txAC3LenMismatch          ,// in
    input wire  txAC2LenMismatch          ,// in
    input wire  txAC1LenMismatch          ,// in
    input wire  txAC0LenMismatch          ,// in
    input wire  txBcnLenMismatch          ,// in

    //$port_g DMASTATUS3REG register.
    input wire  rxPayNewHeadErr           ,// in
    input wire  rxHdrNewHeadErr           ,// in
    input wire  rxPayBusErr               ,// in
    input wire  rxHdrBusErr               ,// in
    input wire  rxPayNextPointerErr       ,// in
    input wire  rxHdrNextPointerErr       ,// in
    input wire  rxPayUPatternErr          ,// in
    input wire  rxHdrUPatternErr          ,// in

    //$port_g DMASTATUS4REG register.
    input wire  txAC3HaltAfterTXOP        ,// in
    input wire  txAC2HaltAfterTXOP        ,// in
    input wire  txAC1HaltAfterTXOP        ,// in
    input wire  txAC0HaltAfterTXOP        ,// in
    input wire  txBcnHaltAfterTXOP        ,// in
    input wire  txAC3EndQ                 ,// in
    input wire  txAC2EndQ                 ,// in
    input wire  txAC1EndQ                 ,// in
    input wire  txAC0EndQ                 ,// in
    input wire  txBcnEndQ                 ,// in
    input wire  txAC3Startup              ,// in
    input wire  txAC2Startup              ,// in
    input wire  txAC1Startup              ,// in
    input wire  txAC0Startup              ,// in
    input wire  txBcnStartup              ,// in

    //$port_g EDCAACHASDATASETREG register.
    input wire  statussetac3HasData             ,// in
    input wire  statussetac2HasData             ,// in
    input wire  statussetac1HasData             ,// in
    input wire  statussetac0HasData             ,// in

    //$port_g MOT1REG register.
    input wire [15 : 0] ac1MOT                    ,// in
    input wire [15 : 0] ac0MOT                    ,// in

    //$port_g MOT2REG register.
    input wire [15 : 0] ac3MOT                    ,// in
    input wire [15 : 0] ac2MOT                    ,// in

    //$port_g MOT3REG register.
    input wire [15 : 0] miscMOT                   ,// in
    input wire [15 : 0] hccaQAPMOT                ,// in

    //$port_g TXBWDROPINFOREG register.
    input wire [1 : 0] txBWAfterDrop             ,// in

    //$port_g DEBUGBCNSPTRREG register.
    input wire [31 : 0] bcnStatusPointer          ,// in

    //$port_g DEBUGAC0SPTRREG register.
    input wire [31 : 0] ac0StatusPointer          ,// in

    //$port_g DEBUGAC1SPTRREG register.
    input wire [31 : 0] ac1StatusPointer          ,// in

    //$port_g DEBUGAC2SPTRREG register.
    input wire [31 : 0] ac2StatusPointer          ,// in

    //$port_g DEBUGAC3SPTRREG register.
    input wire [31 : 0] ac3StatusPointer          ,// in

    //$port_g DEBUGTXCPTRREG register.
    input wire [31 : 0] txCurrentPointer          ,// in

    //$port_g DEBUGRXPAYSPTRREG register.
    input wire [31 : 0] rxPayStatPointer          ,// in

    //$port_g DEBUGRXHDRCPTRREG register.
    input wire [31 : 0] rxHdrStatPointer          ,// in

    //$port_g DEBUGRXPAYCPTRREG register.
    input wire [31 : 0] rxPayCurrentPointer       ,// in

    //$port_g SWPROFILINGREG register.
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
    input wire  statusswSetProf31               ,// in
    input wire  statusswSetProf30               ,// in
    input wire  statusswSetProf29               ,// in
    input wire  statusswSetProf28               ,// in
    input wire  statusswSetProf27               ,// in
    input wire  statusswSetProf26               ,// in
    input wire  statusswSetProf25               ,// in
    input wire  statusswSetProf24               ,// in
    input wire  statusswSetProf23               ,// in
    input wire  statusswSetProf22               ,// in
    input wire  statusswSetProf21               ,// in
    input wire  statusswSetProf20               ,// in
    input wire  statusswSetProf19               ,// in
    input wire  statusswSetProf18               ,// in
    input wire  statusswSetProf17               ,// in
    input wire  statusswSetProf16               ,// in
    input wire  statusswSetProf15               ,// in
    input wire  statusswSetProf14               ,// in
    input wire  statusswSetProf13               ,// in
    input wire  statusswSetProf12               ,// in
    input wire  statusswSetProf11               ,// in
    input wire  statusswSetProf10               ,// in
    input wire  statusswSetProf9                ,// in
    input wire  statusswSetProf8                ,// in
    input wire  statusswSetProf7                ,// in
    input wire  statusswSetProf6                ,// in
    input wire  statusswSetProf5                ,// in
    input wire  statusswSetProf4                ,// in
    input wire  statusswSetProf3                ,// in
    input wire  statusswSetProf2                ,// in
    input wire  statusswSetProf1                ,// in
    input wire  statusswSetProf0                ,// in
    //

    //$port_g DOZECNTRL2REG register.
    output wire  wakeUpFromDoze        ,// out
    output wire  wakeUpSW              ,// out

    //$port_g MACCNTRL2REG register.
    output wire  softReset             ,// out

    //$port_g GENINTEVENTSETREG register.
    output wire  setrxPayloadDMADead   ,// out
    output wire  setrxHeaderDMADead    ,// out
    output wire  setphyRxStart         ,// out
    output wire  setphyErr             ,// out
    output wire  setmacPHYIFUnderRun   ,// out
    output wire  sethwErr              ,// out
    output wire  setimpSecDTIM         ,// out
    output wire  setimpPriDTIM         ,// out
    output wire  setbcnTxDMADead       ,// out
    output wire  setac3TxDMADead       ,// out
    output wire  setac2TxDMADead       ,// out
    output wire  setac1TxDMADead       ,// out
    output wire  setac0TxDMADead       ,// out
    output wire  setptError            ,// out
    output wire  settimSet             ,// out
    output wire  setolbcDSSS           ,// out
    output wire  setolbcOFDM           ,// out
    output wire  setrxFIFOOverFlow     ,// out
    output wire  setrxDMAEmpty         ,// out
    output wire  setmacPHYIFOverflow   ,// out
    output wire  absGenTimers          ,// out
    output wire  setidleInterrupt      ,// out
    output wire  setimpSecTBTT         ,// out
    output wire  setimpPriTBTT         ,// out

    //$port_g GENINTEVENTCLEARREG register.
    output wire  clearrxPayloadDMADead ,// out
    output wire  clearrxHeaderDMADead  ,// out
    output wire  clearphyRxStart       ,// out
    output wire  clearphyErr           ,// out
    output wire  clearmacPHYIFUnderRun ,// out
    output wire  clearhwErr            ,// out
    output wire  clearimpSecDTIM       ,// out
    output wire  clearimpPriDTIM       ,// out
    output wire  clearbcnTxDMADead     ,// out
    output wire  clearac3TxDMADead     ,// out
    output wire  clearac2TxDMADead     ,// out
    output wire  clearac1TxDMADead     ,// out
    output wire  clearac0TxDMADead     ,// out
    output wire  clearptError          ,// out
    output wire  cleartimSet           ,// out
    output wire  clearolbcDSSS         ,// out
    output wire  clearolbcOFDM         ,// out
    output wire  clearrxFIFOOverFlow   ,// out
    output wire  clearrxDMAEmpty       ,// out
    output wire  clearmacPHYIFOverflow ,// out
    output wire  clearidleInterrupt    ,// out
    output wire  clearimpSecTBTT       ,// out
    output wire  clearimpPriTBTT       ,// out

    //$port_g GENINTUNMASKREG register.
    output wire  masterGenIntEn        ,// out
    output wire  maskrxPayloadDMADead  ,// out
    output wire  maskrxHeaderDMADead   ,// out
    output wire  maskphyRxStart        ,// out
    output wire  maskphyErr            ,// out
    output wire  maskmacPHYIFUnderRun  ,// out
    output wire  maskhwErr             ,// out
    output wire  maskimpSecDTIM        ,// out
    output wire  maskimpPriDTIM        ,// out
    output wire  maskbcnTxDMADead      ,// out
    output wire  maskac3TxDMADead      ,// out
    output wire  maskac2TxDMADead      ,// out
    output wire  maskac1TxDMADead      ,// out
    output wire  maskac0TxDMADead      ,// out
    output wire  maskptError           ,// out
    output wire  masktimSet            ,// out
    output wire  maskolbcDSSS          ,// out
    output wire  maskolbcOFDM          ,// out
    output wire  maskrxFIFOOverFlow    ,// out
    output wire  maskrxDMAEmpty        ,// out
    output wire  maskmacPHYIFOverflow  ,// out
    output wire  maskabsGenTimers      ,// out
    output wire  maskidleInterrupt     ,// out
    output wire  maskimpSecTBTT        ,// out
    output wire  maskimpPriTBTT        ,// out

    //$port_g TXRXINTEVENTSETREG register.
    output wire  setbcnTxBufTrigger    ,// out
    output wire  setac3TxBufTrigger    ,// out
    output wire  setac2TxBufTrigger    ,// out
    output wire  setac1TxBufTrigger    ,// out
    output wire  setac0TxBufTrigger    ,// out
    output wire  setac3BWDropTrigger   ,// out
    output wire  setac2BWDropTrigger   ,// out
    output wire  setac1BWDropTrigger   ,// out
    output wire  setac0BWDropTrigger   ,// out
    output wire  setcounterRxTrigger   ,// out
    output wire  setbaRxTrigger        ,// out
    output wire  settimerRxTrigger     ,// out
    output wire  setrxTrigger          ,// out
    output wire  settimerTxTrigger     ,// out
    output wire  settxopComplete       ,// out
    output wire  setrdTxTrigger        ,// out
    output wire  sethccaTxTrigger      ,// out
    output wire  setbcnTxTrigger       ,// out
    output wire  setac3TxTrigger       ,// out
    output wire  setac2TxTrigger       ,// out
    output wire  setac1TxTrigger       ,// out
    output wire  setac0TxTrigger       ,// out
    output wire  setrdProtTrigger      ,// out
    output wire  sethccaProtTrigger    ,// out
    output wire  setac3ProtTrigger     ,// out
    output wire  setac2ProtTrigger     ,// out
    output wire  setac1ProtTrigger     ,// out
    output wire  setac0ProtTrigger     ,// out

    //$port_g TXRXINTEVENTCLEARREG register.
    output wire  clearbcnTxBufTrigger  ,// out
    output wire  clearac3TxBufTrigger  ,// out
    output wire  clearac2TxBufTrigger  ,// out
    output wire  clearac1TxBufTrigger  ,// out
    output wire  clearac0TxBufTrigger  ,// out
    output wire  clearac3BWDropTrigger ,// out
    output wire  clearac2BWDropTrigger ,// out
    output wire  clearac1BWDropTrigger ,// out
    output wire  clearac0BWDropTrigger ,// out
    output wire  clearcounterRxTrigger ,// out
    output wire  clearbaRxTrigger      ,// out
    output wire  cleartimerRxTrigger   ,// out
    output wire  clearrxTrigger        ,// out
    output wire  cleartimerTxTrigger   ,// out
    output wire  cleartxopComplete     ,// out
    output wire  clearrdTxTrigger      ,// out
    output wire  clearhccaTxTrigger    ,// out
    output wire  clearbcnTxTrigger     ,// out
    output wire  clearac3TxTrigger     ,// out
    output wire  clearac2TxTrigger     ,// out
    output wire  clearac1TxTrigger     ,// out
    output wire  clearac0TxTrigger     ,// out
    output wire  clearrdProtTrigger    ,// out
    output wire  clearhccaProtTrigger  ,// out
    output wire  clearac3ProtTrigger   ,// out
    output wire  clearac2ProtTrigger   ,// out
    output wire  clearac1ProtTrigger   ,// out
    output wire  clearac0ProtTrigger   ,// out

    //$port_g TXRXINTUNMASKREG register.
    output wire  masterTxRxIntEn       ,// out
    output wire  maskbcnTxBufTrigger   ,// out
    output wire  maskac3TxBufTrigger   ,// out
    output wire  maskac2TxBufTrigger   ,// out
    output wire  maskac1TxBufTrigger   ,// out
    output wire  maskac0TxBufTrigger   ,// out
    output wire  maskac3BWDropTrigger  ,// out
    output wire  maskac2BWDropTrigger  ,// out
    output wire  maskac1BWDropTrigger  ,// out
    output wire  maskac0BWDropTrigger  ,// out
    output wire  maskcounterRxTrigger  ,// out
    output wire  maskbaRxTrigger       ,// out
    output wire  masktimerRxTrigger    ,// out
    output wire  maskrxTrigger         ,// out
    output wire  masktimerTxTrigger    ,// out
    output wire  masktxopComplete      ,// out
    output wire  maskrdTxTrigger       ,// out
    output wire  maskhccaTxTrigger     ,// out
    output wire  maskbcnTxTrigger      ,// out
    output wire  maskac3TxTrigger      ,// out
    output wire  maskac2TxTrigger      ,// out
    output wire  maskac1TxTrigger      ,// out
    output wire  maskac0TxTrigger      ,// out
    output wire  maskrdProtTrigger     ,// out
    output wire  maskhccaProtTrigger   ,// out
    output wire  maskac3ProtTrigger    ,// out
    output wire  maskac2ProtTrigger    ,// out
    output wire  maskac1ProtTrigger    ,// out
    output wire  maskac0ProtTrigger    ,// out

    //$port_g TIMERSINTEVENTSETREG register.
    output wire  setabsTimers9         ,// out
    output wire  setabsTimers8         ,// out
    output wire  setabsTimers7         ,// out
    output wire  setabsTimers6         ,// out
    output wire  setabsTimers5         ,// out
    output wire  setabsTimers4         ,// out
    output wire  setabsTimers3         ,// out
    output wire  setabsTimers2         ,// out
    output wire  setabsTimers1         ,// out
    output wire  setabsTimers0         ,// out

    //$port_g TIMERSINTEVENTCLEARREG register.
    output wire  clearabsTimers9       ,// out
    output wire  clearabsTimers8       ,// out
    output wire  clearabsTimers7       ,// out
    output wire  clearabsTimers6       ,// out
    output wire  clearabsTimers5       ,// out
    output wire  clearabsTimers4       ,// out
    output wire  clearabsTimers3       ,// out
    output wire  clearabsTimers2       ,// out
    output wire  clearabsTimers1       ,// out
    output wire  clearabsTimers0       ,// out

    //$port_g TIMERSINTUNMASKREG register.
    output wire  maskabsTimers9        ,// out
    output wire  maskabsTimers8        ,// out
    output wire  maskabsTimers7        ,// out
    output wire  maskabsTimers6        ,// out
    output wire  maskabsTimers5        ,// out
    output wire  maskabsTimers4        ,// out
    output wire  maskabsTimers3        ,// out
    output wire  maskabsTimers2        ,// out
    output wire  maskabsTimers1        ,// out
    output wire  maskabsTimers0        ,// out

    //$port_g TSFLOREG register.
    output wire [31 : 0] tsfTimerLow           ,// out

    //$port_g TSFHIREG register.
    output wire [31 : 0] tsfTimerHigh          ,// out

    //$port_g TIMEONAIRPARAM1REG register.
    output wire [1 : 0] ppduSTBC              ,// out
    output wire [1 : 0] ppduNumExtnSS         ,// out
    output wire  ppduShortGI           ,// out
    output wire [2 : 0] ppduPreType           ,// out
    output wire [1 : 0] ppduBW                ,// out
    output wire [19 : 0] ppduLength            ,// out

    //$port_g TIMEONAIRPARAM2REG register.
    output wire [6 : 0] ppduMCSIndex          ,// out

    //$port_g TIMEONAIRVALUEREG register.
    output wire  computeDuration       ,// out

    //$port_g DMACNTRLSETREG register.
    output wire  setrxPayloadNewHead   ,// out
    output wire  setrxHeaderNewHead    ,// out
    output wire  setrxPayloadNewTail   ,// out
    output wire  setrxHeaderNewTail    ,// out
    output wire  sethaltAC3AfterTXOP   ,// out
    output wire  sethaltAC2AfterTXOP   ,// out
    output wire  sethaltAC1AfterTXOP   ,// out
    output wire  sethaltAC0AfterTXOP   ,// out
    output wire  sethaltBcnAfterTXOP   ,// out
    output wire  settxAC3NewHead       ,// out
    output wire  settxAC2NewHead       ,// out
    output wire  settxAC1NewHead       ,// out
    output wire  settxAC0NewHead       ,// out
    output wire  settxBcnNewHead       ,// out
    output wire  settxAC3NewTail       ,// out
    output wire  settxAC2NewTail       ,// out
    output wire  settxAC1NewTail       ,// out
    output wire  settxAC0NewTail       ,// out
    output wire  settxBcnNewTail       ,// out

    //$port_g DMACNTRLCLEARREG register.
    output wire  clearrxPayloadNewHead ,// out
    output wire  clearrxHeaderNewHead  ,// out
    output wire  clearrxPayloadNewTail ,// out
    output wire  clearrxHeaderNewTail  ,// out
    output wire  clearhaltAC3AfterTXOP ,// out
    output wire  clearhaltAC2AfterTXOP ,// out
    output wire  clearhaltAC1AfterTXOP ,// out
    output wire  clearhaltAC0AfterTXOP ,// out
    output wire  clearhaltBcnAfterTXOP ,// out
    output wire  cleartxAC3NewHead     ,// out
    output wire  cleartxAC2NewHead     ,// out
    output wire  cleartxAC1NewHead     ,// out
    output wire  cleartxAC0NewHead     ,// out
    output wire  cleartxBcnNewHead     ,// out
    output wire  cleartxAC3NewTail     ,// out
    output wire  cleartxAC2NewTail     ,// out
    output wire  cleartxAC1NewTail     ,// out
    output wire  cleartxAC0NewTail     ,// out
    output wire  cleartxBcnNewTail     ,// out

    //$port_g TXBCNHEADPTRREG register.
    output wire [31 : 0] txBcnHeadPtr          ,// out

    //$port_g TXAC0HEADPTRREG register.
    output wire [31 : 0] txAC0HeadPtr          ,// out

    //$port_g TXAC1HEADPTRREG register.
    output wire [31 : 0] txAC1HeadPtr          ,// out

    //$port_g TXAC2HEADPTRREG register.
    output wire [31 : 0] txAC2HeadPtr          ,// out

    //$port_g TXAC3HEADPTRREG register.
    output wire [31 : 0] txAC3HeadPtr          ,// out

    //$port_g TXSTRUCTSIZESREG register.
    output wire [5 : 0] dmaRBDSize            ,// out
    output wire [5 : 0] dmaRHDSize            ,// out
    output wire [5 : 0] dmaTBDSize            ,// out
    output wire [5 : 0] dmaTHDSize            ,// out
    output wire [5 : 0] ptEntrySize           ,// out

    //$port_g RXHEADERHEADPTRREG register.
    output wire [29 : 0] rxHeaderHeadPtr       ,// out
    output wire  rxHeaderHeadPtrValid  ,// out

    //$port_g RXPAYLOADHEADPTRREG register.
    output wire [29 : 0] rxPayloadHeadPtr      ,// out
    output wire  rxPayloadHeadPtrValid ,// out

    //$port_g DMATHRESHOLDREG register.
    output wire [7 : 0] rxFIFOThreshold       ,// out
    output wire [7 : 0] txFIFOThreshold       ,// out

    //$port_g EDCAACHASDATASETREG register.
    output wire  setac3HasData         ,// out
    output wire  setac2HasData         ,// out
    output wire  setac1HasData         ,// out
    output wire  setac0HasData         ,// out

    //$port_g EDCAACHASDATACLEARREG register.
    output wire  clearac3HasData       ,// out
    output wire  clearac2HasData       ,// out
    output wire  clearac1HasData       ,// out
    output wire  clearac0HasData       ,// out

    //$port_g SWPROFILINGREG register.
    output wire  swProf31              ,// out
    output wire  swProf30              ,// out
    output wire  swProf29              ,// out
    output wire  swProf28              ,// out
    output wire  swProf27              ,// out
    output wire  swProf26              ,// out
    output wire  swProf25              ,// out
    output wire  swProf24              ,// out
    output wire  swProf23              ,// out
    output wire  swProf22              ,// out
    output wire  swProf21              ,// out
    output wire  swProf20              ,// out
    output wire  swProf19              ,// out
    output wire  swProf18              ,// out
    output wire  swProf17              ,// out
    output wire  swProf16              ,// out
    output wire  swProf15              ,// out
    output wire  swProf14              ,// out
    output wire  swProf13              ,// out
    output wire  swProf12              ,// out
    output wire  swProf11              ,// out
    output wire  swProf10              ,// out
    output wire  swProf9               ,// out
    output wire  swProf8               ,// out
    output wire  swProf7               ,// out
    output wire  swProf6               ,// out
    output wire  swProf5               ,// out
    output wire  swProf4               ,// out
    output wire  swProf3               ,// out
    output wire  swProf2               ,// out
    output wire  swProf1               ,// out
    output wire  swProf0               ,// out

    //$port_g SWSETPROFILINGREG register.
    output wire  swSetProf31           ,// out
    output wire  swSetProf30           ,// out
    output wire  swSetProf29           ,// out
    output wire  swSetProf28           ,// out
    output wire  swSetProf27           ,// out
    output wire  swSetProf26           ,// out
    output wire  swSetProf25           ,// out
    output wire  swSetProf24           ,// out
    output wire  swSetProf23           ,// out
    output wire  swSetProf22           ,// out
    output wire  swSetProf21           ,// out
    output wire  swSetProf20           ,// out
    output wire  swSetProf19           ,// out
    output wire  swSetProf18           ,// out
    output wire  swSetProf17           ,// out
    output wire  swSetProf16           ,// out
    output wire  swSetProf15           ,// out
    output wire  swSetProf14           ,// out
    output wire  swSetProf13           ,// out
    output wire  swSetProf12           ,// out
    output wire  swSetProf11           ,// out
    output wire  swSetProf10           ,// out
    output wire  swSetProf9            ,// out
    output wire  swSetProf8            ,// out
    output wire  swSetProf7            ,// out
    output wire  swSetProf6            ,// out
    output wire  swSetProf5            ,// out
    output wire  swSetProf4            ,// out
    output wire  swSetProf3            ,// out
    output wire  swSetProf2            ,// out
    output wire  swSetProf1            ,// out
    output wire  swSetProf0            ,// out

    //$port_g SWCLEARPROFILINGREG register.
    output wire  swClearProf31         ,// out
    output wire  swClearProf30         ,// out
    output wire  swClearProf29         ,// out
    output wire  swClearProf28         ,// out
    output wire  swClearProf27         ,// out
    output wire  swClearProf26         ,// out
    output wire  swClearProf25         ,// out
    output wire  swClearProf24         ,// out
    output wire  swClearProf23         ,// out
    output wire  swClearProf22         ,// out
    output wire  swClearProf21         ,// out
    output wire  swClearProf20         ,// out
    output wire  swClearProf19         ,// out
    output wire  swClearProf18         ,// out
    output wire  swClearProf17         ,// out
    output wire  swClearProf16         ,// out
    output wire  swClearProf15         ,// out
    output wire  swClearProf14         ,// out
    output wire  swClearProf13         ,// out
    output wire  swClearProf12         ,// out
    output wire  swClearProf11         ,// out
    output wire  swClearProf10         ,// out
    output wire  swClearProf9          ,// out
    output wire  swClearProf8          ,// out
    output wire  swClearProf7          ,// out
    output wire  swClearProf6          ,// out
    output wire  swClearProf5          ,// out
    output wire  swClearProf4          ,// out
    output wire  swClearProf3          ,// out
    output wire  swClearProf2          ,// out
    output wire  swClearProf1          ,// out
    output wire  swClearProf0          ,// out

    ////////////////////////////////////////////
    // APB slave
    ////////////////////////////////////////////
    input wire regSel            , // Device select.
    input wire regWrite          , // Defines the enable cycle.
    input wire regRead           , // Write signal.
    output wire latchNextState_p  , // Next state latch
    input wire [12:0] regAddr , // Address.
    input wire [31:0] regWriteData, // Write data.
    // 
    output reg [31:0] regReadData  // Read data.

    
  );
////////////////////////////////////////////////////////////////////////////////
// Port Declaration 
////////////////////////////////////////////////////////////////////////////////
 
  //////////////////////////////////////////////////////////////////////////////
  // Constants for registers addresses
  //////////////////////////////////////////////////////////////////////////////

  // Constants for register addresses.
localparam NEXTTBTTREG_ADDR_CT             = 13'b000000010000;
localparam DOZECNTRL2REG_ADDR_CT           = 13'b000000010010;
localparam MACCNTRL2REG_ADDR_CT            = 13'b000000010100;
localparam GENINTEVENTSETREG_ADDR_CT       = 13'b000000011011;
localparam GENINTEVENTCLEARREG_ADDR_CT     = 13'b000000011100;
localparam GENINTUNMASKREG_ADDR_CT         = 13'b000000011101;
localparam TXRXINTEVENTSETREG_ADDR_CT      = 13'b000000011110;
localparam TXRXINTEVENTCLEARREG_ADDR_CT    = 13'b000000011111;
localparam TXRXINTUNMASKREG_ADDR_CT        = 13'b000000100000;
localparam TIMERSINTEVENTSETREG_ADDR_CT    = 13'b000000100001;
localparam TIMERSINTEVENTCLEARREG_ADDR_CT  = 13'b000000100010;
localparam TIMERSINTUNMASKREG_ADDR_CT      = 13'b000000100011;
localparam TSFLOREG_ADDR_CT                = 13'b000000101001;
localparam TSFHIREG_ADDR_CT                = 13'b000000101010;
`ifdef RW_THD_V2
localparam TIMEONAIRPARAM1REG_ADDR_CT      = 13'b000000110100;
localparam TIMEONAIRPARAM2REG_ADDR_CT      = 13'b000000110101;
localparam TIMEONAIRVALUEREG_ADDR_CT       = 13'b000000110110;
`else // RW_THD_V2
localparam TIMEONAIRPARAM1REG_ADDR_CT      = 13'b000001011000;
localparam TIMEONAIRPARAM2REG_ADDR_CT      = 13'b000001011001;
localparam TIMEONAIRVALUEREG_ADDR_CT       = 13'b000001011010;
`endif // RW_THD_V2
localparam DMACNTRLSETREG_ADDR_CT          = 13'b000001100000;
localparam DMACNTRLCLEARREG_ADDR_CT        = 13'b000001100001;
localparam DMASTATUS1REG_ADDR_CT           = 13'b000001100010;
localparam DMASTATUS2REG_ADDR_CT           = 13'b000001100011;
localparam DMASTATUS3REG_ADDR_CT           = 13'b000001100100;
localparam DMASTATUS4REG_ADDR_CT           = 13'b000001100101;
localparam TXBCNHEADPTRREG_ADDR_CT         = 13'b000001100110;
localparam TXAC0HEADPTRREG_ADDR_CT         = 13'b000001100111;
localparam TXAC1HEADPTRREG_ADDR_CT         = 13'b000001101000;
localparam TXAC2HEADPTRREG_ADDR_CT         = 13'b000001101001;
localparam TXAC3HEADPTRREG_ADDR_CT         = 13'b000001101010;
localparam TXSTRUCTSIZESREG_ADDR_CT        = 13'b000001101011;
localparam RXHEADERHEADPTRREG_ADDR_CT      = 13'b000001101110;
localparam RXPAYLOADHEADPTRREG_ADDR_CT     = 13'b000001101111;
localparam DMATHRESHOLDREG_ADDR_CT         = 13'b000001110000;
localparam EDCAACHASDATASETREG_ADDR_CT     = 13'b000010000100;
localparam EDCAACHASDATACLEARREG_ADDR_CT   = 13'b000010000101;
localparam MOT1REG_ADDR_CT                 = 13'b000010001010;
localparam MOT2REG_ADDR_CT                 = 13'b000010001011;
localparam MOT3REG_ADDR_CT                 = 13'b000010001100;
localparam TXBWDROPINFOREG_ADDR_CT         = 13'b000011001100;
localparam DEBUGBCNSPTRREG_ADDR_CT         = 13'b000101001001;
localparam DEBUGAC0SPTRREG_ADDR_CT         = 13'b000101001010;
localparam DEBUGAC1SPTRREG_ADDR_CT         = 13'b000101001011;
localparam DEBUGAC2SPTRREG_ADDR_CT         = 13'b000101001100;
localparam DEBUGAC3SPTRREG_ADDR_CT         = 13'b000101001101;
localparam DEBUGTXCPTRREG_ADDR_CT          = 13'b000101010000;
localparam DEBUGRXPAYSPTRREG_ADDR_CT       = 13'b000101010001;
localparam DEBUGRXHDRCPTRREG_ADDR_CT       = 13'b000101010010;
localparam DEBUGRXPAYCPTRREG_ADDR_CT       = 13'b000101010011;
localparam SWPROFILINGREG_ADDR_CT          = 13'b000101011000;
localparam SWSETPROFILINGREG_ADDR_CT       = 13'b000101011001;
localparam SWCLEARPROFILINGREG_ADDR_CT     = 13'b000101011010;

  //////////////////////////////////////////////////////////////////////////////
  // Signals
  //////////////////////////////////////////////////////////////////////////////
  //$port_g DOZECNTRL2REG register.
  reg  int_wakeUpFromDoze        ;
  reg  int_wakeUpSW              ;
  //$port_g MACCNTRL2REG register.
  reg  int_softReset             ;
  reg  int_setrxPayloadDMADead   ;
  reg  int_setrxHeaderDMADead    ;
  reg  int_setphyRxStart         ;
  reg  int_setphyErr             ;
  reg  int_setmacPHYIFUnderRun   ;
  reg  int_sethwErr              ;
  reg  int_setimpSecDTIM         ;
  reg  int_setimpPriDTIM         ;
  reg  int_setbcnTxDMADead       ;
  reg  int_setac3TxDMADead       ;
  reg  int_setac2TxDMADead       ;
  reg  int_setac1TxDMADead       ;
  reg  int_setac0TxDMADead       ;
  reg  int_setptError            ;
  reg  int_settimSet             ;
  reg  int_setolbcDSSS           ;
  reg  int_setolbcOFDM           ;
  reg  int_setrxFIFOOverFlow     ;
  reg  int_setrxDMAEmpty         ;
  reg  int_setmacPHYIFOverflow   ;
  reg  int_absGenTimers          ;
  reg  int_setidleInterrupt      ;
  reg  int_setimpSecTBTT         ;
  reg  int_setimpPriTBTT         ;
  reg  int_clearrxPayloadDMADead ;
  reg  int_clearrxHeaderDMADead  ;
  reg  int_clearphyRxStart       ;
  reg  int_clearphyErr           ;
  reg  int_clearmacPHYIFUnderRun ;
  reg  int_clearhwErr            ;
  reg  int_clearimpSecDTIM       ;
  reg  int_clearimpPriDTIM       ;
  reg  int_clearbcnTxDMADead     ;
  reg  int_clearac3TxDMADead     ;
  reg  int_clearac2TxDMADead     ;
  reg  int_clearac1TxDMADead     ;
  reg  int_clearac0TxDMADead     ;
  reg  int_clearptError          ;
  reg  int_cleartimSet           ;
  reg  int_clearolbcDSSS         ;
  reg  int_clearolbcOFDM         ;
  reg  int_clearrxFIFOOverFlow   ;
  reg  int_clearrxDMAEmpty       ;
  reg  int_clearmacPHYIFOverflow ;
  reg  int_clearidleInterrupt    ;
  reg  int_clearimpSecTBTT       ;
  reg  int_clearimpPriTBTT       ;
  //$port_g GENINTUNMASKREG register.
  reg  int_masterGenIntEn        ;
  reg  int_maskrxPayloadDMADead  ;
  reg  int_maskrxHeaderDMADead   ;
  reg  int_maskphyRxStart        ;
  reg  int_maskphyErr            ;
  reg  int_maskmacPHYIFUnderRun  ;
  reg  int_maskhwErr             ;
  reg  int_maskimpSecDTIM        ;
  reg  int_maskimpPriDTIM        ;
  reg  int_maskbcnTxDMADead      ;
  reg  int_maskac3TxDMADead      ;
  reg  int_maskac2TxDMADead      ;
  reg  int_maskac1TxDMADead      ;
  reg  int_maskac0TxDMADead      ;
  reg  int_maskptError           ;
  reg  int_masktimSet            ;
  reg  int_maskolbcDSSS          ;
  reg  int_maskolbcOFDM          ;
  reg  int_maskrxFIFOOverFlow    ;
  reg  int_maskrxDMAEmpty        ;
  reg  int_maskmacPHYIFOverflow  ;
  reg  int_maskabsGenTimers      ;
  reg  int_maskidleInterrupt     ;
  reg  int_maskimpSecTBTT        ;
  reg  int_maskimpPriTBTT        ;
  reg  int_setbcnTxBufTrigger    ;
  reg  int_setac3TxBufTrigger    ;
  reg  int_setac2TxBufTrigger    ;
  reg  int_setac1TxBufTrigger    ;
  reg  int_setac0TxBufTrigger    ;
  reg  int_setac3BWDropTrigger   ;
  reg  int_setac2BWDropTrigger   ;
  reg  int_setac1BWDropTrigger   ;
  reg  int_setac0BWDropTrigger   ;
  reg  int_setcounterRxTrigger   ;
  reg  int_setbaRxTrigger        ;
  reg  int_settimerRxTrigger     ;
  reg  int_setrxTrigger          ;
  reg  int_settimerTxTrigger     ;
  reg  int_settxopComplete       ;
  reg  int_setrdTxTrigger        ;
  reg  int_sethccaTxTrigger      ;
  reg  int_setbcnTxTrigger       ;
  reg  int_setac3TxTrigger       ;
  reg  int_setac2TxTrigger       ;
  reg  int_setac1TxTrigger       ;
  reg  int_setac0TxTrigger       ;
  reg  int_setrdProtTrigger      ;
  reg  int_sethccaProtTrigger    ;
  reg  int_setac3ProtTrigger     ;
  reg  int_setac2ProtTrigger     ;
  reg  int_setac1ProtTrigger     ;
  reg  int_setac0ProtTrigger     ;
  reg  int_clearbcnTxBufTrigger  ;
  reg  int_clearac3TxBufTrigger  ;
  reg  int_clearac2TxBufTrigger  ;
  reg  int_clearac1TxBufTrigger  ;
  reg  int_clearac0TxBufTrigger  ;
  reg  int_clearac3BWDropTrigger ;
  reg  int_clearac2BWDropTrigger ;
  reg  int_clearac1BWDropTrigger ;
  reg  int_clearac0BWDropTrigger ;
  reg  int_clearcounterRxTrigger ;
  reg  int_clearbaRxTrigger      ;
  reg  int_cleartimerRxTrigger   ;
  reg  int_clearrxTrigger        ;
  reg  int_cleartimerTxTrigger   ;
  reg  int_cleartxopComplete     ;
  reg  int_clearrdTxTrigger      ;
  reg  int_clearhccaTxTrigger    ;
  reg  int_clearbcnTxTrigger     ;
  reg  int_clearac3TxTrigger     ;
  reg  int_clearac2TxTrigger     ;
  reg  int_clearac1TxTrigger     ;
  reg  int_clearac0TxTrigger     ;
  reg  int_clearrdProtTrigger    ;
  reg  int_clearhccaProtTrigger  ;
  reg  int_clearac3ProtTrigger   ;
  reg  int_clearac2ProtTrigger   ;
  reg  int_clearac1ProtTrigger   ;
  reg  int_clearac0ProtTrigger   ;
  //$port_g TXRXINTUNMASKREG register.
  reg  int_masterTxRxIntEn       ;
  reg  int_maskbcnTxBufTrigger   ;
  reg  int_maskac3TxBufTrigger   ;
  reg  int_maskac2TxBufTrigger   ;
  reg  int_maskac1TxBufTrigger   ;
  reg  int_maskac0TxBufTrigger   ;
  reg  int_maskac3BWDropTrigger  ;
  reg  int_maskac2BWDropTrigger  ;
  reg  int_maskac1BWDropTrigger  ;
  reg  int_maskac0BWDropTrigger  ;
  reg  int_maskcounterRxTrigger  ;
  reg  int_maskbaRxTrigger       ;
  reg  int_masktimerRxTrigger    ;
  reg  int_maskrxTrigger         ;
  reg  int_masktimerTxTrigger    ;
  reg  int_masktxopComplete      ;
  reg  int_maskrdTxTrigger       ;
  reg  int_maskhccaTxTrigger     ;
  reg  int_maskbcnTxTrigger      ;
  reg  int_maskac3TxTrigger      ;
  reg  int_maskac2TxTrigger      ;
  reg  int_maskac1TxTrigger      ;
  reg  int_maskac0TxTrigger      ;
  reg  int_maskrdProtTrigger     ;
  reg  int_maskhccaProtTrigger   ;
  reg  int_maskac3ProtTrigger    ;
  reg  int_maskac2ProtTrigger    ;
  reg  int_maskac1ProtTrigger    ;
  reg  int_maskac0ProtTrigger    ;
  reg  int_setabsTimers9         ;
  reg  int_setabsTimers8         ;
  reg  int_setabsTimers7         ;
  reg  int_setabsTimers6         ;
  reg  int_setabsTimers5         ;
  reg  int_setabsTimers4         ;
  reg  int_setabsTimers3         ;
  reg  int_setabsTimers2         ;
  reg  int_setabsTimers1         ;
  reg  int_setabsTimers0         ;
  reg  int_clearabsTimers9       ;
  reg  int_clearabsTimers8       ;
  reg  int_clearabsTimers7       ;
  reg  int_clearabsTimers6       ;
  reg  int_clearabsTimers5       ;
  reg  int_clearabsTimers4       ;
  reg  int_clearabsTimers3       ;
  reg  int_clearabsTimers2       ;
  reg  int_clearabsTimers1       ;
  reg  int_clearabsTimers0       ;
  //$port_g TIMERSINTUNMASKREG register.
  reg  int_maskabsTimers9        ;
  reg  int_maskabsTimers8        ;
  reg  int_maskabsTimers7        ;
  reg  int_maskabsTimers6        ;
  reg  int_maskabsTimers5        ;
  reg  int_maskabsTimers4        ;
  reg  int_maskabsTimers3        ;
  reg  int_maskabsTimers2        ;
  reg  int_maskabsTimers1        ;
  reg  int_maskabsTimers0        ;
  //$port_g TSFLOREG register.
  reg [31 : 0] int_tsfTimerLow           ;
  //$port_g TSFHIREG register.
  reg [31 : 0] int_tsfTimerHigh          ;
  //$port_g TIMEONAIRPARAM1REG register.
  reg [1 : 0] int_ppduSTBC              ;
  reg [1 : 0] int_ppduNumExtnSS         ;
  reg  int_ppduShortGI           ;
  reg [2 : 0] int_ppduPreType           ;
  reg [1 : 0] int_ppduBW                ;
  reg [19 : 0] int_ppduLength            ;
  //$port_g TIMEONAIRPARAM2REG register.
  reg [6 : 0] int_ppduMCSIndex          ;
  //$port_g TIMEONAIRVALUEREG register.
  reg  int_computeDuration       ;
  reg  int_setrxPayloadNewHead   ;
  reg  int_setrxHeaderNewHead    ;
  reg  int_setrxPayloadNewTail   ;
  reg  int_setrxHeaderNewTail    ;
  reg  int_sethaltAC3AfterTXOP   ;
  reg  int_sethaltAC2AfterTXOP   ;
  reg  int_sethaltAC1AfterTXOP   ;
  reg  int_sethaltAC0AfterTXOP   ;
  reg  int_sethaltBcnAfterTXOP   ;
  reg  int_settxAC3NewHead       ;
  reg  int_settxAC2NewHead       ;
  reg  int_settxAC1NewHead       ;
  reg  int_settxAC0NewHead       ;
  reg  int_settxBcnNewHead       ;
  reg  int_settxAC3NewTail       ;
  reg  int_settxAC2NewTail       ;
  reg  int_settxAC1NewTail       ;
  reg  int_settxAC0NewTail       ;
  reg  int_settxBcnNewTail       ;
  reg  int_clearrxPayloadNewHead ;
  reg  int_clearrxHeaderNewHead  ;
  reg  int_clearrxPayloadNewTail ;
  reg  int_clearrxHeaderNewTail  ;
  reg  int_clearhaltAC3AfterTXOP ;
  reg  int_clearhaltAC2AfterTXOP ;
  reg  int_clearhaltAC1AfterTXOP ;
  reg  int_clearhaltAC0AfterTXOP ;
  reg  int_clearhaltBcnAfterTXOP ;
  reg  int_cleartxAC3NewHead     ;
  reg  int_cleartxAC2NewHead     ;
  reg  int_cleartxAC1NewHead     ;
  reg  int_cleartxAC0NewHead     ;
  reg  int_cleartxBcnNewHead     ;
  reg  int_cleartxAC3NewTail     ;
  reg  int_cleartxAC2NewTail     ;
  reg  int_cleartxAC1NewTail     ;
  reg  int_cleartxAC0NewTail     ;
  reg  int_cleartxBcnNewTail     ;
  //$port_g TXBCNHEADPTRREG register.
  reg [31 : 0] int_txBcnHeadPtr          ;
  //$port_g TXAC0HEADPTRREG register.
  reg [31 : 0] int_txAC0HeadPtr          ;
  //$port_g TXAC1HEADPTRREG register.
  reg [31 : 0] int_txAC1HeadPtr          ;
  //$port_g TXAC2HEADPTRREG register.
  reg [31 : 0] int_txAC2HeadPtr          ;
  //$port_g TXAC3HEADPTRREG register.
  reg [31 : 0] int_txAC3HeadPtr          ;
  //$port_g TXSTRUCTSIZESREG register.
  reg [5 : 0] int_dmaRBDSize            ;
  reg [5 : 0] int_dmaRHDSize            ;
  reg [5 : 0] int_dmaTBDSize            ;
  reg [5 : 0] int_dmaTHDSize            ;
  reg [5 : 0] int_ptEntrySize           ;
  //$port_g RXHEADERHEADPTRREG register.
  reg [29 : 0] int_rxHeaderHeadPtr       ;
  reg  int_rxHeaderHeadPtrValid  ;
  //$port_g RXPAYLOADHEADPTRREG register.
  reg [29 : 0] int_rxPayloadHeadPtr      ;
  reg  int_rxPayloadHeadPtrValid ;
  //$port_g DMATHRESHOLDREG register.
  reg [7 : 0] int_rxFIFOThreshold       ;
  reg [7 : 0] int_txFIFOThreshold       ;
  reg  int_setac3HasData         ;
  reg  int_setac2HasData         ;
  reg  int_setac1HasData         ;
  reg  int_setac0HasData         ;
  reg  int_clearac3HasData       ;
  reg  int_clearac2HasData       ;
  reg  int_clearac1HasData       ;
  reg  int_clearac0HasData       ;
  //$port_g SWPROFILINGREG register.
  reg  int_swProf31              ;
  reg  int_swProf30              ;
  reg  int_swProf29              ;
  reg  int_swProf28              ;
  reg  int_swProf27              ;
  reg  int_swProf26              ;
  reg  int_swProf25              ;
  reg  int_swProf24              ;
  reg  int_swProf23              ;
  reg  int_swProf22              ;
  reg  int_swProf21              ;
  reg  int_swProf20              ;
  reg  int_swProf19              ;
  reg  int_swProf18              ;
  reg  int_swProf17              ;
  reg  int_swProf16              ;
  reg  int_swProf15              ;
  reg  int_swProf14              ;
  reg  int_swProf13              ;
  reg  int_swProf12              ;
  reg  int_swProf11              ;
  reg  int_swProf10              ;
  reg  int_swProf9               ;
  reg  int_swProf8               ;
  reg  int_swProf7               ;
  reg  int_swProf6               ;
  reg  int_swProf5               ;
  reg  int_swProf4               ;
  reg  int_swProf3               ;
  reg  int_swProf2               ;
  reg  int_swProf1               ;
  reg  int_swProf0               ;
  reg  int_swSetProf31           ;
  reg  int_swSetProf30           ;
  reg  int_swSetProf29           ;
  reg  int_swSetProf28           ;
  reg  int_swSetProf27           ;
  reg  int_swSetProf26           ;
  reg  int_swSetProf25           ;
  reg  int_swSetProf24           ;
  reg  int_swSetProf23           ;
  reg  int_swSetProf22           ;
  reg  int_swSetProf21           ;
  reg  int_swSetProf20           ;
  reg  int_swSetProf19           ;
  reg  int_swSetProf18           ;
  reg  int_swSetProf17           ;
  reg  int_swSetProf16           ;
  reg  int_swSetProf15           ;
  reg  int_swSetProf14           ;
  reg  int_swSetProf13           ;
  reg  int_swSetProf12           ;
  reg  int_swSetProf11           ;
  reg  int_swSetProf10           ;
  reg  int_swSetProf9            ;
  reg  int_swSetProf8            ;
  reg  int_swSetProf7            ;
  reg  int_swSetProf6            ;
  reg  int_swSetProf5            ;
  reg  int_swSetProf4            ;
  reg  int_swSetProf3            ;
  reg  int_swSetProf2            ;
  reg  int_swSetProf1            ;
  reg  int_swSetProf0            ;
  reg  int_swClearProf31         ;
  reg  int_swClearProf30         ;
  reg  int_swClearProf29         ;
  reg  int_swClearProf28         ;
  reg  int_swClearProf27         ;
  reg  int_swClearProf26         ;
  reg  int_swClearProf25         ;
  reg  int_swClearProf24         ;
  reg  int_swClearProf23         ;
  reg  int_swClearProf22         ;
  reg  int_swClearProf21         ;
  reg  int_swClearProf20         ;
  reg  int_swClearProf19         ;
  reg  int_swClearProf18         ;
  reg  int_swClearProf17         ;
  reg  int_swClearProf16         ;
  reg  int_swClearProf15         ;
  reg  int_swClearProf14         ;
  reg  int_swClearProf13         ;
  reg  int_swClearProf12         ;
  reg  int_swClearProf11         ;
  reg  int_swClearProf10         ;
  reg  int_swClearProf9          ;
  reg  int_swClearProf8          ;
  reg  int_swClearProf7          ;
  reg  int_swClearProf6          ;
  reg  int_swClearProf5          ;
  reg  int_swClearProf4          ;
  reg  int_swClearProf3          ;
  reg  int_swClearProf2          ;
  reg  int_swClearProf1          ;
  reg  int_swClearProf0          ;
  
  //////////////////////////////////////////////////////////////////////////////
  // Ouput linkage
  //////////////////////////////////////////////////////////////////////////////
   assign wakeUpFromDoze        = int_wakeUpFromDoze        ;
   assign wakeUpSW              = int_wakeUpSW              ;
   assign softReset             = int_softReset             ;
   assign setrxPayloadDMADead   = int_setrxPayloadDMADead   ;
   assign setrxHeaderDMADead    = int_setrxHeaderDMADead    ;
   assign setphyRxStart         = int_setphyRxStart         ;
   assign setphyErr             = int_setphyErr             ;
   assign setmacPHYIFUnderRun   = int_setmacPHYIFUnderRun   ;
   assign sethwErr              = int_sethwErr              ;
   assign setimpSecDTIM         = int_setimpSecDTIM         ;
   assign setimpPriDTIM         = int_setimpPriDTIM         ;
   assign setbcnTxDMADead       = int_setbcnTxDMADead       ;
   assign setac3TxDMADead       = int_setac3TxDMADead       ;
   assign setac2TxDMADead       = int_setac2TxDMADead       ;
   assign setac1TxDMADead       = int_setac1TxDMADead       ;
   assign setac0TxDMADead       = int_setac0TxDMADead       ;
   assign setptError            = int_setptError            ;
   assign settimSet             = int_settimSet             ;
   assign setolbcDSSS           = int_setolbcDSSS           ;
   assign setolbcOFDM           = int_setolbcOFDM           ;
   assign setrxFIFOOverFlow     = int_setrxFIFOOverFlow     ;
   assign setrxDMAEmpty         = int_setrxDMAEmpty         ;
   assign setmacPHYIFOverflow   = int_setmacPHYIFOverflow   ;
   assign absGenTimers          = int_absGenTimers          ;
   assign setidleInterrupt      = int_setidleInterrupt      ;
   assign setimpSecTBTT         = int_setimpSecTBTT         ;
   assign setimpPriTBTT         = int_setimpPriTBTT         ;
   assign clearrxPayloadDMADead = int_clearrxPayloadDMADead ;
   assign clearrxHeaderDMADead  = int_clearrxHeaderDMADead  ;
   assign clearphyRxStart       = int_clearphyRxStart       ;
   assign clearphyErr           = int_clearphyErr           ;
   assign clearmacPHYIFUnderRun = int_clearmacPHYIFUnderRun ;
   assign clearhwErr            = int_clearhwErr            ;
   assign clearimpSecDTIM       = int_clearimpSecDTIM       ;
   assign clearimpPriDTIM       = int_clearimpPriDTIM       ;
   assign clearbcnTxDMADead     = int_clearbcnTxDMADead     ;
   assign clearac3TxDMADead     = int_clearac3TxDMADead     ;
   assign clearac2TxDMADead     = int_clearac2TxDMADead     ;
   assign clearac1TxDMADead     = int_clearac1TxDMADead     ;
   assign clearac0TxDMADead     = int_clearac0TxDMADead     ;
   assign clearptError          = int_clearptError          ;
   assign cleartimSet           = int_cleartimSet           ;
   assign clearolbcDSSS         = int_clearolbcDSSS         ;
   assign clearolbcOFDM         = int_clearolbcOFDM         ;
   assign clearrxFIFOOverFlow   = int_clearrxFIFOOverFlow   ;
   assign clearrxDMAEmpty       = int_clearrxDMAEmpty       ;
   assign clearmacPHYIFOverflow = int_clearmacPHYIFOverflow ;
   assign clearidleInterrupt    = int_clearidleInterrupt    ;
   assign clearimpSecTBTT       = int_clearimpSecTBTT       ;
   assign clearimpPriTBTT       = int_clearimpPriTBTT       ;
   assign masterGenIntEn        = int_masterGenIntEn        ;
   assign maskrxPayloadDMADead  = int_maskrxPayloadDMADead  ;
   assign maskrxHeaderDMADead   = int_maskrxHeaderDMADead   ;
   assign maskphyRxStart        = int_maskphyRxStart        ;
   assign maskphyErr            = int_maskphyErr            ;
   assign maskmacPHYIFUnderRun  = int_maskmacPHYIFUnderRun  ;
   assign maskhwErr             = int_maskhwErr             ;
   assign maskimpSecDTIM        = int_maskimpSecDTIM        ;
   assign maskimpPriDTIM        = int_maskimpPriDTIM        ;
   assign maskbcnTxDMADead      = int_maskbcnTxDMADead      ;
   assign maskac3TxDMADead      = int_maskac3TxDMADead      ;
   assign maskac2TxDMADead      = int_maskac2TxDMADead      ;
   assign maskac1TxDMADead      = int_maskac1TxDMADead      ;
   assign maskac0TxDMADead      = int_maskac0TxDMADead      ;
   assign maskptError           = int_maskptError           ;
   assign masktimSet            = int_masktimSet            ;
   assign maskolbcDSSS          = int_maskolbcDSSS          ;
   assign maskolbcOFDM          = int_maskolbcOFDM          ;
   assign maskrxFIFOOverFlow    = int_maskrxFIFOOverFlow    ;
   assign maskrxDMAEmpty        = int_maskrxDMAEmpty        ;
   assign maskmacPHYIFOverflow  = int_maskmacPHYIFOverflow  ;
   assign maskabsGenTimers      = int_maskabsGenTimers      ;
   assign maskidleInterrupt     = int_maskidleInterrupt     ;
   assign maskimpSecTBTT        = int_maskimpSecTBTT        ;
   assign maskimpPriTBTT        = int_maskimpPriTBTT        ;
   assign setbcnTxBufTrigger    = int_setbcnTxBufTrigger    ;
   assign setac3TxBufTrigger    = int_setac3TxBufTrigger    ;
   assign setac2TxBufTrigger    = int_setac2TxBufTrigger    ;
   assign setac1TxBufTrigger    = int_setac1TxBufTrigger    ;
   assign setac0TxBufTrigger    = int_setac0TxBufTrigger    ;
   assign setac3BWDropTrigger   = int_setac3BWDropTrigger   ;
   assign setac2BWDropTrigger   = int_setac2BWDropTrigger   ;
   assign setac1BWDropTrigger   = int_setac1BWDropTrigger   ;
   assign setac0BWDropTrigger   = int_setac0BWDropTrigger   ;
   assign setcounterRxTrigger   = int_setcounterRxTrigger   ;
   assign setbaRxTrigger        = int_setbaRxTrigger        ;
   assign settimerRxTrigger     = int_settimerRxTrigger     ;
   assign setrxTrigger          = int_setrxTrigger          ;
   assign settimerTxTrigger     = int_settimerTxTrigger     ;
   assign settxopComplete       = int_settxopComplete       ;
   assign setrdTxTrigger        = int_setrdTxTrigger        ;
   assign sethccaTxTrigger      = int_sethccaTxTrigger      ;
   assign setbcnTxTrigger       = int_setbcnTxTrigger       ;
   assign setac3TxTrigger       = int_setac3TxTrigger       ;
   assign setac2TxTrigger       = int_setac2TxTrigger       ;
   assign setac1TxTrigger       = int_setac1TxTrigger       ;
   assign setac0TxTrigger       = int_setac0TxTrigger       ;
   assign setrdProtTrigger      = int_setrdProtTrigger      ;
   assign sethccaProtTrigger    = int_sethccaProtTrigger    ;
   assign setac3ProtTrigger     = int_setac3ProtTrigger     ;
   assign setac2ProtTrigger     = int_setac2ProtTrigger     ;
   assign setac1ProtTrigger     = int_setac1ProtTrigger     ;
   assign setac0ProtTrigger     = int_setac0ProtTrigger     ;
   assign clearbcnTxBufTrigger  = int_clearbcnTxBufTrigger  ;
   assign clearac3TxBufTrigger  = int_clearac3TxBufTrigger  ;
   assign clearac2TxBufTrigger  = int_clearac2TxBufTrigger  ;
   assign clearac1TxBufTrigger  = int_clearac1TxBufTrigger  ;
   assign clearac0TxBufTrigger  = int_clearac0TxBufTrigger  ;
   assign clearac3BWDropTrigger = int_clearac3BWDropTrigger ;
   assign clearac2BWDropTrigger = int_clearac2BWDropTrigger ;
   assign clearac1BWDropTrigger = int_clearac1BWDropTrigger ;
   assign clearac0BWDropTrigger = int_clearac0BWDropTrigger ;
   assign clearcounterRxTrigger = int_clearcounterRxTrigger ;
   assign clearbaRxTrigger      = int_clearbaRxTrigger      ;
   assign cleartimerRxTrigger   = int_cleartimerRxTrigger   ;
   assign clearrxTrigger        = int_clearrxTrigger        ;
   assign cleartimerTxTrigger   = int_cleartimerTxTrigger   ;
   assign cleartxopComplete     = int_cleartxopComplete     ;
   assign clearrdTxTrigger      = int_clearrdTxTrigger      ;
   assign clearhccaTxTrigger    = int_clearhccaTxTrigger    ;
   assign clearbcnTxTrigger     = int_clearbcnTxTrigger     ;
   assign clearac3TxTrigger     = int_clearac3TxTrigger     ;
   assign clearac2TxTrigger     = int_clearac2TxTrigger     ;
   assign clearac1TxTrigger     = int_clearac1TxTrigger     ;
   assign clearac0TxTrigger     = int_clearac0TxTrigger     ;
   assign clearrdProtTrigger    = int_clearrdProtTrigger    ;
   assign clearhccaProtTrigger  = int_clearhccaProtTrigger  ;
   assign clearac3ProtTrigger   = int_clearac3ProtTrigger   ;
   assign clearac2ProtTrigger   = int_clearac2ProtTrigger   ;
   assign clearac1ProtTrigger   = int_clearac1ProtTrigger   ;
   assign clearac0ProtTrigger   = int_clearac0ProtTrigger   ;
   assign masterTxRxIntEn       = int_masterTxRxIntEn       ;
   assign maskbcnTxBufTrigger   = int_maskbcnTxBufTrigger   ;
   assign maskac3TxBufTrigger   = int_maskac3TxBufTrigger   ;
   assign maskac2TxBufTrigger   = int_maskac2TxBufTrigger   ;
   assign maskac1TxBufTrigger   = int_maskac1TxBufTrigger   ;
   assign maskac0TxBufTrigger   = int_maskac0TxBufTrigger   ;
   assign maskac3BWDropTrigger  = int_maskac3BWDropTrigger  ;
   assign maskac2BWDropTrigger  = int_maskac2BWDropTrigger  ;
   assign maskac1BWDropTrigger  = int_maskac1BWDropTrigger  ;
   assign maskac0BWDropTrigger  = int_maskac0BWDropTrigger  ;
   assign maskcounterRxTrigger  = int_maskcounterRxTrigger  ;
   assign maskbaRxTrigger       = int_maskbaRxTrigger       ;
   assign masktimerRxTrigger    = int_masktimerRxTrigger    ;
   assign maskrxTrigger         = int_maskrxTrigger         ;
   assign masktimerTxTrigger    = int_masktimerTxTrigger    ;
   assign masktxopComplete      = int_masktxopComplete      ;
   assign maskrdTxTrigger       = int_maskrdTxTrigger       ;
   assign maskhccaTxTrigger     = int_maskhccaTxTrigger     ;
   assign maskbcnTxTrigger      = int_maskbcnTxTrigger      ;
   assign maskac3TxTrigger      = int_maskac3TxTrigger      ;
   assign maskac2TxTrigger      = int_maskac2TxTrigger      ;
   assign maskac1TxTrigger      = int_maskac1TxTrigger      ;
   assign maskac0TxTrigger      = int_maskac0TxTrigger      ;
   assign maskrdProtTrigger     = int_maskrdProtTrigger     ;
   assign maskhccaProtTrigger   = int_maskhccaProtTrigger   ;
   assign maskac3ProtTrigger    = int_maskac3ProtTrigger    ;
   assign maskac2ProtTrigger    = int_maskac2ProtTrigger    ;
   assign maskac1ProtTrigger    = int_maskac1ProtTrigger    ;
   assign maskac0ProtTrigger    = int_maskac0ProtTrigger    ;
   assign setabsTimers9         = int_setabsTimers9         ;
   assign setabsTimers8         = int_setabsTimers8         ;
   assign setabsTimers7         = int_setabsTimers7         ;
   assign setabsTimers6         = int_setabsTimers6         ;
   assign setabsTimers5         = int_setabsTimers5         ;
   assign setabsTimers4         = int_setabsTimers4         ;
   assign setabsTimers3         = int_setabsTimers3         ;
   assign setabsTimers2         = int_setabsTimers2         ;
   assign setabsTimers1         = int_setabsTimers1         ;
   assign setabsTimers0         = int_setabsTimers0         ;
   assign clearabsTimers9       = int_clearabsTimers9       ;
   assign clearabsTimers8       = int_clearabsTimers8       ;
   assign clearabsTimers7       = int_clearabsTimers7       ;
   assign clearabsTimers6       = int_clearabsTimers6       ;
   assign clearabsTimers5       = int_clearabsTimers5       ;
   assign clearabsTimers4       = int_clearabsTimers4       ;
   assign clearabsTimers3       = int_clearabsTimers3       ;
   assign clearabsTimers2       = int_clearabsTimers2       ;
   assign clearabsTimers1       = int_clearabsTimers1       ;
   assign clearabsTimers0       = int_clearabsTimers0       ;
   assign maskabsTimers9        = int_maskabsTimers9        ;
   assign maskabsTimers8        = int_maskabsTimers8        ;
   assign maskabsTimers7        = int_maskabsTimers7        ;
   assign maskabsTimers6        = int_maskabsTimers6        ;
   assign maskabsTimers5        = int_maskabsTimers5        ;
   assign maskabsTimers4        = int_maskabsTimers4        ;
   assign maskabsTimers3        = int_maskabsTimers3        ;
   assign maskabsTimers2        = int_maskabsTimers2        ;
   assign maskabsTimers1        = int_maskabsTimers1        ;
   assign maskabsTimers0        = int_maskabsTimers0        ;
   assign tsfTimerLow           = int_tsfTimerLow           ;
   assign tsfTimerHigh          = int_tsfTimerHigh          ;
   assign ppduSTBC              = int_ppduSTBC              ;
   assign ppduNumExtnSS         = int_ppduNumExtnSS         ;
   assign ppduShortGI           = int_ppduShortGI           ;
   assign ppduPreType           = int_ppduPreType           ;
   assign ppduBW                = int_ppduBW                ;
   assign ppduLength            = int_ppduLength            ;
   assign ppduMCSIndex          = int_ppduMCSIndex          ;
   assign computeDuration       = int_computeDuration       ;
   assign setrxPayloadNewHead   = int_setrxPayloadNewHead   ;
   assign setrxHeaderNewHead    = int_setrxHeaderNewHead    ;
   assign setrxPayloadNewTail   = int_setrxPayloadNewTail   ;
   assign setrxHeaderNewTail    = int_setrxHeaderNewTail    ;
   assign sethaltAC3AfterTXOP   = int_sethaltAC3AfterTXOP   ;
   assign sethaltAC2AfterTXOP   = int_sethaltAC2AfterTXOP   ;
   assign sethaltAC1AfterTXOP   = int_sethaltAC1AfterTXOP   ;
   assign sethaltAC0AfterTXOP   = int_sethaltAC0AfterTXOP   ;
   assign sethaltBcnAfterTXOP   = int_sethaltBcnAfterTXOP   ;
   assign settxAC3NewHead       = int_settxAC3NewHead       ;
   assign settxAC2NewHead       = int_settxAC2NewHead       ;
   assign settxAC1NewHead       = int_settxAC1NewHead       ;
   assign settxAC0NewHead       = int_settxAC0NewHead       ;
   assign settxBcnNewHead       = int_settxBcnNewHead       ;
   assign settxAC3NewTail       = int_settxAC3NewTail       ;
   assign settxAC2NewTail       = int_settxAC2NewTail       ;
   assign settxAC1NewTail       = int_settxAC1NewTail       ;
   assign settxAC0NewTail       = int_settxAC0NewTail       ;
   assign settxBcnNewTail       = int_settxBcnNewTail       ;
   assign clearrxPayloadNewHead = int_clearrxPayloadNewHead ;
   assign clearrxHeaderNewHead  = int_clearrxHeaderNewHead  ;
   assign clearrxPayloadNewTail = int_clearrxPayloadNewTail ;
   assign clearrxHeaderNewTail  = int_clearrxHeaderNewTail  ;
   assign clearhaltAC3AfterTXOP = int_clearhaltAC3AfterTXOP ;
   assign clearhaltAC2AfterTXOP = int_clearhaltAC2AfterTXOP ;
   assign clearhaltAC1AfterTXOP = int_clearhaltAC1AfterTXOP ;
   assign clearhaltAC0AfterTXOP = int_clearhaltAC0AfterTXOP ;
   assign clearhaltBcnAfterTXOP = int_clearhaltBcnAfterTXOP ;
   assign cleartxAC3NewHead     = int_cleartxAC3NewHead     ;
   assign cleartxAC2NewHead     = int_cleartxAC2NewHead     ;
   assign cleartxAC1NewHead     = int_cleartxAC1NewHead     ;
   assign cleartxAC0NewHead     = int_cleartxAC0NewHead     ;
   assign cleartxBcnNewHead     = int_cleartxBcnNewHead     ;
   assign cleartxAC3NewTail     = int_cleartxAC3NewTail     ;
   assign cleartxAC2NewTail     = int_cleartxAC2NewTail     ;
   assign cleartxAC1NewTail     = int_cleartxAC1NewTail     ;
   assign cleartxAC0NewTail     = int_cleartxAC0NewTail     ;
   assign cleartxBcnNewTail     = int_cleartxBcnNewTail     ;
   assign txBcnHeadPtr          = int_txBcnHeadPtr          ;
   assign txAC0HeadPtr          = int_txAC0HeadPtr          ;
   assign txAC1HeadPtr          = int_txAC1HeadPtr          ;
   assign txAC2HeadPtr          = int_txAC2HeadPtr          ;
   assign txAC3HeadPtr          = int_txAC3HeadPtr          ;
   assign dmaRBDSize            = int_dmaRBDSize            ;
   assign dmaRHDSize            = int_dmaRHDSize            ;
   assign dmaTBDSize            = int_dmaTBDSize            ;
   assign dmaTHDSize            = int_dmaTHDSize            ;
   assign ptEntrySize           = int_ptEntrySize           ;
   assign rxHeaderHeadPtr       = int_rxHeaderHeadPtr       ;
   assign rxHeaderHeadPtrValid  = int_rxHeaderHeadPtrValid  ;
   assign rxPayloadHeadPtr      = int_rxPayloadHeadPtr      ;
   assign rxPayloadHeadPtrValid = int_rxPayloadHeadPtrValid ;
   assign rxFIFOThreshold       = int_rxFIFOThreshold       ;
   assign txFIFOThreshold       = int_txFIFOThreshold       ;
   assign setac3HasData         = int_setac3HasData         ;
   assign setac2HasData         = int_setac2HasData         ;
   assign setac1HasData         = int_setac1HasData         ;
   assign setac0HasData         = int_setac0HasData         ;
   assign clearac3HasData       = int_clearac3HasData       ;
   assign clearac2HasData       = int_clearac2HasData       ;
   assign clearac1HasData       = int_clearac1HasData       ;
   assign clearac0HasData       = int_clearac0HasData       ;
   assign swProf31              = int_swProf31              ;
   assign swProf30              = int_swProf30              ;
   assign swProf29              = int_swProf29              ;
   assign swProf28              = int_swProf28              ;
   assign swProf27              = int_swProf27              ;
   assign swProf26              = int_swProf26              ;
   assign swProf25              = int_swProf25              ;
   assign swProf24              = int_swProf24              ;
   assign swProf23              = int_swProf23              ;
   assign swProf22              = int_swProf22              ;
   assign swProf21              = int_swProf21              ;
   assign swProf20              = int_swProf20              ;
   assign swProf19              = int_swProf19              ;
   assign swProf18              = int_swProf18              ;
   assign swProf17              = int_swProf17              ;
   assign swProf16              = int_swProf16              ;
   assign swProf15              = int_swProf15              ;
   assign swProf14              = int_swProf14              ;
   assign swProf13              = int_swProf13              ;
   assign swProf12              = int_swProf12              ;
   assign swProf11              = int_swProf11              ;
   assign swProf10              = int_swProf10              ;
   assign swProf9               = int_swProf9               ;
   assign swProf8               = int_swProf8               ;
   assign swProf7               = int_swProf7               ;
   assign swProf6               = int_swProf6               ;
   assign swProf5               = int_swProf5               ;
   assign swProf4               = int_swProf4               ;
   assign swProf3               = int_swProf3               ;
   assign swProf2               = int_swProf2               ;
   assign swProf1               = int_swProf1               ;
   assign swProf0               = int_swProf0               ;
   assign swSetProf31           = int_swSetProf31           ;
   assign swSetProf30           = int_swSetProf30           ;
   assign swSetProf29           = int_swSetProf29           ;
   assign swSetProf28           = int_swSetProf28           ;
   assign swSetProf27           = int_swSetProf27           ;
   assign swSetProf26           = int_swSetProf26           ;
   assign swSetProf25           = int_swSetProf25           ;
   assign swSetProf24           = int_swSetProf24           ;
   assign swSetProf23           = int_swSetProf23           ;
   assign swSetProf22           = int_swSetProf22           ;
   assign swSetProf21           = int_swSetProf21           ;
   assign swSetProf20           = int_swSetProf20           ;
   assign swSetProf19           = int_swSetProf19           ;
   assign swSetProf18           = int_swSetProf18           ;
   assign swSetProf17           = int_swSetProf17           ;
   assign swSetProf16           = int_swSetProf16           ;
   assign swSetProf15           = int_swSetProf15           ;
   assign swSetProf14           = int_swSetProf14           ;
   assign swSetProf13           = int_swSetProf13           ;
   assign swSetProf12           = int_swSetProf12           ;
   assign swSetProf11           = int_swSetProf11           ;
   assign swSetProf10           = int_swSetProf10           ;
   assign swSetProf9            = int_swSetProf9            ;
   assign swSetProf8            = int_swSetProf8            ;
   assign swSetProf7            = int_swSetProf7            ;
   assign swSetProf6            = int_swSetProf6            ;
   assign swSetProf5            = int_swSetProf5            ;
   assign swSetProf4            = int_swSetProf4            ;
   assign swSetProf3            = int_swSetProf3            ;
   assign swSetProf2            = int_swSetProf2            ;
   assign swSetProf1            = int_swSetProf1            ;
   assign swSetProf0            = int_swSetProf0            ;
   assign swClearProf31         = int_swClearProf31         ;
   assign swClearProf30         = int_swClearProf30         ;
   assign swClearProf29         = int_swClearProf29         ;
   assign swClearProf28         = int_swClearProf28         ;
   assign swClearProf27         = int_swClearProf27         ;
   assign swClearProf26         = int_swClearProf26         ;
   assign swClearProf25         = int_swClearProf25         ;
   assign swClearProf24         = int_swClearProf24         ;
   assign swClearProf23         = int_swClearProf23         ;
   assign swClearProf22         = int_swClearProf22         ;
   assign swClearProf21         = int_swClearProf21         ;
   assign swClearProf20         = int_swClearProf20         ;
   assign swClearProf19         = int_swClearProf19         ;
   assign swClearProf18         = int_swClearProf18         ;
   assign swClearProf17         = int_swClearProf17         ;
   assign swClearProf16         = int_swClearProf16         ;
   assign swClearProf15         = int_swClearProf15         ;
   assign swClearProf14         = int_swClearProf14         ;
   assign swClearProf13         = int_swClearProf13         ;
   assign swClearProf12         = int_swClearProf12         ;
   assign swClearProf11         = int_swClearProf11         ;
   assign swClearProf10         = int_swClearProf10         ;
   assign swClearProf9          = int_swClearProf9          ;
   assign swClearProf8          = int_swClearProf8          ;
   assign swClearProf7          = int_swClearProf7          ;
   assign swClearProf6          = int_swClearProf6          ;
   assign swClearProf5          = int_swClearProf5          ;
   assign swClearProf4          = int_swClearProf4          ;
   assign swClearProf3          = int_swClearProf3          ;
   assign swClearProf2          = int_swClearProf2          ;
   assign swClearProf1          = int_swClearProf1          ;
   assign swClearProf0          = int_swClearProf0          ;



  //////////////////////////////////////////////////////////////////////////////
  // Register write
  //////////////////////////////////////////////////////////////////////////////
  assign latchNextState_p = 1'b0;


  // apb_write_p:
  always @(posedge Clk or negedge hardRstClk_n)
  begin
    if (!hardRstClk_n) 
    begin
	
      //$port_g DOZECNTRL2REG register.
      int_wakeUpFromDoze         <= 1'b0;
      int_wakeUpSW               <= 1'b1;
      //$port_g MACCNTRL2REG register.
      int_softReset              <= 1'b0;
      //$port_g GENINTEVENTSETREG register.
      int_setrxPayloadDMADead    <= 1'b0;
      int_setrxHeaderDMADead     <= 1'b0;
      int_setphyRxStart          <= 1'b0;
      int_setphyErr              <= 1'b0;
      int_setmacPHYIFUnderRun    <= 1'b0;
      int_sethwErr               <= 1'b0;
      int_setimpSecDTIM          <= 1'b0;
      int_setimpPriDTIM          <= 1'b0;
      int_setbcnTxDMADead        <= 1'b0;
      int_setac3TxDMADead        <= 1'b0;
      int_setac2TxDMADead        <= 1'b0;
      int_setac1TxDMADead        <= 1'b0;
      int_setac0TxDMADead        <= 1'b0;
      int_setptError             <= 1'b0;
      int_settimSet              <= 1'b0;
      int_setolbcDSSS            <= 1'b0;
      int_setolbcOFDM            <= 1'b0;
      int_setrxFIFOOverFlow      <= 1'b0;
      int_setrxDMAEmpty          <= 1'b0;
      int_setmacPHYIFOverflow    <= 1'b0;
      int_absGenTimers           <= 1'b0;
      int_setidleInterrupt       <= 1'b0;
      int_setimpSecTBTT          <= 1'b0;
      int_setimpPriTBTT          <= 1'b0;
      //$port_g GENINTEVENTCLEARREG register.
      int_clearrxPayloadDMADead  <= 1'b0;
      int_clearrxHeaderDMADead   <= 1'b0;
      int_clearphyRxStart        <= 1'b0;
      int_clearphyErr            <= 1'b0;
      int_clearmacPHYIFUnderRun  <= 1'b0;
      int_clearhwErr             <= 1'b0;
      int_clearimpSecDTIM        <= 1'b0;
      int_clearimpPriDTIM        <= 1'b0;
      int_clearbcnTxDMADead      <= 1'b0;
      int_clearac3TxDMADead      <= 1'b0;
      int_clearac2TxDMADead      <= 1'b0;
      int_clearac1TxDMADead      <= 1'b0;
      int_clearac0TxDMADead      <= 1'b0;
      int_clearptError           <= 1'b0;
      int_cleartimSet            <= 1'b0;
      int_clearolbcDSSS          <= 1'b0;
      int_clearolbcOFDM          <= 1'b0;
      int_clearrxFIFOOverFlow    <= 1'b0;
      int_clearrxDMAEmpty        <= 1'b0;
      int_clearmacPHYIFOverflow  <= 1'b0;
      int_clearidleInterrupt     <= 1'b0;
      int_clearimpSecTBTT        <= 1'b0;
      int_clearimpPriTBTT        <= 1'b0;
      //$port_g GENINTUNMASKREG register.
      int_masterGenIntEn         <= 1'b0;
      int_maskrxPayloadDMADead   <= 1'b0;
      int_maskrxHeaderDMADead    <= 1'b0;
      int_maskphyRxStart         <= 1'b0;
      int_maskphyErr             <= 1'b0;
      int_maskmacPHYIFUnderRun   <= 1'b0;
      int_maskhwErr              <= 1'b0;
      int_maskimpSecDTIM         <= 1'b0;
      int_maskimpPriDTIM         <= 1'b0;
      int_maskbcnTxDMADead       <= 1'b0;
      int_maskac3TxDMADead       <= 1'b0;
      int_maskac2TxDMADead       <= 1'b0;
      int_maskac1TxDMADead       <= 1'b0;
      int_maskac0TxDMADead       <= 1'b0;
      int_maskptError            <= 1'b0;
      int_masktimSet             <= 1'b0;
      int_maskolbcDSSS           <= 1'b0;
      int_maskolbcOFDM           <= 1'b0;
      int_maskrxFIFOOverFlow     <= 1'b0;
      int_maskrxDMAEmpty         <= 1'b0;
      int_maskmacPHYIFOverflow   <= 1'b0;
      int_maskabsGenTimers       <= 1'b0;
      int_maskidleInterrupt      <= 1'b0;
      int_maskimpSecTBTT         <= 1'b0;
      int_maskimpPriTBTT         <= 1'b0;
      //$port_g TXRXINTEVENTSETREG register.
      int_setbcnTxBufTrigger     <= 1'b0;
      int_setac3TxBufTrigger     <= 1'b0;
      int_setac2TxBufTrigger     <= 1'b0;
      int_setac1TxBufTrigger     <= 1'b0;
      int_setac0TxBufTrigger     <= 1'b0;
      int_setac3BWDropTrigger    <= 1'b0;
      int_setac2BWDropTrigger    <= 1'b0;
      int_setac1BWDropTrigger    <= 1'b0;
      int_setac0BWDropTrigger    <= 1'b0;
      int_setcounterRxTrigger    <= 1'b0;
      int_setbaRxTrigger         <= 1'b0;
      int_settimerRxTrigger      <= 1'b0;
      int_setrxTrigger           <= 1'b0;
      int_settimerTxTrigger      <= 1'b0;
      int_settxopComplete        <= 1'b0;
      int_setrdTxTrigger         <= 1'b0;
      int_sethccaTxTrigger       <= 1'b0;
      int_setbcnTxTrigger        <= 1'b0;
      int_setac3TxTrigger        <= 1'b0;
      int_setac2TxTrigger        <= 1'b0;
      int_setac1TxTrigger        <= 1'b0;
      int_setac0TxTrigger        <= 1'b0;
      int_setrdProtTrigger       <= 1'b0;
      int_sethccaProtTrigger     <= 1'b0;
      int_setac3ProtTrigger      <= 1'b0;
      int_setac2ProtTrigger      <= 1'b0;
      int_setac1ProtTrigger      <= 1'b0;
      int_setac0ProtTrigger      <= 1'b0;
      //$port_g TXRXINTEVENTCLEARREG register.
      int_clearbcnTxBufTrigger   <= 1'b0;
      int_clearac3TxBufTrigger   <= 1'b0;
      int_clearac2TxBufTrigger   <= 1'b0;
      int_clearac1TxBufTrigger   <= 1'b0;
      int_clearac0TxBufTrigger   <= 1'b0;
      int_clearac3BWDropTrigger  <= 1'b0;
      int_clearac2BWDropTrigger  <= 1'b0;
      int_clearac1BWDropTrigger  <= 1'b0;
      int_clearac0BWDropTrigger  <= 1'b0;
      int_clearcounterRxTrigger  <= 1'b0;
      int_clearbaRxTrigger       <= 1'b0;
      int_cleartimerRxTrigger    <= 1'b0;
      int_clearrxTrigger         <= 1'b0;
      int_cleartimerTxTrigger    <= 1'b0;
      int_cleartxopComplete      <= 1'b0;
      int_clearrdTxTrigger       <= 1'b0;
      int_clearhccaTxTrigger     <= 1'b0;
      int_clearbcnTxTrigger      <= 1'b0;
      int_clearac3TxTrigger      <= 1'b0;
      int_clearac2TxTrigger      <= 1'b0;
      int_clearac1TxTrigger      <= 1'b0;
      int_clearac0TxTrigger      <= 1'b0;
      int_clearrdProtTrigger     <= 1'b0;
      int_clearhccaProtTrigger   <= 1'b0;
      int_clearac3ProtTrigger    <= 1'b0;
      int_clearac2ProtTrigger    <= 1'b0;
      int_clearac1ProtTrigger    <= 1'b0;
      int_clearac0ProtTrigger    <= 1'b0;
      //$port_g TXRXINTUNMASKREG register.
      int_masterTxRxIntEn        <= 1'b0;
      int_maskbcnTxBufTrigger    <= 1'b0;
      int_maskac3TxBufTrigger    <= 1'b0;
      int_maskac2TxBufTrigger    <= 1'b0;
      int_maskac1TxBufTrigger    <= 1'b0;
      int_maskac0TxBufTrigger    <= 1'b0;
      int_maskac3BWDropTrigger   <= 1'b0;
      int_maskac2BWDropTrigger   <= 1'b0;
      int_maskac1BWDropTrigger   <= 1'b0;
      int_maskac0BWDropTrigger   <= 1'b0;
      int_maskcounterRxTrigger   <= 1'b0;
      int_maskbaRxTrigger        <= 1'b0;
      int_masktimerRxTrigger     <= 1'b0;
      int_maskrxTrigger          <= 1'b0;
      int_masktimerTxTrigger     <= 1'b0;
      int_masktxopComplete       <= 1'b0;
      int_maskrdTxTrigger        <= 1'b0;
      int_maskhccaTxTrigger      <= 1'b0;
      int_maskbcnTxTrigger       <= 1'b0;
      int_maskac3TxTrigger       <= 1'b0;
      int_maskac2TxTrigger       <= 1'b0;
      int_maskac1TxTrigger       <= 1'b0;
      int_maskac0TxTrigger       <= 1'b0;
      int_maskrdProtTrigger      <= 1'b0;
      int_maskhccaProtTrigger    <= 1'b0;
      int_maskac3ProtTrigger     <= 1'b0;
      int_maskac2ProtTrigger     <= 1'b0;
      int_maskac1ProtTrigger     <= 1'b0;
      int_maskac0ProtTrigger     <= 1'b0;
      //$port_g TIMERSINTEVENTSETREG register.
      int_setabsTimers9          <= 1'b0;
      int_setabsTimers8          <= 1'b0;
      int_setabsTimers7          <= 1'b0;
      int_setabsTimers6          <= 1'b0;
      int_setabsTimers5          <= 1'b0;
      int_setabsTimers4          <= 1'b0;
      int_setabsTimers3          <= 1'b0;
      int_setabsTimers2          <= 1'b0;
      int_setabsTimers1          <= 1'b0;
      int_setabsTimers0          <= 1'b0;
      //$port_g TIMERSINTEVENTCLEARREG register.
      int_clearabsTimers9        <= 1'b0;
      int_clearabsTimers8        <= 1'b0;
      int_clearabsTimers7        <= 1'b0;
      int_clearabsTimers6        <= 1'b0;
      int_clearabsTimers5        <= 1'b0;
      int_clearabsTimers4        <= 1'b0;
      int_clearabsTimers3        <= 1'b0;
      int_clearabsTimers2        <= 1'b0;
      int_clearabsTimers1        <= 1'b0;
      int_clearabsTimers0        <= 1'b0;
      //$port_g TIMERSINTUNMASKREG register.
      int_maskabsTimers9         <= 1'b0;
      int_maskabsTimers8         <= 1'b0;
      int_maskabsTimers7         <= 1'b0;
      int_maskabsTimers6         <= 1'b0;
      int_maskabsTimers5         <= 1'b0;
      int_maskabsTimers4         <= 1'b0;
      int_maskabsTimers3         <= 1'b0;
      int_maskabsTimers2         <= 1'b0;
      int_maskabsTimers1         <= 1'b0;
      int_maskabsTimers0         <= 1'b0;
      //$port_g TSFLOREG register.
      int_tsfTimerLow            <= 32'b0000000000000000000000000000000;
      //$port_g TSFHIREG register.
      int_tsfTimerHigh           <= 32'b0000000000000000000000000000000;
      //$port_g TIMEONAIRPARAM1REG register.
      int_ppduSTBC               <= 2'b0;
      int_ppduNumExtnSS          <= 2'b0;
      int_ppduShortGI            <= 1'b0;
      int_ppduPreType            <= 3'b00;
      int_ppduBW                 <= 2'b0;
      int_ppduLength             <= 20'b0000000000000000000;
      //$port_g TIMEONAIRPARAM2REG register.
      int_ppduMCSIndex           <= 7'b000000;
      //$port_g TIMEONAIRVALUEREG register.
      int_computeDuration        <= 1'b0;
      //$port_g DMACNTRLSETREG register.
      int_setrxPayloadNewHead    <= 1'b0;
      int_setrxHeaderNewHead     <= 1'b0;
      int_setrxPayloadNewTail    <= 1'b0;
      int_setrxHeaderNewTail     <= 1'b0;
      int_sethaltAC3AfterTXOP    <= 1'b0;
      int_sethaltAC2AfterTXOP    <= 1'b0;
      int_sethaltAC1AfterTXOP    <= 1'b0;
      int_sethaltAC0AfterTXOP    <= 1'b0;
      int_sethaltBcnAfterTXOP    <= 1'b0;
      int_settxAC3NewHead        <= 1'b0;
      int_settxAC2NewHead        <= 1'b0;
      int_settxAC1NewHead        <= 1'b0;
      int_settxAC0NewHead        <= 1'b0;
      int_settxBcnNewHead        <= 1'b0;
      int_settxAC3NewTail        <= 1'b0;
      int_settxAC2NewTail        <= 1'b0;
      int_settxAC1NewTail        <= 1'b0;
      int_settxAC0NewTail        <= 1'b0;
      int_settxBcnNewTail        <= 1'b0;
      //$port_g DMACNTRLCLEARREG register.
      int_clearrxPayloadNewHead  <= 1'b0;
      int_clearrxHeaderNewHead   <= 1'b0;
      int_clearrxPayloadNewTail  <= 1'b0;
      int_clearrxHeaderNewTail   <= 1'b0;
      int_clearhaltAC3AfterTXOP  <= 1'b0;
      int_clearhaltAC2AfterTXOP  <= 1'b0;
      int_clearhaltAC1AfterTXOP  <= 1'b0;
      int_clearhaltAC0AfterTXOP  <= 1'b0;
      int_clearhaltBcnAfterTXOP  <= 1'b0;
      int_cleartxAC3NewHead      <= 1'b0;
      int_cleartxAC2NewHead      <= 1'b0;
      int_cleartxAC1NewHead      <= 1'b0;
      int_cleartxAC0NewHead      <= 1'b0;
      int_cleartxBcnNewHead      <= 1'b0;
      int_cleartxAC3NewTail      <= 1'b0;
      int_cleartxAC2NewTail      <= 1'b0;
      int_cleartxAC1NewTail      <= 1'b0;
      int_cleartxAC0NewTail      <= 1'b0;
      int_cleartxBcnNewTail      <= 1'b0;
      //$port_g TXBCNHEADPTRREG register.
      int_txBcnHeadPtr           <= 32'b0000000000000000000000000000000;
      //$port_g TXAC0HEADPTRREG register.
      int_txAC0HeadPtr           <= 32'b0000000000000000000000000000000;
      //$port_g TXAC1HEADPTRREG register.
      int_txAC1HeadPtr           <= 32'b0000000000000000000000000000000;
      //$port_g TXAC2HEADPTRREG register.
      int_txAC2HeadPtr           <= 32'b0000000000000000000000000000000;
      //$port_g TXAC3HEADPTRREG register.
      int_txAC3HeadPtr           <= 32'b0000000000000000000000000000000;
      //$port_g TXSTRUCTSIZESREG register.
      int_dmaRBDSize             <= 6'd`RBD_SIZE;
      int_dmaRHDSize             <= 6'd`RHD_SIZE;
      int_dmaTBDSize             <= 6'd`TBD_SIZE;
      int_dmaTHDSize             <= 6'd`THD_SIZE;
      int_ptEntrySize            <= 6'd`PT_SIZE;
      //$port_g RXHEADERHEADPTRREG register.
      int_rxHeaderHeadPtr        <= 30'b00000000000000000000000000000;
      int_rxHeaderHeadPtrValid   <= 1'b0;
      //$port_g RXPAYLOADHEADPTRREG register.
      int_rxPayloadHeadPtr       <= 30'b00000000000000000000000000000;
      int_rxPayloadHeadPtrValid  <= 1'b0;
      //$port_g DMATHRESHOLDREG register.
      int_rxFIFOThreshold        <= 8'b0010000;
      int_txFIFOThreshold        <= 8'b0010000;
      //$port_g EDCAACHASDATASETREG register.
      int_setac3HasData          <= 1'b0;
      int_setac2HasData          <= 1'b0;
      int_setac1HasData          <= 1'b0;
      int_setac0HasData          <= 1'b0;
      //$port_g EDCAACHASDATACLEARREG register.
      int_clearac3HasData        <= 1'b0;
      int_clearac2HasData        <= 1'b0;
      int_clearac1HasData        <= 1'b0;
      int_clearac0HasData        <= 1'b0;
      //$port_g SWPROFILINGREG register.
      int_swProf31               <= 1'b0;
      int_swProf30               <= 1'b0;
      int_swProf29               <= 1'b0;
      int_swProf28               <= 1'b0;
      int_swProf27               <= 1'b0;
      int_swProf26               <= 1'b0;
      int_swProf25               <= 1'b0;
      int_swProf24               <= 1'b0;
      int_swProf23               <= 1'b0;
      int_swProf22               <= 1'b0;
      int_swProf21               <= 1'b0;
      int_swProf20               <= 1'b0;
      int_swProf19               <= 1'b0;
      int_swProf18               <= 1'b0;
      int_swProf17               <= 1'b0;
      int_swProf16               <= 1'b0;
      int_swProf15               <= 1'b0;
      int_swProf14               <= 1'b0;
      int_swProf13               <= 1'b0;
      int_swProf12               <= 1'b0;
      int_swProf11               <= 1'b0;
      int_swProf10               <= 1'b0;
      int_swProf9                <= 1'b0;
      int_swProf8                <= 1'b0;
      int_swProf7                <= 1'b0;
      int_swProf6                <= 1'b0;
      int_swProf5                <= 1'b0;
      int_swProf4                <= 1'b0;
      int_swProf3                <= 1'b0;
      int_swProf2                <= 1'b0;
      int_swProf1                <= 1'b0;
      int_swProf0                <= 1'b0;
      //$port_g SWSETPROFILINGREG register.
      int_swSetProf31            <= 1'b0;
      int_swSetProf30            <= 1'b0;
      int_swSetProf29            <= 1'b0;
      int_swSetProf28            <= 1'b0;
      int_swSetProf27            <= 1'b0;
      int_swSetProf26            <= 1'b0;
      int_swSetProf25            <= 1'b0;
      int_swSetProf24            <= 1'b0;
      int_swSetProf23            <= 1'b0;
      int_swSetProf22            <= 1'b0;
      int_swSetProf21            <= 1'b0;
      int_swSetProf20            <= 1'b0;
      int_swSetProf19            <= 1'b0;
      int_swSetProf18            <= 1'b0;
      int_swSetProf17            <= 1'b0;
      int_swSetProf16            <= 1'b0;
      int_swSetProf15            <= 1'b0;
      int_swSetProf14            <= 1'b0;
      int_swSetProf13            <= 1'b0;
      int_swSetProf12            <= 1'b0;
      int_swSetProf11            <= 1'b0;
      int_swSetProf10            <= 1'b0;
      int_swSetProf9             <= 1'b0;
      int_swSetProf8             <= 1'b0;
      int_swSetProf7             <= 1'b0;
      int_swSetProf6             <= 1'b0;
      int_swSetProf5             <= 1'b0;
      int_swSetProf4             <= 1'b0;
      int_swSetProf3             <= 1'b0;
      int_swSetProf2             <= 1'b0;
      int_swSetProf1             <= 1'b0;
      int_swSetProf0             <= 1'b0;
      //$port_g SWCLEARPROFILINGREG register.
      int_swClearProf31          <= 1'b0;
      int_swClearProf30          <= 1'b0;
      int_swClearProf29          <= 1'b0;
      int_swClearProf28          <= 1'b0;
      int_swClearProf27          <= 1'b0;
      int_swClearProf26          <= 1'b0;
      int_swClearProf25          <= 1'b0;
      int_swClearProf24          <= 1'b0;
      int_swClearProf23          <= 1'b0;
      int_swClearProf22          <= 1'b0;
      int_swClearProf21          <= 1'b0;
      int_swClearProf20          <= 1'b0;
      int_swClearProf19          <= 1'b0;
      int_swClearProf18          <= 1'b0;
      int_swClearProf17          <= 1'b0;
      int_swClearProf16          <= 1'b0;
      int_swClearProf15          <= 1'b0;
      int_swClearProf14          <= 1'b0;
      int_swClearProf13          <= 1'b0;
      int_swClearProf12          <= 1'b0;
      int_swClearProf11          <= 1'b0;
      int_swClearProf10          <= 1'b0;
      int_swClearProf9           <= 1'b0;
      int_swClearProf8           <= 1'b0;
      int_swClearProf7           <= 1'b0;
      int_swClearProf6           <= 1'b0;
      int_swClearProf5           <= 1'b0;
      int_swClearProf4           <= 1'b0;
      int_swClearProf3           <= 1'b0;
      int_swClearProf2           <= 1'b0;
      int_swClearProf1           <= 1'b0;
      int_swClearProf0           <= 1'b0;
    end
    else if (!softRstClk_n) 
    begin
	
      //$port_g DOZECNTRL2REG register.
      int_wakeUpFromDoze         <= 1'b0;
      int_wakeUpSW               <= 1'b1;
      //$port_g MACCNTRL2REG register.
      int_softReset              <= 1'b0;
      //$port_g GENINTEVENTSETREG register.
      int_setrxPayloadDMADead    <= 1'b0;
      int_setrxHeaderDMADead     <= 1'b0;
      int_setphyRxStart          <= 1'b0;
      int_setphyErr              <= 1'b0;
      int_setmacPHYIFUnderRun    <= 1'b0;
      int_sethwErr               <= 1'b0;
      int_setimpSecDTIM          <= 1'b0;
      int_setimpPriDTIM          <= 1'b0;
      int_setbcnTxDMADead        <= 1'b0;
      int_setac3TxDMADead        <= 1'b0;
      int_setac2TxDMADead        <= 1'b0;
      int_setac1TxDMADead        <= 1'b0;
      int_setac0TxDMADead        <= 1'b0;
      int_setptError             <= 1'b0;
      int_settimSet              <= 1'b0;
      int_setolbcDSSS            <= 1'b0;
      int_setolbcOFDM            <= 1'b0;
      int_setrxFIFOOverFlow      <= 1'b0;
      int_setrxDMAEmpty          <= 1'b0;
      int_setmacPHYIFOverflow    <= 1'b0;
      int_absGenTimers           <= 1'b0;
      int_setidleInterrupt       <= 1'b0;
      int_setimpSecTBTT          <= 1'b0;
      int_setimpPriTBTT          <= 1'b0;
      //$port_g GENINTEVENTCLEARREG register.
      int_clearrxPayloadDMADead  <= 1'b0;
      int_clearrxHeaderDMADead   <= 1'b0;
      int_clearphyRxStart        <= 1'b0;
      int_clearphyErr            <= 1'b0;
      int_clearmacPHYIFUnderRun  <= 1'b0;
      int_clearhwErr             <= 1'b0;
      int_clearimpSecDTIM        <= 1'b0;
      int_clearimpPriDTIM        <= 1'b0;
      int_clearbcnTxDMADead      <= 1'b0;
      int_clearac3TxDMADead      <= 1'b0;
      int_clearac2TxDMADead      <= 1'b0;
      int_clearac1TxDMADead      <= 1'b0;
      int_clearac0TxDMADead      <= 1'b0;
      int_clearptError           <= 1'b0;
      int_cleartimSet            <= 1'b0;
      int_clearolbcDSSS          <= 1'b0;
      int_clearolbcOFDM          <= 1'b0;
      int_clearrxFIFOOverFlow    <= 1'b0;
      int_clearrxDMAEmpty        <= 1'b0;
      int_clearmacPHYIFOverflow  <= 1'b0;
      int_clearidleInterrupt     <= 1'b0;
      int_clearimpSecTBTT        <= 1'b0;
      int_clearimpPriTBTT        <= 1'b0;
      //$port_g GENINTUNMASKREG register.
      int_masterGenIntEn         <= 1'b0;
      int_maskrxPayloadDMADead   <= 1'b0;
      int_maskrxHeaderDMADead    <= 1'b0;
      int_maskphyRxStart         <= 1'b0;
      int_maskphyErr             <= 1'b0;
      int_maskmacPHYIFUnderRun   <= 1'b0;
      int_maskhwErr              <= 1'b0;
      int_maskimpSecDTIM         <= 1'b0;
      int_maskimpPriDTIM         <= 1'b0;
      int_maskbcnTxDMADead       <= 1'b0;
      int_maskac3TxDMADead       <= 1'b0;
      int_maskac2TxDMADead       <= 1'b0;
      int_maskac1TxDMADead       <= 1'b0;
      int_maskac0TxDMADead       <= 1'b0;
      int_maskptError            <= 1'b0;
      int_masktimSet             <= 1'b0;
      int_maskolbcDSSS           <= 1'b0;
      int_maskolbcOFDM           <= 1'b0;
      int_maskrxFIFOOverFlow     <= 1'b0;
      int_maskrxDMAEmpty         <= 1'b0;
      int_maskmacPHYIFOverflow   <= 1'b0;
      int_maskabsGenTimers       <= 1'b0;
      int_maskidleInterrupt      <= 1'b0;
      int_maskimpSecTBTT         <= 1'b0;
      int_maskimpPriTBTT         <= 1'b0;
      //$port_g TXRXINTEVENTSETREG register.
      int_setbcnTxBufTrigger     <= 1'b0;
      int_setac3TxBufTrigger     <= 1'b0;
      int_setac2TxBufTrigger     <= 1'b0;
      int_setac1TxBufTrigger     <= 1'b0;
      int_setac0TxBufTrigger     <= 1'b0;
      int_setac3BWDropTrigger    <= 1'b0;
      int_setac2BWDropTrigger    <= 1'b0;
      int_setac1BWDropTrigger    <= 1'b0;
      int_setac0BWDropTrigger    <= 1'b0;
      int_setcounterRxTrigger    <= 1'b0;
      int_setbaRxTrigger         <= 1'b0;
      int_settimerRxTrigger      <= 1'b0;
      int_setrxTrigger           <= 1'b0;
      int_settimerTxTrigger      <= 1'b0;
      int_settxopComplete        <= 1'b0;
      int_setrdTxTrigger         <= 1'b0;
      int_sethccaTxTrigger       <= 1'b0;
      int_setbcnTxTrigger        <= 1'b0;
      int_setac3TxTrigger        <= 1'b0;
      int_setac2TxTrigger        <= 1'b0;
      int_setac1TxTrigger        <= 1'b0;
      int_setac0TxTrigger        <= 1'b0;
      int_setrdProtTrigger       <= 1'b0;
      int_sethccaProtTrigger     <= 1'b0;
      int_setac3ProtTrigger      <= 1'b0;
      int_setac2ProtTrigger      <= 1'b0;
      int_setac1ProtTrigger      <= 1'b0;
      int_setac0ProtTrigger      <= 1'b0;
      //$port_g TXRXINTEVENTCLEARREG register.
      int_clearbcnTxBufTrigger   <= 1'b0;
      int_clearac3TxBufTrigger   <= 1'b0;
      int_clearac2TxBufTrigger   <= 1'b0;
      int_clearac1TxBufTrigger   <= 1'b0;
      int_clearac0TxBufTrigger   <= 1'b0;
      int_clearac3BWDropTrigger  <= 1'b0;
      int_clearac2BWDropTrigger  <= 1'b0;
      int_clearac1BWDropTrigger  <= 1'b0;
      int_clearac0BWDropTrigger  <= 1'b0;
      int_clearcounterRxTrigger  <= 1'b0;
      int_clearbaRxTrigger       <= 1'b0;
      int_cleartimerRxTrigger    <= 1'b0;
      int_clearrxTrigger         <= 1'b0;
      int_cleartimerTxTrigger    <= 1'b0;
      int_cleartxopComplete      <= 1'b0;
      int_clearrdTxTrigger       <= 1'b0;
      int_clearhccaTxTrigger     <= 1'b0;
      int_clearbcnTxTrigger      <= 1'b0;
      int_clearac3TxTrigger      <= 1'b0;
      int_clearac2TxTrigger      <= 1'b0;
      int_clearac1TxTrigger      <= 1'b0;
      int_clearac0TxTrigger      <= 1'b0;
      int_clearrdProtTrigger     <= 1'b0;
      int_clearhccaProtTrigger   <= 1'b0;
      int_clearac3ProtTrigger    <= 1'b0;
      int_clearac2ProtTrigger    <= 1'b0;
      int_clearac1ProtTrigger    <= 1'b0;
      int_clearac0ProtTrigger    <= 1'b0;
      //$port_g TXRXINTUNMASKREG register.
      int_masterTxRxIntEn        <= 1'b0;
      int_maskbcnTxBufTrigger    <= 1'b0;
      int_maskac3TxBufTrigger    <= 1'b0;
      int_maskac2TxBufTrigger    <= 1'b0;
      int_maskac1TxBufTrigger    <= 1'b0;
      int_maskac0TxBufTrigger    <= 1'b0;
      int_maskac3BWDropTrigger   <= 1'b0;
      int_maskac2BWDropTrigger   <= 1'b0;
      int_maskac1BWDropTrigger   <= 1'b0;
      int_maskac0BWDropTrigger   <= 1'b0;
      int_maskcounterRxTrigger   <= 1'b0;
      int_maskbaRxTrigger        <= 1'b0;
      int_masktimerRxTrigger     <= 1'b0;
      int_maskrxTrigger          <= 1'b0;
      int_masktimerTxTrigger     <= 1'b0;
      int_masktxopComplete       <= 1'b0;
      int_maskrdTxTrigger        <= 1'b0;
      int_maskhccaTxTrigger      <= 1'b0;
      int_maskbcnTxTrigger       <= 1'b0;
      int_maskac3TxTrigger       <= 1'b0;
      int_maskac2TxTrigger       <= 1'b0;
      int_maskac1TxTrigger       <= 1'b0;
      int_maskac0TxTrigger       <= 1'b0;
      int_maskrdProtTrigger      <= 1'b0;
      int_maskhccaProtTrigger    <= 1'b0;
      int_maskac3ProtTrigger     <= 1'b0;
      int_maskac2ProtTrigger     <= 1'b0;
      int_maskac1ProtTrigger     <= 1'b0;
      int_maskac0ProtTrigger     <= 1'b0;
      //$port_g TIMERSINTEVENTSETREG register.
      int_setabsTimers9          <= 1'b0;
      int_setabsTimers8          <= 1'b0;
      int_setabsTimers7          <= 1'b0;
      int_setabsTimers6          <= 1'b0;
      int_setabsTimers5          <= 1'b0;
      int_setabsTimers4          <= 1'b0;
      int_setabsTimers3          <= 1'b0;
      int_setabsTimers2          <= 1'b0;
      int_setabsTimers1          <= 1'b0;
      int_setabsTimers0          <= 1'b0;
      //$port_g TIMERSINTEVENTCLEARREG register.
      int_clearabsTimers9        <= 1'b0;
      int_clearabsTimers8        <= 1'b0;
      int_clearabsTimers7        <= 1'b0;
      int_clearabsTimers6        <= 1'b0;
      int_clearabsTimers5        <= 1'b0;
      int_clearabsTimers4        <= 1'b0;
      int_clearabsTimers3        <= 1'b0;
      int_clearabsTimers2        <= 1'b0;
      int_clearabsTimers1        <= 1'b0;
      int_clearabsTimers0        <= 1'b0;
      //$port_g TIMERSINTUNMASKREG register.
      int_maskabsTimers9         <= 1'b0;
      int_maskabsTimers8         <= 1'b0;
      int_maskabsTimers7         <= 1'b0;
      int_maskabsTimers6         <= 1'b0;
      int_maskabsTimers5         <= 1'b0;
      int_maskabsTimers4         <= 1'b0;
      int_maskabsTimers3         <= 1'b0;
      int_maskabsTimers2         <= 1'b0;
      int_maskabsTimers1         <= 1'b0;
      int_maskabsTimers0         <= 1'b0;
      //$port_g TSFLOREG register.
      int_tsfTimerLow            <= 32'b0000000000000000000000000000000;
      //$port_g TSFHIREG register.
      int_tsfTimerHigh           <= 32'b0000000000000000000000000000000;
      //$port_g TIMEONAIRPARAM1REG register.
      int_ppduSTBC               <= 2'b0;
      int_ppduNumExtnSS          <= 2'b0;
      int_ppduShortGI            <= 1'b0;
      int_ppduPreType            <= 3'b00;
      int_ppduBW                 <= 2'b0;
      int_ppduLength             <= 20'b0000000000000000000;
      //$port_g TIMEONAIRPARAM2REG register.
      int_ppduMCSIndex           <= 7'b000000;
      //$port_g TIMEONAIRVALUEREG register.
      int_computeDuration        <= 1'b0;
      //$port_g DMACNTRLSETREG register.
      int_setrxPayloadNewHead    <= 1'b0;
      int_setrxHeaderNewHead     <= 1'b0;
      int_setrxPayloadNewTail    <= 1'b0;
      int_setrxHeaderNewTail     <= 1'b0;
      int_sethaltAC3AfterTXOP    <= 1'b0;
      int_sethaltAC2AfterTXOP    <= 1'b0;
      int_sethaltAC1AfterTXOP    <= 1'b0;
      int_sethaltAC0AfterTXOP    <= 1'b0;
      int_sethaltBcnAfterTXOP    <= 1'b0;
      int_settxAC3NewHead        <= 1'b0;
      int_settxAC2NewHead        <= 1'b0;
      int_settxAC1NewHead        <= 1'b0;
      int_settxAC0NewHead        <= 1'b0;
      int_settxBcnNewHead        <= 1'b0;
      int_settxAC3NewTail        <= 1'b0;
      int_settxAC2NewTail        <= 1'b0;
      int_settxAC1NewTail        <= 1'b0;
      int_settxAC0NewTail        <= 1'b0;
      int_settxBcnNewTail        <= 1'b0;
      //$port_g DMACNTRLCLEARREG register.
      int_clearrxPayloadNewHead  <= 1'b0;
      int_clearrxHeaderNewHead   <= 1'b0;
      int_clearrxPayloadNewTail  <= 1'b0;
      int_clearrxHeaderNewTail   <= 1'b0;
      int_clearhaltAC3AfterTXOP  <= 1'b0;
      int_clearhaltAC2AfterTXOP  <= 1'b0;
      int_clearhaltAC1AfterTXOP  <= 1'b0;
      int_clearhaltAC0AfterTXOP  <= 1'b0;
      int_clearhaltBcnAfterTXOP  <= 1'b0;
      int_cleartxAC3NewHead      <= 1'b0;
      int_cleartxAC2NewHead      <= 1'b0;
      int_cleartxAC1NewHead      <= 1'b0;
      int_cleartxAC0NewHead      <= 1'b0;
      int_cleartxBcnNewHead      <= 1'b0;
      int_cleartxAC3NewTail      <= 1'b0;
      int_cleartxAC2NewTail      <= 1'b0;
      int_cleartxAC1NewTail      <= 1'b0;
      int_cleartxAC0NewTail      <= 1'b0;
      int_cleartxBcnNewTail      <= 1'b0;
      //$port_g TXBCNHEADPTRREG register.
      int_txBcnHeadPtr           <= 32'b0000000000000000000000000000000;
      //$port_g TXAC0HEADPTRREG register.
      int_txAC0HeadPtr           <= 32'b0000000000000000000000000000000;
      //$port_g TXAC1HEADPTRREG register.
      int_txAC1HeadPtr           <= 32'b0000000000000000000000000000000;
      //$port_g TXAC2HEADPTRREG register.
      int_txAC2HeadPtr           <= 32'b0000000000000000000000000000000;
      //$port_g TXAC3HEADPTRREG register.
      int_txAC3HeadPtr           <= 32'b0000000000000000000000000000000;
      //$port_g TXSTRUCTSIZESREG register.
      int_dmaRBDSize             <= 6'd`RBD_SIZE;
      int_dmaRHDSize             <= 6'd`RHD_SIZE;
      int_dmaTBDSize             <= 6'd`TBD_SIZE;
      int_dmaTHDSize             <= 6'd`THD_SIZE;
      int_ptEntrySize            <= 6'd`PT_SIZE;
      //$port_g RXHEADERHEADPTRREG register.
      int_rxHeaderHeadPtr        <= 30'b00000000000000000000000000000;
      int_rxHeaderHeadPtrValid   <= 1'b0;
      //$port_g RXPAYLOADHEADPTRREG register.
      int_rxPayloadHeadPtr       <= 30'b00000000000000000000000000000;
      int_rxPayloadHeadPtrValid  <= 1'b0;
      //$port_g DMATHRESHOLDREG register.
      int_rxFIFOThreshold        <= 8'b0010000;
      int_txFIFOThreshold        <= 8'b0010000;
      //$port_g EDCAACHASDATASETREG register.
      int_setac3HasData          <= 1'b0;
      int_setac2HasData          <= 1'b0;
      int_setac1HasData          <= 1'b0;
      int_setac0HasData          <= 1'b0;
      //$port_g EDCAACHASDATACLEARREG register.
      int_clearac3HasData        <= 1'b0;
      int_clearac2HasData        <= 1'b0;
      int_clearac1HasData        <= 1'b0;
      int_clearac0HasData        <= 1'b0;
      //$port_g SWPROFILINGREG register.
      int_swProf31               <= 1'b0;
      int_swProf30               <= 1'b0;
      int_swProf29               <= 1'b0;
      int_swProf28               <= 1'b0;
      int_swProf27               <= 1'b0;
      int_swProf26               <= 1'b0;
      int_swProf25               <= 1'b0;
      int_swProf24               <= 1'b0;
      int_swProf23               <= 1'b0;
      int_swProf22               <= 1'b0;
      int_swProf21               <= 1'b0;
      int_swProf20               <= 1'b0;
      int_swProf19               <= 1'b0;
      int_swProf18               <= 1'b0;
      int_swProf17               <= 1'b0;
      int_swProf16               <= 1'b0;
      int_swProf15               <= 1'b0;
      int_swProf14               <= 1'b0;
      int_swProf13               <= 1'b0;
      int_swProf12               <= 1'b0;
      int_swProf11               <= 1'b0;
      int_swProf10               <= 1'b0;
      int_swProf9                <= 1'b0;
      int_swProf8                <= 1'b0;
      int_swProf7                <= 1'b0;
      int_swProf6                <= 1'b0;
      int_swProf5                <= 1'b0;
      int_swProf4                <= 1'b0;
      int_swProf3                <= 1'b0;
      int_swProf2                <= 1'b0;
      int_swProf1                <= 1'b0;
      int_swProf0                <= 1'b0;
      //$port_g SWSETPROFILINGREG register.
      int_swSetProf31            <= 1'b0;
      int_swSetProf30            <= 1'b0;
      int_swSetProf29            <= 1'b0;
      int_swSetProf28            <= 1'b0;
      int_swSetProf27            <= 1'b0;
      int_swSetProf26            <= 1'b0;
      int_swSetProf25            <= 1'b0;
      int_swSetProf24            <= 1'b0;
      int_swSetProf23            <= 1'b0;
      int_swSetProf22            <= 1'b0;
      int_swSetProf21            <= 1'b0;
      int_swSetProf20            <= 1'b0;
      int_swSetProf19            <= 1'b0;
      int_swSetProf18            <= 1'b0;
      int_swSetProf17            <= 1'b0;
      int_swSetProf16            <= 1'b0;
      int_swSetProf15            <= 1'b0;
      int_swSetProf14            <= 1'b0;
      int_swSetProf13            <= 1'b0;
      int_swSetProf12            <= 1'b0;
      int_swSetProf11            <= 1'b0;
      int_swSetProf10            <= 1'b0;
      int_swSetProf9             <= 1'b0;
      int_swSetProf8             <= 1'b0;
      int_swSetProf7             <= 1'b0;
      int_swSetProf6             <= 1'b0;
      int_swSetProf5             <= 1'b0;
      int_swSetProf4             <= 1'b0;
      int_swSetProf3             <= 1'b0;
      int_swSetProf2             <= 1'b0;
      int_swSetProf1             <= 1'b0;
      int_swSetProf0             <= 1'b0;
      //$port_g SWCLEARPROFILINGREG register.
      int_swClearProf31          <= 1'b0;
      int_swClearProf30          <= 1'b0;
      int_swClearProf29          <= 1'b0;
      int_swClearProf28          <= 1'b0;
      int_swClearProf27          <= 1'b0;
      int_swClearProf26          <= 1'b0;
      int_swClearProf25          <= 1'b0;
      int_swClearProf24          <= 1'b0;
      int_swClearProf23          <= 1'b0;
      int_swClearProf22          <= 1'b0;
      int_swClearProf21          <= 1'b0;
      int_swClearProf20          <= 1'b0;
      int_swClearProf19          <= 1'b0;
      int_swClearProf18          <= 1'b0;
      int_swClearProf17          <= 1'b0;
      int_swClearProf16          <= 1'b0;
      int_swClearProf15          <= 1'b0;
      int_swClearProf14          <= 1'b0;
      int_swClearProf13          <= 1'b0;
      int_swClearProf12          <= 1'b0;
      int_swClearProf11          <= 1'b0;
      int_swClearProf10          <= 1'b0;
      int_swClearProf9           <= 1'b0;
      int_swClearProf8           <= 1'b0;
      int_swClearProf7           <= 1'b0;
      int_swClearProf6           <= 1'b0;
      int_swClearProf5           <= 1'b0;
      int_swClearProf4           <= 1'b0;
      int_swClearProf3           <= 1'b0;
      int_swClearProf2           <= 1'b0;
      int_swClearProf1           <= 1'b0;
      int_swClearProf0           <= 1'b0;
    end
    else
        begin
          if (tsfTimerLowInValid)
            int_tsfTimerLow            <= tsfTimerLowIn;
          if (tsfTimerHighInValid)
            int_tsfTimerHigh           <= tsfTimerHighIn;
          if (computeDurationInValid)
            int_computeDuration        <= computeDurationIn;
          if (swProf31InValid)
            int_swProf31               <= swProf31In;
          if (swProf30InValid)
            int_swProf30               <= swProf30In;
          if (swProf29InValid)
            int_swProf29               <= swProf29In;
          if (swProf28InValid)
            int_swProf28               <= swProf28In;
          if (swProf27InValid)
            int_swProf27               <= swProf27In;
          if (swProf26InValid)
            int_swProf26               <= swProf26In;
          if (swProf25InValid)
            int_swProf25               <= swProf25In;
          if (swProf24InValid)
            int_swProf24               <= swProf24In;
          if (swProf23InValid)
            int_swProf23               <= swProf23In;
          if (swProf22InValid)
            int_swProf22               <= swProf22In;
          if (swProf21InValid)
            int_swProf21               <= swProf21In;
          if (swProf20InValid)
            int_swProf20               <= swProf20In;
          if (swProf19InValid)
            int_swProf19               <= swProf19In;
          if (swProf18InValid)
            int_swProf18               <= swProf18In;
          if (swProf17InValid)
            int_swProf17               <= swProf17In;
          if (swProf16InValid)
            int_swProf16               <= swProf16In;
          if (swProf15InValid)
            int_swProf15               <= swProf15In;
          if (swProf14InValid)
            int_swProf14               <= swProf14In;
          if (swProf13InValid)
            int_swProf13               <= swProf13In;
          if (swProf12InValid)
            int_swProf12               <= swProf12In;
          if (swProf11InValid)
            int_swProf11               <= swProf11In;
          if (swProf10InValid)
            int_swProf10               <= swProf10In;
          if (swProf9InValid)
            int_swProf9                <= swProf9In;
          if (swProf8InValid)
            int_swProf8                <= swProf8In;
          if (swProf7InValid)
            int_swProf7                <= swProf7In;
          if (swProf6InValid)
            int_swProf6                <= swProf6In;
          if (swProf5InValid)
            int_swProf5                <= swProf5In;
          if (swProf4InValid)
            int_swProf4                <= swProf4In;
          if (swProf3InValid)
            int_swProf3                <= swProf3In;
          if (swProf2InValid)
            int_swProf2                <= swProf2In;
          if (swProf1InValid)
            int_swProf1                <= swProf1In;
          if (swProf0InValid)
            int_swProf0                <= swProf0In;
          if(regSel && regWrite)
          begin
            case(regAddr)
    
              //$port_g Write DOZECNTRL2REG register.
              DOZECNTRL2REG_ADDR_CT : begin
                int_wakeUpFromDoze         <= regWriteData[31];
                int_wakeUpSW               <= regWriteData[0];
              end
    
              //$port_g Write MACCNTRL2REG register.
              MACCNTRL2REG_ADDR_CT : begin
                int_softReset              <= regWriteData[0];
              end
    
              //$port_g Write GENINTEVENTSETREG register.
              GENINTEVENTSETREG_ADDR_CT : begin
                int_setrxPayloadDMADead    <= regWriteData[25];
                int_setrxHeaderDMADead     <= regWriteData[24];
                int_setphyRxStart          <= regWriteData[23];
                int_setphyErr              <= regWriteData[22];
                int_setmacPHYIFUnderRun    <= regWriteData[21];
                int_sethwErr               <= regWriteData[20];
                int_setimpSecDTIM          <= regWriteData[19];
                int_setimpPriDTIM          <= regWriteData[18];
                int_setbcnTxDMADead        <= regWriteData[17];
                int_setac3TxDMADead        <= regWriteData[16];
                int_setac2TxDMADead        <= regWriteData[15];
                int_setac1TxDMADead        <= regWriteData[14];
                int_setac0TxDMADead        <= regWriteData[13];
                int_setptError             <= regWriteData[12];
                int_settimSet              <= regWriteData[11];
                int_setolbcDSSS            <= regWriteData[10];
                int_setolbcOFDM            <= regWriteData[9];
                int_setrxFIFOOverFlow      <= regWriteData[8];
                int_setrxDMAEmpty          <= regWriteData[7];
                int_setmacPHYIFOverflow    <= regWriteData[6];
                int_absGenTimers           <= regWriteData[3];
                int_setidleInterrupt       <= regWriteData[2];
                int_setimpSecTBTT          <= regWriteData[1];
                int_setimpPriTBTT          <= regWriteData[0];
              end
    
              //$port_g Write GENINTEVENTCLEARREG register.
              GENINTEVENTCLEARREG_ADDR_CT : begin
                int_clearrxPayloadDMADead  <= regWriteData[25];
                int_clearrxHeaderDMADead   <= regWriteData[24];
                int_clearphyRxStart        <= regWriteData[23];
                int_clearphyErr            <= regWriteData[22];
                int_clearmacPHYIFUnderRun  <= regWriteData[21];
                int_clearhwErr             <= regWriteData[20];
                int_clearimpSecDTIM        <= regWriteData[19];
                int_clearimpPriDTIM        <= regWriteData[18];
                int_clearbcnTxDMADead      <= regWriteData[17];
                int_clearac3TxDMADead      <= regWriteData[16];
                int_clearac2TxDMADead      <= regWriteData[15];
                int_clearac1TxDMADead      <= regWriteData[14];
                int_clearac0TxDMADead      <= regWriteData[13];
                int_clearptError           <= regWriteData[12];
                int_cleartimSet            <= regWriteData[11];
                int_clearolbcDSSS          <= regWriteData[10];
                int_clearolbcOFDM          <= regWriteData[9];
                int_clearrxFIFOOverFlow    <= regWriteData[8];
                int_clearrxDMAEmpty        <= regWriteData[7];
                int_clearmacPHYIFOverflow  <= regWriteData[6];
                int_clearidleInterrupt     <= regWriteData[2];
                int_clearimpSecTBTT        <= regWriteData[1];
                int_clearimpPriTBTT        <= regWriteData[0];
              end
    
              //$port_g Write GENINTUNMASKREG register.
              GENINTUNMASKREG_ADDR_CT : begin
                int_masterGenIntEn         <= regWriteData[31];
                int_maskrxPayloadDMADead   <= regWriteData[25];
                int_maskrxHeaderDMADead    <= regWriteData[24];
                int_maskphyRxStart         <= regWriteData[23];
                int_maskphyErr             <= regWriteData[22];
                int_maskmacPHYIFUnderRun   <= regWriteData[21];
                int_maskhwErr              <= regWriteData[20];
                int_maskimpSecDTIM         <= regWriteData[19];
                int_maskimpPriDTIM         <= regWriteData[18];
                int_maskbcnTxDMADead       <= regWriteData[17];
                int_maskac3TxDMADead       <= regWriteData[16];
                int_maskac2TxDMADead       <= regWriteData[15];
                int_maskac1TxDMADead       <= regWriteData[14];
                int_maskac0TxDMADead       <= regWriteData[13];
                int_maskptError            <= regWriteData[12];
                int_masktimSet             <= regWriteData[11];
                int_maskolbcDSSS           <= regWriteData[10];
                int_maskolbcOFDM           <= regWriteData[9];
                int_maskrxFIFOOverFlow     <= regWriteData[8];
                int_maskrxDMAEmpty         <= regWriteData[7];
                int_maskmacPHYIFOverflow   <= regWriteData[6];
                int_maskabsGenTimers       <= regWriteData[3];
                int_maskidleInterrupt      <= regWriteData[2];
                int_maskimpSecTBTT         <= regWriteData[1];
                int_maskimpPriTBTT         <= regWriteData[0];
              end
    
              //$port_g Write TXRXINTEVENTSETREG register.
              TXRXINTEVENTSETREG_ADDR_CT : begin
                int_setbcnTxBufTrigger     <= regWriteData[28];
                int_setac3TxBufTrigger     <= regWriteData[27];
                int_setac2TxBufTrigger     <= regWriteData[26];
                int_setac1TxBufTrigger     <= regWriteData[25];
                int_setac0TxBufTrigger     <= regWriteData[24];
                int_setac3BWDropTrigger    <= regWriteData[23];
                int_setac2BWDropTrigger    <= regWriteData[22];
                int_setac1BWDropTrigger    <= regWriteData[21];
                int_setac0BWDropTrigger    <= regWriteData[20];
                int_setcounterRxTrigger    <= regWriteData[19];
                int_setbaRxTrigger         <= regWriteData[18];
                int_settimerRxTrigger      <= regWriteData[17];
                int_setrxTrigger           <= regWriteData[16];
                int_settimerTxTrigger      <= regWriteData[14];
                int_settxopComplete        <= regWriteData[13];
                int_setrdTxTrigger         <= regWriteData[12];
                int_sethccaTxTrigger       <= regWriteData[11];
                int_setbcnTxTrigger        <= regWriteData[10];
                int_setac3TxTrigger        <= regWriteData[9];
                int_setac2TxTrigger        <= regWriteData[8];
                int_setac1TxTrigger        <= regWriteData[7];
                int_setac0TxTrigger        <= regWriteData[6];
                int_setrdProtTrigger       <= regWriteData[5];
                int_sethccaProtTrigger     <= regWriteData[4];
                int_setac3ProtTrigger      <= regWriteData[3];
                int_setac2ProtTrigger      <= regWriteData[2];
                int_setac1ProtTrigger      <= regWriteData[1];
                int_setac0ProtTrigger      <= regWriteData[0];
              end
    
              //$port_g Write TXRXINTEVENTCLEARREG register.
              TXRXINTEVENTCLEARREG_ADDR_CT : begin
                int_clearbcnTxBufTrigger   <= regWriteData[28];
                int_clearac3TxBufTrigger   <= regWriteData[27];
                int_clearac2TxBufTrigger   <= regWriteData[26];
                int_clearac1TxBufTrigger   <= regWriteData[25];
                int_clearac0TxBufTrigger   <= regWriteData[24];
                int_clearac3BWDropTrigger  <= regWriteData[23];
                int_clearac2BWDropTrigger  <= regWriteData[22];
                int_clearac1BWDropTrigger  <= regWriteData[21];
                int_clearac0BWDropTrigger  <= regWriteData[20];
                int_clearcounterRxTrigger  <= regWriteData[19];
                int_clearbaRxTrigger       <= regWriteData[18];
                int_cleartimerRxTrigger    <= regWriteData[17];
                int_clearrxTrigger         <= regWriteData[16];
                int_cleartimerTxTrigger    <= regWriteData[14];
                int_cleartxopComplete      <= regWriteData[13];
                int_clearrdTxTrigger       <= regWriteData[12];
                int_clearhccaTxTrigger     <= regWriteData[11];
                int_clearbcnTxTrigger      <= regWriteData[10];
                int_clearac3TxTrigger      <= regWriteData[9];
                int_clearac2TxTrigger      <= regWriteData[8];
                int_clearac1TxTrigger      <= regWriteData[7];
                int_clearac0TxTrigger      <= regWriteData[6];
                int_clearrdProtTrigger     <= regWriteData[5];
                int_clearhccaProtTrigger   <= regWriteData[4];
                int_clearac3ProtTrigger    <= regWriteData[3];
                int_clearac2ProtTrigger    <= regWriteData[2];
                int_clearac1ProtTrigger    <= regWriteData[1];
                int_clearac0ProtTrigger    <= regWriteData[0];
              end
    
              //$port_g Write TXRXINTUNMASKREG register.
              TXRXINTUNMASKREG_ADDR_CT : begin
                int_masterTxRxIntEn        <= regWriteData[31];
                int_maskbcnTxBufTrigger    <= regWriteData[28];
                int_maskac3TxBufTrigger    <= regWriteData[27];
                int_maskac2TxBufTrigger    <= regWriteData[26];
                int_maskac1TxBufTrigger    <= regWriteData[25];
                int_maskac0TxBufTrigger    <= regWriteData[24];
                int_maskac3BWDropTrigger   <= regWriteData[23];
                int_maskac2BWDropTrigger   <= regWriteData[22];
                int_maskac1BWDropTrigger   <= regWriteData[21];
                int_maskac0BWDropTrigger   <= regWriteData[20];
                int_maskcounterRxTrigger   <= regWriteData[19];
                int_maskbaRxTrigger        <= regWriteData[18];
                int_masktimerRxTrigger     <= regWriteData[17];
                int_maskrxTrigger          <= regWriteData[16];
                int_masktimerTxTrigger     <= regWriteData[14];
                int_masktxopComplete       <= regWriteData[13];
                int_maskrdTxTrigger        <= regWriteData[12];
                int_maskhccaTxTrigger      <= regWriteData[11];
                int_maskbcnTxTrigger       <= regWriteData[10];
                int_maskac3TxTrigger       <= regWriteData[9];
                int_maskac2TxTrigger       <= regWriteData[8];
                int_maskac1TxTrigger       <= regWriteData[7];
                int_maskac0TxTrigger       <= regWriteData[6];
                int_maskrdProtTrigger      <= regWriteData[5];
                int_maskhccaProtTrigger    <= regWriteData[4];
                int_maskac3ProtTrigger     <= regWriteData[3];
                int_maskac2ProtTrigger     <= regWriteData[2];
                int_maskac1ProtTrigger     <= regWriteData[1];
                int_maskac0ProtTrigger     <= regWriteData[0];
              end
    
              //$port_g Write TIMERSINTEVENTSETREG register.
              TIMERSINTEVENTSETREG_ADDR_CT : begin
                int_setabsTimers9          <= regWriteData[9];
                int_setabsTimers8          <= regWriteData[8];
                int_setabsTimers7          <= regWriteData[7];
                int_setabsTimers6          <= regWriteData[6];
                int_setabsTimers5          <= regWriteData[5];
                int_setabsTimers4          <= regWriteData[4];
                int_setabsTimers3          <= regWriteData[3];
                int_setabsTimers2          <= regWriteData[2];
                int_setabsTimers1          <= regWriteData[1];
                int_setabsTimers0          <= regWriteData[0];
              end
    
              //$port_g Write TIMERSINTEVENTCLEARREG register.
              TIMERSINTEVENTCLEARREG_ADDR_CT : begin
                int_clearabsTimers9        <= regWriteData[9];
                int_clearabsTimers8        <= regWriteData[8];
                int_clearabsTimers7        <= regWriteData[7];
                int_clearabsTimers6        <= regWriteData[6];
                int_clearabsTimers5        <= regWriteData[5];
                int_clearabsTimers4        <= regWriteData[4];
                int_clearabsTimers3        <= regWriteData[3];
                int_clearabsTimers2        <= regWriteData[2];
                int_clearabsTimers1        <= regWriteData[1];
                int_clearabsTimers0        <= regWriteData[0];
              end
    
              //$port_g Write TIMERSINTUNMASKREG register.
              TIMERSINTUNMASKREG_ADDR_CT : begin
                int_maskabsTimers9         <= regWriteData[9];
                int_maskabsTimers8         <= regWriteData[8];
                int_maskabsTimers7         <= regWriteData[7];
                int_maskabsTimers6         <= regWriteData[6];
                int_maskabsTimers5         <= regWriteData[5];
                int_maskabsTimers4         <= regWriteData[4];
                int_maskabsTimers3         <= regWriteData[3];
                int_maskabsTimers2         <= regWriteData[2];
                int_maskabsTimers1         <= regWriteData[1];
                int_maskabsTimers0         <= regWriteData[0];
              end
    
              //$port_g Write TSFLOREG register.
              TSFLOREG_ADDR_CT : begin
                int_tsfTimerLow            <= regWriteData[31 : 0];
              end
    
              //$port_g Write TSFHIREG register.
              TSFHIREG_ADDR_CT : begin
                int_tsfTimerHigh           <= regWriteData[31 : 0];
              end
    
              //$port_g Write TIMEONAIRPARAM1REG register.
              TIMEONAIRPARAM1REG_ADDR_CT : begin
                int_ppduSTBC               <= regWriteData[31 : 30];
                int_ppduNumExtnSS          <= regWriteData[29 : 28];
                int_ppduShortGI            <= regWriteData[27];
                int_ppduPreType            <= regWriteData[26 : 24];
                int_ppduBW                 <= regWriteData[23 : 22];
                int_ppduLength             <= regWriteData[19 : 0];
              end
    
              //$port_g Write TIMEONAIRPARAM2REG register.
              TIMEONAIRPARAM2REG_ADDR_CT : begin
                int_ppduMCSIndex           <= regWriteData[6 : 0];
              end
    
              //$port_g Write TIMEONAIRVALUEREG register.
              TIMEONAIRVALUEREG_ADDR_CT : begin
                int_computeDuration        <= regWriteData[31];
              end
    
              //$port_g Write DMACNTRLSETREG register.
              DMACNTRLSETREG_ADDR_CT : begin
                int_setrxPayloadNewHead    <= regWriteData[27];
                int_setrxHeaderNewHead     <= regWriteData[26];
                int_setrxPayloadNewTail    <= regWriteData[25];
                int_setrxHeaderNewTail     <= regWriteData[24];
                int_sethaltAC3AfterTXOP    <= regWriteData[19];
                int_sethaltAC2AfterTXOP    <= regWriteData[18];
                int_sethaltAC1AfterTXOP    <= regWriteData[17];
                int_sethaltAC0AfterTXOP    <= regWriteData[16];
                int_sethaltBcnAfterTXOP    <= regWriteData[15];
                int_settxAC3NewHead        <= regWriteData[12];
                int_settxAC2NewHead        <= regWriteData[11];
                int_settxAC1NewHead        <= regWriteData[10];
                int_settxAC0NewHead        <= regWriteData[9];
                int_settxBcnNewHead        <= regWriteData[8];
                int_settxAC3NewTail        <= regWriteData[4];
                int_settxAC2NewTail        <= regWriteData[3];
                int_settxAC1NewTail        <= regWriteData[2];
                int_settxAC0NewTail        <= regWriteData[1];
                int_settxBcnNewTail        <= regWriteData[0];
              end
    
              //$port_g Write DMACNTRLCLEARREG register.
              DMACNTRLCLEARREG_ADDR_CT : begin
                int_clearrxPayloadNewHead  <= regWriteData[27];
                int_clearrxHeaderNewHead   <= regWriteData[26];
                int_clearrxPayloadNewTail  <= regWriteData[25];
                int_clearrxHeaderNewTail   <= regWriteData[24];
                int_clearhaltAC3AfterTXOP  <= regWriteData[19];
                int_clearhaltAC2AfterTXOP  <= regWriteData[18];
                int_clearhaltAC1AfterTXOP  <= regWriteData[17];
                int_clearhaltAC0AfterTXOP  <= regWriteData[16];
                int_clearhaltBcnAfterTXOP  <= regWriteData[15];
                int_cleartxAC3NewHead      <= regWriteData[12];
                int_cleartxAC2NewHead      <= regWriteData[11];
                int_cleartxAC1NewHead      <= regWriteData[10];
                int_cleartxAC0NewHead      <= regWriteData[9];
                int_cleartxBcnNewHead      <= regWriteData[8];
                int_cleartxAC3NewTail      <= regWriteData[4];
                int_cleartxAC2NewTail      <= regWriteData[3];
                int_cleartxAC1NewTail      <= regWriteData[2];
                int_cleartxAC0NewTail      <= regWriteData[1];
                int_cleartxBcnNewTail      <= regWriteData[0];
              end
    
              //$port_g Write TXBCNHEADPTRREG register.
              TXBCNHEADPTRREG_ADDR_CT : begin
                int_txBcnHeadPtr           <= regWriteData[31 : 0];
              end
    
              //$port_g Write TXAC0HEADPTRREG register.
              TXAC0HEADPTRREG_ADDR_CT : begin
                int_txAC0HeadPtr           <= regWriteData[31 : 0];
              end
    
              //$port_g Write TXAC1HEADPTRREG register.
              TXAC1HEADPTRREG_ADDR_CT : begin
                int_txAC1HeadPtr           <= regWriteData[31 : 0];
              end
    
              //$port_g Write TXAC2HEADPTRREG register.
              TXAC2HEADPTRREG_ADDR_CT : begin
                int_txAC2HeadPtr           <= regWriteData[31 : 0];
              end
    
              //$port_g Write TXAC3HEADPTRREG register.
              TXAC3HEADPTRREG_ADDR_CT : begin
                int_txAC3HeadPtr           <= regWriteData[31 : 0];
              end
    
              //$port_g Write TXSTRUCTSIZESREG register.
              TXSTRUCTSIZESREG_ADDR_CT : begin
                int_dmaRBDSize             <= regWriteData[29 : 24];
                int_dmaRHDSize             <= regWriteData[23 : 18];
                int_dmaTBDSize             <= regWriteData[17 : 12];
                int_dmaTHDSize             <= regWriteData[11 : 6];
                int_ptEntrySize            <= regWriteData[5 : 0];
              end
    
              //$port_g Write RXHEADERHEADPTRREG register.
              RXHEADERHEADPTRREG_ADDR_CT : begin
                int_rxHeaderHeadPtr        <= regWriteData[31 : 2];
                int_rxHeaderHeadPtrValid   <= regWriteData[0];
              end
    
              //$port_g Write RXPAYLOADHEADPTRREG register.
              RXPAYLOADHEADPTRREG_ADDR_CT : begin
                int_rxPayloadHeadPtr       <= regWriteData[31 : 2];
                int_rxPayloadHeadPtrValid  <= regWriteData[0];
              end
    
              //$port_g Write DMATHRESHOLDREG register.
              DMATHRESHOLDREG_ADDR_CT : begin
                int_rxFIFOThreshold        <= regWriteData[23 : 16];
                int_txFIFOThreshold        <= regWriteData[7 : 0];
              end
    
              //$port_g Write EDCAACHASDATASETREG register.
              EDCAACHASDATASETREG_ADDR_CT : begin
                int_setac3HasData          <= regWriteData[3];
                int_setac2HasData          <= regWriteData[2];
                int_setac1HasData          <= regWriteData[1];
                int_setac0HasData          <= regWriteData[0];
              end
    
              //$port_g Write EDCAACHASDATACLEARREG register.
              EDCAACHASDATACLEARREG_ADDR_CT : begin
                int_clearac3HasData        <= regWriteData[3];
                int_clearac2HasData        <= regWriteData[2];
                int_clearac1HasData        <= regWriteData[1];
                int_clearac0HasData        <= regWriteData[0];
              end
    
              //$port_g Write SWPROFILINGREG register.
              SWPROFILINGREG_ADDR_CT : begin
                int_swProf31               <= regWriteData[31];
                int_swProf30               <= regWriteData[30];
                int_swProf29               <= regWriteData[29];
                int_swProf28               <= regWriteData[28];
                int_swProf27               <= regWriteData[27];
                int_swProf26               <= regWriteData[26];
                int_swProf25               <= regWriteData[25];
                int_swProf24               <= regWriteData[24];
                int_swProf23               <= regWriteData[23];
                int_swProf22               <= regWriteData[22];
                int_swProf21               <= regWriteData[21];
                int_swProf20               <= regWriteData[20];
                int_swProf19               <= regWriteData[19];
                int_swProf18               <= regWriteData[18];
                int_swProf17               <= regWriteData[17];
                int_swProf16               <= regWriteData[16];
                int_swProf15               <= regWriteData[15];
                int_swProf14               <= regWriteData[14];
                int_swProf13               <= regWriteData[13];
                int_swProf12               <= regWriteData[12];
                int_swProf11               <= regWriteData[11];
                int_swProf10               <= regWriteData[10];
                int_swProf9                <= regWriteData[9];
                int_swProf8                <= regWriteData[8];
                int_swProf7                <= regWriteData[7];
                int_swProf6                <= regWriteData[6];
                int_swProf5                <= regWriteData[5];
                int_swProf4                <= regWriteData[4];
                int_swProf3                <= regWriteData[3];
                int_swProf2                <= regWriteData[2];
                int_swProf1                <= regWriteData[1];
                int_swProf0                <= regWriteData[0];
              end
    
              //$port_g Write SWSETPROFILINGREG register.
              SWSETPROFILINGREG_ADDR_CT : begin
                int_swSetProf31            <= regWriteData[31];
                int_swSetProf30            <= regWriteData[30];
                int_swSetProf29            <= regWriteData[29];
                int_swSetProf28            <= regWriteData[28];
                int_swSetProf27            <= regWriteData[27];
                int_swSetProf26            <= regWriteData[26];
                int_swSetProf25            <= regWriteData[25];
                int_swSetProf24            <= regWriteData[24];
                int_swSetProf23            <= regWriteData[23];
                int_swSetProf22            <= regWriteData[22];
                int_swSetProf21            <= regWriteData[21];
                int_swSetProf20            <= regWriteData[20];
                int_swSetProf19            <= regWriteData[19];
                int_swSetProf18            <= regWriteData[18];
                int_swSetProf17            <= regWriteData[17];
                int_swSetProf16            <= regWriteData[16];
                int_swSetProf15            <= regWriteData[15];
                int_swSetProf14            <= regWriteData[14];
                int_swSetProf13            <= regWriteData[13];
                int_swSetProf12            <= regWriteData[12];
                int_swSetProf11            <= regWriteData[11];
                int_swSetProf10            <= regWriteData[10];
                int_swSetProf9             <= regWriteData[9];
                int_swSetProf8             <= regWriteData[8];
                int_swSetProf7             <= regWriteData[7];
                int_swSetProf6             <= regWriteData[6];
                int_swSetProf5             <= regWriteData[5];
                int_swSetProf4             <= regWriteData[4];
                int_swSetProf3             <= regWriteData[3];
                int_swSetProf2             <= regWriteData[2];
                int_swSetProf1             <= regWriteData[1];
                int_swSetProf0             <= regWriteData[0];
              end
    
              //$port_g Write SWCLEARPROFILINGREG register.
              SWCLEARPROFILINGREG_ADDR_CT : begin
                int_swClearProf31          <= regWriteData[31];
                int_swClearProf30          <= regWriteData[30];
                int_swClearProf29          <= regWriteData[29];
                int_swClearProf28          <= regWriteData[28];
                int_swClearProf27          <= regWriteData[27];
                int_swClearProf26          <= regWriteData[26];
                int_swClearProf25          <= regWriteData[25];
                int_swClearProf24          <= regWriteData[24];
                int_swClearProf23          <= regWriteData[23];
                int_swClearProf22          <= regWriteData[22];
                int_swClearProf21          <= regWriteData[21];
                int_swClearProf20          <= regWriteData[20];
                int_swClearProf19          <= regWriteData[19];
                int_swClearProf18          <= regWriteData[18];
                int_swClearProf17          <= regWriteData[17];
                int_swClearProf16          <= regWriteData[16];
                int_swClearProf15          <= regWriteData[15];
                int_swClearProf14          <= regWriteData[14];
                int_swClearProf13          <= regWriteData[13];
                int_swClearProf12          <= regWriteData[12];
                int_swClearProf11          <= regWriteData[11];
                int_swClearProf10          <= regWriteData[10];
                int_swClearProf9           <= regWriteData[9];
                int_swClearProf8           <= regWriteData[8];
                int_swClearProf7           <= regWriteData[7];
                int_swClearProf6           <= regWriteData[6];
                int_swClearProf5           <= regWriteData[5];
                int_swClearProf4           <= regWriteData[4];
                int_swClearProf3           <= regWriteData[3];
                int_swClearProf2           <= regWriteData[2];
                int_swClearProf1           <= regWriteData[1];
                int_swClearProf0           <= regWriteData[0];
              end
    
              
              // Disable coverage on the default state because it cannot be reached.
              // pragma coverage block = off 
              default : begin
              end
              // pragma coverage block = on 
    
            endcase
          end
          else begin
            int_setrxPayloadDMADead    <= 1'b0;
            int_setrxHeaderDMADead     <= 1'b0;
            int_setphyRxStart          <= 1'b0;
            int_setphyErr              <= 1'b0;
            int_setmacPHYIFUnderRun    <= 1'b0;
            int_sethwErr               <= 1'b0;
            int_setimpSecDTIM          <= 1'b0;
            int_setimpPriDTIM          <= 1'b0;
            int_setbcnTxDMADead        <= 1'b0;
            int_setac3TxDMADead        <= 1'b0;
            int_setac2TxDMADead        <= 1'b0;
            int_setac1TxDMADead        <= 1'b0;
            int_setac0TxDMADead        <= 1'b0;
            int_setptError             <= 1'b0;
            int_settimSet              <= 1'b0;
            int_setolbcDSSS            <= 1'b0;
            int_setolbcOFDM            <= 1'b0;
            int_setrxFIFOOverFlow      <= 1'b0;
            int_setrxDMAEmpty          <= 1'b0;
            int_setmacPHYIFOverflow    <= 1'b0;
            int_absGenTimers           <= 1'b0;
            int_setidleInterrupt       <= 1'b0;
            int_setimpSecTBTT          <= 1'b0;
            int_setimpPriTBTT          <= 1'b0;
            int_clearrxPayloadDMADead  <= 1'b0;
            int_clearrxHeaderDMADead   <= 1'b0;
            int_clearphyRxStart        <= 1'b0;
            int_clearphyErr            <= 1'b0;
            int_clearmacPHYIFUnderRun  <= 1'b0;
            int_clearhwErr             <= 1'b0;
            int_clearimpSecDTIM        <= 1'b0;
            int_clearimpPriDTIM        <= 1'b0;
            int_clearbcnTxDMADead      <= 1'b0;
            int_clearac3TxDMADead      <= 1'b0;
            int_clearac2TxDMADead      <= 1'b0;
            int_clearac1TxDMADead      <= 1'b0;
            int_clearac0TxDMADead      <= 1'b0;
            int_clearptError           <= 1'b0;
            int_cleartimSet            <= 1'b0;
            int_clearolbcDSSS          <= 1'b0;
            int_clearolbcOFDM          <= 1'b0;
            int_clearrxFIFOOverFlow    <= 1'b0;
            int_clearrxDMAEmpty        <= 1'b0;
            int_clearmacPHYIFOverflow  <= 1'b0;
            int_clearidleInterrupt     <= 1'b0;
            int_clearimpSecTBTT        <= 1'b0;
            int_clearimpPriTBTT        <= 1'b0;
            int_setbcnTxBufTrigger     <= 1'b0;
            int_setac3TxBufTrigger     <= 1'b0;
            int_setac2TxBufTrigger     <= 1'b0;
            int_setac1TxBufTrigger     <= 1'b0;
            int_setac0TxBufTrigger     <= 1'b0;
            int_setac3BWDropTrigger    <= 1'b0;
            int_setac2BWDropTrigger    <= 1'b0;
            int_setac1BWDropTrigger    <= 1'b0;
            int_setac0BWDropTrigger    <= 1'b0;
            int_setcounterRxTrigger    <= 1'b0;
            int_setbaRxTrigger         <= 1'b0;
            int_settimerRxTrigger      <= 1'b0;
            int_setrxTrigger           <= 1'b0;
            int_settimerTxTrigger      <= 1'b0;
            int_settxopComplete        <= 1'b0;
            int_setrdTxTrigger         <= 1'b0;
            int_sethccaTxTrigger       <= 1'b0;
            int_setbcnTxTrigger        <= 1'b0;
            int_setac3TxTrigger        <= 1'b0;
            int_setac2TxTrigger        <= 1'b0;
            int_setac1TxTrigger        <= 1'b0;
            int_setac0TxTrigger        <= 1'b0;
            int_setrdProtTrigger       <= 1'b0;
            int_sethccaProtTrigger     <= 1'b0;
            int_setac3ProtTrigger      <= 1'b0;
            int_setac2ProtTrigger      <= 1'b0;
            int_setac1ProtTrigger      <= 1'b0;
            int_setac0ProtTrigger      <= 1'b0;
            int_clearbcnTxBufTrigger   <= 1'b0;
            int_clearac3TxBufTrigger   <= 1'b0;
            int_clearac2TxBufTrigger   <= 1'b0;
            int_clearac1TxBufTrigger   <= 1'b0;
            int_clearac0TxBufTrigger   <= 1'b0;
            int_clearac3BWDropTrigger  <= 1'b0;
            int_clearac2BWDropTrigger  <= 1'b0;
            int_clearac1BWDropTrigger  <= 1'b0;
            int_clearac0BWDropTrigger  <= 1'b0;
            int_clearcounterRxTrigger  <= 1'b0;
            int_clearbaRxTrigger       <= 1'b0;
            int_cleartimerRxTrigger    <= 1'b0;
            int_clearrxTrigger         <= 1'b0;
            int_cleartimerTxTrigger    <= 1'b0;
            int_cleartxopComplete      <= 1'b0;
            int_clearrdTxTrigger       <= 1'b0;
            int_clearhccaTxTrigger     <= 1'b0;
            int_clearbcnTxTrigger      <= 1'b0;
            int_clearac3TxTrigger      <= 1'b0;
            int_clearac2TxTrigger      <= 1'b0;
            int_clearac1TxTrigger      <= 1'b0;
            int_clearac0TxTrigger      <= 1'b0;
            int_clearrdProtTrigger     <= 1'b0;
            int_clearhccaProtTrigger   <= 1'b0;
            int_clearac3ProtTrigger    <= 1'b0;
            int_clearac2ProtTrigger    <= 1'b0;
            int_clearac1ProtTrigger    <= 1'b0;
            int_clearac0ProtTrigger    <= 1'b0;
            int_setabsTimers9          <= 1'b0;
            int_setabsTimers8          <= 1'b0;
            int_setabsTimers7          <= 1'b0;
            int_setabsTimers6          <= 1'b0;
            int_setabsTimers5          <= 1'b0;
            int_setabsTimers4          <= 1'b0;
            int_setabsTimers3          <= 1'b0;
            int_setabsTimers2          <= 1'b0;
            int_setabsTimers1          <= 1'b0;
            int_setabsTimers0          <= 1'b0;
            int_clearabsTimers9        <= 1'b0;
            int_clearabsTimers8        <= 1'b0;
            int_clearabsTimers7        <= 1'b0;
            int_clearabsTimers6        <= 1'b0;
            int_clearabsTimers5        <= 1'b0;
            int_clearabsTimers4        <= 1'b0;
            int_clearabsTimers3        <= 1'b0;
            int_clearabsTimers2        <= 1'b0;
            int_clearabsTimers1        <= 1'b0;
            int_clearabsTimers0        <= 1'b0;
            int_setrxPayloadNewHead    <= 1'b0;
            int_setrxHeaderNewHead     <= 1'b0;
            int_setrxPayloadNewTail    <= 1'b0;
            int_setrxHeaderNewTail     <= 1'b0;
            int_sethaltAC3AfterTXOP    <= 1'b0;
            int_sethaltAC2AfterTXOP    <= 1'b0;
            int_sethaltAC1AfterTXOP    <= 1'b0;
            int_sethaltAC0AfterTXOP    <= 1'b0;
            int_sethaltBcnAfterTXOP    <= 1'b0;
            int_settxAC3NewHead        <= 1'b0;
            int_settxAC2NewHead        <= 1'b0;
            int_settxAC1NewHead        <= 1'b0;
            int_settxAC0NewHead        <= 1'b0;
            int_settxBcnNewHead        <= 1'b0;
            int_settxAC3NewTail        <= 1'b0;
            int_settxAC2NewTail        <= 1'b0;
            int_settxAC1NewTail        <= 1'b0;
            int_settxAC0NewTail        <= 1'b0;
            int_settxBcnNewTail        <= 1'b0;
            int_clearrxPayloadNewHead  <= 1'b0;
            int_clearrxHeaderNewHead   <= 1'b0;
            int_clearrxPayloadNewTail  <= 1'b0;
            int_clearrxHeaderNewTail   <= 1'b0;
            int_clearhaltAC3AfterTXOP  <= 1'b0;
            int_clearhaltAC2AfterTXOP  <= 1'b0;
            int_clearhaltAC1AfterTXOP  <= 1'b0;
            int_clearhaltAC0AfterTXOP  <= 1'b0;
            int_clearhaltBcnAfterTXOP  <= 1'b0;
            int_cleartxAC3NewHead      <= 1'b0;
            int_cleartxAC2NewHead      <= 1'b0;
            int_cleartxAC1NewHead      <= 1'b0;
            int_cleartxAC0NewHead      <= 1'b0;
            int_cleartxBcnNewHead      <= 1'b0;
            int_cleartxAC3NewTail      <= 1'b0;
            int_cleartxAC2NewTail      <= 1'b0;
            int_cleartxAC1NewTail      <= 1'b0;
            int_cleartxAC0NewTail      <= 1'b0;
            int_cleartxBcnNewTail      <= 1'b0;
            int_setac3HasData          <= 1'b0;
            int_setac2HasData          <= 1'b0;
            int_setac1HasData          <= 1'b0;
            int_setac0HasData          <= 1'b0;
            int_clearac3HasData        <= 1'b0;
            int_clearac2HasData        <= 1'b0;
            int_clearac1HasData        <= 1'b0;
            int_clearac0HasData        <= 1'b0;
            int_swSetProf31            <= 1'b0;
            int_swSetProf30            <= 1'b0;
            int_swSetProf29            <= 1'b0;
            int_swSetProf28            <= 1'b0;
            int_swSetProf27            <= 1'b0;
            int_swSetProf26            <= 1'b0;
            int_swSetProf25            <= 1'b0;
            int_swSetProf24            <= 1'b0;
            int_swSetProf23            <= 1'b0;
            int_swSetProf22            <= 1'b0;
            int_swSetProf21            <= 1'b0;
            int_swSetProf20            <= 1'b0;
            int_swSetProf19            <= 1'b0;
            int_swSetProf18            <= 1'b0;
            int_swSetProf17            <= 1'b0;
            int_swSetProf16            <= 1'b0;
            int_swSetProf15            <= 1'b0;
            int_swSetProf14            <= 1'b0;
            int_swSetProf13            <= 1'b0;
            int_swSetProf12            <= 1'b0;
            int_swSetProf11            <= 1'b0;
            int_swSetProf10            <= 1'b0;
            int_swSetProf9             <= 1'b0;
            int_swSetProf8             <= 1'b0;
            int_swSetProf7             <= 1'b0;
            int_swSetProf6             <= 1'b0;
            int_swSetProf5             <= 1'b0;
            int_swSetProf4             <= 1'b0;
            int_swSetProf3             <= 1'b0;
            int_swSetProf2             <= 1'b0;
            int_swSetProf1             <= 1'b0;
            int_swSetProf0             <= 1'b0;
            int_swClearProf31          <= 1'b0;
            int_swClearProf30          <= 1'b0;
            int_swClearProf29          <= 1'b0;
            int_swClearProf28          <= 1'b0;
            int_swClearProf27          <= 1'b0;
            int_swClearProf26          <= 1'b0;
            int_swClearProf25          <= 1'b0;
            int_swClearProf24          <= 1'b0;
            int_swClearProf23          <= 1'b0;
            int_swClearProf22          <= 1'b0;
            int_swClearProf21          <= 1'b0;
            int_swClearProf20          <= 1'b0;
            int_swClearProf19          <= 1'b0;
            int_swClearProf18          <= 1'b0;
            int_swClearProf17          <= 1'b0;
            int_swClearProf16          <= 1'b0;
            int_swClearProf15          <= 1'b0;
            int_swClearProf14          <= 1'b0;
            int_swClearProf13          <= 1'b0;
            int_swClearProf12          <= 1'b0;
            int_swClearProf11          <= 1'b0;
            int_swClearProf10          <= 1'b0;
            int_swClearProf9           <= 1'b0;
            int_swClearProf8           <= 1'b0;
            int_swClearProf7           <= 1'b0;
            int_swClearProf6           <= 1'b0;
            int_swClearProf5           <= 1'b0;
            int_swClearProf4           <= 1'b0;
            int_swClearProf3           <= 1'b0;
            int_swClearProf2           <= 1'b0;
            int_swClearProf1           <= 1'b0;
            int_swClearProf0           <= 1'b0;
          end
        end
      end
            
      //////////////////////////////////////////////////////////////////////////////
      // Registers read
      //////////////////////////////////////////////////////////////////////////////
      //Read_p: 
      
      always @*
      begin
    
        regReadData = `RW_REG_DATA_WIDTH'b0;
        // Test only psel to detect first cycle of the two-cycles APB read access.
        if (regSel && regRead)
        begin
    
          case (regAddr)
    
            //$port_g Read NEXTTBTTREG register.
            NEXTTBTTREG_ADDR_CT : begin
              regReadData[15 : 0]        = nextTBTT;
            end
    
            //$port_g Read DOZECNTRL2REG register.
            DOZECNTRL2REG_ADDR_CT : begin
              regReadData[31]            = wakeUpFromDoze;
              regReadData[0]             = wakeUpSW;
            end
    
            //$port_g Read MACCNTRL2REG register.
            MACCNTRL2REG_ADDR_CT : begin
              regReadData[0]             = softReset;
            end
    
            //$port_g Read GENINTEVENTSETREG register.
            GENINTEVENTSETREG_ADDR_CT : begin
              regReadData[25]            = statussetrxPayloadDMADead;
              regReadData[24]            = statussetrxHeaderDMADead;
              regReadData[23]            = statussetphyRxStart;
              regReadData[22]            = statussetphyErr;
              regReadData[21]            = statussetmacPHYIFUnderRun;
              regReadData[20]            = statussethwErr;
              regReadData[19]            = statussetimpSecDTIM;
              regReadData[18]            = statussetimpPriDTIM;
              regReadData[17]            = statussetbcnTxDMADead;
              regReadData[16]            = statussetac3TxDMADead;
              regReadData[15]            = statussetac2TxDMADead;
              regReadData[14]            = statussetac1TxDMADead;
              regReadData[13]            = statussetac0TxDMADead;
              regReadData[12]            = statussetptError;
              regReadData[11]            = statussettimSet;
              regReadData[10]            = statussetolbcDSSS;
              regReadData[9]             = statussetolbcOFDM;
              regReadData[8]             = statussetrxFIFOOverFlow;
              regReadData[7]             = statussetrxDMAEmpty;
              regReadData[6]             = statussetmacPHYIFOverflow;
              regReadData[3]             = statusabsGenTimers;
              regReadData[2]             = statussetidleInterrupt;
              regReadData[1]             = statussetimpSecTBTT;
              regReadData[0]             = statussetimpPriTBTT;
            end
    
            //$port_g Read GENINTEVENTCLEARREG register.
            GENINTEVENTCLEARREG_ADDR_CT : begin
              regReadData[25]            = clearrxPayloadDMADead;
              regReadData[24]            = clearrxHeaderDMADead;
              regReadData[23]            = clearphyRxStart;
              regReadData[22]            = clearphyErr;
              regReadData[21]            = clearmacPHYIFUnderRun;
              regReadData[20]            = clearhwErr;
              regReadData[19]            = clearimpSecDTIM;
              regReadData[18]            = clearimpPriDTIM;
              regReadData[17]            = clearbcnTxDMADead;
              regReadData[16]            = clearac3TxDMADead;
              regReadData[15]            = clearac2TxDMADead;
              regReadData[14]            = clearac1TxDMADead;
              regReadData[13]            = clearac0TxDMADead;
              regReadData[12]            = clearptError;
              regReadData[11]            = cleartimSet;
              regReadData[10]            = clearolbcDSSS;
              regReadData[9]             = clearolbcOFDM;
              regReadData[8]             = clearrxFIFOOverFlow;
              regReadData[7]             = clearrxDMAEmpty;
              regReadData[6]             = clearmacPHYIFOverflow;
              regReadData[2]             = clearidleInterrupt;
              regReadData[1]             = clearimpSecTBTT;
              regReadData[0]             = clearimpPriTBTT;
            end
    
            //$port_g Read GENINTUNMASKREG register.
            GENINTUNMASKREG_ADDR_CT : begin
              regReadData[31]            = masterGenIntEn;
              regReadData[25]            = maskrxPayloadDMADead;
              regReadData[24]            = maskrxHeaderDMADead;
              regReadData[23]            = maskphyRxStart;
              regReadData[22]            = maskphyErr;
              regReadData[21]            = maskmacPHYIFUnderRun;
              regReadData[20]            = maskhwErr;
              regReadData[19]            = maskimpSecDTIM;
              regReadData[18]            = maskimpPriDTIM;
              regReadData[17]            = maskbcnTxDMADead;
              regReadData[16]            = maskac3TxDMADead;
              regReadData[15]            = maskac2TxDMADead;
              regReadData[14]            = maskac1TxDMADead;
              regReadData[13]            = maskac0TxDMADead;
              regReadData[12]            = maskptError;
              regReadData[11]            = masktimSet;
              regReadData[10]            = maskolbcDSSS;
              regReadData[9]             = maskolbcOFDM;
              regReadData[8]             = maskrxFIFOOverFlow;
              regReadData[7]             = maskrxDMAEmpty;
              regReadData[6]             = maskmacPHYIFOverflow;
              regReadData[3]             = maskabsGenTimers;
              regReadData[2]             = maskidleInterrupt;
              regReadData[1]             = maskimpSecTBTT;
              regReadData[0]             = maskimpPriTBTT;
            end
    
            //$port_g Read TXRXINTEVENTSETREG register.
            TXRXINTEVENTSETREG_ADDR_CT : begin
              regReadData[28]            = statussetbcnTxBufTrigger;
              regReadData[27]            = statussetac3TxBufTrigger;
              regReadData[26]            = statussetac2TxBufTrigger;
              regReadData[25]            = statussetac1TxBufTrigger;
              regReadData[24]            = statussetac0TxBufTrigger;
              regReadData[23]            = statussetac3BWDropTrigger;
              regReadData[22]            = statussetac2BWDropTrigger;
              regReadData[21]            = statussetac1BWDropTrigger;
              regReadData[20]            = statussetac0BWDropTrigger;
              regReadData[19]            = statussetcounterRxTrigger;
              regReadData[18]            = statussetbaRxTrigger;
              regReadData[17]            = statussettimerRxTrigger;
              regReadData[16]            = statussetrxTrigger;
              regReadData[14]            = statussettimerTxTrigger;
              regReadData[13]            = statussettxopComplete;
              regReadData[12]            = statussetrdTxTrigger;
              regReadData[11]            = statussethccaTxTrigger;
              regReadData[10]            = statussetbcnTxTrigger;
              regReadData[9]             = statussetac3TxTrigger;
              regReadData[8]             = statussetac2TxTrigger;
              regReadData[7]             = statussetac1TxTrigger;
              regReadData[6]             = statussetac0TxTrigger;
              regReadData[5]             = statussetrdProtTrigger;
              regReadData[4]             = statussethccaProtTrigger;
              regReadData[3]             = statussetac3ProtTrigger;
              regReadData[2]             = statussetac2ProtTrigger;
              regReadData[1]             = statussetac1ProtTrigger;
              regReadData[0]             = statussetac0ProtTrigger;
            end
    
            //$port_g Read TXRXINTEVENTCLEARREG register.
            TXRXINTEVENTCLEARREG_ADDR_CT : begin
              regReadData[28]            = clearbcnTxBufTrigger;
              regReadData[27]            = clearac3TxBufTrigger;
              regReadData[26]            = clearac2TxBufTrigger;
              regReadData[25]            = clearac1TxBufTrigger;
              regReadData[24]            = clearac0TxBufTrigger;
              regReadData[23]            = clearac3BWDropTrigger;
              regReadData[22]            = clearac2BWDropTrigger;
              regReadData[21]            = clearac1BWDropTrigger;
              regReadData[20]            = clearac0BWDropTrigger;
              regReadData[19]            = clearcounterRxTrigger;
              regReadData[18]            = clearbaRxTrigger;
              regReadData[17]            = cleartimerRxTrigger;
              regReadData[16]            = clearrxTrigger;
              regReadData[14]            = cleartimerTxTrigger;
              regReadData[13]            = cleartxopComplete;
              regReadData[12]            = clearrdTxTrigger;
              regReadData[11]            = clearhccaTxTrigger;
              regReadData[10]            = clearbcnTxTrigger;
              regReadData[9]             = clearac3TxTrigger;
              regReadData[8]             = clearac2TxTrigger;
              regReadData[7]             = clearac1TxTrigger;
              regReadData[6]             = clearac0TxTrigger;
              regReadData[5]             = clearrdProtTrigger;
              regReadData[4]             = clearhccaProtTrigger;
              regReadData[3]             = clearac3ProtTrigger;
              regReadData[2]             = clearac2ProtTrigger;
              regReadData[1]             = clearac1ProtTrigger;
              regReadData[0]             = clearac0ProtTrigger;
            end
    
            //$port_g Read TXRXINTUNMASKREG register.
            TXRXINTUNMASKREG_ADDR_CT : begin
              regReadData[31]            = masterTxRxIntEn;
              regReadData[28]            = maskbcnTxBufTrigger;
              regReadData[27]            = maskac3TxBufTrigger;
              regReadData[26]            = maskac2TxBufTrigger;
              regReadData[25]            = maskac1TxBufTrigger;
              regReadData[24]            = maskac0TxBufTrigger;
              regReadData[23]            = maskac3BWDropTrigger;
              regReadData[22]            = maskac2BWDropTrigger;
              regReadData[21]            = maskac1BWDropTrigger;
              regReadData[20]            = maskac0BWDropTrigger;
              regReadData[19]            = maskcounterRxTrigger;
              regReadData[18]            = maskbaRxTrigger;
              regReadData[17]            = masktimerRxTrigger;
              regReadData[16]            = maskrxTrigger;
              regReadData[14]            = masktimerTxTrigger;
              regReadData[13]            = masktxopComplete;
              regReadData[12]            = maskrdTxTrigger;
              regReadData[11]            = maskhccaTxTrigger;
              regReadData[10]            = maskbcnTxTrigger;
              regReadData[9]             = maskac3TxTrigger;
              regReadData[8]             = maskac2TxTrigger;
              regReadData[7]             = maskac1TxTrigger;
              regReadData[6]             = maskac0TxTrigger;
              regReadData[5]             = maskrdProtTrigger;
              regReadData[4]             = maskhccaProtTrigger;
              regReadData[3]             = maskac3ProtTrigger;
              regReadData[2]             = maskac2ProtTrigger;
              regReadData[1]             = maskac1ProtTrigger;
              regReadData[0]             = maskac0ProtTrigger;
            end
    
            //$port_g Read TIMERSINTEVENTSETREG register.
            TIMERSINTEVENTSETREG_ADDR_CT : begin
              regReadData[9]             = statussetabsTimers9;
              regReadData[8]             = statussetabsTimers8;
              regReadData[7]             = statussetabsTimers7;
              regReadData[6]             = statussetabsTimers6;
              regReadData[5]             = statussetabsTimers5;
              regReadData[4]             = statussetabsTimers4;
              regReadData[3]             = statussetabsTimers3;
              regReadData[2]             = statussetabsTimers2;
              regReadData[1]             = statussetabsTimers1;
              regReadData[0]             = statussetabsTimers0;
            end
    
            //$port_g Read TIMERSINTEVENTCLEARREG register.
            TIMERSINTEVENTCLEARREG_ADDR_CT : begin
              regReadData[9]             = clearabsTimers9;
              regReadData[8]             = clearabsTimers8;
              regReadData[7]             = clearabsTimers7;
              regReadData[6]             = clearabsTimers6;
              regReadData[5]             = clearabsTimers5;
              regReadData[4]             = clearabsTimers4;
              regReadData[3]             = clearabsTimers3;
              regReadData[2]             = clearabsTimers2;
              regReadData[1]             = clearabsTimers1;
              regReadData[0]             = clearabsTimers0;
            end
    
            //$port_g Read TIMERSINTUNMASKREG register.
            TIMERSINTUNMASKREG_ADDR_CT : begin
              regReadData[9]             = maskabsTimers9;
              regReadData[8]             = maskabsTimers8;
              regReadData[7]             = maskabsTimers7;
              regReadData[6]             = maskabsTimers6;
              regReadData[5]             = maskabsTimers5;
              regReadData[4]             = maskabsTimers4;
              regReadData[3]             = maskabsTimers3;
              regReadData[2]             = maskabsTimers2;
              regReadData[1]             = maskabsTimers1;
              regReadData[0]             = maskabsTimers0;
            end
    
            //$port_g Read TSFLOREG register.
            TSFLOREG_ADDR_CT : begin
              regReadData[31 : 0]        = tsfTimerLow;
            end
    
            //$port_g Read TSFHIREG register.
            TSFHIREG_ADDR_CT : begin
              regReadData[31 : 0]        = tsfTimerHigh;
            end
    
            //$port_g Read TIMEONAIRPARAM1REG register.
            TIMEONAIRPARAM1REG_ADDR_CT : begin
              regReadData[31 : 30]       = ppduSTBC;
              regReadData[29 : 28]       = ppduNumExtnSS;
              regReadData[27]            = ppduShortGI;
              regReadData[26 : 24]       = ppduPreType;
              regReadData[23 : 22]       = ppduBW;
              regReadData[19 : 0]        = ppduLength;
            end
    
            //$port_g Read TIMEONAIRPARAM2REG register.
            TIMEONAIRPARAM2REG_ADDR_CT : begin
              regReadData[6 : 0]         = ppduMCSIndex;
            end
    
            //$port_g Read TIMEONAIRVALUEREG register.
            TIMEONAIRVALUEREG_ADDR_CT : begin
              regReadData[31]            = computeDuration;
              regReadData[30]            = timeOnAirValid;
              regReadData[15 : 0]        = timeOnAir;
            end
    
            //$port_g Read DMACNTRLSETREG register.
            DMACNTRLSETREG_ADDR_CT : begin
              regReadData[27]            = statussetrxPayloadNewHead;
              regReadData[26]            = statussetrxHeaderNewHead;
              regReadData[25]            = statussetrxPayloadNewTail;
              regReadData[24]            = statussetrxHeaderNewTail;
              regReadData[19]            = statussethaltAC3AfterTXOP;
              regReadData[18]            = statussethaltAC2AfterTXOP;
              regReadData[17]            = statussethaltAC1AfterTXOP;
              regReadData[16]            = statussethaltAC0AfterTXOP;
              regReadData[15]            = statussethaltBcnAfterTXOP;
              regReadData[12]            = statussettxAC3NewHead;
              regReadData[11]            = statussettxAC2NewHead;
              regReadData[10]            = statussettxAC1NewHead;
              regReadData[9]             = statussettxAC0NewHead;
              regReadData[8]             = statussettxBcnNewHead;
              regReadData[4]             = statussettxAC3NewTail;
              regReadData[3]             = statussettxAC2NewTail;
              regReadData[2]             = statussettxAC1NewTail;
              regReadData[1]             = statussettxAC0NewTail;
              regReadData[0]             = statussettxBcnNewTail;
            end
    
            //$port_g Read DMACNTRLCLEARREG register.
            DMACNTRLCLEARREG_ADDR_CT : begin
              regReadData[27]            = clearrxPayloadNewHead;
              regReadData[26]            = clearrxHeaderNewHead;
              regReadData[25]            = clearrxPayloadNewTail;
              regReadData[24]            = clearrxHeaderNewTail;
              regReadData[19]            = clearhaltAC3AfterTXOP;
              regReadData[18]            = clearhaltAC2AfterTXOP;
              regReadData[17]            = clearhaltAC1AfterTXOP;
              regReadData[16]            = clearhaltAC0AfterTXOP;
              regReadData[15]            = clearhaltBcnAfterTXOP;
              regReadData[12]            = cleartxAC3NewHead;
              regReadData[11]            = cleartxAC2NewHead;
              regReadData[10]            = cleartxAC1NewHead;
              regReadData[9]             = cleartxAC0NewHead;
              regReadData[8]             = cleartxBcnNewHead;
              regReadData[4]             = cleartxAC3NewTail;
              regReadData[3]             = cleartxAC2NewTail;
              regReadData[2]             = cleartxAC1NewTail;
              regReadData[1]             = cleartxAC0NewTail;
              regReadData[0]             = cleartxBcnNewTail;
            end
    
            //$port_g Read DMASTATUS1REG register.
            DMASTATUS1REG_ADDR_CT : begin
              regReadData[29 : 28]       = rxPayloadState;
              regReadData[25 : 24]       = rxHeaderState;
              regReadData[17 : 16]       = txAC3State;
              regReadData[13 : 12]       = txAC2State;
              regReadData[9 : 8]         = txAC1State;
              regReadData[5 : 4]         = txAC0State;
              regReadData[1 : 0]         = txBcnState;
            end
    
            //$port_g Read DMASTATUS2REG register.
            DMASTATUS2REG_ADDR_CT : begin
              regReadData[29]            = txAC3NewHeadErr;
              regReadData[28]            = txAC2NewHeadErr;
              regReadData[27]            = txAC1NewHeadErr;
              regReadData[26]            = txAC0NewHeadErr;
              regReadData[25]            = txBcnNewHeadErr;
              regReadData[24]            = txAC3BusErr;
              regReadData[23]            = txAC2BusErr;
              regReadData[22]            = txAC1BusErr;
              regReadData[21]            = txAC0BusErr;
              regReadData[20]            = txBcnBusErr;
              regReadData[19]            = txAC3PTAddressErr;
              regReadData[18]            = txAC2PTAddressErr;
              regReadData[17]            = txAC1PTAddressErr;
              regReadData[16]            = txAC0PTAddressErr;
              regReadData[15]            = txBcnPTAddressErr;
              regReadData[14]            = txAC3NextPointerErr;
              regReadData[13]            = txAC2NextPointerErr;
              regReadData[12]            = txAC1NextPointerErr;
              regReadData[11]            = txAC0NextPointerErr;
              regReadData[10]            = txBcnNextPointerErr;
              regReadData[9]             = txAC3UPatternErr;
              regReadData[8]             = txAC2UPatternErr;
              regReadData[7]             = txAC1UPatternErr;
              regReadData[6]             = txAC0UPatternErr;
              regReadData[5]             = txBcnUPatternErr;
              regReadData[4]             = txAC3LenMismatch;
              regReadData[3]             = txAC2LenMismatch;
              regReadData[2]             = txAC1LenMismatch;
              regReadData[1]             = txAC0LenMismatch;
              regReadData[0]             = txBcnLenMismatch;
            end
    
            //$port_g Read DMASTATUS3REG register.
            DMASTATUS3REG_ADDR_CT : begin
              regReadData[7]             = rxPayNewHeadErr;
              regReadData[6]             = rxHdrNewHeadErr;
              regReadData[5]             = rxPayBusErr;
              regReadData[4]             = rxHdrBusErr;
              regReadData[3]             = rxPayNextPointerErr;
              regReadData[2]             = rxHdrNextPointerErr;
              regReadData[1]             = rxPayUPatternErr;
              regReadData[0]             = rxHdrUPatternErr;
            end
    
            //$port_g Read DMASTATUS4REG register.
            DMASTATUS4REG_ADDR_CT : begin
              regReadData[14]            = txAC3HaltAfterTXOP;
              regReadData[13]            = txAC2HaltAfterTXOP;
              regReadData[12]            = txAC1HaltAfterTXOP;
              regReadData[11]            = txAC0HaltAfterTXOP;
              regReadData[10]            = txBcnHaltAfterTXOP;
              regReadData[9]             = txAC3EndQ;
              regReadData[8]             = txAC2EndQ;
              regReadData[7]             = txAC1EndQ;
              regReadData[6]             = txAC0EndQ;
              regReadData[5]             = txBcnEndQ;
              regReadData[4]             = txAC3Startup;
              regReadData[3]             = txAC2Startup;
              regReadData[2]             = txAC1Startup;
              regReadData[1]             = txAC0Startup;
              regReadData[0]             = txBcnStartup;
            end
    
            //$port_g Read TXBCNHEADPTRREG register.
            TXBCNHEADPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = txBcnHeadPtr;
            end
    
            //$port_g Read TXAC0HEADPTRREG register.
            TXAC0HEADPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = txAC0HeadPtr;
            end
    
            //$port_g Read TXAC1HEADPTRREG register.
            TXAC1HEADPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = txAC1HeadPtr;
            end
    
            //$port_g Read TXAC2HEADPTRREG register.
            TXAC2HEADPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = txAC2HeadPtr;
            end
    
            //$port_g Read TXAC3HEADPTRREG register.
            TXAC3HEADPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = txAC3HeadPtr;
            end
    
            //$port_g Read TXSTRUCTSIZESREG register.
            TXSTRUCTSIZESREG_ADDR_CT : begin
              regReadData[29 : 24]       = dmaRBDSize;
              regReadData[23 : 18]       = dmaRHDSize;
              regReadData[17 : 12]       = dmaTBDSize;
              regReadData[11 : 6]        = dmaTHDSize;
              regReadData[5 : 0]         = ptEntrySize;
            end
    
            //$port_g Read RXHEADERHEADPTRREG register.
            RXHEADERHEADPTRREG_ADDR_CT : begin
              regReadData[31 : 2]        = rxHeaderHeadPtr;
              regReadData[0]             = rxHeaderHeadPtrValid;
            end
    
            //$port_g Read RXPAYLOADHEADPTRREG register.
            RXPAYLOADHEADPTRREG_ADDR_CT : begin
              regReadData[31 : 2]        = rxPayloadHeadPtr;
              regReadData[0]             = rxPayloadHeadPtrValid;
            end
    
            //$port_g Read DMATHRESHOLDREG register.
            DMATHRESHOLDREG_ADDR_CT : begin
              regReadData[23 : 16]       = rxFIFOThreshold;
              regReadData[7 : 0]         = txFIFOThreshold;
            end
    
            //$port_g Read EDCAACHASDATASETREG register.
            EDCAACHASDATASETREG_ADDR_CT : begin
              regReadData[3]             = statussetac3HasData;
              regReadData[2]             = statussetac2HasData;
              regReadData[1]             = statussetac1HasData;
              regReadData[0]             = statussetac0HasData;
            end
    
            //$port_g Read EDCAACHASDATACLEARREG register.
            EDCAACHASDATACLEARREG_ADDR_CT : begin
              regReadData[3]             = clearac3HasData;
              regReadData[2]             = clearac2HasData;
              regReadData[1]             = clearac1HasData;
              regReadData[0]             = clearac0HasData;
            end
    
            //$port_g Read MOT1REG register.
            MOT1REG_ADDR_CT : begin
              regReadData[31 : 16]       = ac1MOT;
              regReadData[15 : 0]        = ac0MOT;
            end
    
            //$port_g Read MOT2REG register.
            MOT2REG_ADDR_CT : begin
              regReadData[31 : 16]       = ac3MOT;
              regReadData[15 : 0]        = ac2MOT;
            end
    
            //$port_g Read MOT3REG register.
            MOT3REG_ADDR_CT : begin
              regReadData[31 : 16]       = miscMOT;
              regReadData[15 : 0]        = hccaQAPMOT;
            end
    
            //$port_g Read TXBWDROPINFOREG register.
            TXBWDROPINFOREG_ADDR_CT : begin
              regReadData[1 : 0]         = txBWAfterDrop;
            end
    
            //$port_g Read DEBUGBCNSPTRREG register.
            DEBUGBCNSPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = bcnStatusPointer;
            end
    
            //$port_g Read DEBUGAC0SPTRREG register.
            DEBUGAC0SPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = ac0StatusPointer;
            end
    
            //$port_g Read DEBUGAC1SPTRREG register.
            DEBUGAC1SPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = ac1StatusPointer;
            end
    
            //$port_g Read DEBUGAC2SPTRREG register.
            DEBUGAC2SPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = ac2StatusPointer;
            end
    
            //$port_g Read DEBUGAC3SPTRREG register.
            DEBUGAC3SPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = ac3StatusPointer;
            end
    
            //$port_g Read DEBUGTXCPTRREG register.
            DEBUGTXCPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = txCurrentPointer;
            end
    
            //$port_g Read DEBUGRXPAYSPTRREG register.
            DEBUGRXPAYSPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = rxPayStatPointer;
            end
    
            //$port_g Read DEBUGRXHDRCPTRREG register.
            DEBUGRXHDRCPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = rxHdrStatPointer;
            end
    
            //$port_g Read DEBUGRXPAYCPTRREG register.
            DEBUGRXPAYCPTRREG_ADDR_CT : begin
              regReadData[31 : 0]        = rxPayCurrentPointer;
            end
    
            //$port_g Read SWPROFILINGREG register.
            SWPROFILINGREG_ADDR_CT : begin
              regReadData[31]            = swProf31;
              regReadData[30]            = swProf30;
              regReadData[29]            = swProf29;
              regReadData[28]            = swProf28;
              regReadData[27]            = swProf27;
              regReadData[26]            = swProf26;
              regReadData[25]            = swProf25;
              regReadData[24]            = swProf24;
              regReadData[23]            = swProf23;
              regReadData[22]            = swProf22;
              regReadData[21]            = swProf21;
              regReadData[20]            = swProf20;
              regReadData[19]            = swProf19;
              regReadData[18]            = swProf18;
              regReadData[17]            = swProf17;
              regReadData[16]            = swProf16;
              regReadData[15]            = swProf15;
              regReadData[14]            = swProf14;
              regReadData[13]            = swProf13;
              regReadData[12]            = swProf12;
              regReadData[11]            = swProf11;
              regReadData[10]            = swProf10;
              regReadData[9]             = swProf9;
              regReadData[8]             = swProf8;
              regReadData[7]             = swProf7;
              regReadData[6]             = swProf6;
              regReadData[5]             = swProf5;
              regReadData[4]             = swProf4;
              regReadData[3]             = swProf3;
              regReadData[2]             = swProf2;
              regReadData[1]             = swProf1;
              regReadData[0]             = swProf0;
            end
    
            //$port_g Read SWSETPROFILINGREG register.
            SWSETPROFILINGREG_ADDR_CT : begin
              regReadData[31]            = statusswSetProf31;
              regReadData[30]            = statusswSetProf30;
              regReadData[29]            = statusswSetProf29;
              regReadData[28]            = statusswSetProf28;
              regReadData[27]            = statusswSetProf27;
              regReadData[26]            = statusswSetProf26;
              regReadData[25]            = statusswSetProf25;
              regReadData[24]            = statusswSetProf24;
              regReadData[23]            = statusswSetProf23;
              regReadData[24]            = statusswSetProf24;
                        regReadData[23]            = statusswSetProf23;
                        regReadData[22]            = statusswSetProf22;
                        regReadData[21]            = statusswSetProf21;
                        regReadData[20]            = statusswSetProf20;
                        regReadData[19]            = statusswSetProf19;
                        regReadData[18]            = statusswSetProf18;
                        regReadData[17]            = statusswSetProf17;
                        regReadData[16]            = statusswSetProf16;
                        regReadData[15]            = statusswSetProf15;
                        regReadData[14]            = statusswSetProf14;
                        regReadData[13]            = statusswSetProf13;
                        regReadData[12]            = statusswSetProf12;
                        regReadData[11]            = statusswSetProf11;
                        regReadData[10]            = statusswSetProf10;
                        regReadData[9]             = statusswSetProf9;
                        regReadData[8]             = statusswSetProf8;
                        regReadData[7]             = statusswSetProf7;
                        regReadData[6]             = statusswSetProf6;
                        regReadData[5]             = statusswSetProf5;
                        regReadData[4]             = statusswSetProf4;
                        regReadData[3]             = statusswSetProf3;
                        regReadData[2]             = statusswSetProf2;
                        regReadData[1]             = statusswSetProf1;
                        regReadData[0]             = statusswSetProf0;
                      end
              
                      //$port_g Read SWCLEARPROFILINGREG register.
                      SWCLEARPROFILINGREG_ADDR_CT : begin
                        regReadData[31]            = swClearProf31;
                        regReadData[30]            = swClearProf30;
                        regReadData[29]            = swClearProf29;
                        regReadData[28]            = swClearProf28;
                        regReadData[27]            = swClearProf27;
                        regReadData[26]            = swClearProf26;
                        regReadData[25]            = swClearProf25;
                        regReadData[24]            = swClearProf24;
                        regReadData[23]            = swClearProf23;
                        regReadData[22]            = swClearProf22;
                        regReadData[21]            = swClearProf21;
                        regReadData[20]            = swClearProf20;
                        regReadData[19]            = swClearProf19;
                        regReadData[18]            = swClearProf18;
                        regReadData[17]            = swClearProf17;
                        regReadData[16]            = swClearProf16;
                        regReadData[15]            = swClearProf15;
                        regReadData[14]            = swClearProf14;
                        regReadData[13]            = swClearProf13;
                        regReadData[12]            = swClearProf12;
                        regReadData[11]            = swClearProf11;
                        regReadData[10]            = swClearProf10;
                        regReadData[9]             = swClearProf9;
                        regReadData[8]             = swClearProf8;
                        regReadData[7]             = swClearProf7;
                        regReadData[6]             = swClearProf6;
                        regReadData[5]             = swClearProf5;
                        regReadData[4]             = swClearProf4;
                        regReadData[3]             = swClearProf3;
                        regReadData[2]             = swClearProf2;
                        regReadData[1]             = swClearProf1;
                        regReadData[0]             = swClearProf0;
                      end
              
                      // Disable coverage on the default state because it cannot be reached.
                      // pragma coverage block = off 
                      default : regReadData = `RW_REG_DATA_WIDTH'b0;
                      // pragma coverage block = on 
              
                    endcase
                  
                  end
                  else
                    regReadData = `RW_REG_DATA_WIDTH'b0;
                  
                end 
                
                
              endmodule
              
              ////////////////////////////////////////////////////////////////////////////////
              // End of file
              ////////////////////////////////////////////////////////////////////////////////