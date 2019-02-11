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
// Description      : Core register
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
module macCoreReg (
    ////////////////////////////////////////////
    // clock and reset
    ////////////////////////////////////////////
    input wire hardRstClk_n     , // Hard Reset.
    input wire softRstClk_n     , // Soft Reset.
    input wire Clk              , // clock clock.

    ////////////////////////////////////////////
    // Registers
    ////////////////////////////////////////////

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

    //$port_g DEBUGNAVREG register.
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

    ////////////////////////////////////////////
    // APB slave
    ////////////////////////////////////////////
    input wire regSel            , // Device select.
    input wire regWrite          , // Defines the enable cycle.
    input wire regRead           , // Write signal.
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
localparam SIGNATUREREG_ADDR_CT            = 13'b000000000000;
localparam VERSION1REG_ADDR_CT             = 13'b000000000001;
localparam VERSION2REG_ADDR_CT             = 13'b000000000010;
localparam BITMAPCNTREG_ADDR_CT            = 13'b000000000011;
localparam MACADDRLOWREG_ADDR_CT           = 13'b000000000100;
localparam MACADDRHIREG_ADDR_CT            = 13'b000000000101;
localparam MACADDRLOWMASKREG_ADDR_CT       = 13'b000000000110;
localparam MACADDRHIMASKREG_ADDR_CT        = 13'b000000000111;
localparam BSSIDLOWREG_ADDR_CT             = 13'b000000001000;
localparam BSSIDHIREG_ADDR_CT              = 13'b000000001001;
localparam BSSIDLOWMASKREG_ADDR_CT         = 13'b000000001010;
localparam BSSIDHIMASKREG_ADDR_CT          = 13'b000000001011;
localparam STATECNTRLREG_ADDR_CT           = 13'b000000001110;
localparam SCANCNTRLREG_ADDR_CT            = 13'b000000001111;
localparam DOZECNTRL1REG_ADDR_CT           = 13'b000000010001;
localparam MACCNTRL1REG_ADDR_CT            = 13'b000000010011;
localparam MACERRRECCNTRLREG_ADDR_CT       = 13'b000000010101;
localparam MACERRSETSTATUSREG_ADDR_CT      = 13'b000000010110;
localparam MACERRCLEARSTATUSREG_ADDR_CT    = 13'b000000010111;
localparam RXCNTRLREG_ADDR_CT              = 13'b000000011000;
localparam BCNCNTRL1REG_ADDR_CT            = 13'b000000011001;
localparam BCNCNTRL2REG_ADDR_CT            = 13'b000000011010;
localparam DTIMCFP1REG_ADDR_CT             = 13'b000000100100;
localparam DTIMCFP2REG_ADDR_CT             = 13'b000000100101;
localparam RETRYLIMITSREG_ADDR_CT          = 13'b000000100110;
localparam BBSERVICEREG_ADDR_CT            = 13'b000000100111;
localparam MAXPOWERLEVELREG_ADDR_CT        = 13'b000000101000;
localparam ENCRKEY0REG_ADDR_CT             = 13'b000000101011;
localparam ENCRKEY1REG_ADDR_CT             = 13'b000000101100;
localparam ENCRKEY2REG_ADDR_CT             = 13'b000000101101;
localparam ENCRKEY3REG_ADDR_CT             = 13'b000000101110;
localparam ENCRMACADDRLOWREG_ADDR_CT       = 13'b000000101111;
localparam ENCRMACADDRHIGHREG_ADDR_CT      = 13'b000000110000;
localparam ENCRCNTRLREG_ADDR_CT            = 13'b000000110001;
`ifdef RW_WAPI_EN                     
localparam ENCRWPIINTKEY0REG_ADDR_CT       = 13'b000000110010;
localparam ENCRWPIINTKEY1REG_ADDR_CT       = 13'b000000110011;
localparam ENCRWPIINTKEY2REG_ADDR_CT       = 13'b000000110100;
localparam ENCRWPIINTKEY3REG_ADDR_CT       = 13'b000000110101;
`endif // RW_WAPI_EN                     
localparam RATESREG_ADDR_CT                = 13'b000000110111;
localparam OLBCREG_ADDR_CT                 = 13'b000000111000;
localparam TIMINGS1REG_ADDR_CT             = 13'b000000111001;
localparam TIMINGS2REG_ADDR_CT             = 13'b000000111010;
localparam TIMINGS3REG_ADDR_CT             = 13'b000000111011;
localparam TIMINGS4REG_ADDR_CT             = 13'b000000111100;
localparam TIMINGS5REG_ADDR_CT             = 13'b000000111101;
localparam TIMINGS6REG_ADDR_CT             = 13'b000000111110;
localparam TIMINGS7REG_ADDR_CT             = 13'b000000111111;
localparam TIMINGS8REG_ADDR_CT             = 13'b000001000000;
localparam TIMINGS9REG_ADDR_CT             = 13'b000001000001;
localparam PROTTRIGTIMERREG_ADDR_CT        = 13'b000001000011;
localparam TXTRIGGERTIMERREG_ADDR_CT       = 13'b000001000100;
localparam RXTRIGGERTIMERREG_ADDR_CT       = 13'b000001000101;
localparam MIBTABLEWRITEREG_ADDR_CT        = 13'b000001000110;
localparam MONOTONICCOUNTER1REG_ADDR_CT    = 13'b000001000111;
localparam MONOTONICCOUNTER2LOREG_ADDR_CT  = 13'b000001001000;
localparam MONOTONICCOUNTER2HIREG_ADDR_CT  = 13'b000001001001;
localparam ABSTIMERREG0_ADDR_CT            = 13'b000001001010;
localparam ABSTIMERREG1_ADDR_CT            = 13'b000001001011;
localparam ABSTIMERREG2_ADDR_CT            = 13'b000001001100;
localparam ABSTIMERREG3_ADDR_CT            = 13'b000001001101;
localparam ABSTIMERREG4_ADDR_CT            = 13'b000001001110;
localparam ABSTIMERREG5_ADDR_CT            = 13'b000001001111;
localparam ABSTIMERREG6_ADDR_CT            = 13'b000001010000;
localparam ABSTIMERREG7_ADDR_CT            = 13'b000001010001;
localparam ABSTIMERREG8_ADDR_CT            = 13'b000001010010;
localparam ABSTIMERREG9_ADDR_CT            = 13'b000001010011;
localparam MAXRXLENGTHREG_ADDR_CT          = 13'b000001010100;
localparam EDCAAC0REG_ADDR_CT              = 13'b000010000000;
localparam EDCAAC1REG_ADDR_CT              = 13'b000010000001;
localparam EDCAAC2REG_ADDR_CT              = 13'b000010000010;
localparam EDCAAC3REG_ADDR_CT              = 13'b000010000011;
localparam EDCACCABUSYREG_ADDR_CT          = 13'b000010001000;
localparam EDCACNTRLREG_ADDR_CT            = 13'b000010001001;
localparam QUIETELEMENT1AREG_ADDR_CT       = 13'b000010100000;
localparam QUIETELEMENT1BREG_ADDR_CT       = 13'b000010100001;
localparam QUIETELEMENT2AREG_ADDR_CT       = 13'b000010100010;
localparam QUIETELEMENT2BREG_ADDR_CT       = 13'b000010100011;
localparam ADDCCABUSYSEC20REG_ADDR_CT      = 13'b000010100100;
localparam ADDCCABUSYSEC40REG_ADDR_CT      = 13'b000010100101;
localparam ADDCCABUSYSEC80REG_ADDR_CT      = 13'b000010100110;
localparam STBCCNTRLREG_ADDR_CT            = 13'b000011000000;
localparam STARTTX1REG_ADDR_CT             = 13'b000011000001;
localparam STARTTX2REG_ADDR_CT             = 13'b000011000010;
localparam STARTTX3REG_ADDR_CT             = 13'b000011000011;
localparam TXBWCNTRLREG_ADDR_CT            = 13'b000011000100;
localparam HTMCSREG_ADDR_CT                = 13'b000011000101;
localparam VHTMCSREG_ADDR_CT               = 13'b000011000111;
localparam LSTPREG_ADDR_CT                 = 13'b000011001000;
`ifdef RW_WLAN_COEX_EN                
localparam COEXCONTROLREG_ADDR_CT          = 13'b000100000000;
localparam COEXPTIREG_ADDR_CT              = 13'b000100000001;
`endif // RW_WLAN_COEX_EN                
localparam DEBUGHWSM1REG_ADDR_CT           = 13'b000101000000;
localparam DEBUGHWSM2REG_ADDR_CT           = 13'b000101000001;
localparam DEBUGPORTVALUEREG_ADDR_CT       = 13'b000101000011;
localparam DEBUGPORTSELREG_ADDR_CT         = 13'b000101000100;
localparam DEBUGNAVREG_ADDR_CT             = 13'b000101000101;
localparam DEBUGCWREG_ADDR_CT              = 13'b000101000110;
localparam DEBUGQSRCREG_ADDR_CT            = 13'b000101000111;
localparam DEBUGQLRCREG_ADDR_CT            = 13'b000101001000;
localparam DEBUGPHYREG_ADDR_CT             = 13'b000101010111;

//////////////////////////////////////////////////////////////////////////////
// Signals
//////////////////////////////////////////////////////////////////////////////
  //$port_g MACADDRLOWREG register.
  reg [31 : 0] int_macAddrLow               ;
  //$port_g MACADDRHIREG register.
  reg [15 : 0] int_macAddrHigh              ;
  //$port_g MACADDRLOWMASKREG register.
  reg [31 : 0] int_macAddrLowMask           ;
  //$port_g MACADDRHIMASKREG register.
  reg [15 : 0] int_macAddrHighMask          ;
  //$port_g BSSIDLOWREG register.
  reg [31 : 0] int_bssIDLow                 ;
  //$port_g BSSIDHIREG register.
  reg [15 : 0] int_bssIDHigh                ;
  //$port_g BSSIDLOWMASKREG register.
  reg [31 : 0] int_bssIDLowMask             ;
  //$port_g BSSIDHIMASKREG register.
  reg [15 : 0] int_bssIDHighMask            ;
  //$port_g STATECNTRLREG register.
  reg [3 : 0] int_nextState                ;
  //$port_g SCANCNTRLREG register.
  reg [15 : 0] int_probeDelay               ;
  //$port_g DOZECNTRL1REG register.
  reg [14 : 0] int_atimW                    ;
  reg  int_wakeupDTIM               ;
  reg [15 : 0] int_listenInterval           ;
  //$port_g MACCNTRL1REG register.
  reg  int_rxRIFSEn                 ;
  reg  int_tsfMgtDisable            ;
  reg  int_tsfUpdatedBySW           ;
  reg [2 : 0] int_abgnMode                 ;
  reg  int_keyStoRAMReset           ;
  reg  int_mibTableReset            ;
  reg  int_rateControllerMPIF       ;
  reg  int_disableBAResp            ;
  reg  int_disableCTSResp           ;
  reg  int_disableACKResp           ;
  reg  int_activeClkGating          ;
  reg  int_enableLPClkSwitch        ;
  reg  int_cfpAware                 ;
  reg  int_pwrMgt                   ;
  reg  int_ap                       ;
  reg  int_bssType                  ;
  //$port_g MACERRRECCNTRLREG register.
  reg  int_rxFlowCntrlEn            ;
  reg  int_baPSBitmapReset          ;
  reg  int_encrRxFIFOReset          ;
  reg  int_macPHYIFFIFOReset        ;
  reg  int_txFIFOReset              ;
  reg  int_rxFIFOReset              ;
  reg  int_hwFSMReset               ;
  reg  int_useErrDet                ;
  reg  int_errInHWLevel3            ;
  reg  int_errInTxRxLevel2          ;
  reg  int_errInRxLevel1            ;
  reg  int_errInTxLevel1            ;
  reg  int_clearErrInHWLevel3       ;
  reg  int_clearErrInTxRxLevel2     ;
  reg  int_clearErrInRxLevel1       ;
  reg  int_clearErrInTxLevel1       ;
  //$port_g RXCNTRLREG register.
  reg  int_acceptUnknown            ;
  reg  int_acceptOtherDataFrames    ;
  reg  int_acceptQoSNull            ;
  reg  int_acceptQCFWOData          ;
  reg  int_acceptQData              ;
  reg  int_acceptCFWOData           ;
  reg  int_acceptData               ;
  reg  int_acceptOtherCntrlFrames   ;
  reg  int_acceptCFEnd              ;
  reg  int_acceptACK                ;
  reg  int_acceptCTS                ;
  reg  int_acceptRTS                ;
  reg  int_acceptPSPoll             ;
  reg  int_acceptBA                 ;
  reg  int_acceptBAR                ;
  reg  int_acceptOtherMgmtFrames    ;
  reg  int_acceptAllBeacon          ;
  reg  int_acceptNotExpectedBA      ;
  reg  int_acceptDecryptErrorFrames ;
  reg  int_acceptBeacon             ;
  reg  int_acceptProbeResp          ;
  reg  int_acceptProbeReq           ;
  reg  int_acceptMyUnicast          ;
  reg  int_acceptUnicast            ;
  reg  int_acceptErrorFrames        ;
  reg  int_acceptOtherBSSID         ;
  reg  int_acceptBroadcast          ;
  reg  int_acceptMulticast          ;
  reg  int_dontDecrypt              ;
  reg  int_excUnencrypted           ;
  //$port_g BCNCNTRL1REG register.
  reg [7 : 0] int_noBcnTxTime              ;
  reg  int_impTBTTIn128Us           ;
  reg [6 : 0] int_impTBTTPeriod            ;
  reg [15 : 0] int_beaconInt                ;
  //$port_g BCNCNTRL2REG register.
  reg [11 : 0] int_aid                      ;
  reg [7 : 0] int_timOffset                ;
  reg [7 : 0] int_bcnUpdateOffset          ;
  //$port_g DTIMCFP1REG register.
  reg  int_dtimUpdatedBySW          ;
  reg [7 : 0] int_cfpPeriod                ;
  reg [7 : 0] int_dtimPeriod               ;
  //$port_g DTIMCFP2REG register.
  reg [15 : 0] int_cfpMaxDuration           ;
  //$port_g RETRYLIMITSREG register.
  reg [7 : 0] int_dot11LongRetryLimit      ;
  reg [7 : 0] int_dot11ShortRetryLimit     ;
  //$port_g BBSERVICEREG register.
  reg [2 : 0] int_maxPHYNtx                ;
  reg [7 : 0] int_bbServiceB               ;
  reg [15 : 0] int_bbServiceA               ;
  //$port_g MAXPOWERLEVELREG register.
  reg [7 : 0] int_dsssMaxPwrLevel          ;
  reg [7 : 0] int_ofdmMaxPwrLevel          ;
  //$port_g ENCRKEY0REG register.
  reg [31 : 0] int_encrKeyRAMWord0          ;
  //$port_g ENCRKEY1REG register.
  reg [31 : 0] int_encrKeyRAMWord1          ;
  //$port_g ENCRKEY2REG register.
  reg [31 : 0] int_encrKeyRAMWord2          ;
  //$port_g ENCRKEY3REG register.
  reg [31 : 0] int_encrKeyRAMWord3          ;
  //$port_g ENCRMACADDRLOWREG register.
  reg [31 : 0] int_macAddrRAMLow            ;
  //$port_g ENCRMACADDRHIGHREG register.
  reg [15 : 0] int_macAddrRAMHigh           ;
  //$port_g ENCRCNTRLREG register.
  reg  int_newRead                  ;
  reg  int_newWrite                 ;
  reg [9 : 0] int_keyIndexRAM              ;
  reg [2 : 0] int_cTypeRAM                 ;
  reg [3 : 0] int_vlanIDRAM                ;
  reg [1 : 0] int_sppRAM                   ;
  reg  int_useDefKeyRAM             ;
  reg  int_cLenRAM                  ;
`ifdef RW_WAPI_EN                     
  //$port_g ENCRWPIINTKEY0REG register.
  reg [31 : 0] int_encrIntKeyRAMWord0       ;
  //$port_g ENCRWPIINTKEY1REG register.
  reg [31 : 0] int_encrIntKeyRAMWord1       ;
  //$port_g ENCRWPIINTKEY2REG register.
  reg [31 : 0] int_encrIntKeyRAMWord2       ;
  //$port_g ENCRWPIINTKEY3REG register.
  reg [31 : 0] int_encrIntKeyRAMWord3       ;
`endif // RW_WAPI_EN                     
  //$port_g RATESREG register.
  reg [11 : 0] int_bssBasicRateSet          ;
  //$port_g OLBCREG register.
  reg [7 : 0] int_dsssCount                ;
  reg [7 : 0] int_ofdmCount                ;
  reg [15 : 0] int_olbcTimer                ;
  //$port_g TIMINGS1REG register.
  reg [9 : 0] int_txChainDelayInMACClk     ;
  reg [9 : 0] int_txRFDelayInMACClk        ;
  reg [7 : 0] int_macCoreClkFreq           ;
  //$port_g TIMINGS2REG register.
  reg [15 : 0] int_slotTimeInMACClk         ;
  reg [7 : 0] int_slotTime                 ;
  //$port_g TIMINGS3REG register.
  reg [9 : 0] int_rxRFDelayInMACClk        ;
  reg [9 : 0] int_txDelayRFOnInMACClk      ;
  reg [9 : 0] int_macProcDelayInMACClk     ;
  //$port_g TIMINGS4REG register.
  reg [9 : 0] int_radioWakeUpTime          ;
  reg [9 : 0] int_radioChirpTime           ;
  //$port_g TIMINGS5REG register.
  reg [15 : 0] int_sifsBInMACClk            ;
  reg [7 : 0] int_sifsB                    ;
  //$port_g TIMINGS6REG register.
  reg [15 : 0] int_sifsAInMACClk            ;
  reg [7 : 0] int_sifsA                    ;
  //$port_g TIMINGS7REG register.
  reg [3 : 0] int_rxCCADelay               ;
  reg [7 : 0] int_rifs                     ;
  //$port_g TIMINGS8REG register.
  reg [7 : 0] int_rxStartDelayMIMO         ;
  reg [7 : 0] int_rxStartDelayShort        ;
  reg [7 : 0] int_rxStartDelayLong         ;
  reg [7 : 0] int_rxStartDelayOFDM         ;
  //$port_g TIMINGS9REG register.
  reg [9 : 0] int_rifsTOInMACClk           ;
  reg [9 : 0] int_rifsInMACClk             ;
  reg [9 : 0] int_txDMAProcDlyInMACClk     ;
  //$port_g PROTTRIGTIMERREG register.
  reg [7 : 0] int_edcaTriggerTimer         ;
  //$port_g TXTRIGGERTIMERREG register.
  reg [7 : 0] int_txPacketTimeout          ;
  reg [7 : 0] int_txAbsoluteTimeout        ;
  //$port_g RXTRIGGERTIMERREG register.
  reg [7 : 0] int_rxPayloadUsedCount       ;
  reg [7 : 0] int_rxPacketTimeout          ;
  reg [7 : 0] int_rxAbsoluteTimeout        ;
  //$port_g MIBTABLEWRITEREG register.
  reg [15 : 0] int_mibValue                 ;
  reg  int_mibWrite                 ;
  reg  int_mibIncrementMode         ;
  reg [9 : 0] int_mibTableIndex            ;
  //$port_g ABSTIMERREG0 register.
  reg [31 : 0] int_absTimerValue0           ;
  //$port_g ABSTIMERREG1 register.
  reg [31 : 0] int_absTimerValue1           ;
  //$port_g ABSTIMERREG2 register.
  reg [31 : 0] int_absTimerValue2           ;
  //$port_g ABSTIMERREG3 register.
  reg [31 : 0] int_absTimerValue3           ;
  //$port_g ABSTIMERREG4 register.
  reg [31 : 0] int_absTimerValue4           ;
  //$port_g ABSTIMERREG5 register.
  reg [31 : 0] int_absTimerValue5           ;
  //$port_g ABSTIMERREG6 register.
  reg [31 : 0] int_absTimerValue6           ;
  //$port_g ABSTIMERREG7 register.
  reg [31 : 0] int_absTimerValue7           ;
  //$port_g ABSTIMERREG8 register.
  reg [31 : 0] int_absTimerValue8           ;
  //$port_g ABSTIMERREG9 register.
  reg [31 : 0] int_absTimerValue9           ;
  //$port_g MAXRXLENGTHREG register.
  reg [19 : 0] int_maxAllowedLength         ;
  //$port_g EDCAAC0REG register.
  reg [15 : 0] int_txOpLimit0               ;
  reg [3 : 0] int_cwMax0                   ;
  reg [3 : 0] int_cwMin0                   ;
  reg [3 : 0] int_aifsn0                   ;
  //$port_g EDCAAC1REG register.
  reg [15 : 0] int_txOpLimit1               ;
  reg [3 : 0] int_cwMax1                   ;
  reg [3 : 0] int_cwMin1                   ;
  reg [3 : 0] int_aifsn1                   ;
  //$port_g EDCAAC2REG register.
  reg [15 : 0] int_txOpLimit2               ;
  reg [3 : 0] int_cwMax2                   ;
  reg [3 : 0] int_cwMin2                   ;
  reg [3 : 0] int_aifsn2                   ;
  //$port_g EDCAAC3REG register.
  reg [15 : 0] int_txOpLimit3               ;
  reg [3 : 0] int_cwMax3                   ;
  reg [3 : 0] int_cwMin3                   ;
  reg [3 : 0] int_aifsn3                   ;
  //$port_g EDCACCABUSYREG register.
  reg [31 : 0] int_ccaBusyDur               ;
  //$port_g EDCACNTRLREG register.
  reg  int_keepTXOPOpen             ;
  reg  int_remTXOPInDurField        ;
  reg  int_sendCFEnd                ;
  reg  int_sendCFEndNow             ;
  //$port_g QUIETELEMENT1AREG register.
  reg [15 : 0] int_quietDuration1           ;
  reg [7 : 0] int_quietPeriod1             ;
  reg [7 : 0] int_quietCount1              ;
  //$port_g QUIETELEMENT1BREG register.
  reg [15 : 0] int_quietOffset1             ;
  //$port_g QUIETELEMENT2AREG register.
  reg [15 : 0] int_quietDuration2           ;
  reg [7 : 0] int_quietPeriod2             ;
  reg [7 : 0] int_quietCount2              ;
  //$port_g QUIETELEMENT2BREG register.
  reg [15 : 0] int_quietOffset2             ;
  //$port_g ADDCCABUSYSEC20REG register.
  reg [31 : 0] int_ccaBusyDurSec20          ;
  //$port_g ADDCCABUSYSEC40REG register.
  reg [31 : 0] int_ccaBusyDurSec40          ;
  //$port_g ADDCCABUSYSEC80REG register.
  reg [31 : 0] int_ccaBusyDurSec80          ;
  //$port_g STBCCNTRLREG register.
  reg [6 : 0] int_basicSTBCMCS             ;
  reg  int_dualCTSProt              ;
  reg [7 : 0] int_ctsSTBCDur               ;
  reg [15 : 0] int_cfEndSTBCDur             ;
  //$port_g STARTTX1REG register.
  reg [1 : 0] int_startTxBW                ;
  reg  int_startTxPreType           ;
  reg [2 : 0] int_startTxFormatMod         ;
  reg [7 : 0] int_startTxMCSIndex0         ;
  reg [9 : 0] int_startTxKSRIndex          ;
  reg [1 : 0] int_startTxAC                ;
  reg [1 : 0] int_startTxFrmExType         ;
  reg  int_startTxFrameEx           ;
  //$port_g STARTTX2REG register.
  reg [15 : 0] int_durControlFrm            ;
  //$port_g STARTTX3REG register.
  reg [7 : 0] int_startTxSMMIndex          ;
  reg [7 : 0] int_startTxAntennaSet        ;
  reg  int_startTxLSTP              ;
  reg  int_startTxSmoothing         ;
  reg  int_startTxShortGI           ;
  reg [2 : 0] int_startTxNTx               ;
  reg  int_startTxFecCoding         ;
  reg [1 : 0] int_startTxSTBC              ;
  reg [1 : 0] int_startTxNumExtnSS         ;
  //$port_g TXBWCNTRLREG register.
  reg [1 : 0] int_maxSupportedBW           ;
  reg [7 : 0] int_aPPDUMaxTime             ;
  reg  int_dynBWEn                  ;
  reg [2 : 0] int_numTryBWAcquisition      ;
  reg  int_dropToLowerBW            ;
  reg [1 : 0] int_defaultBWTXOP            ;
  reg  int_defaultBWTXOPV           ;
  //$port_g HTMCSREG register.
  reg [5 : 0] int_bssBasicHTMCSSetUM       ;
  reg [15 : 0] int_bssBasicHTMCSSetEM       ;
  //$port_g VHTMCSREG register.
  reg [15 : 0] int_bssBasicVHTMCSSet        ;
  //$port_g LSTPREG register.
  reg  int_supportLSTP              ;
`ifdef RW_WLAN_COEX_EN                
  //$port_g COEXCONTROLREG register.
  reg [6 : 0] int_coexWlanChanFreq         ;
  reg  int_coexWlanChanOffset       ;
  reg  int_coexEnable               ;
  //$port_g COEXPTIREG register.
  reg [3 : 0] int_coexPTIBcnData           ;
  reg [3 : 0] int_coexPTIBKData            ;
  reg [3 : 0] int_coexPTIBEData            ;
  reg [3 : 0] int_coexPTIVIData            ;
  reg [3 : 0] int_coexPTIVOData            ;
  reg [3 : 0] int_coexPTIMgt               ;
  reg [3 : 0] int_coexPTICntl              ;
  reg [3 : 0] int_coexPTIAck               ;
`endif // RW_WLAN_COEX_EN                
  //$port_g DEBUGPORTSELREG register.
  reg [7 : 0] int_debugPortSel2            ;
  reg [7 : 0] int_debugPortSel1            ;
  //$port_g DEBUGNAVREG register.
  reg [25 : 0] int_navCounter               ;
  //$port_g DEBUGCWREG register.
  reg [1 : 0] int_backoffOffset            ;
  //$port_g DEBUGPHYREG register.
  reg  int_rxReqForceDeassertion    ;
  
  //////////////////////////////////////////////////////////////////////////////
// Ouput linkage
//////////////////////////////////////////////////////////////////////////////
   assign macAddrLow               = int_macAddrLow               ;
   assign macAddrHigh              = int_macAddrHigh              ;
   assign macAddrLowMask           = int_macAddrLowMask           ;
   assign macAddrHighMask          = int_macAddrHighMask          ;
   assign bssIDLow                 = int_bssIDLow                 ;
   assign bssIDHigh                = int_bssIDHigh                ;
   assign bssIDLowMask             = int_bssIDLowMask             ;
   assign bssIDHighMask            = int_bssIDHighMask            ;
   assign nextState                = int_nextState                ;
   assign probeDelay               = int_probeDelay               ;
   assign atimW                    = int_atimW                    ;
   assign wakeupDTIM               = int_wakeupDTIM               ;
   assign listenInterval           = int_listenInterval           ;
   assign rxRIFSEn                 = int_rxRIFSEn                 ;
   assign tsfMgtDisable            = int_tsfMgtDisable            ;
   assign tsfUpdatedBySW           = int_tsfUpdatedBySW           ;
   assign abgnMode                 = int_abgnMode                 ;
   assign keyStoRAMReset           = int_keyStoRAMReset           ;
   assign mibTableReset            = int_mibTableReset            ;
   assign rateControllerMPIF       = int_rateControllerMPIF       ;
   assign disableBAResp            = int_disableBAResp            ;
   assign disableCTSResp           = int_disableCTSResp           ;
   assign disableACKResp           = int_disableACKResp           ;
   assign activeClkGating          = int_activeClkGating          ;
   assign enableLPClkSwitch        = int_enableLPClkSwitch        ;
   assign cfpAware                 = int_cfpAware                 ;
   assign pwrMgt                   = int_pwrMgt                   ;
   assign ap                       = int_ap                       ;
   assign bssType                  = int_bssType                  ;
   assign rxFlowCntrlEn            = int_rxFlowCntrlEn            ;
   assign baPSBitmapReset          = int_baPSBitmapReset          ;
   assign encrRxFIFOReset          = int_encrRxFIFOReset          ;
   assign macPHYIFFIFOReset        = int_macPHYIFFIFOReset        ;
   assign txFIFOReset              = int_txFIFOReset              ;
   assign rxFIFOReset              = int_rxFIFOReset              ;
   assign hwFSMReset               = int_hwFSMReset               ;
   assign useErrDet                = int_useErrDet                ;
   assign errInHWLevel3            = int_errInHWLevel3            ;
   assign errInTxRxLevel2          = int_errInTxRxLevel2          ;
   assign errInRxLevel1            = int_errInRxLevel1            ;
   assign errInTxLevel1            = int_errInTxLevel1            ;
   assign clearErrInHWLevel3       = int_clearErrInHWLevel3       ;
   assign clearErrInTxRxLevel2     = int_clearErrInTxRxLevel2     ;
   assign clearErrInRxLevel1       = int_clearErrInRxLevel1       ;
   assign clearErrInTxLevel1       = int_clearErrInTxLevel1       ;
   assign acceptUnknown            = int_acceptUnknown            ;
   assign acceptOtherDataFrames    = int_acceptOtherDataFrames    ;
   assign acceptQoSNull            = int_acceptQoSNull            ;
   assign acceptQCFWOData          = int_acceptQCFWOData          ;
   assign acceptQData              = int_acceptQData              ;
   assign acceptCFWOData           = int_acceptCFWOData           ;
   assign acceptData               = int_acceptData               ;
   assign acceptOtherCntrlFrames   = int_acceptOtherCntrlFrames   ;
   assign acceptCFEnd              = int_acceptCFEnd              ;
   assign acceptACK                = int_acceptACK                ;
   assign acceptCTS                = int_acceptCTS                ;
   assign acceptRTS                = int_acceptRTS                ;
   assign acceptPSPoll             = int_acceptPSPoll             ;
   assign acceptBA                 = int_acceptBA                 ;
   assign acceptBAR                = int_acceptBAR                ;
   assign acceptOtherMgmtFrames    = int_acceptOtherMgmtFrames    ;
   assign acceptAllBeacon          = int_acceptAllBeacon          ;
   assign acceptNotExpectedBA      = int_acceptNotExpectedBA      ;
   assign acceptDecryptErrorFrames = int_acceptDecryptErrorFrames ;
   assign acceptBeacon             = int_acceptBeacon             ;
   assign acceptProbeResp          = int_acceptProbeResp          ;
   assign acceptProbeReq           = int_acceptProbeReq           ;
   assign acceptMyUnicast          = int_acceptMyUnicast          ;
   assign acceptUnicast            = int_acceptUnicast            ;
   assign acceptErrorFrames        = int_acceptErrorFrames        ;
   assign acceptOtherBSSID         = int_acceptOtherBSSID         ;
   assign acceptBroadcast          = int_acceptBroadcast          ;
   assign acceptMulticast          = int_acceptMulticast          ;
   assign dontDecrypt              = int_dontDecrypt              ;
   assign excUnencrypted           = int_excUnencrypted           ;
   assign noBcnTxTime              = int_noBcnTxTime              ;
   assign impTBTTIn128Us           = int_impTBTTIn128Us           ;
   assign impTBTTPeriod            = int_impTBTTPeriod            ;
   assign beaconInt                = int_beaconInt                ;
   assign aid                      = int_aid                      ;
   assign timOffset                = int_timOffset                ;
   assign bcnUpdateOffset          = int_bcnUpdateOffset          ;
   assign dtimUpdatedBySW          = int_dtimUpdatedBySW          ;
   assign cfpPeriod                = int_cfpPeriod                ;
   assign dtimPeriod               = int_dtimPeriod               ;
   assign cfpMaxDuration           = int_cfpMaxDuration           ;
   assign dot11LongRetryLimit      = int_dot11LongRetryLimit      ;
   assign dot11ShortRetryLimit     = int_dot11ShortRetryLimit     ;
   assign maxPHYNtx                = int_maxPHYNtx                ;
   assign bbServiceB               = int_bbServiceB               ;
   assign bbServiceA               = int_bbServiceA               ;
   assign dsssMaxPwrLevel          = int_dsssMaxPwrLevel          ;
   assign ofdmMaxPwrLevel          = int_ofdmMaxPwrLevel          ;
   assign encrKeyRAMWord0          = int_encrKeyRAMWord0          ;
   assign encrKeyRAMWord1          = int_encrKeyRAMWord1          ;
   assign encrKeyRAMWord2          = int_encrKeyRAMWord2          ;
   assign encrKeyRAMWord3          = int_encrKeyRAMWord3          ;
   assign macAddrRAMLow            = int_macAddrRAMLow            ;
   assign macAddrRAMHigh           = int_macAddrRAMHigh           ;
   assign newRead                  = int_newRead                  ;
   assign newWrite                 = int_newWrite                 ;
   assign keyIndexRAM              = int_keyIndexRAM              ;
   assign cTypeRAM                 = int_cTypeRAM                 ;
   assign vlanIDRAM                = int_vlanIDRAM                ;
   assign sppRAM                   = int_sppRAM                   ;
   assign useDefKeyRAM             = int_useDefKeyRAM             ;
   assign cLenRAM                  = int_cLenRAM                  ;
`ifdef RW_WAPI_EN                     
   assign encrIntKeyRAMWord0       = int_encrIntKeyRAMWord0       ;
   assign encrIntKeyRAMWord1       = int_encrIntKeyRAMWord1       ;
   assign encrIntKeyRAMWord2       = int_encrIntKeyRAMWord2       ;
   assign encrIntKeyRAMWord3       = int_encrIntKeyRAMWord3       ;
`endif // RW_WAPI_EN                     
   assign bssBasicRateSet          = int_bssBasicRateSet          ;
   assign dsssCount                = int_dsssCount                ;
   assign ofdmCount                = int_ofdmCount                ;
   assign olbcTimer                = int_olbcTimer                ;
   assign txChainDelayInMACClk     = int_txChainDelayInMACClk     ;
   assign txRFDelayInMACClk        = int_txRFDelayInMACClk        ;
   assign macCoreClkFreq           = int_macCoreClkFreq           ;
   assign slotTimeInMACClk         = int_slotTimeInMACClk         ;
   assign slotTime                 = int_slotTime                 ;
   assign rxRFDelayInMACClk        = int_rxRFDelayInMACClk        ;
   assign txDelayRFOnInMACClk      = int_txDelayRFOnInMACClk      ;
   assign macProcDelayInMACClk     = int_macProcDelayInMACClk     ;
   assign radioWakeUpTime          = int_radioWakeUpTime          ;
   assign radioChirpTime           = int_radioChirpTime           ;
   assign sifsBInMACClk            = int_sifsBInMACClk            ;
   assign sifsB                    = int_sifsB                    ;
   assign sifsAInMACClk            = int_sifsAInMACClk            ;
   assign sifsA                    = int_sifsA                    ;
   assign rxCCADelay               = int_rxCCADelay               ;
   assign rifs                     = int_rifs                     ;
   assign rxStartDelayMIMO         = int_rxStartDelayMIMO         ;
   assign rxStartDelayShort        = int_rxStartDelayShort        ;
   assign rxStartDelayLong         = int_rxStartDelayLong         ;
   assign rxStartDelayOFDM         = int_rxStartDelayOFDM         ;
   assign rifsTOInMACClk           = int_rifsTOInMACClk           ;
   assign rifsInMACClk             = int_rifsInMACClk             ;
   assign txDMAProcDlyInMACClk     = int_txDMAProcDlyInMACClk     ;
   assign edcaTriggerTimer         = int_edcaTriggerTimer         ;
   assign txPacketTimeout          = int_txPacketTimeout          ;
   assign txAbsoluteTimeout        = int_txAbsoluteTimeout        ;
   assign rxPayloadUsedCount       = int_rxPayloadUsedCount       ;
   assign rxPacketTimeout          = int_rxPacketTimeout          ;
   assign rxAbsoluteTimeout        = int_rxAbsoluteTimeout        ;
   assign mibValue                 = int_mibValue                 ;
   assign mibWrite                 = int_mibWrite                 ;
   assign mibIncrementMode         = int_mibIncrementMode         ;
   assign mibTableIndex            = int_mibTableIndex            ;
   assign absTimerValue0           = int_absTimerValue0           ;
   assign absTimerValue1           = int_absTimerValue1           ;
   assign absTimerValue2           = int_absTimerValue2           ;
   assign absTimerValue3           = int_absTimerValue3           ;
   assign absTimerValue4           = int_absTimerValue4           ;
   assign absTimerValue5           = int_absTimerValue5           ;
   assign absTimerValue6           = int_absTimerValue6           ;
   assign absTimerValue7           = int_absTimerValue7           ;
   assign absTimerValue8           = int_absTimerValue8           ;
   assign absTimerValue9           = int_absTimerValue9           ;
   assign maxAllowedLength         = int_maxAllowedLength         ;
   assign txOpLimit0               = int_txOpLimit0               ;
   assign cwMax0                   = int_cwMax0                   ;
   assign cwMin0                   = int_cwMin0                   ;
   assign aifsn0                   = int_aifsn0                   ;
   assign txOpLimit1               = int_txOpLimit1               ;
   assign cwMax1                   = int_cwMax1                   ;
   assign cwMin1                   = int_cwMin1                   ;
   assign aifsn1                   = int_aifsn1                   ;
   assign txOpLimit2               = int_txOpLimit2               ;
   assign cwMax2                   = int_cwMax2                   ;
   assign cwMin2                   = int_cwMin2                   ;
   assign aifsn2                   = int_aifsn2                   ;
   assign txOpLimit3               = int_txOpLimit3               ;
   assign cwMax3                   = int_cwMax3                   ;
   assign cwMin3                   = int_cwMin3                   ;
   assign aifsn3                   = int_aifsn3                   ;
   assign ccaBusyDur               = int_ccaBusyDur               ;
   assign keepTXOPOpen             = int_keepTXOPOpen             ;
   assign remTXOPInDurField        = int_remTXOPInDurField        ;
   assign sendCFEnd                = int_sendCFEnd                ;
   assign sendCFEndNow             = int_sendCFEndNow             ;
   assign quietDuration1           = int_quietDuration1           ;
   assign quietPeriod1             = int_quietPeriod1             ;
   assign quietCount1              = int_quietCount1              ;
   assign quietOffset1             = int_quietOffset1             ;
   assign quietDuration2           = int_quietDuration2           ;
   assign quietPeriod2             = int_quietPeriod2             ;
   assign quietCount2              = int_quietCount2              ;
   assign quietOffset2             = int_quietOffset2             ;
   assign ccaBusyDurSec20          = int_ccaBusyDurSec20          ;
   assign ccaBusyDurSec40          = int_ccaBusyDurSec40          ;
   assign ccaBusyDurSec80          = int_ccaBusyDurSec80          ;
   assign basicSTBCMCS             = int_basicSTBCMCS             ;
   assign dualCTSProt              = int_dualCTSProt              ;
   assign ctsSTBCDur               = int_ctsSTBCDur               ;
   assign cfEndSTBCDur             = int_cfEndSTBCDur             ;
   assign startTxBW                = int_startTxBW                ;
   assign startTxPreType           = int_startTxPreType           ;
   assign startTxFormatMod         = int_startTxFormatMod         ;
   assign startTxMCSIndex0         = int_startTxMCSIndex0         ;
   assign startTxKSRIndex          = int_startTxKSRIndex          ;
   assign startTxAC                = int_startTxAC                ;
   assign startTxFrmExType         = int_startTxFrmExType         ;
   assign startTxFrameEx           = int_startTxFrameEx           ;
   assign durControlFrm            = int_durControlFrm            ;
   assign startTxSMMIndex          = int_startTxSMMIndex          ;
   assign startTxAntennaSet        = int_startTxAntennaSet        ;
   assign startTxLSTP              = int_startTxLSTP              ;
   assign startTxSmoothing         = int_startTxSmoothing         ;
   assign startTxShortGI           = int_startTxShortGI           ;
   assign startTxNTx               = int_startTxNTx               ;
   assign startTxFecCoding         = int_startTxFecCoding         ;
   assign startTxSTBC              = int_startTxSTBC              ;
   assign startTxNumExtnSS         = int_startTxNumExtnSS         ;
   assign maxSupportedBW           = int_maxSupportedBW           ;
   assign aPPDUMaxTime             = int_aPPDUMaxTime             ;
   assign dynBWEn                  = int_dynBWEn                  ;
   assign numTryBWAcquisition      = int_numTryBWAcquisition      ;
   assign dropToLowerBW            = int_dropToLowerBW            ;
   assign defaultBWTXOP            = int_defaultBWTXOP            ;
   assign defaultBWTXOPV           = int_defaultBWTXOPV           ;
   assign bssBasicHTMCSSetUM       = int_bssBasicHTMCSSetUM       ;
   assign bssBasicHTMCSSetEM       = int_bssBasicHTMCSSetEM       ;
   assign bssBasicVHTMCSSet        = int_bssBasicVHTMCSSet        ;
   assign supportLSTP              = int_supportLSTP              ;
`ifdef RW_WLAN_COEX_EN                
   assign coexWlanChanFreq         = int_coexWlanChanFreq         ;
   assign coexWlanChanOffset       = int_coexWlanChanOffset       ;
   assign coexEnable               = int_coexEnable               ;
   assign coexPTIBcnData           = int_coexPTIBcnData           ;
   assign coexPTIBKData            = int_coexPTIBKData            ;
   assign coexPTIBEData            = int_coexPTIBEData            ;
   assign coexPTIVIData            = int_coexPTIVIData            ;
   assign coexPTIVOData            = int_coexPTIVOData            ;
   assign coexPTIMgt               = int_coexPTIMgt               ;
   assign coexPTICntl              = int_coexPTICntl              ;
   assign coexPTIAck               = int_coexPTIAck               ;
`endif // RW_WLAN_COEX_EN                
   assign debugPortSel2            = int_debugPortSel2            ;
   assign debugPortSel1            = int_debugPortSel1            ;
   assign navCounter               = int_navCounter               ;
   assign backoffOffset            = int_backoffOffset            ;
   assign rxReqForceDeassertion    = int_rxReqForceDeassertion    ;


  //////////////////////////////////////////////////////////////////////////////
  // Register write
  //////////////////////////////////////////////////////////////////////////////
  // apb_write_p:


  always @(posedge Clk or negedge hardRstClk_n)
  begin
    if (!hardRstClk_n) 
    begin
	
      //$port_g MACADDRLOWREG register.
      int_macAddrLow                <= 32'b0000000000000000000000000000000;
      //$port_g MACADDRHIREG register.
      int_macAddrHigh               <= 16'b000000000000000;
      //$port_g MACADDRLOWMASKREG register.
      int_macAddrLowMask            <= 32'b0000000000000000000000000000000;
      //$port_g MACADDRHIMASKREG register.
      int_macAddrHighMask           <= 16'b000000000000000;
      //$port_g BSSIDLOWREG register.
      int_bssIDLow                  <= 32'b0000000000000000000000000000000;
      //$port_g BSSIDHIREG register.
      int_bssIDHigh                 <= 16'b000000000000000;
      //$port_g BSSIDLOWMASKREG register.
      int_bssIDLowMask              <= 32'b0000000000000000000000000000000;
      //$port_g BSSIDHIMASKREG register.
      int_bssIDHighMask             <= 16'b000000000000000;
      //$port_g STATECNTRLREG register.
      int_nextState                 <= 4'b000;
      //$port_g SCANCNTRLREG register.
      int_probeDelay                <= 16'b000000000000000;
      //$port_g DOZECNTRL1REG register.
      int_atimW                     <= 15'b00000000000000;
      int_wakeupDTIM                <= 1'b0;
      int_listenInterval            <= 16'b000000000000000;
      //$port_g MACCNTRL1REG register.
      int_rxRIFSEn                  <= 1'b0;
      int_tsfMgtDisable             <= 1'b0;
      int_tsfUpdatedBySW            <= 1'b0;
      int_abgnMode                  <= 3'b11;
      int_keyStoRAMReset            <= 1'b0;
      int_mibTableReset             <= 1'b0;
      int_rateControllerMPIF        <= 1'b1;
      int_disableBAResp             <= 1'b0;
      int_disableCTSResp            <= 1'b0;
      int_disableACKResp            <= 1'b0;
      int_activeClkGating           <= 1'b1;
      int_enableLPClkSwitch         <= 1'b0;
      int_cfpAware                  <= 1'b0;
      int_pwrMgt                    <= 1'b0;
      int_ap                        <= 1'b0;
      int_bssType                   <= 1'b1;
      //$port_g MACERRRECCNTRLREG register.
      int_rxFlowCntrlEn             <= 1'b0;
      int_baPSBitmapReset           <= 1'b0;
      int_encrRxFIFOReset           <= 1'b0;
      int_macPHYIFFIFOReset         <= 1'b0;
      int_txFIFOReset               <= 1'b0;
      int_rxFIFOReset               <= 1'b0;
      int_hwFSMReset                <= 1'b0;
      int_useErrDet                 <= 1'b0;
      //$port_g MACERRSETSTATUSREG register.
      int_errInHWLevel3             <= 1'b0;
      int_errInTxRxLevel2           <= 1'b0;
      int_errInRxLevel1             <= 1'b0;
      int_errInTxLevel1             <= 1'b0;
      //$port_g MACERRCLEARSTATUSREG register.
      int_clearErrInHWLevel3        <= 1'b0;
      int_clearErrInTxRxLevel2      <= 1'b0;
      int_clearErrInRxLevel1        <= 1'b0;
      int_clearErrInTxLevel1        <= 1'b0;
      //$port_g RXCNTRLREG register.
      int_acceptUnknown             <= 1'b0;
      int_acceptOtherDataFrames     <= 1'b0;
      int_acceptQoSNull             <= 1'b1;
      int_acceptQCFWOData           <= 1'b0;
      int_acceptQData               <= 1'b1;
      int_acceptCFWOData            <= 1'b0;
      int_acceptData                <= 1'b1;
      int_acceptOtherCntrlFrames    <= 1'b0;
      int_acceptCFEnd               <= 1'b0;
      int_acceptACK                 <= 1'b0;
      int_acceptCTS                 <= 1'b0;
      int_acceptRTS                 <= 1'b0;
      int_acceptPSPoll              <= 1'b1;
      int_acceptBA                  <= 1'b1;
      int_acceptBAR                 <= 1'b1;
      int_acceptOtherMgmtFrames     <= 1'b1;
      int_acceptAllBeacon           <= 1'b0;
      int_acceptNotExpectedBA       <= 1'b0;
      int_acceptDecryptErrorFrames  <= 1'b0;
      int_acceptBeacon              <= 1'b1;
      int_acceptProbeResp           <= 1'b1;
      int_acceptProbeReq            <= 1'b1;
      int_acceptMyUnicast           <= 1'b1;
      int_acceptUnicast             <= 1'b0;
      int_acceptErrorFrames         <= 1'b0;
      int_acceptOtherBSSID          <= 1'b0;
      int_acceptBroadcast           <= 1'b1;
      int_acceptMulticast           <= 1'b0;
      int_dontDecrypt               <= 1'b0;
      int_excUnencrypted            <= 1'b0;
      //$port_g BCNCNTRL1REG register.
      int_noBcnTxTime               <= 8'd`NO_BCN_TX_TIME;
      int_impTBTTIn128Us            <= 1'b0;
      int_impTBTTPeriod             <= 7'd`IMP_TBTT_TIME;
      int_beaconInt                 <= 16'b000000000000000;
      //$port_g BCNCNTRL2REG register.
      int_aid                       <= 12'b00000000000;
      int_timOffset                 <= 8'b0000000;
      int_bcnUpdateOffset           <= 8'b0000000;
      //$port_g DTIMCFP1REG register.
      int_dtimUpdatedBySW           <= 1'b0;
      int_cfpPeriod                 <= 8'b0000000;
      int_dtimPeriod                <= 8'b0000000;
      //$port_g DTIMCFP2REG register.
      int_cfpMaxDuration            <= 16'b000000000000000;
      //$port_g RETRYLIMITSREG register.
      int_dot11LongRetryLimit       <= 8'b0000100;
      int_dot11ShortRetryLimit      <= 8'b0000111;
      //$port_g BBSERVICEREG register.
      int_maxPHYNtx                 <= 3'b10;
      int_bbServiceB                <= 8'b0000000;
      int_bbServiceA                <= 16'b000000000000000;
      //$port_g MAXPOWERLEVELREG register.
      int_dsssMaxPwrLevel           <= 8'b0000100;
      int_ofdmMaxPwrLevel           <= 8'b0000100;
      //$port_g ENCRKEY0REG register.
      int_encrKeyRAMWord0           <= 32'b0000000000000000000000000000000;
      //$port_g ENCRKEY1REG register.
      int_encrKeyRAMWord1           <= 32'b0000000000000000000000000000000;
      //$port_g ENCRKEY2REG register.
      int_encrKeyRAMWord2           <= 32'b0000000000000000000000000000000;
      //$port_g ENCRKEY3REG register.
      int_encrKeyRAMWord3           <= 32'b0000000000000000000000000000000;
      //$port_g ENCRMACADDRLOWREG register.
      int_macAddrRAMLow             <= 32'b11111111111111111111111111111111;
      //$port_g ENCRMACADDRHIGHREG register.
      int_macAddrRAMHigh            <= 16'b1111111111111111;
      //$port_g ENCRCNTRLREG register.
      int_newRead                   <= 1'b0;
      int_newWrite                  <= 1'b0;
      int_keyIndexRAM               <= 10'b000000000;
      int_cTypeRAM                  <= 3'b00;
      int_vlanIDRAM                 <= 4'b000;
      int_sppRAM                    <= 2'b0;
      int_useDefKeyRAM              <= 1'b0;
      int_cLenRAM                   <= 1'b0;
`ifdef RW_WAPI_EN                     
      //$port_g ENCRWPIINTKEY0REG register.
      int_encrIntKeyRAMWord0        <= 32'b0000000000000000000000000000000;
      //$port_g ENCRWPIINTKEY1REG register.
      int_encrIntKeyRAMWord1        <= 32'b0000000000000000000000000000000;
      //$port_g ENCRWPIINTKEY2REG register.
      int_encrIntKeyRAMWord2        <= 32'b0000000000000000000000000000000;
      //$port_g ENCRWPIINTKEY3REG register.
      int_encrIntKeyRAMWord3        <= 32'b0000000000000000000000000000000;
`endif // RW_WAPI_EN                     
      //$port_g RATESREG register.
      int_bssBasicRateSet           <= 12'b00101010000;
      //$port_g OLBCREG register.
      int_dsssCount                 <= 8'b0000000;
      int_ofdmCount                 <= 8'b0000000;
      int_olbcTimer                 <= 16'b000000000000000;
      //$port_g TIMINGS1REG register.
      int_txChainDelayInMACClk      <= 10'd`TX_CHAIN_DLY * 10'd`MAC_FREQ;
      int_txRFDelayInMACClk         <= 10'd`TX_RF_DLY * 10'd`MAC_FREQ;
      int_macCoreClkFreq            <= 8'd`MAC_FREQ;
      //$port_g TIMINGS2REG register.
      int_slotTimeInMACClk          <= 16'd`SHORT_SLOT * 16'd`MAC_FREQ;
      int_slotTime                  <= 8'd`SHORT_SLOT;
      //$port_g TIMINGS3REG register.
      int_rxRFDelayInMACClk         <= 10'd`RX_RF_DLY * 10'd`MAC_FREQ;
      int_txDelayRFOnInMACClk       <= 10'd`TX_DLY_RF_ON * 10'd`MAC_FREQ;
      int_macProcDelayInMACClk      <= 10'd`MAC_PROC_DELAY * 10'd`MAC_FREQ;
      //$port_g TIMINGS4REG register.
      int_radioWakeUpTime           <= 10'd`RADIOWAKEUP_TIME;
      int_radioChirpTime            <= 10'd`RADIO_CHIRP_TIME;
      //$port_g TIMINGS5REG register.
      int_sifsBInMACClk             <= 16'd`SIFS_B * 16'd`MAC_FREQ;
      int_sifsB                     <= 8'd`SIFS_B;
      //$port_g TIMINGS6REG register.
      int_sifsAInMACClk             <= 16'd`SIFS_A* 16'd`MAC_FREQ;
      int_sifsA                     <= 8'd`SIFS_A;
      //$port_g TIMINGS7REG register.
      int_rxCCADelay                <= 4'd`RX_CCA_DLY;
      int_rifs                      <= 8'd`RIFS ;
      //$port_g TIMINGS8REG register.
      int_rxStartDelayMIMO          <= 8'b0100001;
      int_rxStartDelayShort         <= 8'b1100000;
      int_rxStartDelayLong          <= 8'b11000000;
      int_rxStartDelayOFDM          <= 8'b0100001;
      //$port_g TIMINGS9REG register.
      int_rifsTOInMACClk            <= 10'd`RIFSTO * 10'd`MAC_FREQ;
      int_rifsInMACClk              <= 10'd`RIFS * 10'd`MAC_FREQ;
      int_txDMAProcDlyInMACClk      <= 10'd`TX_DMA_PROC_DLY * 10'd`MAC_FREQ;
      //$port_g PROTTRIGTIMERREG register.
      int_edcaTriggerTimer          <= 8'b0001001;
      //$port_g TXTRIGGERTIMERREG register.
      int_txPacketTimeout           <= 8'b0001111;
      int_txAbsoluteTimeout         <= 8'b10011100;
      //$port_g RXTRIGGERTIMERREG register.
      int_rxPayloadUsedCount        <= 8'b0001111;
      int_rxPacketTimeout           <= 8'b0001111;
      int_rxAbsoluteTimeout         <= 8'b10011100;
      //$port_g MIBTABLEWRITEREG register.
      int_mibValue                  <= 16'b000000000000000;
      int_mibWrite                  <= 1'b0;
      int_mibIncrementMode          <= 1'b1;
      int_mibTableIndex             <= 10'b000000000;
      //$port_g ABSTIMERREG0 register.
      int_absTimerValue0            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG1 register.
      int_absTimerValue1            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG2 register.
      int_absTimerValue2            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG3 register.
      int_absTimerValue3            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG4 register.
      int_absTimerValue4            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG5 register.
      int_absTimerValue5            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG6 register.
      int_absTimerValue6            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG7 register.
      int_absTimerValue7            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG8 register.
      int_absTimerValue8            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG9 register.
      int_absTimerValue9            <= 32'b0000000000000000000000000000000;
      //$port_g MAXRXLENGTHREG register.
      int_maxAllowedLength          <= 20'b0001111111111111111;
      //$port_g EDCAAC0REG register.
      int_txOpLimit0                <= 16'b000000000000000;
      int_cwMax0                    <= 4'b1010;
      int_cwMin0                    <= 4'b100;
      int_aifsn0                    <= 4'b111;
      //$port_g EDCAAC1REG register.
      int_txOpLimit1                <= 16'b000000000000000;
      int_cwMax1                    <= 4'b1010;
      int_cwMin1                    <= 4'b100;
      int_aifsn1                    <= 4'b011;
      //$port_g EDCAAC2REG register.
      int_txOpLimit2                <= 16'b000000001011110;
      int_cwMax2                    <= 4'b100;
      int_cwMin2                    <= 4'b011;
      int_aifsn2                    <= 4'b010;
      //$port_g EDCAAC3REG register.
      int_txOpLimit3                <= 16'b000000000101111;
      int_cwMax3                    <= 4'b011;
      int_cwMin3                    <= 4'b010;
      int_aifsn3                    <= 4'b010;
      //$port_g EDCACCABUSYREG register.
      int_ccaBusyDur                <= 32'b0000000000000000000000000000000;
      //$port_g EDCACNTRLREG register.
      int_keepTXOPOpen              <= 1'b0;
      int_remTXOPInDurField         <= 1'b0;
      int_sendCFEnd                 <= 1'b0;
      int_sendCFEndNow              <= 1'b0;
      //$port_g QUIETELEMENT1AREG register.
      int_quietDuration1            <= 16'b000000000000000;
      int_quietPeriod1              <= 8'b0000000;
      int_quietCount1               <= 8'b0000000;
      //$port_g QUIETELEMENT1BREG register.
      int_quietOffset1              <= 16'b000000000000000;
      //$port_g QUIETELEMENT2AREG register.
      int_quietDuration2            <= 16'b000000000000000;
      int_quietPeriod2              <= 8'b0000000;
      int_quietCount2               <= 8'b0000000;
      //$port_g QUIETELEMENT2BREG register.
      int_quietOffset2              <= 16'b000000000000000;
      //$port_g ADDCCABUSYSEC20REG register.
      int_ccaBusyDurSec20           <= 32'b0000000000000000000000000000000;
      //$port_g ADDCCABUSYSEC40REG register.
      int_ccaBusyDurSec40           <= 32'b0000000000000000000000000000000;
      //$port_g ADDCCABUSYSEC80REG register.
      int_ccaBusyDurSec80           <= 32'b0000000000000000000000000000000;
      //$port_g STBCCNTRLREG register.
      int_basicSTBCMCS              <= 7'b000000;
      int_dualCTSProt               <= 1'b0;
      int_ctsSTBCDur                <= 8'b0000000;
      int_cfEndSTBCDur              <= 16'b000000000000000;
      //$port_g STARTTX1REG register.
      int_startTxBW                 <= 2'b0;
      int_startTxPreType            <= 1'b0;
      int_startTxFormatMod          <= 3'b00;
      int_startTxMCSIndex0          <= 8'b0000000;
      int_startTxKSRIndex           <= 10'b000000000;
      int_startTxAC                 <= 2'b0;
      int_startTxFrmExType          <= 2'b0;
      int_startTxFrameEx            <= 1'b0;
      //$port_g STARTTX2REG register.
      int_durControlFrm             <= 16'b000000000000000;
      //$port_g STARTTX3REG register.
      int_startTxSMMIndex           <= 8'b0000000;
      int_startTxAntennaSet         <= 8'b0000000;
      int_startTxLSTP               <= 1'b0;
      int_startTxSmoothing          <= 1'b0;
      int_startTxShortGI            <= 1'b0;
      int_startTxNTx                <= 3'b00;
      int_startTxFecCoding          <= 1'b0;
      int_startTxSTBC               <= 2'b0;
      int_startTxNumExtnSS          <= 2'b0;
      //$port_g TXBWCNTRLREG register.
      int_maxSupportedBW            <= 2'b10;
      int_aPPDUMaxTime              <= 8'b0001010;
      int_dynBWEn                   <= 1'b0;
      int_numTryBWAcquisition       <= 3'b01;
      int_dropToLowerBW             <= 1'b1;
      int_defaultBWTXOP             <= 2'b0;
      int_defaultBWTXOPV            <= 1'b0;
      //$port_g HTMCSREG register.
      int_bssBasicHTMCSSetUM        <= 6'b00000;
      int_bssBasicHTMCSSetEM        <= 16'b1111111111111111;
      //$port_g VHTMCSREG register.
      int_bssBasicVHTMCSSet         <= 16'b1111111111111111;
      //$port_g LSTPREG register.
      int_supportLSTP               <= 1'b0;
`ifdef RW_WLAN_COEX_EN                
      //$port_g COEXCONTROLREG register.
      int_coexWlanChanFreq          <= 7'b000000;
      int_coexWlanChanOffset        <= 1'b0;
      int_coexEnable                <= 1'b0;
      //$port_g COEXPTIREG register.
      int_coexPTIBcnData            <= 4'b000;
      int_coexPTIBKData             <= 4'b000;
      int_coexPTIBEData             <= 4'b010;
      int_coexPTIVIData             <= 4'b100;
      int_coexPTIVOData             <= 4'b110;
      int_coexPTIMgt                <= 4'b110;
      int_coexPTICntl               <= 4'b011;
      int_coexPTIAck                <= 4'b111;
`endif // RW_WLAN_COEX_EN                
      //$port_g DEBUGPORTSELREG register.
      int_debugPortSel2             <= 8'b0000000;
      int_debugPortSel1             <= 8'b0000000;
      //$port_g DEBUGNAVREG register.
      int_navCounter                <= 26'b0000000000000000000000000;
      //$port_g DEBUGCWREG register.
      int_backoffOffset             <= 2'b0;
      //$port_g DEBUGPHYREG register.
      int_rxReqForceDeassertion     <= 1'b0;
    end
    else if (!softRstClk_n) 
    begin
	
      //$port_g MACADDRLOWREG register.
      int_macAddrLow                <= 32'b0000000000000000000000000000000;
      //$port_g MACADDRHIREG register.
      int_macAddrHigh               <= 16'b000000000000000;
      //$port_g MACADDRLOWMASKREG register.
      int_macAddrLowMask            <= 32'b0000000000000000000000000000000;
      //$port_g MACADDRHIMASKREG register.
      int_macAddrHighMask           <= 16'b000000000000000;
      //$port_g BSSIDLOWREG register.
      int_bssIDLow                  <= 32'b0000000000000000000000000000000;
      //$port_g BSSIDHIREG register.
      int_bssIDHigh                 <= 16'b000000000000000;
      //$port_g BSSIDLOWMASKREG register.
      int_bssIDLowMask              <= 32'b0000000000000000000000000000000;
      //$port_g BSSIDHIMASKREG register.
      int_bssIDHighMask             <= 16'b000000000000000;
      //$port_g STATECNTRLREG register.
      int_nextState                 <= 4'b000;
      //$port_g SCANCNTRLREG register.
      int_probeDelay                <= 16'b000000000000000;
      //$port_g DOZECNTRL1REG register.
      int_atimW                     <= 15'b00000000000000;
      int_wakeupDTIM                <= 1'b0;
      int_listenInterval            <= 16'b000000000000000;
      //$port_g MACCNTRL1REG register.
      int_rxRIFSEn                  <= 1'b0;
      int_tsfMgtDisable             <= 1'b0;
      int_tsfUpdatedBySW            <= 1'b0;
      int_abgnMode                  <= 3'b11;
      int_keyStoRAMReset            <= 1'b0;
      int_mibTableReset             <= 1'b0;
      int_rateControllerMPIF        <= 1'b1;
      int_disableBAResp             <= 1'b0;
      int_disableCTSResp            <= 1'b0;
      int_disableACKResp            <= 1'b0;
      int_activeClkGating           <= 1'b1;
      int_enableLPClkSwitch         <= 1'b0;
      int_cfpAware                  <= 1'b0;
      int_pwrMgt                    <= 1'b0;
      int_ap                        <= 1'b0;
      int_bssType                   <= 1'b1;
      //$port_g MACERRRECCNTRLREG register.
      int_rxFlowCntrlEn             <= 1'b0;
      int_baPSBitmapReset           <= 1'b0;
      int_encrRxFIFOReset           <= 1'b0;
      int_macPHYIFFIFOReset         <= 1'b0;
      int_txFIFOReset               <= 1'b0;
      int_rxFIFOReset               <= 1'b0;
      int_hwFSMReset                <= 1'b0;
      int_useErrDet                 <= 1'b0;
      //$port_g MACERRSETSTATUSREG register.
      int_errInHWLevel3             <= 1'b0;
      int_errInTxRxLevel2           <= 1'b0;
      int_errInRxLevel1             <= 1'b0;
      int_errInTxLevel1             <= 1'b0;
      //$port_g MACERRCLEARSTATUSREG register.
      int_clearErrInHWLevel3        <= 1'b0;
      int_clearErrInTxRxLevel2      <= 1'b0;
      int_clearErrInRxLevel1        <= 1'b0;
      int_clearErrInTxLevel1        <= 1'b0;
      //$port_g RXCNTRLREG register.
      int_acceptUnknown             <= 1'b0;
      int_acceptOtherDataFrames     <= 1'b0;
      int_acceptQoSNull             <= 1'b1;
      int_acceptQCFWOData           <= 1'b0;
      int_acceptQData               <= 1'b1;
      int_acceptCFWOData            <= 1'b0;
      int_acceptData                <= 1'b1;
      int_acceptOtherCntrlFrames    <= 1'b0;
      int_acceptCFEnd               <= 1'b0;
      int_acceptACK                 <= 1'b0;
      int_acceptCTS                 <= 1'b0;
      int_acceptRTS                 <= 1'b0;
      int_acceptPSPoll              <= 1'b1;
      int_acceptBA                  <= 1'b1;
      int_acceptBAR                 <= 1'b1;
      int_acceptOtherMgmtFrames     <= 1'b1;
      int_acceptAllBeacon           <= 1'b0;
      int_acceptNotExpectedBA       <= 1'b0;
      int_acceptDecryptErrorFrames  <= 1'b0;
      int_acceptBeacon              <= 1'b1;
      int_acceptProbeResp           <= 1'b1;
      int_acceptProbeReq            <= 1'b1;
      int_acceptMyUnicast           <= 1'b1;
      int_acceptUnicast             <= 1'b0;
      int_acceptErrorFrames         <= 1'b0;
      int_acceptOtherBSSID          <= 1'b0;
      int_acceptBroadcast           <= 1'b1;
      int_acceptMulticast           <= 1'b0;
      int_dontDecrypt               <= 1'b0;
      int_excUnencrypted            <= 1'b0;
      //$port_g BCNCNTRL1REG register.
      int_noBcnTxTime               <= 8'd`NO_BCN_TX_TIME;
      int_impTBTTIn128Us            <= 1'b0;
      int_impTBTTPeriod             <= 7'd`IMP_TBTT_TIME;
      int_beaconInt                 <= 16'b000000000000000;
      //$port_g BCNCNTRL2REG register.
      int_aid                       <= 12'b00000000000;
      int_timOffset                 <= 8'b0000000;
      int_bcnUpdateOffset           <= 8'b0000000;
      //$port_g DTIMCFP1REG register.
      int_dtimUpdatedBySW           <= 1'b0;
      int_cfpPeriod                 <= 8'b0000000;
      int_dtimPeriod                <= 8'b0000000;
      //$port_g DTIMCFP2REG register.
      int_cfpMaxDuration            <= 16'b000000000000000;
      //$port_g RETRYLIMITSREG register.
      int_dot11LongRetryLimit       <= 8'b0000100;
      int_dot11ShortRetryLimit      <= 8'b0000111;
      //$port_g BBSERVICEREG register.
      int_maxPHYNtx                 <= 3'b10;
      int_bbServiceB                <= 8'b0000000;
      int_bbServiceA                <= 16'b000000000000000;
      //$port_g MAXPOWERLEVELREG register.
      int_dsssMaxPwrLevel           <= 8'b0000100;
      int_ofdmMaxPwrLevel           <= 8'b0000100;
      //$port_g ENCRKEY0REG register.
      int_encrKeyRAMWord0           <= 32'b0000000000000000000000000000000;
      //$port_g ENCRKEY1REG register.
      int_encrKeyRAMWord1           <= 32'b0000000000000000000000000000000;
      //$port_g ENCRKEY2REG register.
      int_encrKeyRAMWord2           <= 32'b0000000000000000000000000000000;
      //$port_g ENCRKEY3REG register.
      int_encrKeyRAMWord3           <= 32'b0000000000000000000000000000000;
      //$port_g ENCRMACADDRLOWREG register.
      int_macAddrRAMLow             <= 32'b11111111111111111111111111111111;
      //$port_g ENCRMACADDRHIGHREG register.
      int_macAddrRAMHigh            <= 16'b1111111111111111;
      //$port_g ENCRCNTRLREG register.
      int_newRead                   <= 1'b0;
      int_newWrite                  <= 1'b0;
      int_keyIndexRAM               <= 10'b000000000;
      int_cTypeRAM                  <= 3'b00;
      int_vlanIDRAM                 <= 4'b000;
      int_sppRAM                    <= 2'b0;
      int_useDefKeyRAM              <= 1'b0;
      int_cLenRAM                   <= 1'b0;
`ifdef RW_WAPI_EN                     
      //$port_g ENCRWPIINTKEY0REG register.
      int_encrIntKeyRAMWord0        <= 32'b0000000000000000000000000000000;
      //$port_g ENCRWPIINTKEY1REG register.
      int_encrIntKeyRAMWord1        <= 32'b0000000000000000000000000000000;
      //$port_g ENCRWPIINTKEY2REG register.
      int_encrIntKeyRAMWord2        <= 32'b0000000000000000000000000000000;
      //$port_g ENCRWPIINTKEY3REG register.
      int_encrIntKeyRAMWord3        <= 32'b0000000000000000000000000000000;
`endif // RW_WAPI_EN                     
      //$port_g RATESREG register.
      int_bssBasicRateSet           <= 12'b00101010000;
      //$port_g OLBCREG register.
      int_dsssCount                 <= 8'b0000000;
      int_ofdmCount                 <= 8'b0000000;
      int_olbcTimer                 <= 16'b000000000000000;
      //$port_g TIMINGS1REG register.
      int_txChainDelayInMACClk      <= 10'd`TX_CHAIN_DLY * 10'd`MAC_FREQ;
      int_txRFDelayInMACClk         <= 10'd`TX_RF_DLY * 10'd`MAC_FREQ;
      int_macCoreClkFreq            <= 8'd`MAC_FREQ;
      //$port_g TIMINGS2REG register.
      int_slotTimeInMACClk          <= 16'd`SHORT_SLOT * 16'd`MAC_FREQ;
      int_slotTime                  <= 8'd`SHORT_SLOT;
      //$port_g TIMINGS3REG register.
      int_rxRFDelayInMACClk         <= 10'd`RX_RF_DLY * 10'd`MAC_FREQ;
      int_txDelayRFOnInMACClk       <= 10'd`TX_DLY_RF_ON * 10'd`MAC_FREQ;
      int_macProcDelayInMACClk      <= 10'd`MAC_PROC_DELAY * 10'd`MAC_FREQ;
      //$port_g TIMINGS4REG register.
      int_radioWakeUpTime           <= 10'd`RADIOWAKEUP_TIME;
      int_radioChirpTime            <= 10'd`RADIO_CHIRP_TIME;
      //$port_g TIMINGS5REG register.
      int_sifsBInMACClk             <= 16'd`SIFS_B * 16'd`MAC_FREQ;
      int_sifsB                     <= 8'd`SIFS_B;
      //$port_g TIMINGS6REG register.
      int_sifsAInMACClk             <= 16'd`SIFS_A* 16'd`MAC_FREQ;
      int_sifsA                     <= 8'd`SIFS_A;
      //$port_g TIMINGS7REG register.
      int_rxCCADelay                <= 4'd`RX_CCA_DLY;
      int_rifs                      <= 8'd`RIFS ;
      //$port_g TIMINGS8REG register.
      int_rxStartDelayMIMO          <= 8'b0100001;
      int_rxStartDelayShort         <= 8'b1100000;
      int_rxStartDelayLong          <= 8'b11000000;
      int_rxStartDelayOFDM          <= 8'b0100001;
      //$port_g TIMINGS9REG register.
      int_rifsTOInMACClk            <= 10'd`RIFSTO * 10'd`MAC_FREQ;
      int_rifsInMACClk              <= 10'd`RIFS * 10'd`MAC_FREQ;
      int_txDMAProcDlyInMACClk      <= 10'd`TX_DMA_PROC_DLY * 10'd`MAC_FREQ;
      //$port_g PROTTRIGTIMERREG register.
      int_edcaTriggerTimer          <= 8'b0001001;
      //$port_g TXTRIGGERTIMERREG register.
      int_txPacketTimeout           <= 8'b0001111;
      int_txAbsoluteTimeout         <= 8'b10011100;
      //$port_g RXTRIGGERTIMERREG register.
      int_rxPayloadUsedCount        <= 8'b0001111;
      int_rxPacketTimeout           <= 8'b0001111;
      int_rxAbsoluteTimeout         <= 8'b10011100;
      //$port_g MIBTABLEWRITEREG register.
      int_mibValue                  <= 16'b000000000000000;
      int_mibWrite                  <= 1'b0;
      int_mibIncrementMode          <= 1'b1;
      int_mibTableIndex             <= 10'b000000000;
      //$port_g ABSTIMERREG0 register.
      int_absTimerValue0            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG1 register.
      int_absTimerValue1            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG2 register.
      int_absTimerValue2            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG3 register.
      int_absTimerValue3            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG4 register.
      int_absTimerValue4            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG5 register.
      int_absTimerValue5            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG6 register.
      int_absTimerValue6            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG7 register.
      int_absTimerValue7            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG8 register.
      int_absTimerValue8            <= 32'b0000000000000000000000000000000;
      //$port_g ABSTIMERREG9 register.
      int_absTimerValue9            <= 32'b0000000000000000000000000000000;
      //$port_g MAXRXLENGTHREG register.
      int_maxAllowedLength          <= 20'b0001111111111111111;
      //$port_g EDCAAC0REG register.
      int_txOpLimit0                <= 16'b000000000000000;
      int_cwMax0                    <= 4'b1010;
      int_cwMin0                    <= 4'b100;
      int_aifsn0                    <= 4'b111;
      //$port_g EDCAAC1REG register.
      int_txOpLimit1                <= 16'b000000000000000;
      int_cwMax1                    <= 4'b1010;
      int_cwMin1                    <= 4'b100;
      int_aifsn1                    <= 4'b011;
      //$port_g EDCAAC2REG register.
      int_txOpLimit2                <= 16'b000000001011110;
      int_cwMax2                    <= 4'b100;
      int_cwMin2                    <= 4'b011;
      int_aifsn2                    <= 4'b010;
      //$port_g EDCAAC3REG register.
      int_txOpLimit3                <= 16'b000000000101111;
      int_cwMax3                    <= 4'b011;
      int_cwMin3                    <= 4'b010;
      int_aifsn3                    <= 4'b010;
      //$port_g EDCACCABUSYREG register.
      int_ccaBusyDur                <= 32'b0000000000000000000000000000000;
      //$port_g EDCACNTRLREG register.
      int_keepTXOPOpen              <= 1'b0;
      int_remTXOPInDurField         <= 1'b0;
      int_sendCFEnd                 <= 1'b0;
      int_sendCFEndNow              <= 1'b0;
      //$port_g QUIETELEMENT1AREG register.
      int_quietDuration1            <= 16'b000000000000000;
      int_quietPeriod1              <= 8'b0000000;
      int_quietCount1               <= 8'b0000000;
      //$port_g QUIETELEMENT1BREG register.
      int_quietOffset1              <= 16'b000000000000000;
      //$port_g QUIETELEMENT2AREG register.
      int_quietDuration2            <= 16'b000000000000000;
      int_quietPeriod2              <= 8'b0000000;
      int_quietCount2               <= 8'b0000000;
      //$port_g QUIETELEMENT2BREG register.
      int_quietOffset2              <= 16'b000000000000000;
      //$port_g ADDCCABUSYSEC20REG register.
      int_ccaBusyDurSec20           <= 32'b0000000000000000000000000000000;
      //$port_g ADDCCABUSYSEC40REG register.
      int_ccaBusyDurSec40           <= 32'b0000000000000000000000000000000;
      //$port_g ADDCCABUSYSEC80REG register.
      int_ccaBusyDurSec80           <= 32'b0000000000000000000000000000000;
      //$port_g STBCCNTRLREG register.
      int_basicSTBCMCS              <= 7'b000000;
      int_dualCTSProt               <= 1'b0;
      int_ctsSTBCDur                <= 8'b0000000;
      int_cfEndSTBCDur              <= 16'b000000000000000;
      //$port_g STARTTX1REG register.
      int_startTxBW                 <= 2'b0;
      int_startTxPreType            <= 1'b0;
      int_startTxFormatMod          <= 3'b00;
      int_startTxMCSIndex0          <= 8'b0000000;
      int_startTxKSRIndex           <= 10'b000000000;
      int_startTxAC                 <= 2'b0;
      int_startTxFrmExType          <= 2'b0;
      int_startTxFrameEx            <= 1'b0;
      //$port_g STARTTX2REG register.
      int_durControlFrm             <= 16'b000000000000000;
      //$port_g STARTTX3REG register.
      int_startTxSMMIndex           <= 8'b0000000;
      int_startTxAntennaSet         <= 8'b0000000;
      int_startTxLSTP               <= 1'b0;
      int_startTxSmoothing          <= 1'b0;
      int_startTxShortGI            <= 1'b0;
      int_startTxNTx                <= 3'b00;
      int_startTxFecCoding          <= 1'b0;
      int_startTxSTBC               <= 2'b0;
      int_startTxNumExtnSS          <= 2'b0;
      //$port_g TXBWCNTRLREG register.
      int_maxSupportedBW            <= 2'b10;
      int_aPPDUMaxTime              <= 8'b0001010;
      int_dynBWEn                   <= 1'b0;
      int_numTryBWAcquisition       <= 3'b01;
      int_dropToLowerBW             <= 1'b1;
      int_defaultBWTXOP             <= 2'b0;
      int_defaultBWTXOPV            <= 1'b0;
      //$port_g HTMCSREG register.
      int_bssBasicHTMCSSetUM        <= 6'b00000;
      int_bssBasicHTMCSSetEM        <= 16'b1111111111111111;
      //$port_g VHTMCSREG register.
      int_bssBasicVHTMCSSet         <= 16'b1111111111111111;
      //$port_g LSTPREG register.
      int_supportLSTP               <= 1'b0;
`ifdef RW_WLAN_COEX_EN                
      //$port_g COEXCONTROLREG register.
      int_coexWlanChanFreq          <= 7'b000000;
      int_coexWlanChanOffset        <= 1'b0;
      int_coexEnable                <= 1'b0;
      //$port_g COEXPTIREG register.
      int_coexPTIBcnData            <= 4'b000;
      int_coexPTIBKData             <= 4'b000;
      int_coexPTIBEData             <= 4'b010;
      int_coexPTIVIData             <= 4'b100;
      int_coexPTIVOData             <= 4'b110;
      int_coexPTIMgt                <= 4'b110;
      int_coexPTICntl               <= 4'b011;
      int_coexPTIAck                <= 4'b111;
`endif // RW_WLAN_COEX_EN                
      //$port_g DEBUGPORTSELREG register.
      int_debugPortSel2             <= 8'b0000000;
      int_debugPortSel1             <= 8'b0000000;
      //$port_g DEBUGNAVREG register.
      int_navCounter                <= 26'b0000000000000000000000000;
      //$port_g DEBUGCWREG register.
      int_backoffOffset             <= 2'b0;
      //$port_g DEBUGPHYREG register.
      int_rxReqForceDeassertion     <= 1'b0;
    end
    
    else
    begin
      if (nextStateInValid)
        int_nextState                 <= nextStateIn;
      if (tsfUpdatedBySWInValid)
        int_tsfUpdatedBySW            <= tsfUpdatedBySWIn;
      if (keyStoRAMResetInValid)
        int_keyStoRAMReset            <= keyStoRAMResetIn;
      if (mibTableResetInValid)
        int_mibTableReset             <= mibTableResetIn;
      if (baPSBitmapResetInValid)
        int_baPSBitmapReset           <= baPSBitmapResetIn;
      if (encrRxFIFOResetInValid)
        int_encrRxFIFOReset           <= encrRxFIFOResetIn;
      if (macPHYIFFIFOResetInValid)
        int_macPHYIFFIFOReset         <= macPHYIFFIFOResetIn;
      if (txFIFOResetInValid)
        int_txFIFOReset               <= txFIFOResetIn;
      if (rxFIFOResetInValid)
        int_rxFIFOReset               <= rxFIFOResetIn;
      if (hwFSMResetInValid)
        int_hwFSMReset                <= hwFSMResetIn;
      if (dtimUpdatedBySWInValid)
        int_dtimUpdatedBySW           <= dtimUpdatedBySWIn;
      if (cfpPeriodInValid)
        int_cfpPeriod                 <= cfpPeriodIn;
      if (dtimPeriodInValid)
        int_dtimPeriod                <= dtimPeriodIn;
      if (encrKeyRAMWord0InValid)
        int_encrKeyRAMWord0           <= encrKeyRAMWord0In;
      if (encrKeyRAMWord1InValid)
        int_encrKeyRAMWord1           <= encrKeyRAMWord1In;
      if (encrKeyRAMWord2InValid)
        int_encrKeyRAMWord2           <= encrKeyRAMWord2In;
      if (encrKeyRAMWord3InValid)
        int_encrKeyRAMWord3           <= encrKeyRAMWord3In;
      if (macAddrRAMLowInValid)
        int_macAddrRAMLow             <= macAddrRAMLowIn;
      if (macAddrRAMHighInValid)
        int_macAddrRAMHigh            <= macAddrRAMHighIn;
      if (newReadInValid)
        int_newRead                   <= newReadIn;
      if (newWriteInValid)
        int_newWrite                  <= newWriteIn;
      if (cTypeRAMInValid)
        int_cTypeRAM                  <= cTypeRAMIn;
      if (vlanIDRAMInValid)
        int_vlanIDRAM                 <= vlanIDRAMIn;
      if (sppRAMInValid)
        int_sppRAM                    <= sppRAMIn;
      if (useDefKeyRAMInValid)
        int_useDefKeyRAM              <= useDefKeyRAMIn;
      if (cLenRAMInValid)
        int_cLenRAM                   <= cLenRAMIn;
`ifdef RW_WAPI_EN                     
      if (encrIntKeyRAMWord0InValid)
        int_encrIntKeyRAMWord0        <= encrIntKeyRAMWord0In;
      if (encrIntKeyRAMWord1InValid)
        int_encrIntKeyRAMWord1        <= encrIntKeyRAMWord1In;
      if (encrIntKeyRAMWord2InValid)
        int_encrIntKeyRAMWord2        <= encrIntKeyRAMWord2In;
      if (encrIntKeyRAMWord3InValid)
        int_encrIntKeyRAMWord3        <= encrIntKeyRAMWord3In;
`endif // RW_WAPI_EN                     
      if (mibWriteInValid)
        int_mibWrite                  <= mibWriteIn;
      if (ccaBusyDurInValid)
        int_ccaBusyDur                <= ccaBusyDurIn;
      if (sendCFEndNowInValid)
        int_sendCFEndNow              <= sendCFEndNowIn;
      if (quietDuration1InValid)
        int_quietDuration1            <= quietDuration1In;
      if (quietPeriod1InValid)
        int_quietPeriod1              <= quietPeriod1In;
      if (quietCount1InValid)
        int_quietCount1               <= quietCount1In;
      if (quietOffset1InValid)
        int_quietOffset1              <= quietOffset1In;
      if (quietDuration2InValid)
        int_quietDuration2            <= quietDuration2In;
      if (quietPeriod2InValid)
        int_quietPeriod2              <= quietPeriod2In;
      if (quietCount2InValid)
        int_quietCount2               <= quietCount2In;
      if (quietOffset2InValid)
        int_quietOffset2              <= quietOffset2In;
      if (ccaBusyDurSec20InValid)
        int_ccaBusyDurSec20           <= ccaBusyDurSec20In;
      if (ccaBusyDurSec40InValid)
        int_ccaBusyDurSec40           <= ccaBusyDurSec40In;
      if (ccaBusyDurSec80InValid)
        int_ccaBusyDurSec80           <= ccaBusyDurSec80In;
      if (startTxFrameExInValid)
        int_startTxFrameEx            <= startTxFrameExIn;
`ifdef RW_WLAN_COEX_EN                
`endif // RW_WLAN_COEX_EN                
      if (navCounterInValid)
        int_navCounter                <= navCounterIn;
      if(regSel && regWrite)
      begin
        case(regAddr)

          //$port_g Write MACADDRLOWREG register.
          MACADDRLOWREG_ADDR_CT : begin
            int_macAddrLow                <= regWriteData[31 : 0];
          end

          //$port_g Write MACADDRHIREG register.
          MACADDRHIREG_ADDR_CT : begin
            int_macAddrHigh               <= regWriteData[15 : 0];
          end

          //$port_g Write MACADDRLOWMASKREG register.
          MACADDRLOWMASKREG_ADDR_CT : begin
            int_macAddrLowMask            <= regWriteData[31 : 0];
          end

          //$port_g Write MACADDRHIMASKREG register.
          MACADDRHIMASKREG_ADDR_CT : begin
            int_macAddrHighMask           <= regWriteData[15 : 0];
          end

          //$port_g Write BSSIDLOWREG register.
          BSSIDLOWREG_ADDR_CT : begin
            int_bssIDLow                  <= regWriteData[31 : 0];
          end

          //$port_g Write BSSIDHIREG register.
          BSSIDHIREG_ADDR_CT : begin
            int_bssIDHigh                 <= regWriteData[15 : 0];
          end

          //$port_g Write BSSIDLOWMASKREG register.
          BSSIDLOWMASKREG_ADDR_CT : begin
            int_bssIDLowMask              <= regWriteData[31 : 0];
          end

          //$port_g Write BSSIDHIMASKREG register.
          BSSIDHIMASKREG_ADDR_CT : begin
            int_bssIDHighMask             <= regWriteData[15 : 0];
          end

          //$port_g Write STATECNTRLREG register.
          STATECNTRLREG_ADDR_CT : begin
            int_nextState                 <= regWriteData[7 : 4];
          end

          //$port_g Write SCANCNTRLREG register.
          SCANCNTRLREG_ADDR_CT : begin
            int_probeDelay                <= regWriteData[15 : 0];
          end

          //$port_g Write DOZECNTRL1REG register.
          DOZECNTRL1REG_ADDR_CT : begin
            int_atimW                     <= regWriteData[31 : 17];
            int_wakeupDTIM                <= regWriteData[16];
            int_listenInterval            <= regWriteData[15 : 0];
          end

          //$port_g Write MACCNTRL1REG register.
          MACCNTRL1REG_ADDR_CT : begin
            int_rxRIFSEn                  <= regWriteData[26];
            int_tsfMgtDisable             <= regWriteData[25];
            int_tsfUpdatedBySW            <= regWriteData[24];
            int_abgnMode                  <= regWriteData[16 : 14];
            int_keyStoRAMReset            <= regWriteData[13];
            int_mibTableReset             <= regWriteData[12];
            int_rateControllerMPIF        <= regWriteData[11];
            int_disableBAResp             <= regWriteData[10];
            int_disableCTSResp            <= regWriteData[9];
            int_disableACKResp            <= regWriteData[8];
            int_activeClkGating           <= regWriteData[7];
            int_enableLPClkSwitch         <= regWriteData[6];
            int_cfpAware                  <= regWriteData[3];
            int_pwrMgt                    <= regWriteData[2];
            int_ap                        <= regWriteData[1];
            int_bssType                   <= regWriteData[0];
          end

          //$port_g Write MACERRRECCNTRLREG register.
          MACERRRECCNTRLREG_ADDR_CT : begin
            int_rxFlowCntrlEn             <= regWriteData[16];
            int_baPSBitmapReset           <= regWriteData[7];
            int_encrRxFIFOReset           <= regWriteData[6];
            int_macPHYIFFIFOReset         <= regWriteData[5];
            int_txFIFOReset               <= regWriteData[4];
            int_rxFIFOReset               <= regWriteData[3];
            int_hwFSMReset                <= regWriteData[2];
            int_useErrDet                 <= regWriteData[1];
          end

          //$port_g Write MACERRSETSTATUSREG register.
          MACERRSETSTATUSREG_ADDR_CT : begin
            int_errInHWLevel3             <= regWriteData[3];
            int_errInTxRxLevel2           <= regWriteData[2];
            int_errInRxLevel1             <= regWriteData[1];
            int_errInTxLevel1             <= regWriteData[0];
          end

          //$port_g Write MACERRCLEARSTATUSREG register.
          MACERRCLEARSTATUSREG_ADDR_CT : begin
            int_clearErrInHWLevel3        <= regWriteData[3];
            int_clearErrInTxRxLevel2      <= regWriteData[2];
            int_clearErrInRxLevel1        <= regWriteData[1];
            int_clearErrInTxLevel1        <= regWriteData[0];
          end

          //$port_g Write RXCNTRLREG register.
          RXCNTRLREG_ADDR_CT : begin
            int_acceptUnknown             <= regWriteData[30];
            int_acceptOtherDataFrames     <= regWriteData[29];
            int_acceptQoSNull             <= regWriteData[28];
            int_acceptQCFWOData           <= regWriteData[27];
            int_acceptQData               <= regWriteData[26];
            int_acceptCFWOData            <= regWriteData[25];
            int_acceptData                <= regWriteData[24];
            int_acceptOtherCntrlFrames    <= regWriteData[23];
            int_acceptCFEnd               <= regWriteData[22];
            int_acceptACK                 <= regWriteData[21];
            int_acceptCTS                 <= regWriteData[20];
            int_acceptRTS                 <= regWriteData[19];
            int_acceptPSPoll              <= regWriteData[18];
            int_acceptBA                  <= regWriteData[17];
            int_acceptBAR                 <= regWriteData[16];
            int_acceptOtherMgmtFrames     <= regWriteData[15];
            int_acceptAllBeacon           <= regWriteData[13];
            int_acceptNotExpectedBA       <= regWriteData[12];
            int_acceptDecryptErrorFrames  <= regWriteData[11];
            int_acceptBeacon              <= regWriteData[10];
            int_acceptProbeResp           <= regWriteData[9];
            int_acceptProbeReq            <= regWriteData[8];
            int_acceptMyUnicast           <= regWriteData[7];
            int_acceptUnicast             <= regWriteData[6];
            int_acceptErrorFrames         <= regWriteData[5];
            int_acceptOtherBSSID          <= regWriteData[4];
            int_acceptBroadcast           <= regWriteData[3];
            int_acceptMulticast           <= regWriteData[2];
            int_dontDecrypt               <= regWriteData[1];
            int_excUnencrypted            <= regWriteData[0];
          end

          //$port_g Write BCNCNTRL1REG register.
          BCNCNTRL1REG_ADDR_CT : begin
            int_noBcnTxTime               <= regWriteData[31 : 24];
            int_impTBTTIn128Us            <= regWriteData[23];
            int_impTBTTPeriod             <= regWriteData[22 : 16];
            int_beaconInt                 <= regWriteData[15 : 0];
          end

          //$port_g Write BCNCNTRL2REG register.
          BCNCNTRL2REG_ADDR_CT : begin
            int_aid                       <= regWriteData[27 : 16];
            int_timOffset                 <= regWriteData[15 : 8];
            int_bcnUpdateOffset           <= regWriteData[7 : 0];
          end

          //$port_g Write DTIMCFP1REG register.
          DTIMCFP1REG_ADDR_CT : begin
            int_dtimUpdatedBySW           <= regWriteData[31];
            int_cfpPeriod                 <= regWriteData[15 : 8];
            int_dtimPeriod                <= regWriteData[7 : 0];
          end

          //$port_g Write DTIMCFP2REG register.
          DTIMCFP2REG_ADDR_CT : begin
            int_cfpMaxDuration            <= regWriteData[15 : 0];
          end

          //$port_g Write RETRYLIMITSREG register.
          RETRYLIMITSREG_ADDR_CT : begin
            int_dot11LongRetryLimit       <= regWriteData[15 : 8];
            int_dot11ShortRetryLimit      <= regWriteData[7 : 0];
          end

          //$port_g Write BBSERVICEREG register.
          BBSERVICEREG_ADDR_CT : begin
            int_maxPHYNtx                 <= regWriteData[28 : 26];
            int_bbServiceB                <= regWriteData[23 : 16];
            int_bbServiceA                <= regWriteData[15 : 0];
          end

          //$port_g Write MAXPOWERLEVELREG register.
          MAXPOWERLEVELREG_ADDR_CT : begin
            int_dsssMaxPwrLevel           <= regWriteData[15 : 8];
            int_ofdmMaxPwrLevel           <= regWriteData[7 : 0];
          end

          //$port_g Write ENCRKEY0REG register.
          ENCRKEY0REG_ADDR_CT : begin
            int_encrKeyRAMWord0           <= regWriteData[31 : 0];
          end

          //$port_g Write ENCRKEY1REG register.
          ENCRKEY1REG_ADDR_CT : begin
            int_encrKeyRAMWord1           <= regWriteData[31 : 0];
          end

          //$port_g Write ENCRKEY2REG register.
          ENCRKEY2REG_ADDR_CT : begin
            int_encrKeyRAMWord2           <= regWriteData[31 : 0];
          end

          //$port_g Write ENCRKEY3REG register.
          ENCRKEY3REG_ADDR_CT : begin
            int_encrKeyRAMWord3           <= regWriteData[31 : 0];
          end

          //$port_g Write ENCRMACADDRLOWREG register.
          ENCRMACADDRLOWREG_ADDR_CT : begin
            int_macAddrRAMLow             <= regWriteData[31 : 0];
          end

          //$port_g Write ENCRMACADDRHIGHREG register.
          ENCRMACADDRHIGHREG_ADDR_CT : begin
            int_macAddrRAMHigh            <= regWriteData[15 : 0];
          end

          //$port_g Write ENCRCNTRLREG register.
          ENCRCNTRLREG_ADDR_CT : begin
            int_newRead                   <= regWriteData[31];
            int_newWrite                  <= regWriteData[30];
            int_keyIndexRAM               <= regWriteData[25 : 16];
            int_cTypeRAM                  <= regWriteData[10 : 8];
            int_vlanIDRAM                 <= regWriteData[7 : 4];
            int_sppRAM                    <= regWriteData[3 : 2];
            int_useDefKeyRAM              <= regWriteData[1];
            int_cLenRAM                   <= regWriteData[0];
          end
`ifdef RW_WAPI_EN                     

          //$port_g Write ENCRWPIINTKEY0REG register.
          ENCRWPIINTKEY0REG_ADDR_CT : begin
            int_encrIntKeyRAMWord0        <= regWriteData[31 : 0];
          end

          //$port_g Write ENCRWPIINTKEY1REG register.
          ENCRWPIINTKEY1REG_ADDR_CT : begin
            int_encrIntKeyRAMWord1        <= regWriteData[31 : 0];
          end

          //$port_g Write ENCRWPIINTKEY2REG register.
          ENCRWPIINTKEY2REG_ADDR_CT : begin
            int_encrIntKeyRAMWord2        <= regWriteData[31 : 0];
          end

          //$port_g Write ENCRWPIINTKEY3REG register.
          ENCRWPIINTKEY3REG_ADDR_CT : begin
            int_encrIntKeyRAMWord3        <= regWriteData[31 : 0];
          end
`endif // RW_WAPI_EN                     

          //$port_g Write RATESREG register.
          RATESREG_ADDR_CT : begin
            int_bssBasicRateSet           <= regWriteData[11 : 0];
          end

          //$port_g Write OLBCREG register.
          OLBCREG_ADDR_CT : begin
            int_dsssCount                 <= regWriteData[31 : 24];
            int_ofdmCount                 <= regWriteData[23 : 16];
            int_olbcTimer                 <= regWriteData[15 : 0];
          end

          //$port_g Write TIMINGS1REG register.
          TIMINGS1REG_ADDR_CT : begin
            int_txChainDelayInMACClk      <= regWriteData[27 : 18];
            int_txRFDelayInMACClk         <= regWriteData[17 : 8];
            int_macCoreClkFreq            <= regWriteData[7 : 0];
          end

          //$port_g Write TIMINGS2REG register.
          TIMINGS2REG_ADDR_CT : begin
            int_slotTimeInMACClk          <= regWriteData[23 : 8];
            int_slotTime                  <= regWriteData[7 : 0];
          end

          //$port_g Write TIMINGS3REG register.
          TIMINGS3REG_ADDR_CT : begin
            int_rxRFDelayInMACClk         <= regWriteData[29 : 20];
            int_txDelayRFOnInMACClk       <= regWriteData[19 : 10];
            int_macProcDelayInMACClk      <= regWriteData[9 : 0];
          end

          //$port_g Write TIMINGS4REG register.
          TIMINGS4REG_ADDR_CT : begin
            int_radioWakeUpTime           <= regWriteData[31 : 22];
            int_radioChirpTime            <= regWriteData[21 : 12];
          end

          //$port_g Write TIMINGS5REG register.
          TIMINGS5REG_ADDR_CT : begin
            int_sifsBInMACClk             <= regWriteData[23 : 8];
            int_sifsB                     <= regWriteData[7 : 0];
          end

          //$port_g Write TIMINGS6REG register.
          TIMINGS6REG_ADDR_CT : begin
            int_sifsAInMACClk             <= regWriteData[23 : 8];
            int_sifsA                     <= regWriteData[7 : 0];
          end

          //$port_g Write TIMINGS7REG register.
          TIMINGS7REG_ADDR_CT : begin
            int_rxCCADelay                <= regWriteData[11 : 8];
            int_rifs                      <= regWriteData[7 : 0];
          end

          //$port_g Write TIMINGS8REG register.
          TIMINGS8REG_ADDR_CT : begin
            int_rxStartDelayMIMO          <= regWriteData[31 : 24];
            int_rxStartDelayShort         <= regWriteData[23 : 16];
            int_rxStartDelayLong          <= regWriteData[15 : 8];
            int_rxStartDelayOFDM          <= regWriteData[7 : 0];
          end

          //$port_g Write TIMINGS9REG register.
          TIMINGS9REG_ADDR_CT : begin
            int_rifsTOInMACClk            <= regWriteData[29 : 20];
            int_rifsInMACClk              <= regWriteData[19 : 10];
            int_txDMAProcDlyInMACClk      <= regWriteData[9 : 0];
          end

          //$port_g Write PROTTRIGTIMERREG register.
          PROTTRIGTIMERREG_ADDR_CT : begin
            int_edcaTriggerTimer          <= regWriteData[7 : 0];
          end

          //$port_g Write TXTRIGGERTIMERREG register.
          TXTRIGGERTIMERREG_ADDR_CT : begin
            int_txPacketTimeout           <= regWriteData[15 : 8];
            int_txAbsoluteTimeout         <= regWriteData[7 : 0];
          end

          //$port_g Write RXTRIGGERTIMERREG register.
          RXTRIGGERTIMERREG_ADDR_CT : begin
            int_rxPayloadUsedCount        <= regWriteData[23 : 16];
            int_rxPacketTimeout           <= regWriteData[15 : 8];
            int_rxAbsoluteTimeout         <= regWriteData[7 : 0];
          end

          //$port_g Write MIBTABLEWRITEREG register.
          MIBTABLEWRITEREG_ADDR_CT : begin
            int_mibValue                  <= regWriteData[31 : 16];
            int_mibWrite                  <= regWriteData[15];
            int_mibIncrementMode          <= regWriteData[14];
            int_mibTableIndex             <= regWriteData[9 : 0];
          end

          //$port_g Write ABSTIMERREG0 register.
          ABSTIMERREG0_ADDR_CT : begin
            int_absTimerValue0            <= regWriteData[31 : 0];
          end

          //$port_g Write ABSTIMERREG1 register.
          ABSTIMERREG1_ADDR_CT : begin
            int_absTimerValue1            <= regWriteData[31 : 0];
          end

          //$port_g Write ABSTIMERREG2 register.
          ABSTIMERREG2_ADDR_CT : begin
            int_absTimerValue2            <= regWriteData[31 : 0];
          end

          //$port_g Write ABSTIMERREG3 register.
          ABSTIMERREG3_ADDR_CT : begin
            int_absTimerValue3            <= regWriteData[31 : 0];
          end

          //$port_g Write ABSTIMERREG4 register.
          ABSTIMERREG4_ADDR_CT : begin
            int_absTimerValue4            <= regWriteData[31 : 0];
          end

          //$port_g Write ABSTIMERREG5 register.
          ABSTIMERREG5_ADDR_CT : begin
            int_absTimerValue5            <= regWriteData[31 : 0];
          end

          //$port_g Write ABSTIMERREG6 register.
          ABSTIMERREG6_ADDR_CT : begin
            int_absTimerValue6            <= regWriteData[31 : 0];
          end

          //$port_g Write ABSTIMERREG7 register.
          ABSTIMERREG7_ADDR_CT : begin
            int_absTimerValue7            <= regWriteData[31 : 0];
          end

          //$port_g Write ABSTIMERREG8 register.
          ABSTIMERREG8_ADDR_CT : begin
            int_absTimerValue8            <= regWriteData[31 : 0];
          end

          //$port_g Write ABSTIMERREG9 register.
          ABSTIMERREG9_ADDR_CT : begin
            int_absTimerValue9            <= regWriteData[31 : 0];
          end

          //$port_g Write MAXRXLENGTHREG register.
          MAXRXLENGTHREG_ADDR_CT : begin
            int_maxAllowedLength          <= regWriteData[19 : 0];
          end

          //$port_g Write EDCAAC0REG register.
          EDCAAC0REG_ADDR_CT : begin
            int_txOpLimit0                <= regWriteData[27 : 12];
            int_cwMax0                    <= regWriteData[11 : 8];
            int_cwMin0                    <= regWriteData[7 : 4];
            int_aifsn0                    <= regWriteData[3 : 0];
          end

          //$port_g Write EDCAAC1REG register.
          EDCAAC1REG_ADDR_CT : begin
            int_txOpLimit1                <= regWriteData[27 : 12];
            int_cwMax1                    <= regWriteData[11 : 8];
            int_cwMin1                    <= regWriteData[7 : 4];
            int_aifsn1                    <= regWriteData[3 : 0];
          end

          //$port_g Write EDCAAC2REG register.
          EDCAAC2REG_ADDR_CT : begin
            int_txOpLimit2                <= regWriteData[27 : 12];
            int_cwMax2                    <= regWriteData[11 : 8];
            int_cwMin2                    <= regWriteData[7 : 4];
            int_aifsn2                    <= regWriteData[3 : 0];
          end

          //$port_g Write EDCAAC3REG register.
          EDCAAC3REG_ADDR_CT : begin
            int_txOpLimit3                <= regWriteData[27 : 12];
            int_cwMax3                    <= regWriteData[11 : 8];
            int_cwMin3                    <= regWriteData[7 : 4];
            int_aifsn3                    <= regWriteData[3 : 0];
          end

          //$port_g Write EDCACCABUSYREG register.
          EDCACCABUSYREG_ADDR_CT : begin
            int_ccaBusyDur                <= regWriteData[31 : 0];
          end

          //$port_g Write EDCACNTRLREG register.
          EDCACNTRLREG_ADDR_CT : begin
            int_keepTXOPOpen              <= regWriteData[5];
            int_remTXOPInDurField         <= regWriteData[4];
            int_sendCFEnd                 <= regWriteData[1];
            int_sendCFEndNow              <= regWriteData[0];
          end

          //$port_g Write QUIETELEMENT1AREG register.
          QUIETELEMENT1AREG_ADDR_CT : begin
            int_quietDuration1            <= regWriteData[31 : 16];
            int_quietPeriod1              <= regWriteData[15 : 8];
            int_quietCount1               <= regWriteData[7 : 0];
          end

          //$port_g Write QUIETELEMENT1BREG register.
          QUIETELEMENT1BREG_ADDR_CT : begin
            int_quietOffset1              <= regWriteData[15 : 0];
          end

          //$port_g Write QUIETELEMENT2AREG register.
          QUIETELEMENT2AREG_ADDR_CT : begin
            int_quietDuration2            <= regWriteData[31 : 16];
            int_quietPeriod2              <= regWriteData[15 : 8];
            int_quietCount2               <= regWriteData[7 : 0];
          end

          //$port_g Write QUIETELEMENT2BREG register.
          QUIETELEMENT2BREG_ADDR_CT : begin
            int_quietOffset2              <= regWriteData[15 : 0];
          end

          //$port_g Write ADDCCABUSYSEC20REG register.
          ADDCCABUSYSEC20REG_ADDR_CT : begin
            int_ccaBusyDurSec20           <= regWriteData[31 : 0];
          end

          //$port_g Write ADDCCABUSYSEC40REG register.
          ADDCCABUSYSEC40REG_ADDR_CT : begin
            int_ccaBusyDurSec40           <= regWriteData[31 : 0];
          end

          //$port_g Write ADDCCABUSYSEC80REG register.
          ADDCCABUSYSEC80REG_ADDR_CT : begin
            int_ccaBusyDurSec80           <= regWriteData[31 : 0];
          end

          //$port_g Write STBCCNTRLREG register.
          STBCCNTRLREG_ADDR_CT : begin
            int_basicSTBCMCS              <= regWriteData[31 : 25];
            int_dualCTSProt               <= regWriteData[24];
            int_ctsSTBCDur                <= regWriteData[23 : 16];
            int_cfEndSTBCDur              <= regWriteData[15 : 0];
          end

          //$port_g Write STARTTX1REG register.
          STARTTX1REG_ADDR_CT : begin
            int_startTxBW                 <= regWriteData[29 : 28];
            int_startTxPreType            <= regWriteData[27];
            int_startTxFormatMod          <= regWriteData[26 : 24];
            int_startTxMCSIndex0          <= regWriteData[23 : 16];
            int_startTxKSRIndex           <= regWriteData[15 : 6];
            int_startTxAC                 <= regWriteData[4 : 3];
            int_startTxFrmExType          <= regWriteData[2 : 1];
            int_startTxFrameEx            <= regWriteData[0];
          end

          //$port_g Write STARTTX2REG register.
          STARTTX2REG_ADDR_CT : begin
            int_durControlFrm             <= regWriteData[15 : 0];
          end

          //$port_g Write STARTTX3REG register.
          STARTTX3REG_ADDR_CT : begin
            int_startTxSMMIndex           <= regWriteData[31 : 24];
            int_startTxAntennaSet         <= regWriteData[23 : 16];
            int_startTxLSTP               <= regWriteData[13];
            int_startTxSmoothing          <= regWriteData[12];
            int_startTxShortGI            <= regWriteData[8];
            int_startTxNTx                <= regWriteData[7 : 5];
            int_startTxFecCoding          <= regWriteData[4];
            int_startTxSTBC               <= regWriteData[3 : 2];
            int_startTxNumExtnSS          <= regWriteData[1 : 0];
          end

          //$port_g Write TXBWCNTRLREG register.
          TXBWCNTRLREG_ADDR_CT : begin
            int_maxSupportedBW            <= regWriteData[17 : 16];
            int_aPPDUMaxTime              <= regWriteData[15 : 8];
            int_dynBWEn                   <= regWriteData[7];
            int_numTryBWAcquisition       <= regWriteData[6 : 4];
            int_dropToLowerBW             <= regWriteData[3];
            int_defaultBWTXOP             <= regWriteData[2 : 1];
            int_defaultBWTXOPV            <= regWriteData[0];
          end

          //$port_g Write HTMCSREG register.
          HTMCSREG_ADDR_CT : begin
            int_bssBasicHTMCSSetUM        <= regWriteData[21 : 16];
            int_bssBasicHTMCSSetEM        <= regWriteData[15 : 0];
          end

          //$port_g Write VHTMCSREG register.
          VHTMCSREG_ADDR_CT : begin
            int_bssBasicVHTMCSSet         <= regWriteData[15 : 0];
          end

          //$port_g Write LSTPREG register.
          LSTPREG_ADDR_CT : begin
            int_supportLSTP               <= regWriteData[0];
          end
`ifdef RW_WLAN_COEX_EN                

          //$port_g Write COEXCONTROLREG register.
          COEXCONTROLREG_ADDR_CT : begin
            int_coexWlanChanFreq          <= regWriteData[22 : 16];
            int_coexWlanChanOffset        <= regWriteData[12];
            int_coexEnable                <= regWriteData[0];
          end

          //$port_g Write COEXPTIREG register.
          COEXPTIREG_ADDR_CT : begin
            int_coexPTIBcnData            <= regWriteData[31 : 28];
            int_coexPTIBKData             <= regWriteData[27 : 24];
            int_coexPTIBEData             <= regWriteData[23 : 20];
            int_coexPTIVIData             <= regWriteData[19 : 16];
            int_coexPTIVOData             <= regWriteData[15 : 12];
            int_coexPTIMgt                <= regWriteData[11 : 8];
            int_coexPTICntl               <= regWriteData[7 : 4];
            int_coexPTIAck                <= regWriteData[3 : 0];
          end
`endif // RW_WLAN_COEX_EN                

          //$port_g Write DEBUGPORTSELREG register.
          DEBUGPORTSELREG_ADDR_CT : begin
            int_debugPortSel2             <= regWriteData[15 : 8];
            int_debugPortSel1             <= regWriteData[7 : 0];
          end

          //$port_g Write DEBUGNAVREG register.
          DEBUGNAVREG_ADDR_CT : begin
            int_navCounter                <= regWriteData[25 : 0];
          end

          //$port_g Write DEBUGCWREG register.
          DEBUGCWREG_ADDR_CT : begin
            int_backoffOffset             <= regWriteData[25 : 24];
          end

          //$port_g Write DEBUGPHYREG register.
          DEBUGPHYREG_ADDR_CT : begin
            int_rxReqForceDeassertion     <= regWriteData[0];
          end

          
          // Disable coverage on the default state because it cannot be reached.
          // pragma coverage block = off 
          default : begin
          end
          // pragma coverage block = on 

        endcase
      end
      else begin
        int_errInHWLevel3             <= 1'b0;
        int_errInTxRxLevel2           <= 1'b0;
        int_errInRxLevel1             <= 1'b0;
        int_errInTxLevel1             <= 1'b0;
        int_clearErrInHWLevel3        <= 1'b0;
        int_clearErrInTxRxLevel2      <= 1'b0;
        int_clearErrInRxLevel1        <= 1'b0;
        int_clearErrInTxLevel1        <= 1'b0;
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

        //$port_g Read SIGNATUREREG register.
        SIGNATUREREG_ADDR_CT : begin
          regReadData[31 : 0]        = signature;
        end

        //$port_g Read VERSION1REG register.
        VERSION1REG_ADDR_CT : begin
          regReadData[16]            = mac80211MHFormat;
          regReadData[14]            = coex;
          regReadData[13]            = wapi;
          regReadData[12]            = tpc;
          regReadData[11]            = vht;
          regReadData[10]            = ht;
          regReadData[8]             = rce;
          regReadData[7]             = ccmp;
          regReadData[6]             = tkip;
          regReadData[5]             = wep;
          regReadData[4]             = security;
          regReadData[3]             = sme;
          regReadData[2]             = hcca;
          regReadData[1]             = edca;
          regReadData[0]             = qos;
        end

        //$port_g Read VERSION2REG register.
        VERSION2REG_ADDR_CT : begin
          regReadData[16 : 14]       = phaseNumber;
          regReadData[13 : 8]        = releaseNumber;
          regReadData[7]             = ieRelease;
          regReadData[6 : 0]         = umVersion;
        end

        //$port_g Read BITMAPCNTREG register.
        BITMAPCNTREG_ADDR_CT : begin
          regReadData[15 : 0]        = bitmapCnt;
        end

        //$port_g Read MACADDRLOWREG register.
        MACADDRLOWREG_ADDR_CT : begin
          regReadData[31 : 0]        = macAddrLow;
        end

        //$port_g Read MACADDRHIREG register.
        MACADDRHIREG_ADDR_CT : begin
          regReadData[15 : 0]        = macAddrHigh;
        end

        //$port_g Read MACADDRLOWMASKREG register.
        MACADDRLOWMASKREG_ADDR_CT : begin
          regReadData[31 : 0]        = macAddrLowMask;
        end

        //$port_g Read MACADDRHIMASKREG register.
        MACADDRHIMASKREG_ADDR_CT : begin
          regReadData[15 : 0]        = macAddrHighMask;
        end

        //$port_g Read BSSIDLOWREG register.
        BSSIDLOWREG_ADDR_CT : begin
          regReadData[31 : 0]        = bssIDLow;
        end

        //$port_g Read BSSIDHIREG register.
        BSSIDHIREG_ADDR_CT : begin
          regReadData[15 : 0]        = bssIDHigh;
        end

        //$port_g Read BSSIDLOWMASKREG register.
        BSSIDLOWMASKREG_ADDR_CT : begin
          regReadData[31 : 0]        = bssIDLowMask;
        end

        //$port_g Read BSSIDHIMASKREG register.
        BSSIDHIMASKREG_ADDR_CT : begin
          regReadData[15 : 0]        = bssIDHighMask;
        end

        //$port_g Read STATECNTRLREG register.
        STATECNTRLREG_ADDR_CT : begin
          regReadData[7 : 4]         = nextState;
          regReadData[3 : 0]         = currentState;
        end

        //$port_g Read SCANCNTRLREG register.
        SCANCNTRLREG_ADDR_CT : begin
          regReadData[15 : 0]        = probeDelay;
        end

        //$port_g Read DOZECNTRL1REG register.
        DOZECNTRL1REG_ADDR_CT : begin
          regReadData[31 : 17]       = atimW;
          regReadData[16]            = wakeupDTIM;
          regReadData[15 : 0]        = listenInterval;
        end

        //$port_g Read MACCNTRL1REG register.
        MACCNTRL1REG_ADDR_CT : begin
          regReadData[26]            = rxRIFSEn;
          regReadData[25]            = tsfMgtDisable;
          regReadData[24]            = tsfUpdatedBySW;
          regReadData[16 : 14]       = abgnMode;
          regReadData[13]            = keyStoRAMReset;
          regReadData[12]            = mibTableReset;
          regReadData[11]            = rateControllerMPIF;
          regReadData[10]            = disableBAResp;
          regReadData[9]             = disableCTSResp;
          regReadData[8]             = disableACKResp;
          regReadData[7]             = activeClkGating;
          regReadData[6]             = enableLPClkSwitch;
          regReadData[3]             = cfpAware;
          regReadData[2]             = pwrMgt;
          regReadData[1]             = ap;
          regReadData[0]             = bssType;
        end

        //$port_g Read MACERRRECCNTRLREG register.
        MACERRRECCNTRLREG_ADDR_CT : begin
          regReadData[16]            = rxFlowCntrlEn;
          regReadData[7]             = baPSBitmapReset;
          regReadData[6]             = encrRxFIFOReset;
          regReadData[5]             = macPHYIFFIFOReset;
          regReadData[4]             = txFIFOReset;
          regReadData[3]             = rxFIFOReset;
          regReadData[2]             = hwFSMReset;
          regReadData[1]             = useErrDet;
          regReadData[0]             = useErrRec;
        end

        //$port_g Read MACERRSETSTATUSREG register.
        MACERRSETSTATUSREG_ADDR_CT : begin
          regReadData[3]             = statuserrInHWLevel3;
          regReadData[2]             = statuserrInTxRxLevel2;
          regReadData[1]             = statuserrInRxLevel1;
          regReadData[0]             = statuserrInTxLevel1;
        end

        //$port_g Read MACERRCLEARSTATUSREG register.
        MACERRCLEARSTATUSREG_ADDR_CT : begin
          regReadData[3]             = clearErrInHWLevel3;
          regReadData[2]             = clearErrInTxRxLevel2;
          regReadData[1]             = clearErrInRxLevel1;
          regReadData[0]             = clearErrInTxLevel1;
        end
        
        RXCNTRLREG_ADDR_CT : begin
          regReadData[31]            = enDuplicateDetection;
          regReadData[30]            = acceptUnknown;
          regReadData[29]            = acceptOtherDataFrames;
          regReadData[28]            = acceptQoSNull;
          regReadData[27]            = acceptQCFWOData;
          regReadData[26]            = acceptQData;
          regReadData[25]            = acceptCFWOData;
          regReadData[24]            = acceptData;
          regReadData[23]            = acceptOtherCntrlFrames;
          regReadData[22]            = acceptCFEnd;
          regReadData[21]            = acceptACK;
          regReadData[20]            = acceptCTS;
          regReadData[19]            = acceptRTS;
          regReadData[18]            = acceptPSPoll;
          regReadData[17]            = acceptBA;
          regReadData[16]            = acceptBAR;
          regReadData[15]            = acceptOtherMgmtFrames;
          regReadData[13]            = acceptAllBeacon;
          regReadData[12]            = acceptNotExpectedBA;
          regReadData[11]            = acceptDecryptErrorFrames;
          regReadData[10]            = acceptBeacon;
          regReadData[9]             = acceptProbeResp;
          regReadData[8]             = acceptProbeReq;
          regReadData[7]             = acceptMyUnicast;
          regReadData[6]             = acceptUnicast;
          regReadData[5]             = acceptErrorFrames;
          regReadData[4]             = acceptOtherBSSID;
          regReadData[3]             = acceptBroadcast;
          regReadData[2]             = acceptMulticast;
          regReadData[1]             = dontDecrypt;
          regReadData[0]             = excUnencrypted;
        end

        //$port_g Read BCNCNTRL1REG register.
        BCNCNTRL1REG_ADDR_CT : begin
          regReadData[31 : 24]       = noBcnTxTime;
          regReadData[23]            = impTBTTIn128Us;
          regReadData[22 : 16]       = impTBTTPeriod;
          regReadData[15 : 0]        = beaconInt;
        end

        //$port_g Read BCNCNTRL2REG register.
        BCNCNTRL2REG_ADDR_CT : begin
          regReadData[27 : 16]       = aid;
          regReadData[15 : 8]        = timOffset;
          regReadData[7 : 0]         = bcnUpdateOffset;
        end

        //$port_g Read DTIMCFP1REG register.
        DTIMCFP1REG_ADDR_CT : begin
          regReadData[31]            = dtimUpdatedBySW;
          regReadData[15 : 8]        = cfpPeriod;
          regReadData[7 : 0]         = dtimPeriod;
        end

        //$port_g Read DTIMCFP2REG register.
        DTIMCFP2REG_ADDR_CT : begin
          regReadData[15 : 0]        = cfpMaxDuration;
        end

        //$port_g Read RETRYLIMITSREG register.
        RETRYLIMITSREG_ADDR_CT : begin
          regReadData[15 : 8]        = dot11LongRetryLimit;
          regReadData[7 : 0]         = dot11ShortRetryLimit;
        end

        //$port_g Read BBSERVICEREG register.
        BBSERVICEREG_ADDR_CT : begin
          regReadData[28 : 26]       = maxPHYNtx;
          regReadData[23 : 16]       = bbServiceB;
          regReadData[15 : 0]        = bbServiceA;
        end

        //$port_g Read MAXPOWERLEVELREG register.
        MAXPOWERLEVELREG_ADDR_CT : begin
          regReadData[15 : 8]        = dsssMaxPwrLevel;
          regReadData[7 : 0]         = ofdmMaxPwrLevel;
        end

        //$port_g Read ENCRKEY0REG register.
        ENCRKEY0REG_ADDR_CT : begin
          regReadData[31 : 0]        = encrKeyRAMWord0;
        end

        //$port_g Read ENCRKEY1REG register.
        ENCRKEY1REG_ADDR_CT : begin
          regReadData[31 : 0]        = encrKeyRAMWord1;
        end

        //$port_g Read ENCRKEY2REG register.
        ENCRKEY2REG_ADDR_CT : begin
          regReadData[31 : 0]        = encrKeyRAMWord2;
        end

        //$port_g Read ENCRKEY3REG register.
        ENCRKEY3REG_ADDR_CT : begin
          regReadData[31 : 0]        = encrKeyRAMWord3;
        end

        //$port_g Read ENCRMACADDRLOWREG register.
        ENCRMACADDRLOWREG_ADDR_CT : begin
          regReadData[31 : 0]        = macAddrRAMLow;
        end

        //$port_g Read ENCRMACADDRHIGHREG register.
        ENCRMACADDRHIGHREG_ADDR_CT : begin
          regReadData[15 : 0]        = macAddrRAMHigh;
        end

        //$port_g Read ENCRCNTRLREG register.
        ENCRCNTRLREG_ADDR_CT : begin
          regReadData[31]            = newRead;
          regReadData[30]            = newWrite;
          regReadData[25 : 16]       = keyIndexRAM;
          regReadData[10 : 8]        = cTypeRAM;
          regReadData[7 : 4]         = vlanIDRAM;
          regReadData[3 : 2]         = sppRAM;
          regReadData[1]             = useDefKeyRAM;
          regReadData[0]             = cLenRAM;
        end
`ifdef RW_WAPI_EN                     

        //$port_g Read ENCRWPIINTKEY0REG register.
        ENCRWPIINTKEY0REG_ADDR_CT : begin
          regReadData[31 : 0]        = encrIntKeyRAMWord0;
        end

        //$port_g Read ENCRWPIINTKEY1REG register.
        ENCRWPIINTKEY1REG_ADDR_CT : begin
          regReadData[31 : 0]        = encrIntKeyRAMWord1;
        end

        //$port_g Read ENCRWPIINTKEY2REG register.
        ENCRWPIINTKEY2REG_ADDR_CT : begin
          regReadData[31 : 0]        = encrIntKeyRAMWord2;
        end

        //$port_g Read ENCRWPIINTKEY3REG register.
        ENCRWPIINTKEY3REG_ADDR_CT : begin
          regReadData[31 : 0]        = encrIntKeyRAMWord3;
        end
`endif // RW_WAPI_EN                     

        //$port_g Read RATESREG register.
        RATESREG_ADDR_CT : begin
          regReadData[11 : 0]        = bssBasicRateSet;
        end

        //$port_g Read OLBCREG register.
        OLBCREG_ADDR_CT : begin
          regReadData[31 : 24]       = dsssCount;
          regReadData[23 : 16]       = ofdmCount;
          regReadData[15 : 0]        = olbcTimer;
        end

        //$port_g Read TIMINGS1REG register.
        TIMINGS1REG_ADDR_CT : begin
          regReadData[27 : 18]       = txChainDelayInMACClk;
          regReadData[17 : 8]        = txRFDelayInMACClk;
          regReadData[7 : 0]         = macCoreClkFreq;
        end

        //$port_g Read TIMINGS2REG register.
        TIMINGS2REG_ADDR_CT : begin
          regReadData[23 : 8]        = slotTimeInMACClk;
          regReadData[7 : 0]         = slotTime;
        end

        //$port_g Read TIMINGS3REG register.
        TIMINGS3REG_ADDR_CT : begin
          regReadData[29 : 20]       = rxRFDelayInMACClk;
          regReadData[19 : 10]       = txDelayRFOnInMACClk;
          regReadData[9 : 0]         = macProcDelayInMACClk;
        end

        //$port_g Read TIMINGS4REG register.
        TIMINGS4REG_ADDR_CT : begin
          regReadData[31 : 22]       = radioWakeUpTime;
          regReadData[21 : 12]       = radioChirpTime;
        end

        //$port_g Read TIMINGS5REG register.
        TIMINGS5REG_ADDR_CT : begin
          regReadData[23 : 8]        = sifsBInMACClk;
          regReadData[7 : 0]         = sifsB;
        end

        //$port_g Read TIMINGS6REG register.
        TIMINGS6REG_ADDR_CT : begin
          regReadData[23 : 8]        = sifsAInMACClk;
          regReadData[7 : 0]         = sifsA;
        end

        //$port_g Read TIMINGS7REG register.
        TIMINGS7REG_ADDR_CT : begin
          regReadData[11 : 8]        = rxCCADelay;
          regReadData[7 : 0]         = rifs;
        end

        //$port_g Read TIMINGS8REG register.
        TIMINGS8REG_ADDR_CT : begin
          regReadData[31 : 24]       = rxStartDelayMIMO;
          regReadData[23 : 16]       = rxStartDelayShort;
          regReadData[15 : 8]        = rxStartDelayLong;
          regReadData[7 : 0]         = rxStartDelayOFDM;
        end

        //$port_g Read TIMINGS9REG register.
        TIMINGS9REG_ADDR_CT : begin
          regReadData[29 : 20]       = rifsTOInMACClk;
          regReadData[19 : 10]       = rifsInMACClk;
          regReadData[9 : 0]         = txDMAProcDlyInMACClk;
        end

        //$port_g Read PROTTRIGTIMERREG register.
        PROTTRIGTIMERREG_ADDR_CT : begin
          regReadData[15 : 8]        = hccaTriggerTimer;
          regReadData[7 : 0]         = edcaTriggerTimer;
        end

        //$port_g Read TXTRIGGERTIMERREG register.
        TXTRIGGERTIMERREG_ADDR_CT : begin
          regReadData[15 : 8]        = txPacketTimeout;
          regReadData[7 : 0]         = txAbsoluteTimeout;
        end

        //$port_g Read RXTRIGGERTIMERREG register.
        RXTRIGGERTIMERREG_ADDR_CT : begin
          regReadData[23 : 16]       = rxPayloadUsedCount;
          regReadData[15 : 8]        = rxPacketTimeout;
          regReadData[7 : 0]         = rxAbsoluteTimeout;
        end

        //$port_g Read MIBTABLEWRITEREG register.
        MIBTABLEWRITEREG_ADDR_CT : begin
          regReadData[31 : 16]       = mibValue;
          regReadData[15]            = mibWrite;
          regReadData[14]            = mibIncrementMode;
          regReadData[9 : 0]         = mibTableIndex;
        end

        //$port_g Read MONOTONICCOUNTER1REG register.
        MONOTONICCOUNTER1REG_ADDR_CT : begin
          regReadData[31 : 0]        = monotonicCounter1;
        end

        //$port_g Read MONOTONICCOUNTER2LOREG register.
        MONOTONICCOUNTER2LOREG_ADDR_CT : begin
          regReadData[31 : 0]        = monotonicCounterLow2;
        end

        //$port_g Read MONOTONICCOUNTER2HIREG register.
        MONOTONICCOUNTER2HIREG_ADDR_CT : begin
          regReadData[15 : 0]        = monotonicCounterHigh2;
        end

        //$port_g Read ABSTIMERREG0 register.
        ABSTIMERREG0_ADDR_CT : begin
          regReadData[31 : 0]        = absTimerValue0;
        end

        //$port_g Read ABSTIMERREG1 register.
        ABSTIMERREG1_ADDR_CT : begin
          regReadData[31 : 0]        = absTimerValue1;
        end

        //$port_g Read ABSTIMERREG2 register.
        ABSTIMERREG2_ADDR_CT : begin
          regReadData[31 : 0]        = absTimerValue2;
        end

        //$port_g Read ABSTIMERREG3 register.
        ABSTIMERREG3_ADDR_CT : begin
          regReadData[31 : 0]        = absTimerValue3;
        end

        //$port_g Read ABSTIMERREG4 register.
        ABSTIMERREG4_ADDR_CT : begin
          regReadData[31 : 0]        = absTimerValue4;
        end

        //$port_g Read ABSTIMERREG5 register.
        ABSTIMERREG5_ADDR_CT : begin
          regReadData[31 : 0]        = absTimerValue5;
        end

        //$port_g Read ABSTIMERREG6 register.
        ABSTIMERREG6_ADDR_CT : begin
          regReadData[31 : 0]        = absTimerValue6;
        end

        //$port_g Read ABSTIMERREG7 register.
        ABSTIMERREG7_ADDR_CT : begin
          regReadData[31 : 0]        = absTimerValue7;
        end

        //$port_g Read ABSTIMERREG8 register.
        ABSTIMERREG8_ADDR_CT : begin
          regReadData[31 : 0]        = absTimerValue8;
        end

        //$port_g Read ABSTIMERREG9 register.
        ABSTIMERREG9_ADDR_CT : begin
          regReadData[31 : 0]        = absTimerValue9;
        end

        //$port_g Read MAXRXLENGTHREG register.
        MAXRXLENGTHREG_ADDR_CT : begin
          regReadData[19 : 0]        = maxAllowedLength;
        end

        //$port_g Read EDCAAC0REG register.
        EDCAAC0REG_ADDR_CT : begin
          regReadData[27 : 12]       = txOpLimit0;
          regReadData[11 : 8]        = cwMax0;
          regReadData[7 : 4]         = cwMin0;
          regReadData[3 : 0]         = aifsn0;
        end

        //$port_g Read EDCAAC1REG register.
        EDCAAC1REG_ADDR_CT : begin
          regReadData[27 : 12]       = txOpLimit1;
          regReadData[11 : 8]        = cwMax1;
          regReadData[7 : 4]         = cwMin1;
          regReadData[3 : 0]         = aifsn1;
        end

        //$port_g Read EDCAAC2REG register.
        EDCAAC2REG_ADDR_CT : begin
          regReadData[27 : 12]       = txOpLimit2;
          regReadData[11 : 8]        = cwMax2;
          regReadData[7 : 4]         = cwMin2;
          regReadData[3 : 0]         = aifsn2;
        end

        //$port_g Read EDCAAC3REG register.
        EDCAAC3REG_ADDR_CT : begin
          regReadData[27 : 12]       = txOpLimit3;
          regReadData[11 : 8]        = cwMax3;
          regReadData[7 : 4]         = cwMin3;
          regReadData[3 : 0]         = aifsn3;
        end

        //$port_g Read EDCACCABUSYREG register.
        EDCACCABUSYREG_ADDR_CT : begin
          regReadData[31 : 0]        = ccaBusyDur;
        end

        //$port_g Read EDCACNTRLREG register.
        EDCACNTRLREG_ADDR_CT : begin
          regReadData[5]             = keepTXOPOpen;
          regReadData[4]             = remTXOPInDurField;
          regReadData[1]             = sendCFEnd;
          regReadData[0]             = sendCFEndNow;
        end

        //$port_g Read QUIETELEMENT1AREG register.
        QUIETELEMENT1AREG_ADDR_CT : begin
          regReadData[31 : 16]       = quietDuration1;
          regReadData[15 : 8]        = quietPeriod1;
          regReadData[7 : 0]         = quietCount1;
        end

        //$port_g Read QUIETELEMENT1BREG register.
        QUIETELEMENT1BREG_ADDR_CT : begin
          regReadData[15 : 0]        = quietOffset1;
        end

        //$port_g Read QUIETELEMENT2AREG register.
        QUIETELEMENT2AREG_ADDR_CT : begin
          regReadData[31 : 16]       = quietDuration2;
          regReadData[15 : 8]        = quietPeriod2;
          regReadData[7 : 0]         = quietCount2;
        end

        //$port_g Read QUIETELEMENT2BREG register.
        QUIETELEMENT2BREG_ADDR_CT : begin
          regReadData[15 : 0]        = quietOffset2;
        end

        //$port_g Read ADDCCABUSYSEC20REG register.
        ADDCCABUSYSEC20REG_ADDR_CT : begin
          regReadData[31 : 0]        = ccaBusyDurSec20;
        end

        //$port_g Read ADDCCABUSYSEC40REG register.
        ADDCCABUSYSEC40REG_ADDR_CT : begin
          regReadData[31 : 0]        = ccaBusyDurSec40;
        end

        //$port_g Read ADDCCABUSYSEC80REG register.
        ADDCCABUSYSEC80REG_ADDR_CT : begin
          regReadData[31 : 0]        = ccaBusyDurSec80;
        end

        //$port_g Read STBCCNTRLREG register.
        STBCCNTRLREG_ADDR_CT : begin
          regReadData[31 : 25]       = basicSTBCMCS;
          regReadData[24]            = dualCTSProt;
          regReadData[23 : 16]       = ctsSTBCDur;
          regReadData[15 : 0]        = cfEndSTBCDur;
        end

        //$port_g Read STARTTX1REG register.
        STARTTX1REG_ADDR_CT : begin
          regReadData[29 : 28]       = startTxBW;
          regReadData[27]            = startTxPreType;
          regReadData[26 : 24]       = startTxFormatMod;
          regReadData[23 : 16]       = startTxMCSIndex0;
          regReadData[15 : 6]        = startTxKSRIndex;
          regReadData[4 : 3]         = startTxAC;
          regReadData[2 : 1]         = startTxFrmExType;
          regReadData[0]             = startTxFrameEx;
        end

        //$port_g Read STARTTX2REG register.
        STARTTX2REG_ADDR_CT : begin
          regReadData[15 : 0]        = durControlFrm;
        end

        //$port_g Read STARTTX3REG register.
        STARTTX3REG_ADDR_CT : begin
          regReadData[31 : 24]       = startTxSMMIndex;
          regReadData[23 : 16]       = startTxAntennaSet;
          regReadData[13]            = startTxLSTP;
          regReadData[12]            = startTxSmoothing;
          regReadData[8]             = startTxShortGI;
          regReadData[7 : 5]         = startTxNTx;
          regReadData[4]             = startTxFecCoding;
          regReadData[3 : 2]         = startTxSTBC;
          regReadData[1 : 0]         = startTxNumExtnSS;
        end

        //$port_g Read TXBWCNTRLREG register.
        TXBWCNTRLREG_ADDR_CT : begin
          regReadData[17 : 16]       = maxSupportedBW;
          regReadData[15 : 8]        = aPPDUMaxTime;
          regReadData[7]             = dynBWEn;
          regReadData[6 : 4]         = numTryBWAcquisition;
          regReadData[3]             = dropToLowerBW;
          regReadData[2 : 1]         = defaultBWTXOP;
          regReadData[0]             = defaultBWTXOPV;
        end

        //$port_g Read HTMCSREG register.
        HTMCSREG_ADDR_CT : begin
          regReadData[21 : 16]       = bssBasicHTMCSSetUM;
          regReadData[15 : 0]        = bssBasicHTMCSSetEM;
        end

        //$port_g Read VHTMCSREG register.
        VHTMCSREG_ADDR_CT : begin
          regReadData[15 : 0]        = bssBasicVHTMCSSet;
        end

        //$port_g Read LSTPREG register.
        LSTPREG_ADDR_CT : begin
          regReadData[0]             = supportLSTP;
        end
`ifdef RW_WLAN_COEX_EN                

        //$port_g Read COEXCONTROLREG register.
        COEXCONTROLREG_ADDR_CT : begin
          regReadData[22 : 16]       = coexWlanChanFreq;
          regReadData[12]            = coexWlanChanOffset;
          regReadData[0]             = coexEnable;
        end

        //$port_g Read COEXPTIREG register.
        COEXPTIREG_ADDR_CT : begin
          regReadData[31 : 28]       = coexPTIBcnData;
          regReadData[27 : 24]       = coexPTIBKData;
          regReadData[23 : 20]       = coexPTIBEData;
          regReadData[19 : 16]       = coexPTIVIData;
          regReadData[15 : 12]       = coexPTIVOData;
          regReadData[11 : 8]        = coexPTIMgt;
          regReadData[7 : 4]         = coexPTICntl;
          regReadData[3 : 0]         = coexPTIAck;
        end
`endif // RW_WLAN_COEX_EN                

        //$port_g Read DEBUGHWSM1REG register.
        DEBUGHWSM1REG_ADDR_CT : begin
          regReadData[31 : 24]       = macControlLs;
          regReadData[16 : 8]        = txControlLs;
          regReadData[4 : 0]         = rxControlLs;
        end

        //$port_g Read DEBUGHWSM2REG register.
        DEBUGHWSM2REG_ADDR_CT : begin
          regReadData[31 : 24]       = macControlCs;
          regReadData[16 : 8]        = txControlCs;
          regReadData[4 : 0]         = rxControlCs;
        end

        //$port_g Read DEBUGPORTVALUEREG register.
        DEBUGPORTVALUEREG_ADDR_CT : begin
          regReadData[31 : 0]        = debugPortRead;
        end

        //$port_g Read DEBUGPORTSELREG register.
        DEBUGPORTSELREG_ADDR_CT : begin
          regReadData[15 : 8]        = debugPortSel2;
          regReadData[7 : 0]         = debugPortSel1;
        end

        //$port_g Read DEBUGNAVREG register.
        DEBUGNAVREG_ADDR_CT : begin
          regReadData[25 : 0]        = navCounter;
        end

        //$port_g Read DEBUGCWREG register.
        DEBUGCWREG_ADDR_CT : begin
          regReadData[25 : 24]       = backoffOffset;
          regReadData[17 : 16]       = activeAC;
          regReadData[15 : 12]       = currentCW3;
          regReadData[11 : 8]        = currentCW2;
          regReadData[7 : 4]         = currentCW1;
          regReadData[3 : 0]         = currentCW0;
        end

        //$port_g Read DEBUGQSRCREG register.
        DEBUGQSRCREG_ADDR_CT : begin
          regReadData[31 : 24]       = ac3QSRC;
          regReadData[23 : 16]       = ac2QSRC;
          regReadData[15 : 8]        = ac1QSRC;
          regReadData[7 : 0]         = ac0QSRC;
        end

        //$port_g Read DEBUGQLRCREG register.
        DEBUGQLRCREG_ADDR_CT : begin
          regReadData[31 : 24]       = ac3QLRC;
          regReadData[23 : 16]       = ac2QLRC;
          regReadData[15 : 8]        = ac1QLRC;
          regReadData[7 : 0]         = ac0QLRC;
        end

        //$port_g Read DEBUGPHYREG register.
        DEBUGPHYREG_ADDR_CT : begin
          regReadData[0]             = rxReqForceDeassertion;
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
  