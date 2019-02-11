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
// Description      : Resynchonization stage 
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


module intCtrlResync( 
      
      //$port_g clocks and reset
      input wire                         macPIClk,              // Platform clock                     
      input wire                         macPIClkHardRst_n,     // Platfrom Reset
      
      //$port_g interruptions input
      input wire                         phyRxStart           ,// phyRxStart internal interruption
      input wire                         phyErr               ,// phyErr internal interruption
      input wire                         macPHYIFUnderRun     ,// macPHYIFUnderRun internal interruption
      input wire                         macPHYIFOverflow     ,// macPHYIFOverflow internal interruption
      input wire                         hwErr                ,// hwErr internal interruption
      input wire                         impSecDTIM           ,// impSecDTIM internal interruption
      input wire                         impPriDTIM           ,// impPriDTIM internal interruption
      input wire                         timSet               ,// timSet internal interruption
      input wire                         olbcDSSS             ,// olbcDSSS internal interruption
      input wire                         olbcOFDM             ,// olbcOFDM internal interruption
      input wire                         rxFIFOOverFlow       ,// rxFIFOOverFlow internal interruption
      input wire [9:0]                   absTimers            ,// absTimer internal interruption
      input wire                         idleInterrupt        ,// idleInterrupt internal interruption
      input wire                         impSecTBTT           ,// impSecTBTT internal interruption
      input wire                         impPriTBTT           ,// impPriTBTT internal interruption
      input wire                         timerRxTrigger       ,// timerRxTrigger internal interruption
      input wire                         baRxTrigger          ,// baRxTrigger internal interruption
      input wire                         timerTxTrigger       ,// timerTxTrigger internal interruption
      input wire                         txopComplete         ,// txopComplete internal interruption
      input wire                         rdTxTrigger          ,// rdTxTrigger internal interruption
      input wire                         hccaTxTrigger        ,// hccaTxTrigger internal interruption
      input wire                         rdProtTrigger        ,// rdProtTrigger internal interruption
      input wire                         hccaProtTrigger      ,// hccaProtTrigger internal interruption
      input wire                         ac3ProtTrigger       ,// ac3ProtTrigger internal interruption
      input wire                         ac2ProtTrigger       ,// ac2ProtTrigger internal interruption
      input wire                         ac1ProtTrigger       ,// ac1ProtTrigger internal interruption
      input wire                         ac0ProtTrigger       ,// ac0ProtTrigger internal interruption
      input wire                         ac3BWDropTrigger       ,// ac3BWDropTrigger internal interruption
      input wire                         ac2BWDropTrigger       ,// ac2BWDropTrigger internal interruption
      input wire                         ac1BWDropTrigger       ,// ac1BWDropTrigger internal interruption
      input wire                         ac0BWDropTrigger       ,// ac0BWDropTrigger internal interruption
      
      //$port_g resynchronized interrutpions
      output wire                        intphyRxStart        ,// phyRxStart internal interruption
      output wire                        intphyErr            ,// phyErr internal interruption
      output wire                        intmacPHYIFUnderRun  ,// macPHYIFUnderRun internal interruption
      output wire                        intmacPHYIFOverflow  ,// macPHYIFOverflow internal interruption
      output wire                        inthwErr             ,// hwErr internal interruption
      output wire                        intimpSecDTIM        ,// impSecDTIM internal interruption
      output wire                        intimpPriDTIM        ,// impPriDTIM internal interruption
      output wire                        inttimSet            ,// timSet internal interruption
      output wire                        intolbcDSSS          ,// olbcDSSS internal interruption
      output wire                        intolbcOFDM          ,// olbcOFDM internal interruption
      output wire                        intrxFIFOOverFlow    ,// rxFIFOOverFlow internal interruption
      output wire [9:0]                  intabsTimers         ,// absTimer internal interruption
      output wire                        intidleInterrupt     ,// idleInterrupt internal interruption
      output wire                        intimpSecTBTT        ,// impSecTBTT internal interruption
      output wire                        intimpPriTBTT        ,// impPriTBTT internal interruption
      output wire                        inttimerRxTrigger    ,// timerRxTrigger internal interruption
      output wire                        intbaRxTrigger       ,// baRxTrigger internal interruption
      output wire                        inttimerTxTrigger    ,// timerTxTrigger internal interruption
      output wire                        inttxopComplete      ,// txopComplete internal interruption
      output wire                        intrdTxTrigger       ,// rdTxTrigger internal interruption
      output wire                        inthccaTxTrigger     ,// hccaTxTrigger internal interruption
      output wire                        intrdProtTrigger     ,// rdProtTrigger internal interruption
      output wire                        inthccaProtTrigger   ,// hccaProtTrigger internal interruption
      output wire                        intac3ProtTrigger    ,// ac3ProtTrigger internal interruption
      output wire                        intac2ProtTrigger    ,// ac2ProtTrigger internal interruption
      output wire                        intac1ProtTrigger    ,// ac1ProtTrigger internal interruption
      output wire                        intac0ProtTrigger    ,// ac3ProtTrigger internal interruption
      output wire                        intac3BWDropTrigger    ,// ac2BWDropTrigger internal interruption
      output wire                        intac2BWDropTrigger    ,// ac1BWDropTrigger internal interruption
      output wire                        intac1BWDropTrigger    ,// ac1BWDropTrigger internal interruption
      output wire                        intac0BWDropTrigger     // ac0BWDropTrigger internal interruption


);



risingEdgeDetector U_phyRxStart (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (phyRxStart),
                .dstdata      (intphyRxStart)
                );

risingEdgeDetector U_phyErr (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (phyErr),
                .dstdata      (intphyErr)
                );

risingEdgeDetector U_macPHYIFUnderRun (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (macPHYIFUnderRun),
                .dstdata      (intmacPHYIFUnderRun)
                );

risingEdgeDetector U_macPHYIFOverflow (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (macPHYIFOverflow),
                .dstdata      (intmacPHYIFOverflow)
                );

risingEdgeDetector U_hwErr (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (hwErr),
                .dstdata      (inthwErr)
                );

risingEdgeDetector U_impSecDTIM (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (impSecDTIM),
                .dstdata      (intimpSecDTIM)
                );

risingEdgeDetector U_impPriDTIM (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (impPriDTIM),
                .dstdata      (intimpPriDTIM)
                );

risingEdgeDetector U_timSet (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (timSet),
                .dstdata      (inttimSet)
                );

risingEdgeDetector U_olbcDSSS (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (olbcDSSS),
                .dstdata      (intolbcDSSS)
                );

risingEdgeDetector U_olbcOFDM (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (olbcOFDM),
                .dstdata      (intolbcOFDM)
                );

risingEdgeDetector U_rxFIFOOverFlow (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (rxFIFOOverFlow),
                .dstdata      (intrxFIFOOverFlow)
                );

genvar i;
generate
  
  for (i=0; i< 10; i = i+1)
  begin
    risingEdgeDetector U_absTimer (
                    .dstclk       (macPIClk),
                    .dstresetn    (macPIClkHardRst_n),
                    .srcdata      (absTimers[i]),
                    .dstdata      (intabsTimers[i])
                    );
  end
endgenerate


risingEdgeDetector U_idleInterrupt (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (idleInterrupt),
                .dstdata      (intidleInterrupt)
                );

risingEdgeDetector U_impSecTBTT (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (impSecTBTT),
                .dstdata      (intimpSecTBTT)
                );

risingEdgeDetector U_impPriTBTT (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (impPriTBTT),
                .dstdata      (intimpPriTBTT)
                );

risingEdgeDetector U_timerRxTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (timerRxTrigger),
                .dstdata      (inttimerRxTrigger)
                );

risingEdgeDetector U_baRxTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (baRxTrigger),
                .dstdata      (intbaRxTrigger)
                );

risingEdgeDetector U_timerTxTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (timerTxTrigger),
                .dstdata      (inttimerTxTrigger)
                );

risingEdgeDetector U_txopComplete (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (txopComplete),
                .dstdata      (inttxopComplete)
                );

risingEdgeDetector U_rdTxTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (rdTxTrigger),
                .dstdata      (intrdTxTrigger)
                );

risingEdgeDetector U_hccaTxTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (hccaTxTrigger),
                .dstdata      (inthccaTxTrigger)
                );

risingEdgeDetector U_rdProtTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (rdProtTrigger),
                .dstdata      (intrdProtTrigger)
                );

risingEdgeDetector U_hccaProtTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (hccaProtTrigger),
                .dstdata      (inthccaProtTrigger)
                );

risingEdgeDetector U_ac3ProtTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (ac3ProtTrigger),
                .dstdata      (intac3ProtTrigger)
                );

risingEdgeDetector U_ac2ProtTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (ac2ProtTrigger),
                .dstdata      (intac2ProtTrigger)
                );

risingEdgeDetector U_ac1ProtTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (ac1ProtTrigger),
                .dstdata      (intac1ProtTrigger)
                );


risingEdgeDetector U_ac0ProtTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (ac0ProtTrigger),
                .dstdata      (intac0ProtTrigger)
                );

risingEdgeDetector U_ac3BWDropTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (ac3BWDropTrigger),
                .dstdata      (intac3BWDropTrigger)
                );

risingEdgeDetector U_ac2BWDropTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (ac2BWDropTrigger),
                .dstdata      (intac2BWDropTrigger)
                );

risingEdgeDetector U_ac1BWDropTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (ac1BWDropTrigger),
                .dstdata      (intac1BWDropTrigger)
                );


risingEdgeDetector U_ac0BWDropTrigger (
                .dstclk       (macPIClk),
                .dstresetn    (macPIClkHardRst_n),
                .srcdata      (ac0BWDropTrigger),
                .dstdata      (intac0BWDropTrigger)
                );



endmodule
                 
