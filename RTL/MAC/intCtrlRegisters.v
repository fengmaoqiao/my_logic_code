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


module intCtrlRegisters( 

      //$port_g clocks and reset
      input wire                         macPIClk                      ,// Platform clock                     
      input wire                         macPIClkHardRst_n             ,// Platfrom Reset

      //$port_g general set interrupts
      input wire                         setphyRxStart                 ,// set phyRxStart interruption      
      input wire                         setphyErr                     ,// set phyErr interruption          
      input wire                         setmacPHYIFUnderRun           ,// set macPHYIFUnderRun interruption
      input wire                         sethwErr                      ,// set hwErr interruption           
      input wire                         setimpSecDTIM                 ,// set impSecDTIM interruption      
      input wire                         setimpPriDTIM                 ,// set impPriDTIM interruption      
      input wire                         setbcnTxDMADead               ,// set bcnTxDMADead interruption    
      input wire                         setac3TxDMADead               ,// set ac3TxDMADead interruption    
      input wire                         setac2TxDMADead               ,// set ac2TxDMADead interruption    
      input wire                         setac1TxDMADead               ,// set ac1TxDMADead interruption    
      input wire                         setac0TxDMADead               ,// set ac0TxDMADead interruption    
      input wire                         setptError                    ,// set ptError interruption         
      input wire                         settimSet                     ,// set timSet interruption          
      input wire                         setolbcDSSS                   ,// set olbcDSSS interruption        
      input wire                         setolbcOFDM                   ,// set olbcOFDM interruption        
      input wire                         setrxFIFOOverFlow             ,// set rxFIFOOverFlow interruption  
      input wire                         setrxDMAEmpty                 ,// set rxDMAEmpty interruption      
      input wire                         setmacPHYIFOverflow           ,// set macPHYIFOverflow interruption      
      input wire                         setrxPayloadDMADead           ,// set rxPayloadDMADead interruption      
      input wire                         setrxHeaderDMADead            ,// set rxHeaderDMADead interruption      
      input wire [9:0]                   setabsTimers                  ,// set absTimer interruption       
      input wire                         setidleInterrupt              ,// set idleInterrupt interruption   
      input wire                         setimpSecTBTT                 ,// set impSecTBTT interruption      
      input wire                         setimpPriTBTT                 ,// set impPriTBTT interruption      
      
      //$port_g general interrupts clear
      input wire                         clearphyRxStart               ,// clear phyRxStart interruption      
      input wire                         clearphyErr                   ,// clear phyErr interruption            
      input wire                         clearmacPHYIFUnderRun         ,// clear macPHYIFUnderRun interruption  
      input wire                         clearhwErr                    ,// clear hwErr interruption             
      input wire                         clearimpSecDTIM               ,// clear impSecDTIM interruption        
      input wire                         clearimpPriDTIM               ,// clear impPriDTIM interruption        
      input wire                         clearbcnTxDMADead             ,// clear bcnTxDMADead interruption      
      input wire                         clearac3TxDMADead             ,// clear ac3TxDMADead interruption      
      input wire                         clearac2TxDMADead             ,// clear ac2TxDMADead interruption      
      input wire                         clearac1TxDMADead             ,// clear ac1TxDMADead interruption      
      input wire                         clearac0TxDMADead             ,// clear ac0TxDMADead interruption      
      input wire                         clearptError                  ,// clear ptError interruption           
      input wire                         cleartimSet                   ,// clear timSet interruption            
      input wire                         clearolbcDSSS                 ,// clear olbcDSSS interruption          
      input wire                         clearolbcOFDM                 ,// clear olbcOFDM interruption          
      input wire                         clearrxFIFOOverFlow           ,// clear rxFIFOOverFlow interruption    
      input wire                         clearrxDMAEmpty               ,// clear rxDMAEmpty interruption        
      input wire                         clearmacPHYIFOverflow         ,// clear macPHYIFOverflow interruption        
      input wire                         clearrxPayloadDMADead         ,// clear rxPayloadDMADead interruption        
      input wire                         clearrxHeaderDMADead          ,// clear rxHeaderDMADead interruption        
      input wire [9:0]                   clearabsTimers                ,// clear absTimer interruption         
      input wire                         clearidleInterrupt            ,// clear idleInterrupt interruption     
      input wire                         clearimpSecTBTT               ,// clear impSecTBTT interruption        
      input wire                         clearimpPriTBTT               ,// clear impPriTBTT interruption        
      
      //$port_g general interrupts mask
      input wire                         maskphyRxStart                ,// phyRxStart mask interruption
      input wire                         maskphyErr                    ,// phyErr mask interruption
      input wire                         maskmacPHYIFUnderRun          ,// macPHYIFUnderRun mask interruption
      input wire                         maskhwErr                     ,// hwErr mask interruption
      input wire                         maskimpSecDTIM                ,// impSecDTIM mask interruption
      input wire                         maskimpPriDTIM                ,// impPriDTIM mask interruption
      input wire                         maskbcnTxDMADead              ,// bcnTxDMADead mask interruption
      input wire                         maskac3TxDMADead              ,// ac3TxDMADead mask interruption
      input wire                         maskac2TxDMADead              ,// ac2TxDMADead mask interruption
      input wire                         maskac1TxDMADead              ,// ac1TxDMADead mask interruption
      input wire                         maskac0TxDMADead              ,// ac0TxDMADead mask interruption
      input wire                         maskptError                   ,// ptError mask interruption
      input wire                         masktimSet                    ,// timSet mask interruption
      input wire                         maskolbcDSSS                  ,// olbcDSSS mask interruption
      input wire                         maskolbcOFDM                  ,// olbcOFDM mask interruption
      input wire                         maskrxFIFOOverFlow            ,// rxFIFOOverFlow mask interruption
      input wire                         maskrxDMAEmpty                ,// rxDMAEmpty mask interruption
      input wire                         maskmacPHYIFOverflow          ,// macPHYIFOverflow mask interruption
      input wire                         maskrxPayloadDMADead          ,// rxPayloadDMADead mask interruption
      input wire                         maskrxHeaderDMADead           ,// rxHeaderDMADead mask interruption
      input wire [9:0]                   maskabsTimers                 ,// absTimer mask interruption
      input wire                         maskidleInterrupt             ,// idleInterrupt mask interruption
      input wire                         maskimpSecTBTT                ,// impSecTBTT mask interruption
      input wire                         maskimpPriTBTT                ,// impPriTBTT interruption       
      
      //$port_g general interrupts statusset
      output wire                        statussetphyRxStart           ,//  phyRxStart interruption status
      output wire                        statussetphyErr               ,//  phyErr interruption status
      output wire                        statussetmacPHYIFUnderRun     ,//  macPHYIFUnderRun interruption status
      output wire                        statussethwErr                ,//  hwErr interruption status
      output wire                        statussetimpSecDTIM           ,//  impSecDTIM interruption status
      output wire                        statussetimpPriDTIM           ,//  impPriDTIM interruption status
      output wire                        statussetbcnTxDMADead         ,//  bcnTxDMADead interruption status
      output wire                        statussetac3TxDMADead         ,//  ac3TxDMADead interruption status
      output wire                        statussetac2TxDMADead         ,//  ac2TxDMADead interruption status
      output wire                        statussetac1TxDMADead         ,//  ac1TxDMADead interruption status
      output wire                        statussetac0TxDMADead         ,//  ac0TxDMADead interruption status
      output wire                        statussetptError              ,//  ptError interruption status
      output wire                        statussettimSet               ,//  timSet interruption status
      output wire                        statussetolbcDSSS             ,//  olbcDSSS interruption status
      output wire                        statussetolbcOFDM             ,//  olbcOFDM interruption status
      output wire                        statussetrxFIFOOverFlow       ,//  rxFIFOOverFlow interruption status
      output wire                        statussetrxDMAEmpty           ,//  rxDMAEmpty interruption status
      output wire                        statussetmacPHYIFOverflow     ,//  macPHYIFOverflow interruption status
      output wire                        statussetrxPayloadDMADead     ,//  rxPayloadDMADead interruption status
      output wire                        statussetrxHeaderDMADead      ,//  rxHeaderDMADead interruption status
      output wire [9:0]                  statussetabsTimers            ,//  absTimer interruption status
      output wire                        statussetidleInterrupt        ,//  idleInterrupt interruption status
      output wire                        statussetimpSecTBTT           ,//  impSecTBTT interruption status
      output wire                        statussetimpPriTBTT           ,//  impPriTBTT interruption status

      //$port_g Rx/Tx set interrupts
      input wire                         settimerRxTrigger             ,//  set timerRxTrigger  
      input wire                         setrxTrigger                  ,//  set rxTrigger       
      input wire                         setcounterRxTrigger           ,//  set counterRxTrigger       
      input wire                         setbaRxTrigger                ,//  set baRxTrigger       
      input wire                         setac3TxBufTrigger            ,//  set ac3TxBufTrigger    
      input wire                         setac2TxBufTrigger            ,//  set ac2TxBufTrigger    
      input wire                         setac1TxBufTrigger            ,//  set ac1TxBufTrigger    
      input wire                         setac0TxBufTrigger            ,//  set ac0TxBufTrigger    
      input wire                         setbcnTxBufTrigger            ,//  set bcnTxBufTrigger    
      input wire                         settimerTxTrigger             ,//  set timerTxTrigger  
      input wire                         settxopComplete               ,//  set txopComplete    
      input wire                         setrdTxTrigger                ,//  set rdTxTrigger     
      input wire                         sethccaTxTrigger              ,//  set hccaTxTrigger   
      input wire                         setac3TxTrigger               ,//  set ac3TxTrigger    
      input wire                         setac2TxTrigger               ,//  set ac2TxTrigger    
      input wire                         setac1TxTrigger               ,//  set ac1TxTrigger    
      input wire                         setac0TxTrigger               ,//  set ac0TxTrigger    
      input wire                         setbcnTxTrigger               ,//  set bcnTxTrigger    
      input wire                         setrdProtTrigger              ,//  set rdProtTrigger   
      input wire                         sethccaProtTrigger            ,//  set hccaProtTrigger 
      input wire                         setac3ProtTrigger             ,//  set ac3ProtTrigger  
      input wire                         setac2ProtTrigger             ,//  set ac2ProtTrigger  
      input wire                         setac1ProtTrigger             ,//  set ac1ProtTrigger  
      input wire                         setac0ProtTrigger             ,//  set ac0BWDropTrigger  
      input wire                         setac3BWDropTrigger             ,//  set ac3BWDropTrigger  
      input wire                         setac2BWDropTrigger             ,//  set ac2BWDropTrigger  
      input wire                         setac1BWDropTrigger             ,//  set ac1BWDropTrigger  
      input wire                         setac0BWDropTrigger             ,//  set ac0BWDropTrigger  
     
      //$port_g Rx/Tx clear interrupts
      input wire                         cleartimerRxTrigger           ,//  clear timerRxTrigger  
      input wire                         clearrxTrigger                ,//  clear rxTrigger       
      input wire                         clearcounterRxTrigger         ,//  clear counterRxTrigger       
      input wire                         clearbaRxTrigger              ,//  clear baRxTrigger       
      input wire                         clearac3TxBufTrigger          ,//  clear ac3TxBufTrigger    
      input wire                         clearac2TxBufTrigger          ,//  clear ac2TxBufTrigger    
      input wire                         clearac1TxBufTrigger          ,//  clear ac1TxBufTrigger    
      input wire                         clearac0TxBufTrigger          ,//  clear ac0TxBufTrigger    
      input wire                         clearbcnTxBufTrigger          ,//  clear bcnTxBufTrigger    
      input wire                         cleartimerTxTrigger           ,//  clear timerTxTrigger  
      input wire                         cleartxopComplete             ,//  clear txopComplete    
      input wire                         clearrdTxTrigger              ,//  clear rdTxTrigger     
      input wire                         clearhccaTxTrigger            ,//  clear hccaTxTrigger   
      input wire                         clearac3TxTrigger             ,//  clear ac3TxTrigger    
      input wire                         clearac2TxTrigger             ,//  clear ac2TxTrigger    
      input wire                         clearac1TxTrigger             ,//  clear ac1TxTrigger    
      input wire                         clearac0TxTrigger             ,//  clear ac0TxTrigger    
      input wire                         clearbcnTxTrigger             ,//  clear bcnTxTrigger    
      input wire                         clearrdProtTrigger            ,//  clear rdProtTrigger   
      input wire                         clearhccaProtTrigger          ,//  clear hccaProtTrigger 
      input wire                         clearac3ProtTrigger           ,//  clear ac3ProtTrigger  
      input wire                         clearac2ProtTrigger           ,//  clear ac2ProtTrigger  
      input wire                         clearac1ProtTrigger           ,//  clear ac1ProtTrigger  
      input wire                         clearac0ProtTrigger           ,//  clear ac0BWDropTrigger  
      input wire                         clearac3BWDropTrigger           ,//  clear ac3BWDropTrigger  
      input wire                         clearac2BWDropTrigger           ,//  clear ac2BWDropTrigger  
      input wire                         clearac1BWDropTrigger           ,//  clear ac1BWDropTrigger  
      input wire                         clearac0BWDropTrigger           ,//  clear ac0BWDropTrigger  

      //$port_g Rx/Tx mask interrupts
      input wire                         masktimerRxTrigger            ,// timerRxTrigger output interruption mask 
      input wire                         maskrxTrigger                 ,// rxTrigger output interruption mask 
      input wire                         maskcounterRxTrigger          ,// counterRxTrigger output interruption mask 
      input wire                         maskbaRxTrigger               ,// baRxTrigger output interruption mask 
      input wire                         maskac3TxBufTrigger           ,// ac3TxBufTrigger output interruption mask 
      input wire                         maskac2TxBufTrigger           ,// ac2TxBufTrigger output interruption mask 
      input wire                         maskac1TxBufTrigger           ,// ac1TxBufTrigger output interruption mask 
      input wire                         maskac0TxBufTrigger           ,// ac0TxBufTrigger output interruption mask 
      input wire                         maskbcnTxBufTrigger           ,// bcnTxBufTrigger output interruption mask 
      input wire                         masktimerTxTrigger            ,// timerTxTrigger output interruption mask 
      input wire                         masktxopComplete              ,// txopComplete output interruption mask 
      input wire                         maskrdTxTrigger               ,// rdTxTrigger output interruption mask 
      input wire                         maskhccaTxTrigger             ,// hccaTxTrigger output interruption mask 
      input wire                         maskac3TxTrigger              ,// ac3TxTrigger output interruption mask 
      input wire                         maskac2TxTrigger              ,// ac2TxTrigger output interruption mask 
      input wire                         maskac1TxTrigger              ,// ac1TxTrigger output interruption mask 
      input wire                         maskac0TxTrigger              ,// ac0TxTrigger output interruption mask 
      input wire                         maskbcnTxTrigger              ,// bcnTxTrigger output interruption mask 
      input wire                         maskrdProtTrigger             ,// rdProtTrigger output interruption mask 
      input wire                         maskhccaProtTrigger           ,// hccaProtTrigger output interruption mask 
      input wire                         maskac3ProtTrigger            ,// ac3ProtTrigger output interruption mask 
      input wire                         maskac2ProtTrigger            ,// ac2ProtTrigger output interruption mask 
      input wire                         maskac1ProtTrigger            ,// ac1ProtTrigger output interruption mask 
      input wire                         maskac0ProtTrigger            ,// ac0ProtTrigger output interruption mask 
      input wire                         maskac3BWDropTrigger            ,// ac3BWDropTrigger output interruption mask 
      input wire                         maskac2BWDropTrigger            ,// ac2BWDropTrigger output interruption mask 
      input wire                         maskac1BWDropTrigger            ,// ac1BWDropTrigger output interruption mask 
      input wire                         maskac0BWDropTrigger            ,// ac0BWDropTrigger output interruption mask 

      //$port_g Rx/Tx interrupts statusset
      output wire                        statussettimerRxTrigger       ,//  timerRxTrigger interruption status
      output wire                        statussetrxTrigger            ,//  rxTrigger interruption status
      output wire                        statussetcounterRxTrigger     ,//  counterRxTrigger interruption status
      output wire                        statussetbaRxTrigger          ,//  baRxTrigger interruption status
      output wire                        statussetac3TxBufTrigger      ,//  ac3TxBufTrigger interruption status
      output wire                        statussetac2TxBufTrigger      ,//  ac2TxBufTrigger interruption status
      output wire                        statussetac1TxBufTrigger      ,//  ac1TxBufTrigger interruption status
      output wire                        statussetac0TxBufTrigger      ,//  ac0TxBufTrigger interruption status
      output wire                        statussetbcnTxBufTrigger      ,//  bcnTxBufTrigger interruption status
      output wire                        statussettimerTxTrigger       ,//  timerTxTrigger interruption status
      output wire                        statussettxopComplete         ,//  txopComplete interruption status
      output wire                        statussetrdTxTrigger          ,//  rdTxTrigger interruption status
      output wire                        statussethccaTxTrigger        ,//  hccaTxTrigger interruption status
      output wire                        statussetac3TxTrigger         ,//  ac3TxTrigger interruption status
      output wire                        statussetac2TxTrigger         ,//  ac2TxTrigger interruption status
      output wire                        statussetac1TxTrigger         ,//  ac1TxTrigger interruption status
      output wire                        statussetac0TxTrigger         ,//  ac0TxTrigger interruption status
      output wire                        statussetbcnTxTrigger         ,//  bcnTxTrigger interruption status
      output wire                        statussetrdProtTrigger        ,//  rdProtTrigger interruption status
      output wire                        statussethccaProtTrigger      ,//  hccaProtTrigger interruption status
      output wire                        statussetac3ProtTrigger       ,//  ac3ProtTrigger interruption status
      output wire                        statussetac2ProtTrigger       ,//  ac2ProtTrigger interruption status
      output wire                        statussetac1ProtTrigger       ,//  ac1ProtTrigger interruption status
      output wire                        statussetac0ProtTrigger       ,//  ac0ProtTrigger interruption status
      output wire                        statussetac3BWDropTrigger       ,//  ac3BWDropTrigger interruption status
      output wire                        statussetac2BWDropTrigger       ,//  ac2BWDropTrigger interruption status
      output wire                        statussetac1BWDropTrigger       ,//  ac1BWDropTrigger interruption status
      output wire                        statussetac0BWDropTrigger       ,//  ac0BWDropTrigger interruption status


      //$port_g internal interruptions interruption
      input wire                         intphyRxStart                 ,// phyRxStart internal register
      input wire                         intphyErr                     ,// phyErr internal register
      input wire                         intmacPHYIFUnderRun           ,// macPHYIFUnderRun internal register
      input wire                         inthwErr                      ,// hwErr internal register
      input wire                         intimpSecDTIM                 ,// impSecDTIM internal register
      input wire                         intimpPriDTIM                 ,// impPriDTIM internal register
      input wire                         intbcnTxDMADead               ,// bcnTxDMADead internal register
      input wire                         intac3TxDMADead               ,// ac3TxDMADead internal register
      input wire                         intac2TxDMADead               ,// ac2TxDMADead internal register
      input wire                         intac1TxDMADead               ,// ac1TxDMADead internal register
      input wire                         intac0TxDMADead               ,// ac0TxDMADead internal register
      input wire                         intptError                    ,// ptError internal register
      input wire                         inttimSet                     ,// timSet internal register
      input wire                         intolbcDSSS                   ,// olbcDSSS internal register
      input wire                         intolbcOFDM                   ,// olbcOFDM internal register
      input wire                         intrxFIFOOverFlow             ,// rxFIFOOverFlow internal register
      input wire                         intrxDMAEmpty                 ,// rxDMAEmpty internal register
      input wire                         intmacPHYIFOverflow           ,// macPHYIFOverflow internal register
      input wire                         intrxPayloadDMADead           ,// rxPayloadDMADead internal register
      input wire                         intrxHeaderDMADead            ,// rxHeaderDMADead internal register
      input wire [9:0]                   intabsTimers                  ,// absTimer internal register
      input wire                         intidleInterrupt              ,// idleInterrupt internal register
      input wire                         intimpSecTBTT                 ,// impSecTBTT internal register
      input wire                         intimpPriTBTT                 ,// impPriTBTT internal register
      input wire                         inttimerRxTrigger             ,// timerRxTrigger internal register
      input wire                         intrxTrigger                  ,// rxTrigger internal register
      input wire                         intcounterRxTrigger           ,// counterRxTrigger internal register
      input wire                         intbaRxTrigger                ,// baRxTrigger internal register
      input wire                         intac3TxBufTrigger            ,// ac3TxBufTrigger internal register
      input wire                         intac2TxBufTrigger            ,// ac2TxBufTrigger internal register
      input wire                         intac1TxBufTrigger            ,// ac1TxBufTrigger internal register
      input wire                         intac0TxBufTrigger            ,// ac0TxBufTrigger internal register
      input wire                         intbcnTxBufTrigger            ,// bcnTxBufTrigger internal register
      input wire                         inttimerTxTrigger             ,// timerTxTrigger internal register
      input wire                         inttxopComplete               ,// txopComplete internal register
      input wire                         intrdTxTrigger                ,// rdTxTrigger internal register
      input wire                         inthccaTxTrigger              ,// hccaTxTrigger internal register
      input wire                         intac3TxTrigger               ,// ac3TxTrigger internal register
      input wire                         intac2TxTrigger               ,// ac2TxTrigger internal register
      input wire                         intac1TxTrigger               ,// ac1TxTrigger internal register
      input wire                         intac0TxTrigger               ,// ac0TxTrigger internal register
      input wire                         intbcnTxTrigger               ,// bcnTxTrigger internal register
      input wire                         intrdProtTrigger              ,// rdProtTrigger internal register
      input wire                         inthccaProtTrigger            ,// hccaProtTrigger internal register
      input wire                         intac3ProtTrigger             ,// ac3ProtTrigger internal register
      input wire                         intac2ProtTrigger             ,// ac2ProtTrigger internal register
      input wire                         intac1ProtTrigger             ,// ac1ProtTrigger internal register
      input wire                         intac0ProtTrigger             ,// ac0ProtTrigger internal register
      input wire                         intac3BWDropTrigger             ,// ac3BWDropTrigger internal register
      input wire                         intac2BWDropTrigger             ,// ac2BWDropTrigger internal register
      input wire                         intac1BWDropTrigger             ,// ac1BWDropTrigger internal register
      input wire                         intac0BWDropTrigger             //,// ac0BWDropTrigger internal register

      //$port_g internal masked interruption
      //output wire                        maskedIntphyRxStart           ,//  masked IntphyRxStart       
      //output wire                        maskedIntphyErr               ,//  masked IntphyErr           
      //output wire                        maskedIntmacPHYIFUnderRun     ,//  masked IntmacPHYIFUnderRun 
      //output wire                        maskedInthwErr                ,//  masked InthwErr            
      //output wire                        maskedIntimpSecDTIM           ,//  masked IntimpSecDTIM       
      //output wire                        maskedIntimpPriDTIM           ,//  masked IntimpPriDTIM       
      //output wire                        maskedIntbcnTxDMADead         ,//  masked IntbcnTxDMADead     
      //output wire                        maskedIntac3TxDMADead         ,//  masked Intac3TxDMADead     
      //output wire                        maskedIntac2TxDMADead         ,//  masked Intac2TxDMADead     
      //output wire                        maskedIntac1TxDMADead         ,//  masked Intac1TxDMADead     
      //output wire                        maskedIntac0TxDMADead         ,//  masked Intac0TxDMADead     
      //output wire                        maskedIntptError              ,//  masked IntptError          
      //output wire                        maskedInttimSet               ,//  masked InttimSet           
      //output wire                        maskedIntolbcDSSS             ,//  masked IntolbcDSSS         
      //output wire                        maskedIntolbcOFDM             ,//  masked IntolbcOFDM         
      //output wire                        maskedIntrxFIFOOverFlow       ,//  masked IntrxFIFOOverFlow   
      //output wire                        maskedIntrxDMAEmpty           ,//  masked IntrxDMAEmpty       
      //output wire                        maskedIntmacPHYIFOverflow     ,//  masked IntmacPHYIFOverflow     
      //output wire                        maskedIntrxPayloadDMADead     ,//  masked IntrxPayloadDMADead       
      //output wire                        maskedIntrxHeaderDMADead      ,//  masked IntrxHeaderDMADead       
      //output wire                        maskedIntabsTimer2            ,//  masked IntabsTimer2        
      //output wire                        maskedIntabsTimer1            ,//  masked IntabsTimer1        
      //output wire                        maskedIntidleInterrupt        ,//  masked IntidleInterrupt    
      //output wire                        maskedIntimpSecTBTT           ,//  masked IntimpSecTBTT       
      //output wire                        maskedIntimpPriTBTT           ,//  masked IntimpPriTBTT       
      //output wire                        maskedInttimerRxTrigger       ,//  masked InttimerRxTrigger   
      //output wire                        maskedIntrxTrigger            ,//  masked IntrxTrigger        
      //output wire                        maskedIntbaRxTrigger          ,//  masked IntbaRxTrigger        
      //output wire                        maskedInttimerTxTrigger       ,//  masked InttimerTxTrigger   
      //output wire                        maskedInttxopComplete         ,//  masked InttxopComplete     
      //output wire                        maskedIntrdTxTrigger          ,//  masked IntrdTxTrigger      
      //output wire                        maskedInthccaTxTrigger        ,//  masked InthccaTxTrigger    
      //output wire                        maskedIntac3TxTrigger         ,//  masked Intac3TxTrigger     
      //output wire                        maskedIntac2TxTrigger         ,//  masked Intac2TxTrigger     
      //output wire                        maskedIntac1TxTrigger         ,//  masked Intac1TxTrigger     
      //output wire                        maskedIntac0TxTrigger         ,//  masked Intac0TxTrigger     
      //output wire                        maskedIntbcnTxTrigger         ,//  masked IntbcnTxTrigger     
      //output wire                        maskedIntrdProtTrigger        ,//  masked IntrdProtTrigger    
      //output wire                        maskedInthccaProtTrigger      ,//  masked InthccaProtTrigger  
      //output wire                        maskedIntac3ProtTrigger       ,//  masked Intac3ProtTrigger   
      //output wire                        maskedIntac2ProtTrigger       ,//  masked Intac2ProtTrigger   
      //output wire                        maskedIntac1ProtTrigger       ,//  masked Intac1ProtTrigger   
      //output wire                        maskedIntac0ProtTrigger        //  masked Intac0ProtTrigger   

                 );




//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_phyRxStart (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intphyRxStart),
                .set                    (setphyRxStart),
                .clear                  (clearphyRxStart),
                .mask                   (maskphyRxStart),
                .statusset              (statussetphyRxStart)//,
                //.interruptOut           (maskedIntphyRxStart)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_phyErr (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intphyErr),
                .set                    (setphyErr),
                .clear                  (clearphyErr),
                .mask                   (maskphyErr),
                .statusset              (statussetphyErr)//,
                //.interruptOut           (maskedIntphyErr)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_macPHYIFUnderRun (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intmacPHYIFUnderRun),
                .set                    (setmacPHYIFUnderRun),
                .clear                  (clearmacPHYIFUnderRun),
                .mask                   (maskmacPHYIFUnderRun),
                .statusset              (statussetmacPHYIFUnderRun)//,
                //.interruptOut           (maskedIntmacPHYIFUnderRun)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_hwErr (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (inthwErr),
                .set                    (sethwErr),
                .clear                  (clearhwErr),
                .mask                   (maskhwErr),
                .statusset              (statussethwErr)//,
                //.interruptOut           (maskedInthwErr)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_impSecDTIM (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intimpSecDTIM),
                .set                    (setimpSecDTIM),
                .clear                  (clearimpSecDTIM),
                .mask                   (maskimpSecDTIM),
                .statusset              (statussetimpSecDTIM)//,
                //.interruptOut           (maskedIntimpSecDTIM)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_impPriDTIM (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intimpPriDTIM),
                .set                    (setimpPriDTIM),
                .clear                  (clearimpPriDTIM),
                .mask                   (maskimpPriDTIM),
                .statusset              (statussetimpPriDTIM)//,
                //.interruptOut           (maskedIntimpPriDTIM)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_bcnTxDMADead (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intbcnTxDMADead),
                .set                    (setbcnTxDMADead),
                .clear                  (clearbcnTxDMADead),
                .mask                   (maskbcnTxDMADead),
                .statusset              (statussetbcnTxDMADead)//,
                //.interruptOut           (maskedIntbcnTxDMADead)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac3TxDMADead (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac3TxDMADead),
                .set                    (setac3TxDMADead),
                .clear                  (clearac3TxDMADead),
                .mask                   (maskac3TxDMADead),
                .statusset              (statussetac3TxDMADead)//,
                //.interruptOut           (maskedIntac3TxDMADead)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac2TxDMADead (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac2TxDMADead),
                .set                    (setac2TxDMADead),
                .clear                  (clearac2TxDMADead),
                .mask                   (maskac2TxDMADead),
                .statusset              (statussetac2TxDMADead)//,
                //.interruptOut           (maskedIntac2TxDMADead)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac1TxDMADead (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac1TxDMADead),
                .set                    (setac1TxDMADead),
                .clear                  (clearac1TxDMADead),
                .mask                   (maskac1TxDMADead),
                .statusset              (statussetac1TxDMADead)//,
                //.interruptOut           (maskedIntac1TxDMADead)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac0TxDMADead (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac0TxDMADead),
                .set                    (setac0TxDMADead),
                .clear                  (clearac0TxDMADead),
                .mask                   (maskac0TxDMADead),
                .statusset              (statussetac0TxDMADead)//,
                //.interruptOut           (maskedIntac0TxDMADead)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ptError (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intptError),
                .set                    (setptError),
                .clear                  (clearptError),
                .mask                   (maskptError),
                .statusset              (statussetptError)//,
                //.interruptOut           (maskedIntptError)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_timSet (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (inttimSet),
                .set                    (settimSet),
                .clear                  (cleartimSet),
                .mask                   (masktimSet),
                .statusset              (statussettimSet)//,
                //.interruptOut           (maskedInttimSet)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_olbcDSSS (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intolbcDSSS),
                .set                    (setolbcDSSS),
                .clear                  (clearolbcDSSS),
                .mask                   (maskolbcDSSS),
                .statusset              (statussetolbcDSSS)//,
                //.interruptOut           (maskedIntolbcDSSS)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_olbcOFDM (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intolbcOFDM),
                .set                    (setolbcOFDM),
                .clear                  (clearolbcOFDM),
                .mask                   (maskolbcOFDM),
                .statusset              (statussetolbcOFDM)//,
                //.interruptOut           (maskedIntolbcOFDM)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_rxFIFOOverFlow (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intrxFIFOOverFlow),
                .set                    (setrxFIFOOverFlow),
                .clear                  (clearrxFIFOOverFlow),
                .mask                   (maskrxFIFOOverFlow),
                .statusset              (statussetrxFIFOOverFlow)//,
                //.interruptOut           (maskedIntrxFIFOOverFlow)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_rxDMAEmpty (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intrxDMAEmpty),
                .set                    (setrxDMAEmpty),
                .clear                  (clearrxDMAEmpty),
                .mask                   (maskrxDMAEmpty),
                .statusset              (statussetrxDMAEmpty)//,
                //.interruptOut           (maskedIntrxDMAEmpty)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_macPHYIFOverflow (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intmacPHYIFOverflow),
                .set                    (setmacPHYIFOverflow),
                .clear                  (clearmacPHYIFOverflow),
                .mask                   (maskmacPHYIFOverflow),
                .statusset              (statussetmacPHYIFOverflow)//,
                //.interruptOut           (maskedIntmacPHYIFOverflow)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_rxPayloadDMADead (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intrxPayloadDMADead),
                .set                    (setrxPayloadDMADead),
                .clear                  (clearrxPayloadDMADead),
                .mask                   (maskrxPayloadDMADead),
                .statusset              (statussetrxPayloadDMADead)//,
                //.interruptOut           (maskedIntrxPayloadDMADead)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_rxHeaderDMADead (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intrxHeaderDMADead),
                .set                    (setrxHeaderDMADead),
                .clear                  (clearrxHeaderDMADead),
                .mask                   (maskrxHeaderDMADead),
                .statusset              (statussetrxHeaderDMADead)//,
                //.interruptOut           (maskedIntrxHeaderDMADead)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_absTimer
// Name of the file containing this module : intCtrlReg.v

genvar i;
generate
  
  for (i=0; i< 10; i = i+1)
  begin
    intCtrlReg U_absTimer (
                    .macPIClk               (macPIClk),
                    .macPIClkHardRst_n      (macPIClkHardRst_n),
                    .interrupt              (intabsTimers[i]),
                    .set                    (setabsTimers[i]),
                    .clear                  (clearabsTimers[i]),
                    .mask                   (maskabsTimers[i]),
                    .statusset              (statussetabsTimers[i])//,
                  );
  end
endgenerate

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_idleInterrupt (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intidleInterrupt),
                .set                    (setidleInterrupt),
                .clear                  (clearidleInterrupt),
                .mask                   (maskidleInterrupt),
                .statusset              (statussetidleInterrupt)//,
                //.interruptOut           (maskedIntidleInterrupt)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_impSecTBTT (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intimpSecTBTT),
                .set                    (setimpSecTBTT),
                .clear                  (clearimpSecTBTT),
                .mask                   (maskimpSecTBTT),
                .statusset              (statussetimpSecTBTT)//,
                //.interruptOut           (maskedIntimpSecTBTT)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_impPriTBTT (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intimpPriTBTT),
                .set                    (setimpPriTBTT),
                .clear                  (clearimpPriTBTT),
                .mask                   (maskimpPriTBTT),
                .statusset              (statussetimpPriTBTT)//,
                //.interruptOut           (maskedIntimpPriTBTT)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_timerRxTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (inttimerRxTrigger),
                .set                    (settimerRxTrigger),
                .clear                  (cleartimerRxTrigger),
                .mask                   (masktimerRxTrigger),
                .statusset              (statussettimerRxTrigger)//,
                //.interruptOut           (maskedInttimerRxTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_rxTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intrxTrigger),
                .set                    (setrxTrigger),
                .clear                  (clearrxTrigger),
                .mask                   (maskrxTrigger),
                .statusset              (statussetrxTrigger)//,
                //.interruptOut           (maskedIntrxTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_counterRxTrigger
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_counterRxTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intcounterRxTrigger),
                .set                    (setcounterRxTrigger),
                .clear                  (clearcounterRxTrigger),
                .mask                   (maskcounterRxTrigger),
                .statusset              (statussetcounterRxTrigger)//,
                //.interruptOut           (maskedIntbaRxTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_baRxTrigger
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_baRxTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intbaRxTrigger),
                .set                    (setbaRxTrigger),
                .clear                  (clearbaRxTrigger),
                .mask                   (maskbaRxTrigger),
                .statusset              (statussetbaRxTrigger)//,
                //.interruptOut           (maskedIntbaRxTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac3TxBufTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac3TxBufTrigger),
                .set                    (setac3TxBufTrigger),
                .clear                  (clearac3TxBufTrigger),
                .mask                   (maskac3TxBufTrigger),
                .statusset              (statussetac3TxBufTrigger)//,
                //.interruptOut           (maskedIntac3TxBufTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac2TxBufTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac2TxBufTrigger),
                .set                    (setac2TxBufTrigger),
                .clear                  (clearac2TxBufTrigger),
                .mask                   (maskac2TxBufTrigger),
                .statusset              (statussetac2TxBufTrigger)//,
                //.interruptOut           (maskedIntac2TxBufTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac1TxBufTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac1TxBufTrigger),
                .set                    (setac1TxBufTrigger),
                .clear                  (clearac1TxBufTrigger),
                .mask                   (maskac1TxBufTrigger),
                .statusset              (statussetac1TxBufTrigger)//,
                //.interruptOut           (maskedIntac1TxBufTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac0TxBufTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac0TxBufTrigger),
                .set                    (setac0TxBufTrigger),
                .clear                  (clearac0TxBufTrigger),
                .mask                   (maskac0TxBufTrigger),
                .statusset              (statussetac0TxBufTrigger)//,
                //.interruptOut           (maskedIntac0TxBufTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_bcnTxBufTrigger
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_bcnTxBufTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intbcnTxBufTrigger),
                .set                    (setbcnTxBufTrigger),
                .clear                  (clearbcnTxBufTrigger),
                .mask                   (maskbcnTxBufTrigger),
                .statusset              (statussetbcnTxBufTrigger)//,
                //.interruptOut           (maskedIntbcnTxBufTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_timerTxTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (inttimerTxTrigger),
                .set                    (settimerTxTrigger),
                .clear                  (cleartimerTxTrigger),
                .mask                   (masktimerTxTrigger),
                .statusset              (statussettimerTxTrigger)//,
                //.interruptOut           (maskedInttimerTxTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_txopComplete (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (inttxopComplete),
                .set                    (settxopComplete),
                .clear                  (cleartxopComplete),
                .mask                   (masktxopComplete),
                .statusset              (statussettxopComplete)//,
                //.interruptOut           (maskedInttxopComplete)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_rdTxTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intrdTxTrigger),
                .set                    (setrdTxTrigger),
                .clear                  (clearrdTxTrigger),
                .mask                   (maskrdTxTrigger),
                .statusset              (statussetrdTxTrigger)//,
                //.interruptOut           (maskedIntrdTxTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_hccaTxTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (inthccaTxTrigger),
                .set                    (sethccaTxTrigger),
                .clear                  (clearhccaTxTrigger),
                .mask                   (maskhccaTxTrigger),
                .statusset              (statussethccaTxTrigger)//,
                //.interruptOut           (maskedInthccaTxTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac3TxTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac3TxTrigger),
                .set                    (setac3TxTrigger),
                .clear                  (clearac3TxTrigger),
                .mask                   (maskac3TxTrigger),
                .statusset              (statussetac3TxTrigger)//,
                //.interruptOut           (maskedIntac3TxTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac2TxTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac2TxTrigger),
                .set                    (setac2TxTrigger),
                .clear                  (clearac2TxTrigger),
                .mask                   (maskac2TxTrigger),
                .statusset              (statussetac2TxTrigger)//,
                //.interruptOut           (maskedIntac2TxTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac1TxTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac1TxTrigger),
                .set                    (setac1TxTrigger),
                .clear                  (clearac1TxTrigger),
                .mask                   (maskac1TxTrigger),
                .statusset              (statussetac1TxTrigger)//,
                //.interruptOut           (maskedIntac1TxTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac0TxTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac0TxTrigger),
                .set                    (setac0TxTrigger),
                .clear                  (clearac0TxTrigger),
                .mask                   (maskac0TxTrigger),
                .statusset              (statussetac0TxTrigger)//,
                //.interruptOut           (maskedIntac0TxTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_bcnTxTrigger
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_bcnTxTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intbcnTxTrigger),
                .set                    (setbcnTxTrigger),
                .clear                  (clearbcnTxTrigger),
                .mask                   (maskbcnTxTrigger),
                .statusset              (statussetbcnTxTrigger)//,
                //.interruptOut           (maskedIntbcnTxTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_rdProtTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intrdProtTrigger),
                .set                    (setrdProtTrigger),
                .clear                  (clearrdProtTrigger),
                .mask                   (maskrdProtTrigger),
                .statusset              (statussetrdProtTrigger)//,
                //.interruptOut           (maskedIntrdProtTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_hccaProtTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (inthccaProtTrigger),
                .set                    (sethccaProtTrigger),
                .clear                  (clearhccaProtTrigger),
                .mask                   (maskhccaProtTrigger),
                .statusset              (statussethccaProtTrigger)//,
                //.interruptOut           (maskedInthccaProtTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac3ProtTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac3ProtTrigger),
                .set                    (setac3ProtTrigger),
                .clear                  (clearac3ProtTrigger),
                .mask                   (maskac3ProtTrigger),
                .statusset              (statussetac3ProtTrigger)//,
                //.interruptOut           (maskedIntac3ProtTrigger)
                );

// Instanciation of intCtrlReg
// Name of the instance : U_intCtrlReg
// Name of the file containing this module : intCtrlReg.v
intCtrlReg U_ac2ProtTrigger (
                .macPIClk               (macPIClk),
                .macPIClkHardRst_n      (macPIClkHardRst_n),
                .interrupt              (intac2ProtTrigger),
                .set                    (setac2ProtTrigger),
                .clear                  (clearac2ProtTrigger),
                .mask                   (maskac2ProtTrigger),
                .statusset              (statussetac2ProtTrigger)//,
              //.interruptOut           (maskedIntac2ProtTrigger)
                );
                
                // Instanciation of intCtrlReg
                // Name of the instance : U_intCtrlReg
                // Name of the file containing this module : intCtrlReg.v
                intCtrlReg U_ac1ProtTrigger (
                                .macPIClk               (macPIClk),
                                .macPIClkHardRst_n      (macPIClkHardRst_n),
                                .interrupt              (intac1ProtTrigger),
                                .set                    (setac1ProtTrigger),
                                .clear                  (clearac1ProtTrigger),
                                .mask                   (maskac1ProtTrigger),
                                .statusset              (statussetac1ProtTrigger)//,
                                //.interruptOut           (maskedIntac1ProtTrigger)
                                );
                
                // Instanciation of intCtrlReg
                // Name of the instance : U_intCtrlReg
                // Name of the file containing this module : intCtrlReg.v
                intCtrlReg U_ac0ProtTrigger (
                                .macPIClk               (macPIClk),
                                .macPIClkHardRst_n      (macPIClkHardRst_n),
                                .interrupt              (intac0ProtTrigger),
                                .set                    (setac0ProtTrigger),
                                .clear                  (clearac0ProtTrigger),
                                .mask                   (maskac0ProtTrigger),
                                .statusset              (statussetac0ProtTrigger)//,
                                //.interruptOut           (maskedIntac0ProtTrigger)
                                );
                
                // Instanciation of intCtrlReg
                // Name of the instance : U_intCtrlReg
                // Name of the file containing this module : intCtrlReg.v
                intCtrlReg U_ac3BWDropTrigger (
                                .macPIClk               (macPIClk),
                                .macPIClkHardRst_n      (macPIClkHardRst_n),
                                .interrupt              (intac3BWDropTrigger),
                                .set                    (setac3BWDropTrigger),
                                .clear                  (clearac3BWDropTrigger),
                                .mask                   (maskac3BWDropTrigger),
                                .statusset              (statussetac3BWDropTrigger)//,
                                //.interruptOut           (maskedIntac3BWDropTrigger)
                                );
                
                // Instanciation of intCtrlReg
                // Name of the instance : U_intCtrlReg
                // Name of the file containing this module : intCtrlReg.v
                intCtrlReg U_ac2BWDropTrigger (
                                .macPIClk               (macPIClk),
                                .macPIClkHardRst_n      (macPIClkHardRst_n),
                                .interrupt              (intac2BWDropTrigger),
                                .set                    (setac2BWDropTrigger),
                                .clear                  (clearac2BWDropTrigger),
                                .mask                   (maskac2BWDropTrigger),
                                .statusset              (statussetac2BWDropTrigger)//,
                                //.interruptOut           (maskedIntac2BWDropTrigger)
                                );
                
                // Instanciation of intCtrlReg
                // Name of the instance : U_intCtrlReg
                // Name of the file containing this module : intCtrlReg.v
                intCtrlReg U_ac1BWDropTrigger (
                                .macPIClk               (macPIClk),
                                .macPIClkHardRst_n      (macPIClkHardRst_n),
                                .interrupt              (intac1BWDropTrigger),
                                .set                    (setac1BWDropTrigger),
                                .clear                  (clearac1BWDropTrigger),
                                .mask                   (maskac1BWDropTrigger),
                                .statusset              (statussetac1BWDropTrigger)//,
                                //.interruptOut           (maskedIntac1BWDropTrigger)
                                );
                
                // Instanciation of intCtrlReg
                // Name of the instance : U_intCtrlReg
                // Name of the file containing this module : intCtrlReg.v
                intCtrlReg U_ac0BWDropTrigger (
                                .macPIClk               (macPIClk),
                                .macPIClkHardRst_n      (macPIClkHardRst_n),
                                .interrupt              (intac0BWDropTrigger),
                                .set                    (setac0BWDropTrigger),
                                .clear                  (clearac0BWDropTrigger),
                                .mask                   (maskac0BWDropTrigger),
                                .statusset              (statussetac0BWDropTrigger)//,
                                //.interruptOut           (maskedIntac0BWDropTrigger)
                                );
                
                endmodule