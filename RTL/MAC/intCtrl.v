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
// Description      : Top level of intCtrl module
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
// -------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////


module intCtrl( 

      //$port_g clocks and reset
      (* mark_debug = "true" *)input wire                         macPIClk                      ,// Platform clock                     
      input wire                         macPIClkHardRst_n             ,// Platfrom Reset
                                         
      //$port_g  REGISTERS INTERFACE
      //$port_g general interrupts enable
      (* mark_debug = "true" *)input wire                         masterGenIntEn                ,//General Interrupt master Enable
      
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
      input wire                         absGenTimers                  ,// set absTimer interruption              
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
      input wire                         maskabsGenTimers              ,// absTimer mask interruption    
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
      output wire                        statusabsGenTimers         ,//  All absTimer interruption status
      output wire [9:0]                  statussetabsTimers            ,//  absTimer interruption status
      output wire                        statussetidleInterrupt        ,//  idleInterrupt interruption status
      output wire                        statussetimpSecTBTT           ,//  impSecTBTT interruption status
      output wire                        statussetimpPriTBTT           ,//  impPriTBTT interruption status

      //$port_g general interrupts enable
      (* syn_keep = "true" , mark_debug = "true" *)input wire                         masterTxRxIntEn               ,// TxRx Interruption master enable

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
      input wire                         setac0ProtTrigger             ,//  set ac0ProtTrigger  
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
      input wire                         maskac0ProtTrigger            ,// ac0BWDropTrigger output interruption mask 
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
      input wire                         phyRxStart                    ,// phyRxStart internal interruption
      input wire                         phyErr                        ,// phyErr internal interruption
      input wire                         macPHYIFUnderRun              ,// macPHYIFUnderRun internal interruption
      input wire                         hwErr                         ,// hwErr internal interruption
      input wire                         impSecDTIM                    ,// impSecDTIM internal interruption
      input wire                         impPriDTIM                    ,// impPriDTIM internal interruption
      input wire                         bcnTxDMADead                  ,// bcnTxDMADead internal interruption
      input wire                         ac3TxDMADead                  ,// ac3TxDMADead internal interruption
      input wire                         ac2TxDMADead                  ,// ac2TxDMADead internal interruption
      input wire                         ac1TxDMADead                  ,// ac1TxDMADead internal interruption
      input wire                         ac0TxDMADead                  ,// ac0TxDMADead internal interruption
      input wire                         ptError                       ,// ptError internal interruption
      input wire                         timSet                        ,// timSet internal interruption
      input wire                         olbcDSSS                      ,// olbcDSSS internal interruption
      input wire                         olbcOFDM                      ,// olbcOFDM internal interruption
      input wire                         rxFIFOOverFlow                ,// rxFIFOOverFlow internal interruption
      input wire                         rxDMAEmpty                    ,// rxDMAEmpty internal interruption
      input wire                         macPHYIFOverflow              ,// macPHYIFOverflow internal interruption
      input wire                         rxPayloadDMADead              ,// rxPayloadDMADead internal interruption
      input wire                         rxHeaderDMADead               ,// rxHeaderDMADead internal interruption
      input wire [9:0]                   absTimers                     ,// absTimer internal interruption
      input wire                         idleInterrupt                 ,// idleInterrupt internal interruption
      input wire                         impSecTBTT                    ,// impSecTBTT internal interruption
      input wire                         impPriTBTT                    ,// impPriTBTT internal interruption
      input wire                         timerRxTrigger                ,// timerRxTrigger internal interruption
      input wire                         rxTrigger                     ,// rxTrigger internal interruption
      input wire                         counterRxTrigger              ,// counterRxTrigger internal interruption
      input wire                         baRxTrigger                   ,// baRxTrigger internal interruption
      input wire                         ac3TxBufTrigger               ,// ac3TxBufTrigger internal interruption
      input wire                         ac2TxBufTrigger               ,// ac2TxBufTrigger internal interruption
      input wire                         ac1TxBufTrigger               ,// ac1TxBufTrigger internal interruption
      input wire                         ac0TxBufTrigger               ,// ac0TxBufTrigger internal interruption
      input wire                         bcnTxBufTrigger               ,// bcnTxBufTrigger internal interruption
      input wire                         timerTxTrigger                ,// timerTxTrigger internal interruption
      input wire                         txopComplete                  ,// txopComplete internal interruption
      input wire                         rdTxTrigger                   ,// rdTxTrigger internal interruption
      input wire                         hccaTxTrigger                 ,// hccaTxTrigger internal interruption
      input wire                         ac3TxTrigger                  ,// ac3TxTrigger internal interruption
      input wire                         ac2TxTrigger                  ,// ac2TxTrigger internal interruption
      input wire                         ac1TxTrigger                  ,// ac1TxTrigger internal interruption
      input wire                         ac0TxTrigger                  ,// ac0TxTrigger internal interruption
      input wire                         bcnTxTrigger                  ,// bcnTxTrigger internal interruption
      input wire                         rdProtTrigger                 ,// rdProtTrigger internal interruption
      input wire                         hccaProtTrigger               ,// hccaProtTrigger internal interruption
      input wire                         ac3ProtTrigger                ,// ac3ProtTrigger internal interruption
      input wire                         ac2ProtTrigger                ,// ac2ProtTrigger internal interruption
      input wire                         ac1ProtTrigger                ,// ac1ProtTrigger internal interruption
      input wire                         ac0ProtTrigger                ,// ac0ProtTrigger internal interruption
      input wire                         ac3BWDropTrigger,              // ac3BWDropTrigger internal interruption
      input wire                         ac2BWDropTrigger,              // ac2BWDropTrigger internal interruption
      input wire                         ac1BWDropTrigger,              // ac1BWDropTrigger internal interruption
      input wire                         ac0BWDropTrigger,              // ac0BWDropTrigger internal interruption
      
      
      //$port_g Output interruptions
      (* syn_keep = "true" , mark_debug = "true" *)output wire                        intGen_n                      ,// Active low general interrupt signal.
      (* syn_keep = "true" , mark_debug = "true" *)output wire                        intProtTrigger_n              ,// Active low protocol event interrupt signal
      (* syn_keep = "true" , mark_debug = "true" *)output wire                        intTxTrigger_n                ,// Active low TX event interrupt signal
      (* syn_keep = "true" , mark_debug = "true" *)output wire                        intRxTrigger_n                ,// Active low Rx event interrupt signal
      (* syn_keep = "true" , mark_debug = "true" *)output wire                        intTxRxMisc_n                 ,// Active low Misc Tx/Rx event interrupt signal
      (* syn_keep = "true" , mark_debug = "true" *)output wire                        intTxRxTimer_n                 // Active low Timer Rx event interrupt signal


                 );


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
(* syn_keep = "true" , mark_debug = "true" *)wire oredInterruptGen;                                      // ored general interrupt line
(* syn_keep = "true" , mark_debug = "true" *)wire oredIntProtTrigger;                                    // ored protocol event interrupt line
(* syn_keep = "true" , mark_debug = "true" *)wire oredIntTxTrigger;                                      // ored TX event interrupt line
(* syn_keep = "true" , mark_debug = "true" *)wire oredIntRxTrigger;                                      // ored Rx event interrupt line
(* syn_keep = "true" , mark_debug = "true" *)wire oredIntTxRxMisc;                                       // ored Misc Tx/Rx event interrupt line
(* syn_keep = "true" , mark_debug = "true" *)wire oredIntTxRxTimer;                                      // ored Timer Tx/Rx event interrupt line

// interruption masked
//wire                         maskedIntphyRxStart           ;//  masked IntphyRxStart       
//wire                         maskedIntphyErr               ;//  masked IntphyErr           
//wire                         maskedIntmacPHYIFUnderRun     ;//  masked IntmacPHYIFUnderRun 
//wire                         maskedInthwErr                ;//  masked InthwErr            
//wire                         maskedIntimpSecDTIM           ;//  masked IntimpSecDTIM       
//wire                         maskedIntimpPriDTIM           ;//  masked IntimpPriDTIM       
//wire                         maskedIntbcnTxDMADead         ;//  masked IntbcnTxDMADead     
//wire                         maskedIntac3TxDMADead         ;//  masked Intac3TxDMADead     
//wire                         maskedIntac2TxDMADead         ;//  masked Intac2TxDMADead     
//wire                         maskedIntac1TxDMADead         ;//  masked Intac1TxDMADead     
//wire                         maskedIntac0TxDMADead         ;//  masked Intac0TxDMADead     
//wire                         maskedIntptError              ;//  masked IntptError          
//wire                         maskedInttimSet               ;//  masked InttimSet           
//wire                         maskedIntolbcDSSS             ;//  masked IntolbcDSSS         
//wire                         maskedIntolbcOFDM             ;//  masked IntolbcOFDM         
//wire                         maskedIntrxFIFOOverFlow       ;//  masked IntrxFIFOOverFlow   
//wire                         maskedIntrxDMAEmpty           ;//  masked IntrxDMAEmpty       
//wire                         maskedIntmacPHYIFOverflow     ;//  masked IntmacPHYIFOverflow       
//wire                         maskedIntrxPayloadDMADead     ;//  masked IntrxPayloadDMADead       
//wire                         maskedIntrxHeaderDMADead      ;//  masked IntrxHeaderDMADead       
//wire                         maskedIntabsTimer2            ;//  masked IntabsTimer2        
//wire                         maskedIntabsTimer1            ;//  masked IntabsTimer1        
//wire                         maskedIntidleInterrupt        ;//  masked IntidleInterrupt    
//wire                         maskedIntimpSecTBTT           ;//  masked IntimpSecTBTT       
//wire                         maskedIntimpPriTBTT           ;//  masked IntimpPriTBTT       
//wire                         maskedInttimerRxTrigger       ;//  masked InttimerRxTrigger   
//wire                         maskedIntrxTrigger            ;//  masked IntrxTrigger        
//wire                         maskedIntbaRxTrigger          ;//  masked IntbaRxTrigger        
//wire                         maskedInttimerTxTrigger       ;//  masked InttimerTxTrigger   
//wire                         maskedInttxopComplete         ;//  masked InttxopComplete     
//wire                         maskedIntrdTxTrigger          ;//  masked IntrdTxTrigger      
//wire                         maskedInthccaTxTrigger        ;//  masked InthccaTxTrigger    
//wire                         maskedIntac3TxTrigger         ;//  masked Intac3TxTrigger     
//wire                         maskedIntac2TxTrigger         ;//  masked Intac2TxTrigger     
//wire                         maskedIntac1TxTrigger         ;//  masked Intac1TxTrigger     
//wire                         maskedIntac0TxTrigger         ;//  masked Intac0TxTrigger     
//wire                         maskedIntbcnTxTrigger         ;//  masked IntbcnTxTrigger     
//wire                         maskedIntrdProtTrigger        ;//  masked IntrdProtTrigger    
//wire                         maskedInthccaProtTrigger      ;//  masked InthccaProtTrigger  
//wire                         maskedIntac3ProtTrigger       ;//  masked Intac3ProtTrigger   
//wire                         maskedIntac2ProtTrigger       ;//  masked Intac2ProtTrigger   
//wire                         maskedIntac1ProtTrigger       ;//  masked Intac1ProtTrigger   
//wire                         maskedIntac0ProtTrigger       ;//  masked Intac0ProtTrigger   

//resynched interruptions
                             
wire                         intphyRxStart                 ;// phyRxStart internal register
wire                         intphyErr                     ;// phyErr internal register
wire                         intmacPHYIFUnderRun           ;// macPHYIFUnderRun internal register
wire                         intmacPHYIFOverflow           ;// macPHYIFOverflow internal register
wire                         inthwErr                      ;// hwErr internal register
wire                         intimpSecDTIM                 ;// impSecDTIM internal register
wire                         intimpPriDTIM                 ;// impPriDTIM internal register
wire                         inttimSet                     ;// timSet internal register
wire                         intolbcDSSS                   ;// olbcDSSS internal register
wire                         intolbcOFDM                   ;// olbcOFDM internal register
wire                         intrxFIFOOverFlow             ;// rxFIFOOverFlow internal register
wire [9:0]                   intabsTimers                  ;// absTimer internal register
wire                         intidleInterrupt              ;// idleInterrupt internal register
wire                         intimpSecTBTT                 ;// impSecTBTT internal register
wire                         intimpPriTBTT                 ;// impPriTBTT internal register
wire                         inttimerRxTrigger             ;// timerRxTrigger internal register
wire                         intbaRxTrigger                ;// baRxTrigger internal register
wire                         inttimerTxTrigger             ;// timerTxTrigger internal register
wire                         inttxopComplete               ;// txopComplete internal register
wire                         intrdTxTrigger                ;// rdTxTrigger internal register
wire                         inthccaTxTrigger              ;// hccaTxTrigger internal register
wire                         intrdProtTrigger              ;// rdProtTrigger internal register
wire                         inthccaProtTrigger            ;// hccaProtTrigger internal register
wire                         intac3ProtTrigger             ;// ac3ProtTrigger internal register
wire                         intac2ProtTrigger             ;// ac2ProtTrigger internal register
wire                         intac1ProtTrigger             ;// ac1ProtTrigger internal register
wire                         intac0ProtTrigger             ;// ac0ProtTrigger internal register
wire                         intac3BWDropTrigger           ;// ac3BWDropTrigger internal register
wire                         intac2BWDropTrigger           ;// ac2BWDropTrigger internal register
wire                         intac1BWDropTrigger           ;// ac1BWDropTrigger internal register
wire                         intac0BWDropTrigger           ;// ac0BWDropTrigger internal register

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


// output interruptions
assign intGen_n  = (! (oredInterruptGen  && masterGenIntEn ));
assign intProtTrigger_n = (! (oredIntProtTrigger && masterTxRxIntEn));
assign intTxTrigger_n = (! (oredIntTxTrigger && masterTxRxIntEn));
assign intRxTrigger_n = (! (oredIntRxTrigger && masterTxRxIntEn));
assign intTxRxMisc_n = (! (oredIntTxRxMisc && masterTxRxIntEn));
assign intTxRxTimer_n = (! (oredIntTxRxTimer && masterTxRxIntEn));


// ORing interruptions

assign oredInterruptGen     =  statussetphyRxStart       ||
                               statussetphyErr           ||
                               statussetmacPHYIFUnderRun ||
                               statussethwErr            ||
                               statussetimpSecDTIM       ||
                               statussetimpPriDTIM       ||
                               statussetbcnTxDMADead     ||
                               statussetac3TxDMADead     ||
                               statussetac2TxDMADead     ||
                               statussetac1TxDMADead     ||
                               statussetac0TxDMADead     ||
                               statussetptError          ||
                               statussettimSet           ||
                               statussetolbcDSSS         ||
                               statussetolbcOFDM         ||
                               statussetrxFIFOOverFlow   ||
                               statussetrxDMAEmpty       ||
                               statussetmacPHYIFOverflow ||
                               statussetrxPayloadDMADead ||
                               statussetrxHeaderDMADead  ||
                               statusabsGenTimers        ||
                               statussetidleInterrupt    ||
                               statussetimpSecTBTT       ||
                               statussetimpPriTBTT;      


assign oredIntProtTrigger    = statussetrdProtTrigger    ||
                               statussethccaProtTrigger  ||
                               statussetac3ProtTrigger   ||
                               statussetac2ProtTrigger   ||
                               statussetac1ProtTrigger   ||
                               statussetac0ProtTrigger   ||
                               statussetac3BWDropTrigger ||
                               statussetac2BWDropTrigger ||
                               statussetac1BWDropTrigger ||
                               statussetac0BWDropTrigger;

assign oredIntTxTrigger      = statussetrdTxTrigger      ||
                               statussethccaTxTrigger    ||
                               statussetac3TxBufTrigger  ||
                               statussetac2TxBufTrigger  ||
                               statussetac1TxBufTrigger  ||
                               statussetac0TxBufTrigger  ||
                               statussetbcnTxBufTrigger  ||
                               statussetac3TxTrigger     ||
                               statussetac2TxTrigger     ||
                               statussetac1TxTrigger     ||
                               statussetac0TxTrigger     ||
                               statussetbcnTxTrigger;

assign oredIntRxTrigger      = statussetrxTrigger        ||
                               statussetbaRxTrigger      ||
                               statussetcounterRxTrigger;

assign oredIntTxRxMisc       = statussettxopComplete;

assign oredIntTxRxTimer      = statussettimerTxTrigger   ||
                               statussettimerRxTrigger;


assign statusabsGenTimers    = (statussetabsTimers != 10'b0) ? maskabsGenTimers : 1'b0;

// Instanciation of intCtrlRegisters
// Name of the instance : U_intCtrlRegisters
// Name of the file containing this module : intCtrlRegisters.v
intCtrlRegisters U_intCtrlRegisters (
		.macPIClk                         (macPIClk),
		.macPIClkHardRst_n                (macPIClkHardRst_n),
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
		.setrxPayloadDMADead              (setrxPayloadDMADead),
		.setrxHeaderDMADead               (setrxHeaderDMADead),
		.setabsTimers                     (setabsTimers),
		.setidleInterrupt                 (setidleInterrupt),
		.setimpSecTBTT                    (setimpSecTBTT),
		.setimpPriTBTT                    (setimpPriTBTT),
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
		.clearrxPayloadDMADead            (clearrxPayloadDMADead),
		.clearrxHeaderDMADead             (clearrxHeaderDMADead),
		.clearabsTimers                   (clearabsTimers),
		.clearidleInterrupt               (clearidleInterrupt),
		.clearimpSecTBTT                  (clearimpSecTBTT),
		.clearimpPriTBTT                  (clearimpPriTBTT),
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
		.maskrxPayloadDMADead             (maskrxPayloadDMADead),
		.maskrxHeaderDMADead              (maskrxHeaderDMADead),
    .maskabsTimers                    (maskabsTimers),
		.maskidleInterrupt                (maskidleInterrupt),
		.maskimpSecTBTT                   (maskimpSecTBTT),
		.maskimpPriTBTT                   (maskimpPriTBTT),
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
		.statussetrxPayloadDMADead        (statussetrxPayloadDMADead),
		.statussetrxHeaderDMADead         (statussetrxHeaderDMADead),
		.statussetabsTimers               (statussetabsTimers),
		.statussetidleInterrupt           (statussetidleInterrupt),
		.statussetimpSecTBTT              (statussetimpSecTBTT),
		.statussetimpPriTBTT              (statussetimpPriTBTT),
		.settimerRxTrigger                (settimerRxTrigger),
		.setrxTrigger                     (setrxTrigger),
		.setcounterRxTrigger              (setcounterRxTrigger),
		.setbaRxTrigger                   (setbaRxTrigger),
    .setac3TxBufTrigger               (setac3TxBufTrigger),
    .setac2TxBufTrigger               (setac2TxBufTrigger),
    .setac1TxBufTrigger               (setac1TxBufTrigger),
    .setac0TxBufTrigger               (setac0TxBufTrigger),
    .setbcnTxBufTrigger               (setbcnTxBufTrigger),
		.settimerTxTrigger                (settimerTxTrigger),
		.settxopComplete                  (settxopComplete),
		.setrdTxTrigger                   (setrdTxTrigger),
		.sethccaTxTrigger                 (sethccaTxTrigger),
		.setac3TxTrigger                  (setac3TxTrigger),
		.setac2TxTrigger                  (setac2TxTrigger),
		.setac1TxTrigger                  (setac1TxTrigger),
		.setac0TxTrigger                  (setac0TxTrigger),
		.setbcnTxTrigger                  (setbcnTxTrigger),
		.setrdProtTrigger                 (setrdProtTrigger),
		.sethccaProtTrigger               (sethccaProtTrigger),
		.setac3ProtTrigger                (setac3ProtTrigger),
		.setac2ProtTrigger                (setac2ProtTrigger),
		.setac1ProtTrigger                (setac1ProtTrigger),
		.setac0ProtTrigger                (setac0ProtTrigger),
    .setac3BWDropTrigger              (setac3BWDropTrigger),
    .setac2BWDropTrigger              (setac2BWDropTrigger),
    .setac1BWDropTrigger              (setac1BWDropTrigger),
    .setac0BWDropTrigger              (setac0BWDropTrigger),
		.cleartimerRxTrigger              (cleartimerRxTrigger),
		.clearrxTrigger                   (clearrxTrigger),
		.clearcounterRxTrigger            (clearcounterRxTrigger),
		.clearbaRxTrigger                 (clearbaRxTrigger),
    .clearac3TxBufTrigger             (clearac3TxBufTrigger),
    .clearac2TxBufTrigger             (clearac2TxBufTrigger),
    .clearac1TxBufTrigger             (clearac1TxBufTrigger),
    .clearac0TxBufTrigger             (clearac0TxBufTrigger),
    .clearbcnTxBufTrigger             (clearbcnTxBufTrigger),
		.cleartimerTxTrigger              (cleartimerTxTrigger),
		.cleartxopComplete                (cleartxopComplete),
		.clearrdTxTrigger                 (clearrdTxTrigger),
		.clearhccaTxTrigger               (clearhccaTxTrigger),
		.clearac3TxTrigger                (clearac3TxTrigger),
		.clearac2TxTrigger                (clearac2TxTrigger),
		.clearac1TxTrigger                (clearac1TxTrigger),
		.clearac0TxTrigger                (clearac0TxTrigger),
		.clearbcnTxTrigger                (clearbcnTxTrigger),
		.clearrdProtTrigger               (clearrdProtTrigger),
		.clearhccaProtTrigger             (clearhccaProtTrigger),
		.clearac3ProtTrigger              (clearac3ProtTrigger),
		.clearac2ProtTrigger              (clearac2ProtTrigger),
		.clearac1ProtTrigger              (clearac1ProtTrigger),
		.clearac0ProtTrigger              (clearac0ProtTrigger),
    .clearac3BWDropTrigger            (clearac3BWDropTrigger),
    .clearac2BWDropTrigger            (clearac2BWDropTrigger),
    .clearac1BWDropTrigger            (clearac1BWDropTrigger),
    .clearac0BWDropTrigger            (clearac0BWDropTrigger),
		.masktimerRxTrigger               (masktimerRxTrigger),
		.maskrxTrigger                    (maskrxTrigger),
		.maskcounterRxTrigger             (maskcounterRxTrigger),
		.maskbaRxTrigger                  (maskbaRxTrigger),
    .maskac3TxBufTrigger              (maskac3TxBufTrigger),
    .maskac2TxBufTrigger              (maskac2TxBufTrigger),
    .maskac1TxBufTrigger              (maskac1TxBufTrigger),
    .maskac0TxBufTrigger              (maskac0TxBufTrigger),
    .maskbcnTxBufTrigger              (maskbcnTxBufTrigger),
		.masktimerTxTrigger               (masktimerTxTrigger),
		.masktxopComplete                 (masktxopComplete),
		.maskrdTxTrigger                  (maskrdTxTrigger),
		.maskhccaTxTrigger                (maskhccaTxTrigger),
		.maskac3TxTrigger                 (maskac3TxTrigger),
		.maskac2TxTrigger                 (maskac2TxTrigger),
		.maskac1TxTrigger                 (maskac1TxTrigger),
		.maskac0TxTrigger                 (maskac0TxTrigger),
		.maskbcnTxTrigger                 (maskbcnTxTrigger),
		.maskrdProtTrigger                (maskrdProtTrigger),
		.maskhccaProtTrigger              (maskhccaProtTrigger),
		.maskac3ProtTrigger               (maskac3ProtTrigger),
		.maskac2ProtTrigger               (maskac2ProtTrigger),
		.maskac1ProtTrigger               (maskac1ProtTrigger),
		.maskac0ProtTrigger               (maskac0ProtTrigger),
    .maskac3BWDropTrigger             (maskac3BWDropTrigger),
    .maskac2BWDropTrigger             (maskac2BWDropTrigger),
    .maskac1BWDropTrigger             (maskac1BWDropTrigger),
    .maskac0BWDropTrigger             (maskac0BWDropTrigger),
		.statussettimerRxTrigger          (statussettimerRxTrigger),
		.statussetrxTrigger               (statussetrxTrigger),
		.statussetcounterRxTrigger        (statussetcounterRxTrigger),
		.statussetbaRxTrigger             (statussetbaRxTrigger),
    .statussetac3TxBufTrigger         (statussetac3TxBufTrigger),
    .statussetac2TxBufTrigger         (statussetac2TxBufTrigger),
    .statussetac1TxBufTrigger         (statussetac1TxBufTrigger),
    .statussetac0TxBufTrigger         (statussetac0TxBufTrigger),
    .statussetbcnTxBufTrigger         (statussetbcnTxBufTrigger),
		.statussettimerTxTrigger          (statussettimerTxTrigger),
		.statussettxopComplete            (statussettxopComplete),
		.statussetrdTxTrigger             (statussetrdTxTrigger),
		.statussethccaTxTrigger           (statussethccaTxTrigger),
		.statussetac3TxTrigger            (statussetac3TxTrigger),
		.statussetac2TxTrigger            (statussetac2TxTrigger),
		.statussetac1TxTrigger            (statussetac1TxTrigger),
		.statussetac0TxTrigger            (statussetac0TxTrigger),
		.statussetbcnTxTrigger            (statussetbcnTxTrigger),
		.statussetrdProtTrigger           (statussetrdProtTrigger),
		.statussethccaProtTrigger         (statussethccaProtTrigger),
		.statussetac3ProtTrigger          (statussetac3ProtTrigger),
		.statussetac2ProtTrigger          (statussetac2ProtTrigger),
		.statussetac1ProtTrigger          (statussetac1ProtTrigger),
		.statussetac0ProtTrigger          (statussetac0ProtTrigger),
    .statussetac3BWDropTrigger        (statussetac3BWDropTrigger),
    .statussetac2BWDropTrigger        (statussetac2BWDropTrigger),
    .statussetac1BWDropTrigger        (statussetac1BWDropTrigger),
    .statussetac0BWDropTrigger        (statussetac0BWDropTrigger),
		.intphyRxStart                    (intphyRxStart),
		.intphyErr                        (intphyErr),
		.intmacPHYIFUnderRun              (intmacPHYIFUnderRun),
		.inthwErr                         (inthwErr),
		.intimpSecDTIM                    (intimpSecDTIM),
		.intimpPriDTIM                    (intimpPriDTIM),
		.intbcnTxDMADead                  (bcnTxDMADead),
		.intac3TxDMADead                  (ac3TxDMADead),
		.intac2TxDMADead                  (ac2TxDMADead),
		.intac1TxDMADead                  (ac1TxDMADead),
		.intac0TxDMADead                  (ac0TxDMADead),
		.intptError                       (ptError),
		.inttimSet                        (inttimSet),
		.intolbcDSSS                      (intolbcDSSS),
		.intolbcOFDM                      (intolbcOFDM),
		.intrxFIFOOverFlow                (intrxFIFOOverFlow),
		.intrxDMAEmpty                    (rxDMAEmpty),
		.intmacPHYIFOverflow              (intmacPHYIFOverflow),
		.intrxPayloadDMADead              (rxPayloadDMADead),
		.intrxHeaderDMADead               (rxHeaderDMADead),
		.intabsTimers                     (intabsTimers),
		.intidleInterrupt                 (intidleInterrupt),
		.intimpSecTBTT                    (intimpSecTBTT),
		.intimpPriTBTT                    (intimpPriTBTT),
		.inttimerRxTrigger                (inttimerRxTrigger),
		.intrxTrigger                     (rxTrigger),
		.intcounterRxTrigger              (counterRxTrigger),
		.intbaRxTrigger                   (intbaRxTrigger),
    .intac3TxBufTrigger               (ac3TxBufTrigger),
    .intac2TxBufTrigger               (ac2TxBufTrigger),
    .intac1TxBufTrigger               (ac1TxBufTrigger),
    .intac0TxBufTrigger               (ac0TxBufTrigger),
    .intbcnTxBufTrigger               (bcnTxBufTrigger),
		.inttimerTxTrigger                (inttimerTxTrigger),
		.inttxopComplete                  (inttxopComplete),
		.intrdTxTrigger                   (intrdTxTrigger),
		.inthccaTxTrigger                 (inthccaTxTrigger),
		.intac3TxTrigger                  (ac3TxTrigger),
		.intac2TxTrigger                  (ac2TxTrigger),
		.intac1TxTrigger                  (ac1TxTrigger),
		.intac0TxTrigger                  (ac0TxTrigger),
		.intbcnTxTrigger                  (bcnTxTrigger),
		.intrdProtTrigger                 (intrdProtTrigger),
		.inthccaProtTrigger               (inthccaProtTrigger),
		.intac3ProtTrigger                (intac3ProtTrigger),
		.intac2ProtTrigger                (intac2ProtTrigger),
		.intac1ProtTrigger                (intac1ProtTrigger),
		.intac0ProtTrigger                (intac0ProtTrigger),
    .intac3BWDropTrigger                (intac3BWDropTrigger),
    .intac2BWDropTrigger                (intac2BWDropTrigger),
    .intac1BWDropTrigger                (intac1BWDropTrigger),
    .intac0BWDropTrigger                (intac0BWDropTrigger)//,
		//.maskedIntphyRxStart              (maskedIntphyRxStart),
		//.maskedIntphyErr                  (maskedIntphyErr),
		//.maskedIntmacPHYIFUnderRun        (maskedIntmacPHYIFUnderRun),
		//.maskedInthwErr                   (maskedInthwErr),
		//.maskedIntimpSecDTIM              (maskedIntimpSecDTIM),
		//.maskedIntimpPriDTIM              (maskedIntimpPriDTIM),
		//.maskedIntbcnTxDMADead            (maskedIntbcnTxDMADead),
		//.maskedIntac3TxDMADead            (maskedIntac3TxDMADead),
		//.maskedIntac2TxDMADead            (maskedIntac2TxDMADead),
		//.maskedIntac1TxDMADead            (maskedIntac1TxDMADead),
		//.maskedIntac0TxDMADead            (maskedIntac0TxDMADead),
		//.maskedIntptError                 (maskedIntptError),
		//.maskedInttimSet                  (maskedInttimSet),
		//.maskedIntolbcDSSS                (maskedIntolbcDSSS),
		//.maskedIntolbcOFDM                (maskedIntolbcOFDM),
		//.maskedIntrxFIFOOverFlow          (maskedIntrxFIFOOverFlow),
		//.maskedIntrxDMAEmpty              (maskedIntrxDMAEmpty),
		//.maskedIntmacPHYIFOverflow        (maskedIntmacPHYIFOverflow),
		//.maskedIntrxPayloadDMADead        (maskedIntrxPayloadDMADead),
		//.maskedIntrxHeaderDMADead         (maskedIntrxHeaderDMADead),
		//.maskedIntabsTimer2               (maskedIntabsTimer2),
		//.maskedIntabsTimer1               (maskedIntabsTimer1),
		//.maskedIntidleInterrupt           (maskedIntidleInterrupt),
		//.maskedIntimpSecTBTT              (maskedIntimpSecTBTT),
		//.maskedIntimpPriTBTT              (maskedIntimpPriTBTT),
		//.maskedInttimerRxTrigger          (maskedInttimerRxTrigger),
		//.maskedIntrxTrigger               (maskedIntrxTrigger),
		//.maskedIntbaRxTrigger             (maskedIntbaRxTrigger),
		//.maskedInttimerTxTrigger          (maskedInttimerTxTrigger),
		//.maskedInttxopComplete            (maskedInttxopComplete),
		//.maskedIntrdTxTrigger             (maskedIntrdTxTrigger),
		//.maskedInthccaTxTrigger           (maskedInthccaTxTrigger),
		//.maskedIntac3TxTrigger            (maskedIntac3TxTrigger),
		//.maskedIntac2TxTrigger            (maskedIntac2TxTrigger),
		//.maskedIntac1TxTrigger            (maskedIntac1TxTrigger),
		//.maskedIntac0TxTrigger            (maskedIntac0TxTrigger),
		//.maskedIntbcnTxTrigger            (maskedIntbcnTxTrigger),
		//.maskedIntrdProtTrigger           (maskedIntrdProtTrigger),
		//.maskedInthccaProtTrigger         (maskedInthccaProtTrigger),
		//.maskedIntac3ProtTrigger          (maskedIntac3ProtTrigger),
		//.maskedIntac2ProtTrigger          (maskedIntac2ProtTrigger),
		//.maskedIntac1ProtTrigger          (maskedIntac1ProtTrigger),
		//.maskedIntac0ProtTrigger          (maskedIntac0ProtTrigger)
		);


// Instanciation of intCtrlResync
// Name of the instance : U_intCtrlResync
// Name of the file containing this module : intCtrlResync.v
intCtrlResync U_intCtrlResync (
    .macPIClk                         (macPIClk),
    .macPIClkHardRst_n                (macPIClkHardRst_n),
    .phyRxStart                       (phyRxStart),
    .phyErr                           (phyErr),
    .macPHYIFUnderRun                 (macPHYIFUnderRun),
    .macPHYIFOverflow                 (macPHYIFOverflow),
    .hwErr                            (hwErr),
    .impSecDTIM                       (impSecDTIM),
    .impPriDTIM                       (impPriDTIM),
    .timSet                           (timSet),
    .olbcDSSS                         (olbcDSSS),
    .olbcOFDM                         (olbcOFDM),
    .rxFIFOOverFlow                   (rxFIFOOverFlow),
    .absTimers                        (absTimers),
    .idleInterrupt                    (idleInterrupt),
    .impSecTBTT                       (impSecTBTT),
    .impPriTBTT                       (impPriTBTT),
    .timerRxTrigger                   (timerRxTrigger),
    .baRxTrigger                      (baRxTrigger),
    .timerTxTrigger                   (timerTxTrigger),
    .txopComplete                     (txopComplete),
    .rdTxTrigger                      (rdTxTrigger),
    .hccaTxTrigger                    (hccaTxTrigger),
    .rdProtTrigger                    (rdProtTrigger),
    .hccaProtTrigger                  (hccaProtTrigger),
    .ac3ProtTrigger                   (ac3ProtTrigger),
    .ac2ProtTrigger                   (ac2ProtTrigger),
    .ac1ProtTrigger                   (ac1ProtTrigger),
    .ac0ProtTrigger                   (ac0ProtTrigger),
    .ac3BWDropTrigger                 (ac3BWDropTrigger),
    .ac2BWDropTrigger                 (ac2BWDropTrigger),
    .ac1BWDropTrigger                 (ac1BWDropTrigger),
    .ac0BWDropTrigger                 (ac0BWDropTrigger),
    .intphyRxStart                    (intphyRxStart),
    .intphyErr                        (intphyErr),
    .intmacPHYIFUnderRun              (intmacPHYIFUnderRun),
    .intmacPHYIFOverflow              (intmacPHYIFOverflow),
    .inthwErr                         (inthwErr),
    .intimpSecDTIM                    (intimpSecDTIM),
    .intimpPriDTIM                    (intimpPriDTIM),
    .inttimSet                        (inttimSet),
    .intolbcDSSS                      (intolbcDSSS),
    .intolbcOFDM                      (intolbcOFDM),
    .intrxFIFOOverFlow                (intrxFIFOOverFlow),
    .intabsTimers                     (intabsTimers),
    .intidleInterrupt                 (intidleInterrupt),
    .intimpSecTBTT                    (intimpSecTBTT),
    .intimpPriTBTT                    (intimpPriTBTT),
    .inttimerRxTrigger                (inttimerRxTrigger),
    .intbaRxTrigger                   (intbaRxTrigger),
    .inttimerTxTrigger                (inttimerTxTrigger),
    .inttxopComplete                  (inttxopComplete),
    .intrdTxTrigger                   (intrdTxTrigger),
    .inthccaTxTrigger                 (inthccaTxTrigger),
    .intrdProtTrigger                 (intrdProtTrigger),
    .inthccaProtTrigger               (inthccaProtTrigger),
    .intac3ProtTrigger                (intac3ProtTrigger),
    .intac2ProtTrigger                (intac2ProtTrigger),
    .intac1ProtTrigger                (intac1ProtTrigger),
    .intac0ProtTrigger                (intac0ProtTrigger),
    .intac3BWDropTrigger              (intac3BWDropTrigger),
    .intac2BWDropTrigger              (intac2BWDropTrigger),
    .intac1BWDropTrigger              (intac1BWDropTrigger),
    .intac0BWDropTrigger              (intac0BWDropTrigger)
    );
    
    endmodule
                     