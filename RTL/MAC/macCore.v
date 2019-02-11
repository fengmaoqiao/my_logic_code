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
`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"

module macCore(
  ///////////////////////////////////////////////
  //$port_g Resets
  ///////////////////////////////////////////////
  input  wire                            macPIClkHardRst_n,          // Active low hard reset signal synchronized to the macPIClk.
  input  wire                            macCoreClkHardRst_n,        // Active low hard reset signal synchronized to the macCoreClk.
  input  wire                            macWTClkHardRst_n,          // Active low hard reset signal synchronized to the macWTClk.
  input  wire                            mpIFClkHardRst_n,           // Active low hard reset signal synchronized to the mpIFClk. 
  input  wire                            macPIClkSoftRst_n,          // Active low soft reset signal synchronized to the macPIClk.
  input  wire                            macCoreClkSoftRst_n,        // Active low soft reset signal synchronized to the macCoreClk.
  input  wire                            macWTClkSoftRst_n,          // Active low soft reset signal synchronized to the macWTClk.

  ///////////////////////////////////////////////
  //$port_g Clocks
  ///////////////////////////////////////////////
  input  wire                            macPISlaveClk,              // Primary MAC Platform Interface Clock for TX
  input  wire                            macPIClk,                   // Primary MAC Platform Interface Clock for TX
  input  wire                            macPITxClk,                 // Secondary MAC Platform Interface Clock for TX
  input  wire                            macCoreClk,                 // Primary MAC Core Clock
  input  wire                            macCoreTxClk,               // Secondary MAC Core Clock for TX
  input  wire                            macCoreRxClk,               // Secondary MAC Core Clock for RX
  input  wire                            macLPClk,                   // MAC Low Power clock. 
  input  wire                            macWTClk,                   // Clock input for WEP/TKIP blocks.
  input  wire                            macCryptClk,                // Clock input for Crypto Engine blocks.

  ///////////////////////////////////////////////
  //$port_g Clock Enables
  ///////////////////////////////////////////////
  output wire                            macPriClkEn,                // Clock Enable for macPriClk Clocks
  output wire                            macSecClkEn,                // Clock Enable for Secondary Clocks
  output wire                            platformWakeUp,             // Wake Up platform
  output wire                            macCoreTxClkEn,             // Clock Enable for macCoreTxClk Clock
  output reg                             macCoreRxClkEn,             // Clock Enable for macCoreRxClk Clock
  output wire                            macLPClkSwitch,             // Switch MAC Lower Clock.
  output wire                            macWTClkEn,                 // Clock Enable for macWTClk Clock
  output wire                            macCryptClkEn,              // Clock Enable for macCryptClk Clock
  output wire                            mpIFClkEn,                  // Clock Enable for mpIFClk Clock

  ///////////////////////////////////////////////
  //$port_g Interrupt controller interface
  ///////////////////////////////////////////////
  output wire                            txopComplete,               // Indicates the completion of a TXOP
  output wire                            ac3ProtTrigger,             // protocol trigger interruption 
  output wire                            ac2ProtTrigger,             // protocol trigger interruption 
  output wire                            ac1ProtTrigger,             // protocol trigger interruption 
  output wire                            ac0ProtTrigger,             // protocol trigger interruption 
  output wire                            ac3BWDropTrigger,           // BW drop with AMPDU length change 
  output wire                            ac2BWDropTrigger,           // BW drop with AMPDU length change 
  output wire                            ac1BWDropTrigger,           // BW drop with AMPDU length change 
  output wire                            ac0BWDropTrigger,           // BW drop with AMPDU length change 
  output wire                            olbcOFDM,                   // OFDM OLBC
  output wire                            olbcDSSS,                   // DSSS OLBC
  output wire                            impPriTBTT,                 // Impending Primary TBTT
  output wire                            impSecTBTT,                 // Impending Secondary TBTT
  output wire                            impPriDTIM,                 // Impending Primary DTIM
  output wire                            impSecDTIM,                 // Impending Secondary DTIM
  output wire                            timerTxTrigger,             // Tx trigger
  output wire                            timerRxTrigger,             // Rx trigger
  output wire                            idleInterrupt,              // Indicates that the Core has moved to IDLE state
  output wire                            rxFIFOOverFlow,             // RX FIFO overflow
  output wire                            baRxTrigger,                // Block-ACK Receive interrupt
  output wire [9:0]                      absTimers,                  // absTimers interruption


  ///////////////////////////////////////////////
  //$port_g HW Error detected
  ///////////////////////////////////////////////
  input wire                             hwErr,                      // HW error detected
  input wire                             softReset,                  // Software Reset


  ///////////////////////////////////////////////
  //$port_g txCtrlReg Interface with the DMA Engine
  ///////////////////////////////////////////////
  input wire                             txCtrlRegWr,                // TX parameter Cache module signals                 
                                                                     // Write signal to the Tx Parameter Cache.           
  input wire                      [31:0] txCtrlRegData,              // TX parameter Cache module signals                 
                                                                     // Write signal to the Tx Parameter Cache.           
  input wire                             txCtrlRegPT,                // Indicates currently Policy table information is   
                                                                     // being passed.                                     
  input wire                             txCtrlRegHD,                // Indicates currently Header descriptor information 
                                                                     // is being passed.                                  
  input wire                             discardPrevHD_p,            // Signal to TX Parameter Cache module.              
                                                                     // Indicates to discard the recently                 
                                                                     // fetch Header Descriptor.                          
  output wire                            txCtrlRegBusy,              // Indicates there are 2 sets of parameters          
                                                                     // already in the tx Parameter Cache module          
                                                                     // and not to fetch more.                            

  ///////////////////////////////////////////////
  //$port_g rx Controller Interface with the DMA Engine
  ///////////////////////////////////////////////
  input  wire                            rxFrmDiscard,               // Discard current frame 
  input  wire                            rxDescAvailable,            // Indicate that the DMA has all the needed desc for the current rxFrame
  
  ///////////////////////////////////////////////
  //$port_g MAC Controller Interface with the DMA Engine
  ///////////////////////////////////////////////
  input  wire                            statusUpdated_p,            // Indication from the DMA that status have been updated.
  input  wire                      [3:0] txAC0StateMC,               // DMA state for AC0 channel. Registers will be updated with
                                                                     // this information
  input  wire                      [3:0] txAC1StateMC,               // DMA state for AC1 channel. Registers will be updated with
                                                                     // this information
  input  wire                      [3:0] txAC2StateMC,               // DMA state for AC2 channel. Registers will be updated with
                                                                     // this information
  input  wire                      [3:0] txAC3StateMC,               // DMA state for AC3 channel. Registers will be updated with
                                                                     // this information
  input  wire                      [3:0] txBcnStateMC,               // DMA state for Beacon channel. Registers will be updated with
                                                                     // this information
  output wire                            trigTxAC0,                  // Trigger from the MAC Controller to indicate DMA to 
                                                                     // start fetching frames associated with AC0
  output wire                            trigTxAC1,                  // Trigger from the MAC Controller to indicate DMA to
                                                                     // start fetching frames associated with AC1
  output wire                            trigTxAC2,                  // Trigger from the MAC Controller to indicate DMA to 
                                                                     // start fetching frames associated with AC2
  output wire                            trigTxAC3,                  // Trigger from the MAC Controller to indicate DMA to
                                                                     // start fetching frames associated with AC3
  output wire                            trigTxBcn,                  // Trigger from the MAC Controller to indicate DMA to 
                                                                     // start fetching frames associated with Beacon
  output wire                            frameRxed_p,                // MAC Controller indicates a frame is successfully
                                                                     // received
  output wire                            updateDMAStatus_p,          // trigs the DMA Status update.
  output wire                            swRTS_p,                    // Asserted high if the current transmitted packet is a
                                                                     // RTS frame prepared by SW
  output wire                            txMpduDone_p,               // Asserted high after every transmission of MPDU in an 
                                                                     // AMPDU frame
  output wire                            ampduFrm_p,                 // Asserted high if the transmitted packet was an AMPDU
                                                                     // frame
  output wire                            retryFrame_p,               // If the transmitted frame has to be retried then this
                                                                     // signal is asserted.
  output wire                            mpduSuccess_p,              // If the transmitted frame was successful. Not asserted
                                                                     // for RTS frames
  output wire                            mpduFailed_p,               // If the transmitted frame was not successful. Not asserted
                                                                     // if the RTS frame failed
  output wire                            rtsFailed_p,                // If the transmitted frame was a RTS frame and did not 
                                                                     // receive a CTS frame within the CTS timeout
  output wire                            rtsSuccess_p,               // If the transmitted frame was a RTS frame and successfully
                                                                     // received a CTS in reponse.
  output wire                            retryLimitReached_p,        // If the transmitted frame was not successful and has reached  
                                                                     // the retry limit.Is asserted for both RTS and other MPDU's    
  output wire                     [ 1:0] transmissionBW,             // Indicates whether the frame was transmitted with 20MHz, 40Mhz, 80Mhz or 160Mhz BW
  output wire                     [ 7:0] numMPDURetries,             // Indicates the number of retries for this MPDU. Valid when 
                                                                     // rtsFailed_p rtsSuccess_p mpduSuccess_p mpduFailed_p or 
                                                                     // retryLimitReached 
  output wire                     [ 7:0] numRTSRetries,              // Indicates the number of retries for this RTS. Valid when 
                                                                     // rtsFailed_p rtsSuccess_p mpduSuccess_p mpduFailed_p or 
                                                                     // retryLimitReached 
  output wire                     [31:0] mediumTimeUsed,             // Indicates the medium Time Used for current transmission
                                                                     // Valid when DMA status is being updated
  output wire                     [ 3:0] whichDescriptorSW,          // Indicates the value of the partAMorMSDU field Controller



  ///////////////////////////////////////////////
  //$port_g MAC Timer Unit with the DMA Engine
  ///////////////////////////////////////////////
  input  wire                            rxTrig_p,                   // RX trigger

  ///////////////////////////////////////////////
  //$port_g TX FIFO interface
  ///////////////////////////////////////////////
  input  wire                     [ 1:0] txFIFOMPDUDelimiters,       // MPDU delimiters from TX FIFO
  input  wire                     [ 7:0] txFIFORdData,               // Read Data from TX FIFO
  input  wire                            txFIFOEmpty,                // Indicates that the TX FIFO is empty
  input  wire                            txFIFODataValid,            // Indicates when the txFIFORdData is Valid
  output wire                            txFIFORdFlush,              // Request from MAC Core Clock domain to flush the FIFO
  output wire                            txFIFORead,                 // Request a new byte from the TX FIFO
  output wire                            txFIFOReadByFour,           // Read data by four bytes
  output wire                            txFIFOReadByTwo,            // Read data by two bytes

  ///////////////////////////////////////////////
  //$port_g RX FIFO
  ///////////////////////////////////////////////
  input wire                             rxFIFOAlmostFull,           // RX FIFO is almost full
  input wire                             rxFIFOEmptyWrClk,           // RX FIFO is empty
  input wire                             rxFIFOFull,                 // RX FIFO is full
  
  output wire                     [ 3:0] rxFIFOWrTag,                // RX FIFO write tag
  output wire                     [31:0] rxFIFOWrData,               // RX FIFO write data
  output wire                            rxFIFOWrite,                // RX FIFO write enable
  
  ///////////////////////////////////////////////
  //$port_g Mac Controller Interface with the MAC-PHY IF
  ///////////////////////////////////////////////
  input  wire                            macPhyIfRxStart_p,          // Start of reception pulse
  input  wire                            macPhyIfRxFlush_p,          // Rx flush pulse
  output wire                            startRx,                    // Start Rx trigger      
  output wire                            stopRx_p,                   // Stop Rx trigger       
  output wire                            mpifKeepRFon,               // Keep RF On            
                                                                                              
  ///////////////////////////////////////////////
  //$port_g Tx Controller Interface with the MAC-PHY IF                                                            
  ///////////////////////////////////////////////
  output wire                            startTx_p,                  // Start Tx trigger                
  output wire                            stopTx_p,                   // Stop Tx trigger                 
  output wire                     [ 7:0] mpIfTxFifoData,             // Data to transmit                
  output wire                            mpIfTxFifoWrite,            // Data valid                      
                                    
  output wire                     [ 7:0] txPwrLevel,                // Transmit Power Level             
  output wire                     [ 1:0] chBW,                      // TX Vector Channel Bandwidth             
  output wire                     [ 1:0] chOffset,                  // TX Vector transmit vector field              
  output wire                            smoothing,                 // TX Vector Smoothing recommended            
  output wire                     [ 7:0] antennaSet,                // TX Vector Antenna Set           
  output wire                     [ 7:0] smmIndex,                  // TX Vector Spatial Map Matrix Index           
  output wire                     [ 6:0] mcs,                       // TX Vector Modulation Coding Scheme           
  output wire                            preType,                   // TX Vector Preamble Type         
  output wire                     [ 2:0] formatMod,                 // TX Vector Format and Modulation           
  output wire                     [ 1:0] numExtnSS,                 // TX Vector Number of Extension Spatial Streams              
  output wire                     [ 1:0] stbc,                      // TX Vector Space Time Block Coding           
  output wire                            fecCoding,                 // TX Vector FEC Coding             
  output wire                            sounding,                  // TX Vector Indicates whether this PPDU is Sounding        
  output wire                     [11:0] legLength,                 // TX Vector Legacy Length of the PPDU            
  output wire                     [ 3:0] legRate,                   // TX Vector Legacy Rate of the PPDU               
  output wire                     [15:0] service,                   // TX Vector Service              
  output wire                     [19:0] htLength,                  // TX Vector Length of the HT and VHT PPDU              
  output wire                     [ 2:0] nTx,                       // TX Vector Number of Transmit Chains.      
  output wire                     [ 2:0] nSTS,                      // TX Vector Indicates the number of space-time streams.
  output wire                            shortGI,                   // TX Vector Short Guard Interval              
  output wire                            aggreation,                // TX Vector MPDU Aggregate
  output wire                            beamFormed,                // TX Vector BeamFormed
  output wire                            disambiguityBit,           // TX Vector Disambiguity
  output wire                     [8:0]  partialAID,                // TX Vector partial AID
  output wire                     [5:0]  groupID,                   // TX Vector group ID
  output wire                            dozeNotAllowed,            // TX Vector TXOP PS Not Allowed
  output wire                            continuousTx,              // Enable continuous transmit 

  input  wire                            mpIfTxFifoFull,             // FIFO status                     
  input  wire                            mpIfTxErr_p,                // Transmit error                  
  input  wire                            mpIfTxEn,                   // Transmit Enable                 

  ///////////////////////////////////////////////
  //$port_g Rx Controller Interface with the MAC-PHY IF                                                              
  ///////////////////////////////////////////////
  input  wire                            macPhyTxEnd_p,              // Transmit End                    
  output wire                            macPhyIfRxFifoReadEn,       // FIFO read enable from the Rx controller                       
  input  wire                            macPhyIfRxFifoEmpty,        // FIFO empty signal                             
  input  wire                     [ 7:0] macPhyIfRxFifoData,         // FIFO data                                     
  input  wire                            macPhyIfRxErr_p,            // abort pulse                                   
  input  wire                            macPhyIfRxEnd_p,            // end of reception pulse                         
  input  wire                            macPhyIfRxEndForTiming_p,   // end of reception at the antenna                        
  input  wire                            macPhyIfRifsRxDetected,     // RIFS detected indication                      
  input  wire                            macPhyIfRxCca,              // CCA trigger                                   
  input  wire                            macPhyIfRxCcaSec20,         // CCA trigger Secondary 20MHz                                  
  input  wire                            macPhyIfRxCcaSec40,         // CCA trigger Secondary 40MHz                                  
  input  wire                            macPhyIfRxCcaSec80,         // CCA trigger Secondary 80MHz                            
  input  wire                            macPHYIFUnderRun,           // UnderRun Indication
  input  wire                            macPHYIFOverflow,           // Overflow Indication
  
  ///////////////////////////////////////////////
  //$port_g Doze controller
  ///////////////////////////////////////////////
  input  wire                            absGenTimersInt,            // Absolute Timer Interrupt
  output wire                            timWakeUp,                  // AP has data -> wake-up
  output wire                            timSleep,                   // AP has no data -> sleep

  ///////////////////////////////////////////////
  //$port_g Coex Interface
  ///////////////////////////////////////////////
`ifdef RW_WLAN_COEX_EN                
  input  wire                            coexEnable,            // Enable Coex Feature
  input  wire [3:0]                      coexPTIBKData,         // PTI default value for Data frame transmitted on BK AC
  input  wire [3:0]                      coexPTIBEData,         // PTI default value for Data frame transmitted on BE AC
  input  wire [3:0]                      coexPTIVIData,         // PTI default value for Data frame transmitted on VI AC
  input  wire [3:0]                      coexPTIVOData,         // PTI default value for Data frame transmitted on VO AC
  input  wire [3:0]                      coexPTIBcnData,        // PTI default value for Data frame transmitted on Beacon AC
  input  wire [3:0]                      coexPTIMgt,            // PTI default value for Management frame
  input  wire [3:0]                      coexPTICntl,           // PTI default value for Control frames other than ACK and BA
  input  wire [3:0]                      coexPTIAck,            // PTI default value for ACK and BA
  output wire                            coexWlanTx,            // Indicates that a WLAN Transmission is on-going
  output wire                            coexWlanRx,            // Indicates that a WLAN Reception is on-going
  input  wire                            coexWlanTxAbort,       // Requests from external arbiter abort all on-going transmission 
  output wire [3:0]                      coexWlanPTI,           // Indicates the priority of the on-going traffic
  output wire                            coexWlanPTIToggle,     // Indicates a new priority value
  output wire                            coexWlanChanBw,        // Indicates the BW of the on-going traffic
`endif // RW_WLAN_COEX_EN                

`ifdef RW_MAC_MIBCNTL_EN
  ///////////////////////////////////////////////
  //$port_g Host Interface
  ///////////////////////////////////////////////
  input  wire  [`RW_MIB_ADDR_WIDTH-1 :0] mibAddr,                    // Address From Host
  input  wire                            mibRd,                      // Rd Enable signal from host
  output wire  [`RW_MIB_DATA_WIDTH-1 :0] mibRdData,                  // Read Data forwarded to Host
  output wire                            mibBusy,                    // Output MIB busy indication to host

  ///////////////////////////////////////////////
  //$port_g MIB Ram
  ///////////////////////////////////////////////
  output wire                            mibTableEn,                 // Chip Select to RAM
  output wire  [`RW_MIB_ADDR_WIDTH-1 :0] mibTableAddr,               // RAM Address where either read or write has to be made Wr enable to RAM
  output wire                            mibTableWriteEn,            // Wr enable to RAM
  output wire  [`RW_MIB_DATA_WIDTH-1 :0] mibTableWriteData,          // Write Data to RAM during write operation
  
  input wire   [`RW_MIB_DATA_WIDTH-1 :0] mibTableReadData,           // Read Data from RAM
`endif // RW_MAC_MIBCNTL_EN
  
  ///////////////////////////////////////////////
  //$port_g PS BITMAP RAM 8*32 Single Port SRAM
  ///////////////////////////////////////////////                    
  output wire                            psBitmapEn,                 // Partial State Bitmap Enable. 
                                                                     // This signal is asserted for both read and write operations to the Partial State Bitmap.
  output wire                            psBitmapWriteEn,            // Partial State Bitmap Write Enable.
                                                                     // This signal is asserted for write operations to the Partial State Bitmap.
  output wire                     [ 1:0] psBitmapAddr,               // Partial State Bitmap Address bus.
  input  wire                     [87:0] psBitmapReadData,           // Partial State Bitmap Read Data bus.
  output wire                     [87:0] psBitmapWriteData,          // Partial State Bitmap Write Data bus.

  ///////////////////////////////////////////////
  //$port_g Key Storage RAM 64*186 Single Port SRAM 
  ///////////////////////////////////////////////
  output wire                            keyStorageEn,               // Enable Key Storage RAM
                                                                     // This signal is asserted for both read and write operations to the Key Storage RAM
  output wire                            keyStorageWriteEn,          // Write Enable Key Storage RAM
                                                                     // This signal is asserted for write operations to the Key Storage RAM
  output wire     [`KEY_INDEX_WIDTH-1:0] keyStorageAddr,             // Key Storage RAM write data bus
`ifdef RW_WAPI_EN
  input  wire                    [314:0] keyStorageReadData,         // Key Storage RAM read data bus
  output wire                    [314:0] keyStorageWriteData,        // Key Storage RAM address bus
`else
  input  wire                    [186:0] keyStorageReadData,         // Key Storage RAM read data bus
  output wire                    [186:0] keyStorageWriteData,        // Key Storage RAM address bus
`endif // RW_WAPI_EN

  ///////////////////////////////////////////////
  //$port_g DPRAM Interface [s-Box for WEP-TKIP engine]
  ///////////////////////////////////////////////
  input  wire                      [7:0] sBoxAReadData,              // SBox RAM port A read data bus
  input  wire                      [7:0] sBoxBReadData,              // SBox RAM port B read data bus
  output wire                      [7:0] sBoxAAddr,                  // SBox RAM port A address bus
  output wire                      [7:0] sBoxBAddr,                  // SBox RAM port B address bus
  output wire                      [7:0] sBoxAWriteData,             // SBox RAM port A write data bus
  output wire                      [7:0] sBoxBWriteData,             // SBox RAM port B write data bus
  output wire                            sBoxAWriteEn,               // Write Enable SBox RAM port A
  output wire                            sBoxBWriteEn,               // Write Enable SBox RAM port B
  output wire                            sBoxAEn,                    // Enable SBox RAM port A
  output wire                            sBoxBEn,                    // Enable SBox RAM port B

  ///////////////////////////////////////////////
  //$port_g DPRAM Interface [Encryption Buffer]
  ///////////////////////////////////////////////
  input  wire [7:0]                       encrRxFIFOReadData,        // Encryption Receive FIFO Read Data bus
  output wire                             encrRxFIFOWriteEn,         // Encryption Receive FIFO Write Enable
  output wire [`RX_BUFFER_ADDR_WIDTH-1:0] encrRxFIFOWriteAddr,       // Encryption Receive write address 
  output wire [7:0]                       encrRxFIFOWriteData,       // Encryption Receive write data bus
  output wire                             encrRxFIFOReadEn,          // Read enable signal for Encr Buffer
  output wire [`RX_BUFFER_ADDR_WIDTH-1:0] encrRxFIFOReadAddr,        // Encryption Receive FIFO read address
  
  ///////////////////////////////////////////////
  //$port_g Control and Status Register
  ///////////////////////////////////////////////
  input  wire                     [25:0] navCounter,                 // counter value from registers
  output wire                     [25:0] navCounterIn,               // counter value to registers
  output wire                            navCounterInValid,          // counter value to registers

  output wire                     [ 3:0] currentState,               // Indicates the current state of the Core. The state encoding is as follows:
                                                                     // 0000 - IDLE state. This is the default state.
                                                                     // 0010 - DOZE state
                                                                     // 0011 - ACTIVE state
                                                                     // 0100 to 1111  - reserved
  input  wire                     [ 3:0] nextState,                  // Indicates the next state of the Core
  input  wire                            latchNextState_p,           // Indicates next state register has been updated 
  output wire                     [ 3:0] nextStateIn,                // When the current state goes back to IDLE, the nextState is also set to IDLE
  output wire                            nextStateInValid,           // Indicates that the nextStateIn value can be capture.

  input  wire                            wakeUpSW,                   // Wake Up SW
  input  wire                            wakeUpFromDoze,             // Wake Up From Doze
  input  wire                            enableLPClkSwitch,          // Enable the switch to LP clock in DOZE  
  input  wire                            activeClkGating,            // Active Clock Gating This bit is set by SW to turn on 
                                                                     // active clock gating in HW. When reset, the HW does not 
                                                                     // perform active clock gating, i.e. does not turn off 
                                                                     // clocks to save power in ACTIVE state.
  input  wire                            disableACKResp,             // Disable ACK Response This bit is set by SW to disable 
                                                                     // the automatic ACK generation logic in HW.
  input  wire                            disableCTSResp,             // Disable CTS Response This bit is set by SW to disable 
                                                                     // the automatic CTS generation logic in HW.
  input  wire                            disableBAResp,              // Disable BA Response This bit is set by SW to disable 
                                                                     // the automatic BA generation logic in HW.


  input  wire                     [47:0] macAddr,                    // MAC Addr
  input  wire                     [47:0] macAddrMask,                // MAC Addr mask
  
  input  wire                     [47:0] bssID,                      // BSSID
  input  wire                     [47:0] bssIDMask,                  // BSSID Mask
  
  input  wire                            excUnencrypted,             // Exclude unencrypted frames
  input  wire                            dontDecrypt,                // Don't decrypt frames
  input  wire                            acceptMulticast,            // Accept Multicast frames
  input  wire                            acceptBroadcast,            // Accept Broadcast frames
  input  wire                            acceptOtherBSSID,           // Accept other BSSID frames
  input  wire                            acceptErrorFrames,          // Accept error frames
  input  wire                            acceptUnicast,              // Accept Unicast frames
  input  wire                            acceptMyUnicast,            // Accept frames directed to this device
  input  wire                            acceptProbeReq,             // Accept Probe Request frames
  input  wire                            acceptProbeResp,            // Accept Probe Response frames
  input  wire                            acceptBeacon,               // Accept Beacon frames
  input  wire                            acceptAllBeacon,            // Accept all Beacon 
  input  wire                            acceptOtherMgmtFrames,      // Accept other management frames
  input  wire                            acceptBAR,                  // Accept Block Ack Request frames
  input  wire                            acceptBA,                   // Accept Block Ack frames
  input  wire                            acceptDecryptErrorFrames,   // Accept frames which failed decryption
  input  wire                            acceptNotExpectedBA,        // Accept Block Ack Request frames received after SIFS
  input  wire                            acceptPSPoll,               // Accept PS-Poll frames
  input  wire                            acceptRTS,                  // Accept RTS frames
  input  wire                            acceptCTS,                  // Accept CTS frames
  input  wire                            acceptACK,                  // Accept ACK frames
  input  wire                            acceptCFEnd,                // Accept CF-End frames
  input  wire                            acceptOtherCntrlFrames,     // Accept other control frames
  input  wire                            acceptData,                 // Accept Data frames
  input  wire                            acceptCFWOData,             // Accept CF WithOut Data frames
  input  wire                            acceptQData,                // Accept QoS Data frames
  input  wire                            acceptQCFWOData,            // Accept QoS CF WithOut Data frames
  input  wire                            acceptQoSNull,              // Accept QoS Null frames
  input  wire                            acceptOtherDataFrames,      // Accept other Data frames
  input  wire                            acceptUnknown,              // Accept unknown frames

  input  wire                            hwFSMResetPIClk,            // HW FSM Reset
  input  wire                            hwFSMResetWTClk,            // HW FSM Reset
  input  wire                            hwFSMResetCoreClk,          // HW FSM Reset
  input  wire                            baPSBitmapReset,            // Partial state bitmap Reset
  output wire                            baPSBitmapResetIn,          // baPSBitmapResetIn
  output wire                            baPSBitmapResetInValid,     // Clear the baPSBitmapReset bit
  input  wire                            encrRxFIFOReset,            // Encryption RX FIFO Reset
  output wire                            encrRxFIFOResetIn,          // encrRxFIFOResetIn
  output wire                            encrRxFIFOResetInValid,     // Clear the encrRxFIFOReset bit
  input  wire                            mibTableReset,              // mibTableReset from host indicating of mibTableReset bit in macCntrl1Reg
  output wire                            mibTableResetIn,            // mibTableResetIn  
  output wire                            mibTableResetInValid,       // Clear the mibTableReset bit
  input  wire                      [9:0] mibTableIndex,              // MIB Table Index in the MIB Table that needs to be updated.
  input  wire                            mibIncrementMode,           // MIB Increment Mode
                                                                     //   When set, the contents of the MIB entry pointed to 
                                                                     //   by the mibTableIndex are incremented by the mibValue.
                                                                     //   When reset, the contents of the MIB entry pointed to 
                                                                     //   by the mibTableIndex are overwritten by the mibValue.
  
  input  wire [15:0]                     mibValue,                   // MIB Value
  input  wire                            mibWrite,                   // MIB Write
  output wire                            mibWriteInValid,            // Clear the mibWrite bit
  output wire                            mibWriteIn,                 // mibWrite

  output wire                      [7:0] quietCount1In,              // Quiet Count 1
  output wire                      [7:0] quietPeriod1In,             // Quiet Period 1
  output wire                     [15:0] quietDuration1In,           // Quiet Duration 1
  output wire                     [15:0] quietOffset1In,             // Quiet Offset 1
  output wire                            quietElement1InValid,       // Indicates that the Quiet 1 registers have to be updated with Quiet 1 In elements

  output wire                      [7:0] quietCount2In,              // Quiet Count 2
  output wire                      [7:0] quietPeriod2In,             // Quiet Period 2
  output wire                     [15:0] quietDuration2In,           // Quiet Duration 2
  output wire                     [15:0] quietOffset2In,             // Quiet Offset 2
  output wire                            quietElement2InValid,       // Indicates that the Quiet 2 registers have to be updated with Quiet 2 In elements
  
  output wire                      [7:0] dtimPeriodIn,               // DTIM period
  output wire                            dtimPeriodInValid,          // Indicates that the dtimPeriod register has to be updated with dtimPeriodIn
  output wire                      [7:0] cfpPeriodIn,                // CFP period
  output wire                            cfpPeriodInValid,           // Indicates that the cfpPeriod register has to be updated with cfpPeriodIn

  input  wire                     [ 7:0] edcaTriggerTimer,           // EDCA trigger Timer
  output wire                     [ 7:0] hccaTriggerTimer,           // HCCA trigger Timer
  
  input  wire                     [15:0] txOpLimit0,                 // Transmit Opportunity Limit for AC0.
  input  wire                     [15:0] txOpLimit1,                 // Transmit Opportunity Limit for AC1.
  input  wire                     [15:0] txOpLimit2,                 // Transmit Opportunity Limit for AC2.
  input  wire                     [15:0] txOpLimit3,                 // Transmit Opportunity Limit for AC3.

  input  wire                            setac3HasData,              // set ac3 has data
  input  wire                            setac2HasData,              // set ac2 has data
  input  wire                            setac1HasData,              // set ac1 has data
  input  wire                            setac0HasData,              // set ac0 has data
  input  wire                            clearac3HasData,            // clear ac3 has data
  input  wire                            clearac2HasData,            // clear ac2 has data
  input  wire                            clearac1HasData,            // clear ac1 has data
  input  wire                            clearac0HasData,            // clear ac0 has data
                       
  output wire                            statussetac3HasData,        // ac3 has data status
  output wire                            statussetac2HasData,        // ac2 has data status
  output wire                            statussetac1HasData,        // ac1 has data status
  output wire                            statussetac0HasData,        // ac0 has data status

  input  wire                     [ 3:0] aifsn0,                     // AIFSN for AC0.
  input  wire                     [ 3:0] aifsn1,                     // AIFSN for AC1.
  input  wire                     [ 3:0] aifsn2,                     // AIFSN for AC2.
  input  wire                     [ 3:0] aifsn3,                     // AIFSN for AC3.
  input  wire                     [ 3:0] cwMin0,                     // Minimum CW for AC0.
  input  wire                     [ 3:0] cwMin1,                     // Minimum CW for AC1.
  input  wire                     [ 3:0] cwMin2,                     // Minimum CW for AC2.
  input  wire                     [ 3:0] cwMin3,                     // Minimum CW for AC3.
  input  wire                     [ 3:0] cwMax0,                     // Maximum CW for AC0.
  input  wire                     [ 3:0] cwMax1,                     // Maximum CW for AC1.
  input  wire                     [ 3:0] cwMax2,                     // Maximum CW for AC2.
  input  wire                     [ 3:0] cwMax3,                     // Maximum CW for AC3.

  output wire                     [15:0] ac0MOT,                     // AC0 Medium Occupancy timer
  output wire                     [15:0] ac1MOT,                     // AC1 Medium Occupancy timer
  output wire                     [15:0] ac2MOT,                     // AC2 Medium Occupancy timer
  output wire                     [15:0] ac3MOT,                     // AC3 Medium Occupancy timer
  
  output wire                     [ 4:0] rxControlLs,                // RX Controller latched state
  output wire                     [ 4:0] rxControlCs,                // RX Controller current state
  output wire                     [ 8:0] txControlLs,                // TX Controller latched state
  output wire                     [ 8:0] txControlCs,                // TX Controller current state
  output wire                     [ 7:0] macControlLs,               // MAC Controller latched state
  output wire                     [ 7:0] macControlCs,               // MAC Controller current state

  input  wire                     [15:0] probeDelay,                 // Probe delay during active scan

  input  wire                     [15:0] listenInterval,             // Listen interval
  input  wire                            wakeupDTIM,                 // Wakeup DTIM interval
  input  wire                     [14:0] atimW,                      // ATIM Window / Auto Wake Up Time Out

  input  wire                     [15:0] beaconInt,                  // Beacon interval
  input  wire                     [6:0]  impTBTTPeriod,              // Impending TBTT Period
  input  wire                            impTBTTIn128Us,             // Impending TBTT Interrupt Period in 128us
  input  wire                     [7:0]  noBcnTxTime,                // No Beacon Transmit Time in 16us

  input  wire                     [7:0]  dtimPeriod,                 // DTIM Period
  input  wire                     [7:0]  cfpPeriod,                  // CFP period
  input  wire                     [15:0] cfpMaxDuration,             // CFP Max duration
  input  wire                            dtimUpdatedBySW,            // sw programming dtimCfPeriod register

  output wire                            dtimUpdatedBySWIn,          // Input to clear the Software update request
  output wire                            dtimUpdatedBySWInValid,     // Data valid  

  input  wire                     [31:0] tsfTimerHigh,               // TSF[63:32]
  input  wire                     [31:0] tsfTimerLow,                // TSF[31:0]
  input  wire                            tsfUpdatedBySW,             // sw programming tsfTimerLow register
  input  wire                            tsfMgtDisable,              // Disable HW Management of TSF
  
  output wire                     [ 1:0] txBWAfterDropResync,        // Transmission bandwidth afer BW drop

  input  wire                     [ 7:0] timOffset,                  // Indicates to the HW the offset, from the first byte of the Beacon frame, 
                                                                     // at which the first byte of the TIM field is located
  output wire                            tsfUpdatedBySWIn,           // Input to clear the Software update request
  output wire                            tsfUpdatedBySWInValid,      // Data valid  
  output wire                     [31:0] tsfTimerLowIn,              // TSF Timer value [31:0] on macPIClk
  output wire                            tsfTimerLowInValid,         // Indicates that the tsfTimerLow register has to be updated with tsfTimerLowIn
  output wire                     [31:0] tsfTimerHighIn,             // TSF Timer value [63:32] on macPIClk
  output wire                            tsfTimerHighInValid,        // Indicates that the tsfTimerHigh register has to be updated with tsfTimerHighIn

  output reg                      [15:0] nextTBTT,                   // Next TBTT counter in 32 us

  input wire                      [31:0] absTimerValue0,             // absolute timer 0 value
  input wire                      [31:0] absTimerValue1,             // absolute timer 1 value
  input wire                      [31:0] absTimerValue2,             // absolute timer 2 value
  input wire                      [31:0] absTimerValue3,             // absolute timer 3 value
  input wire                      [31:0] absTimerValue4,             // absolute timer 4 value
  input wire                      [31:0] absTimerValue5,             // absolute timer 5 value
  input wire                      [31:0] absTimerValue6,             // absolute timer 6 value
  input wire                      [31:0] absTimerValue7,             // absolute timer 7 value
  input wire                      [31:0] absTimerValue8,             // absolute timer 8 value
  input wire                      [31:0] absTimerValue9,             // absolute timer 9 value
  
  output wire                     [31:0] monotonicCounter1,          // monotonic counter 1 in clk cc
  output wire                     [31:0] monotonicCounterLow2,       // monotonic counter 2 [31:0] in us
  output wire                     [15:0] monotonicCounterHigh2,      // monotonic counter 2 [47:32] in us

  input  wire                     [ 2:0] abgnMode,                   // Indicate the current operating mode

  input  wire                     [15:0] olbcTimer,                  // OLBC Timer
  input  wire                     [7:0]  ofdmCount,                  // OFDM Count
  input  wire                     [7:0]  dsssCount,                  // DSSS/CCK Count

  input  wire                     [7:0]  macCoreClkFreq,             // MAC Core Clock Frequency
  input  wire                     [ 9:0] txRFDelayInMACClk,          // Indicates the TX delay on the RF
  input  wire                     [ 9:0] txChainDelayInMACClk,       // Indicates the TX delay on the PHY

  input  wire                     [ 7:0] slotTime,                   // slot time for timeout
  input  wire                     [15:0] slotTimeInMACClk,           // Slot time in MAC Clocks

  input  wire                     [9:0]  macProcDelayInMACClk,       // MAC Processing Delay in MAC Clocks
  input  wire                     [9:0]  txDelayRFOnInMACClk,        // Transmit Delay with RF On in MAC Clocks
  input  wire                     [9:0]  rxRFDelayInMACClk,          // Receive RF Delay in MAC Clocks

  input  wire                     [9:0]  radioWakeUpTime,            // RF wakeup time in 32us resolution

  input  wire                     [15:0] sifsBInMACClk,              // SIFS Duration for 802.11b in MAC Clocks
  input  wire                     [15:0] sifsAInMACClk,              // SIFS Duration for 802.11a in MAC Clocks
  input  wire                     [ 7:0] sifsB,                      // SIFS Duration for 802.11b in us
  input  wire                     [ 7:0] sifsA,                      // SIFS Duration for 802.11a in us

  input  wire                     [3:0]  rxCCADelay,                 // CCA Delay

  input  wire                     [9:0]  txDMAProcDlyInMACClk,       // Transmit DMA Processing Delay in MAC Clocks
  input  wire                     [9:0]  rifsInMACClk,               // RIFS Duration in MAC Clocks
  input  wire                     [9:0]  rifsTOInMACClk,             // RIFS Timeout Duration in MAC Clocks

  input  wire                     [7:0]  txAbsoluteTimeout,          // Transmission Absolute Timeout
  input  wire                     [7:0]  txPacketTimeout,            // Transmission Packet Timeout

  input  wire                     [7:0]  rxAbsoluteTimeout,          // Reception Absolute Timeout
  input  wire                     [7:0]  rxPacketTimeout,            // Reception Packet Timeout

  input  wire                     [31:0] ccaBusyDur,                 // CCA Busy Duration from CSReg
  output wire                     [31:0] ccaBusyDurIn,               // CCA Busy Duration
  output wire                            ccaBusyDurInValid,          // Indicates that the ccaBusyDur register has to be updated with ccaBusyDurIn

  input  wire                     [31:0] ccaBusyDurSec20,            // CCA Busy Duration on secondary 20MHz from CSReg
  output wire                     [31:0] ccaBusyDurSec20In,          // CCA Busy Duration on secondary 20MHz
  output wire                            ccaBusyDurSec20InValid,     // Indicates that the ccaBusyDurSec20 register has to be updated with ccaBusyDurSec20In

  input  wire                     [31:0] ccaBusyDurSec40,            // CCA Busy Duration on secondary 40MHz from CSReg
  output wire                     [31:0] ccaBusyDurSec40In,          // CCA Busy Duration on secondary 40MHz
  output wire                            ccaBusyDurSec40InValid,     // Indicates that the ccaBusyDurSec40 register has to be updated with ccaBusyDurSec40In

  input  wire                     [31:0] ccaBusyDurSec80,            // CCA Busy Duration on secondary 80MHz from CSReg
  output wire                     [31:0] ccaBusyDurSec80In,          // CCA Busy Duration on secondary 80MHz
  output wire                            ccaBusyDurSec80InValid,     // Indicates that the ccaBusyDurSec80 register has to be updated with ccaBusyDurSec80In

  input  wire                     [7:0]  quietCount1,                // Quiet Count 1
  input  wire                     [7:0]  quietPeriod1,               // Quiet Period 1
  input  wire                     [15:0] quietDuration1,             // Quiet Duration 1
  input  wire                     [15:0] quietOffset1,               // Quiet Offset 1

  input  wire                     [7:0]  quietCount2,                // Quiet Count 2
  input  wire                     [7:0]  quietPeriod2,               // Quiet Period 2
  input  wire                     [15:0] quietDuration2,             // Quiet Duration 2
  input  wire                     [15:0] quietOffset2,               // Quiet Offset 2

  input  wire                      [7:0] rxStartDelayMIMO,           // Receive Start Delay for MIMO
  input  wire                      [7:0] rxStartDelayShort,          // Receive Start Delay for DSSS/CCK Short preamble
  input  wire                      [7:0] rxStartDelayLong,           // Receive Start Delay for DSSS/CCK Long preamble
  input  wire                      [7:0] rxStartDelayOFDM,           // Receive Start Delay for OFDM

  input  wire                            pwrMgt,                     // Power Management is enabled for the current
                                                                     // transmission
  input  wire                            ap,                         // Indicates the type of device (0: STA, 1: AP)
  input  wire                            bssType,                    // Indicates the type of BSS (0: IBSS, 1: Infrastructure)
  input  wire                            cfpAware,                   // CFP Aware
  input  wire                            rxRIFSEn,                   // Enable RIFS in RX    
  input  wire                      [7:0] dsssMaxPwrLevel,            // Maximum Power Level for DSSS/CCK frames
  input  wire                      [7:0] ofdmMaxPwrLevel,            // Maximum Power Level for OFDM frames
  input  wire                      [2:0] maxPHYNtx,                  // Maximum Number of TX chains
  input  wire                     [19:0] maxAllowedLength,           // Filter frames whose length is greater than this length
  input  wire                     [19:0] ppduLength,                 // PPDU Length
                                                                     // This field gives the length of the PPDU for computing time on air.
  input  wire                      [1:0] ppduBW,                     // PPDU Bandwidth
                                                                     // This field indicates that that the PPDU should be transmitted at 20,40,80 or 160 MHz.
  input  wire                      [2:0] ppduPreType,                // PPDU Preamble Type
                                                                     // This field indicates what type of preamble is transmitted for the frame.
                                                                     // The encoding is as follows:
                                                                     // 3'b000: Non-HT-Short
                                                                     // 3'b001: Non-HT-Long
                                                                     // 3'b010: HT-MF
                                                                     // 3'b011: HT-GF
                                                                     // 3'b100: VHT
  input  wire                      [1:0] ppduNumExtnSS,              // Start Transmission with Number of Extension Spatial Streams      
  input  wire                      [1:0] ppduSTBC,                   // Start Transmission with Space Time Block Coding          
  input  wire                            ppduShortGI,                // PPDU Short Guard Interval
                                                                     // Indicates that the frame should be transmitted with Short GI.
  input  wire                      [6:0] ppduMCSIndex,               // PPDU LegRate or MCS Index
                                                                     // This field indicates the rate at which this PPDU is transmitted. 
  input  wire                            computeDuration,            // Request to perform a Time on Air computation
  output wire                            computeDurationIn,          // Time on Air computation done
  output wire                            computeDurationInValid,     // Time on Air computation done valid
  output wire                     [15:0] timeOnAir,                  // Time On Air
                                                                     // This field gives the time taken for frame transmission in microseconds (us)
                                                                     // computed from parameters programmed in timeOnAirParamReg register.
  output wire                            timeOnAirValid,             // Time On Air valid
  input  wire                     [15:0] cfEndSTBCDur,               // CF-End STBC Duration
  input  wire                      [7:0] ctsSTBCDur,                 // CTS STBC Duration
  input  wire                            dualCTSProt,                // Dual-CTS Protection
  input  wire                      [6:0] basicSTBCMCS,               // Basic STBC MCS
  input  wire                            startTxFrameEx,             // Start Transmission with Frame Exchange
  output wire                            startTxFrameExIn,           // Clear the start Transmission with Frame Exchange
  output wire                            startTxFrameExInValid,      // Clear the start Transmission with Frame Exchange
  input  wire                      [1:0] startTxAC,                  // Start Tx AC
  input  wire                      [9:0] startTxKSRIndex,            // Start Transmission with Key Storage RAM Index
  input  wire                      [1:0] startTxFrmExType,           // Start Transmission with Frame Exchange Type
  input  wire                      [7:0] startTxMCSIndex0,           // Start Transmission with MCS Index 0
  input  wire                      [1:0] startTxBW,                  // Start Transmission with Bandwidth        
  input  wire                     [15:0] durControlFrm,              // Start Transmission with duration Control Frame
  input  wire                            startTxSmoothing,           // Start Transmission with Smoothing
  input  wire                     [ 7:0] startTxAntennaSet,          // Start Transmission with Antenna Set
  input  wire                     [ 7:0] startTxSMMIndex,            // Start Transmission with Spatial Map Matrix Index
  input  wire                            startTxPreType,             // Start Transmission with Preamble Type
                                                                     // 1'b0: SHORT
                                                                     // 1'b1: LONG
  input  wire                     [ 2:0] startTxFormatMod,           // Start Transmission with Format and Modulation
                                                                     // 3'b000: NON-HT
                                                                     // 3'b001: NON-HT-DUP-OFDM
                                                                     // 3'b010: HT-MF
                                                                     // 3'b011: HT-GF
                                                                     // 3'b100: VHT
  input  wire                     [ 1:0] startTxNumExtnSS,           // Start Transmission with Number of Extension Spatial Streams
  input  wire                     [ 1:0] startTxSTBC,                // Start Transmission with Space Time Block Coding        
  input  wire                            startTxLSTP,                // Start Transmission with L-SIG TXOP
  input  wire                     [ 2:0] startTxNTx,                 // Start Transmission with Number of Transmit Chains for PPDU        
  input  wire                            startTxShortGI,             // Start Transmission with short GI
  input  wire                            startTxFecCoding,           // Start Transmission with FEC Coding
  input  wire                     [15:0] bbServiceA,                 // Service field when the modulation is OFDM.
  input  wire                     [ 7:0] bbServiceB,                 // Service field when the modulation is DSSS/CCK.

  input  wire                            keepTXOPOpen,               // Keep TXOP Open
  input  wire                            remTXOPInDurField,          // Remaining TXOP Indicated in Duration Field                           
  input  wire                            sendCFEnd,                  // Send CF-End
  input  wire                            sendCFEndNow,               // Send CF-End Now
  output wire                            sendCFEndNowInValid,        // Indicates that the sendCFEndNow register has to be updated with sendCFEndNowIn
  output wire                            sendCFEndNowIn,             // Give the update value of sendCFEndNow

  input  wire                            dynBWEn,                    // Enable dynamic Bandwidth support
  input  wire                            dropToLowerBW,              // Drop To Lower Bandwidth
  input  wire                      [2:0] numTryBWAcquisition,        // Number of Tries for 40/80/160MHz TXOP Acquisition
  input  wire                      [1:0] defaultBWTXOP,              // Indicates the default bandwidth for TXOP acquisition
  input  wire                            defaultBWTXOPV,             // Indicates if the defaultBWTXOP setting is valid.
  input  wire                      [7:0] aPPDUMaxTime,               // aPPDU Maximum Time on Air
  input  wire                      [1:0] maxSupportedBW,             // max Supported BW

  input  wire                            supportLSTP,                // Indicates that the HW support L-SIG TXOP

  input  wire                     [11:0] bssBasicRateSet,            // BSS Basic Rate Set
  input  wire                     [15:0] bssBasicHTMCSSetEM,         // BSS Basic HT MCS Set for Equal Modulation
  input  wire                      [5:0] bssBasicHTMCSSetUM,         // BSS Basic HT MCS Set for Unequal Modulation
  input  wire                     [15:0] bssBasicVHTMCSSet,          // BSS Basic VHT MCS Set

  input  wire                      [1:0] backoffOffset,              // backoff offset
  output wire                      [3:0] currentCW0,                 // current Contetion window value
  output wire                      [3:0] currentCW1,                 // current Contetion window value
  output wire                      [3:0] currentCW2,                 // current Contetion window value
  output wire                      [3:0] currentCW3,                 // current Contetion window value
  output wire                      [7:0] ac3QSRC,                    // short retry count on AC0
  output wire                      [7:0] ac2QSRC,                    // short retry count on AC1
  output wire                      [7:0] ac1QSRC,                    // short retry count on AC2
  output wire                      [7:0] ac0QSRC,                    // short retry count on A
  output wire                      [7:0] ac3QLRC,                    // long retry count on AC0
  output wire                      [7:0] ac2QLRC,                    // long retry count on AC1
  output wire                      [7:0] ac1QLRC,                    // long retry count on AC2
  output wire                      [7:0] ac0QLRC,                    // long retry count on AC3
  output wire                      [2:0] activeAC,                   // Indicates which AC is currently selected.

  input  wire                            keyStoRAMReset,             // Active high reset signal to clear RAM contents
  output wire                            keyStoRAMResetIn,           // keyStoRAMReset clear value
  output wire                            keyStoRAMResetInValid,      // Clearing keyStoRAMReset
  input  wire                            debugKSR,                   // Signal to be asserted for debug purpose only
  input  wire                    [31: 0] encrKeyRAMWord0,            // Write Crypto key [31 : 0]
  input  wire                    [31: 0] encrKeyRAMWord1,            // Write Crypto key [63 :32]
  input  wire                    [31: 0] encrKeyRAMWord2,            // Write Crypto key [95 :64]
  input  wire                    [31: 0] encrKeyRAMWord3,            // Write Crypto key [127:96]
`ifdef RW_WAPI_EN
  input  wire                    [31: 0] encrIntKeyRAMWord0,       // Write Integrity Crypto key [31 : 0]
  input  wire                    [31: 0] encrIntKeyRAMWord1,       // Write Integrity Crypto key [63 :32]
  input  wire                    [31: 0] encrIntKeyRAMWord2,       // Write Integrity Crypto key [95 :64]
  input  wire                    [31: 0] encrIntKeyRAMWord3,       // Write Integrity Crypto key [127:96]
`endif // RW_WAPI_EN
  input  wire                    [31: 0] macAddrRAMLow,              // Write MAC address [31: 0]
  input  wire                    [15: 0] macAddrRAMHigh,             // Write MAC address [47:32]
  output wire                    [31: 0] encrKeyRAMWord0In,          // Read Crypto key [31 : 0]
  output wire                    [31: 0] encrKeyRAMWord1In,          // Read Crypto key [63 :32]
  output wire                    [31: 0] encrKeyRAMWord2In,          // Read Crypto key [95 :64]
  output wire                    [31: 0] encrKeyRAMWord3In,          // Read Crypto key [127:96]
`ifdef RW_WAPI_EN
  output wire                    [31: 0] encrIntKeyRAMWord0In,     // Read Integrity Crypto key [31 : 0]
  output wire                    [31: 0] encrIntKeyRAMWord1In,     // Read Integrity Crypto key [63 :32]
  output wire                    [31: 0] encrIntKeyRAMWord2In,     // Read Integrity Crypto key [95 :64]
  output wire                    [31: 0] encrIntKeyRAMWord3In,     // Read Integrity Crypto key [127:96]
`endif // RW_WAPI_EN
  output wire                    [31: 0] macAddrRAMLowIn,            // Read MAC address [31: 0]
  output wire                    [15: 0] macAddrRAMHighIn,           // Read MAC address [47:32]
  output wire                            encrKeyRAMWord0InValid,     // Read Valid Crypto key [31 : 0]
  output wire                            encrKeyRAMWord1InValid,     // Read Valid Crypto key [63 :32]
  output wire                            encrKeyRAMWord2InValid,     // Read Valid Crypto key [95 :64]
  output wire                            encrKeyRAMWord3InValid,     // Read Valid Crypto key [127:96]
`ifdef RW_WAPI_EN
  output wire                            encrIntKeyRAMWord0InValid,     // Read Valid Crypto key [31 : 0]
  output wire                            encrIntKeyRAMWord1InValid,     // Read Valid Crypto key [63 :32]
  output wire                            encrIntKeyRAMWord2InValid,     // Read Valid Crypto key [95 :64]
  output wire                            encrIntKeyRAMWord3InValid,     // Read Valid Crypto key [127:96]
`endif // RW_WAPI_EN
  output wire                            macAddrRAMLowInValid,       // Read Valid MAC address [31: 0]
  output wire                            macAddrRAMHighInValid,      // Read Valid MAC address [47:32]
  input  wire                    [ 9: 0] keyIndexRAM,                // Index of Key Storage RAM into which the encryption register contents are to be written
  input  wire                            newWrite,                   // Trigger for write operation
  output wire                            newWriteIn,                 // newWriteIn
  output wire                            newWriteInValid,            // Clearing newWrite
  input  wire                            newRead,                    // Trigger for read operation
  output wire                            newReadIn,                  // newReadIn
  output wire                            newReadInValid,             // Clearing newRead
  input  wire                            cLenRAM,                    // Cipher length indication for WEP
  output wire                            cLenRAMIn,                  // cLenRAM from Key Search Engine
  output wire                            cLenRAMInValid,             // cLenRAM update
  input  wire                            useDefKeyRAM,               // Indication for usage of Default Keys.
  output wire                            useDefKeyRAMIn,             // useDefKeyRAM from Key Search Engine
  output wire                            useDefKeyRAMInValid,        // useDefKeyRAM update
  input  wire                      [1:0] sppRAM,                     // Indication for handling A-MSDU frames
  output wire                      [1:0] sppRAMIn,                   // sppRAM from Key Search Engine
  output wire                            sppRAMInValid,              // sppRAM update
  input  wire                      [3:0] vlanIDRAM,                  // Virtual LAN ID for searching default key
  output wire                      [3:0] vlanIDRAMIn,                // vlanIDRAM from Key Search Engine
  output wire                            vlanIDRAMInValid,           // vlanIDRAM update
  input  wire                      [2:0] cTypeRAM,                   // Cipher type
  output wire                      [2:0] cTypeRAMIn,                 // cTypeRAM from Key Search Engine
  output wire                            cTypeRAMInValid,            // cTypeRAM update

  ///////////////////////////////////////////////
  //$port_g Debug ports
  ///////////////////////////////////////////////
  output wire                     [15:0] debugPortMACTimerUnit,      // Debug port from MACTimerUnit
  output wire                     [15:0] debugPortMACTimerUnit2,     // Debug port from MACTimerUnit
  output wire                     [15:0] debugPortMACTimerUnit3,     // Debug port from MACTimerUnit
  output wire                     [15:0] debugPortBackoff,           // Debug port from Backoff
  output wire                     [15:0] debugPortBackoff2,          // Debug port from Backoff
  output wire                     [15:0] debugPortBackoff3,          // Debug port from Backoff
  output wire                     [15:0] debugPortDeaggregator,      // Debug port from Deaggregator
  output wire                     [15:0] debugPortDeaggregator2,     // Debug port from Deaggregator2
  output wire                      [3:0] debugPortDeaggregatorFsm,   // Debug port from Deaggregator FSM
  output wire                     [15:0] debugPortRxController,      // Debug port from Rx Controller
  output wire                     [15:0] debugPortRxFrameDebug1,     // Debug port for Rx frame debug 1
  output wire                     [15:0] debugPortRxFrameDebug2,     // Debug port for Rx frame debug 2
  output wire                     [15:0] debugPortTxFrameDebug1,     // Debug port for Tx frame debug 1
  output wire                     [15:0] debugPortTxFrameDebug2,     // Debug port for Tx frame debug 2
  output wire                     [15:0] debugPortBAController,      // Debug port from BA Controller
  output wire                     [15:0] debugPortBAController2,     // Debug port from BA Controller
  output wire                     [15:0] debugPortBAController3,     // Debug port from BA Controller
  output wire                     [15:0] debugPortTxParametersCache, // Debug Port from TX Parameter Cache
  output wire                     [15:0] debugPortMACController1,    // Debug Port 1 from the MAC Controller
  output wire                     [15:0] debugPortMediumAccess,      // Debug Port Medium Access
  output wire                     [15:0] debugPortNAV,               // Debug Port NAV
  output wire                     [15:0] debugPortMACControllerRx,   // Debug Port of the MAC Controller Rx
  output wire                     [15:0] debugPortMACControllerTx,   // Debug Port of the MAC Controller Tx
  output wire                     [15:0] debugPortBWManagement,      // Debug Port of BW Management
  output wire                     [13:0] debugPortAMPDU,             // Debug Port AMPDU
  output wire                     [31:0] debugPortEncryptionEngine,  // Debug Port of the Encryption Engine
  `ifdef RW_WAPI_EN
  output wire                     [15:0] debugPortWapi,              // Debug Port of Wapi Encryption Engine
  `endif //RW_WAPI_EN
  output wire                     [15:0] debugPortKeySearch,         // Debug Port Key Search Engine
  output wire                     [15:0] debugPortrxFIFOCntrl,       // Debug Port rxFIFOController
  output wire                     [15:0] debugPortDecryptFsm,        // Debug Port rxDecryptFSM
  output wire                     [15:0] debugPortDozeController     // Debug Port of the Doze Controller
   );
//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

wire         macCoreTxClkSoftRst_n;                                  // Active low soft reset signal synchronized to the macCoreClk.

// Interconnect between Tx Parameters Cache and the MAC Controller
wire         toggleHDSet_p;                                          // Indicates that the Header Descriptor Set can be toggled
wire         togglePTSet_p;                                          // Indicates that the Policy Table Set can be toggled
wire         clearSets_p;                                            // Indicates that the Sets have to be cleared.
wire         txParameterHDReady_p;                                   // Indicates that the Header Descriptor fields are usable 
wire         txParameterPTReady_p;                                   // Indicates that the Policy Table fields are usable
wire         txParameterNextPTReady_p;                               // Indicates that a second policy table has already been loaded
wire         txPCtoggleHDSet_p;                                      // Indicates that the Header Descriptor Set can be toggled
wire         txPCtogglePTSet_p;                                      // Indicates that the Policy Table Set can be toggled
wire         txPCclearSets_p;                                        // Indicates that the Sets have to be cleared.
wire         txPCtxParameterHDReady_p;                               // Indicates that the Header Descriptor fields are usable 
wire         txPCtxParameterPTReady_p;                               // Indicates that the Policy Table fields are usable
wire         txPCtxParameterNextPTReady_p;                           // Indicates that a second policy table has already been loaded

// Interconnect between Tx Parameters Cache and P-Table PHY Control Information 1
wire   [2:0] nTxProtPT;                                              // Number of Transmit Chains for Protection Frame
wire   [2:0] nTxPT;                                                  // Number of Transmit Chains for PPDU
wire         shortGIPT;                                              // Short Guard Interval for Transmission
wire   [7:0] txPwrLevelPT;                                           // Transmit Power Level
wire   [7:0] txPwrLevelProtPT;                                       // Transmit Power Level for Protection Frame
wire   [1:0] stbcPT;                                                 // Space Time Block Coding
wire         fecCodingPT;                                            // FEC Coding
wire   [1:0] numExtnSSPT;                                            // Number of Extension Spatial Streams
wire         bfFrmExPT;                                              // Beam Forming Frame Exchange

// Interconnect between Tx Parameters Cache and P-Table PHY Control Information 2
wire         beamFormedPT;                                           // BeamFormed frame
wire   [7:0] smmIndexPT;                                             // Spatial Map Matrix Index
wire   [7:0] antennaSetPT;                                           // Antenna Set

// Interconnect between Tx Parameters Cache and P-Table MAC Control Information 1
wire   [9:0] keySRAMIndex;                                           // Key Storage RAM Index
wire   [9:0] keySRAMIndexRA;                                         // Key Storage RAM Index for Receiver Addr

// Interconnect between Tx Parameters Cache and P-Table MAC Control Information 2
wire  [11:0] rtsThreshold;                                           // RTS Threshold
wire   [7:0] shortRetryLimit;                                        // Short Retry Limit
wire   [7:0] longRetryLimit;                                         // Long Retry Limit

// Interconnect between Tx Parameters Cache and H-Descriptor Status Information
wire        lifetimeExpired;                                         // Indicates that the lifetime of this MPDU expired

// Interconnect between Tx Parameters Cache and H-Descriptor Frame Lenght
wire  [15:0] MPDUFrameLengthTx;                                      // Length of the MPDU

// Interconnect between Tx Parameters Cache and H-Descriptor PHY Control Information 
wire   [2:0] formatModProtTx;                                        // Format and Modulation of Protection frame for Transmission
wire   [2:0] formatModTx;                                            // Format and Modulation of PPDU for Transmission
wire   [1:0] bwProtTx;                                               // Band Width of Protection frame for Transmission
wire   [1:0] bwTx;                                                   // Band Width of PPDU for Transmission
wire         dozeNotAllowedTx;                                       // TXOP PS is not allowed
wire   [8:0] partialAIDTx;                                           // Partial AID
wire   [5:0] groupIDTx;                                              // Group ID

wire         txSingleVHTMPDU;                                        // Indicates that the AMPDU has only one MPDU

// Interconnect between Tx Parameters Cache and H-Descriptor Status Information
wire   [7:0] numMPDURetriesTPC;                                      // Indicates the number of MPDU retries already done  
wire   [7:0] numRTSRetriesTPC;                                       // Indicates the number of RTS retries already done  
wire  [19:0] aMPDUFrameLengthTx;                                     // Length of the entire A-MPDU
wire  [19:0] aMPDUOptFrameLength20Tx;                                // Length of the entire A-MPDU BW drop 20 Mhz
wire  [19:0] aMPDUOptFrameLength40Tx;                                // Length of the entire A-MPDU BW drop 40 Mhz
wire  [19:0] aMPDUOptFrameLength80Tx;                                // Length of the entire A-MPDU BW drop 80 Mhz
wire  [31:0] mediumTimeUsedTPC;

// Interconnect between Tx Parameters Cache and H-Descriptor PHY Control Information 
wire   [6:0] mcsIndex0ProtTx;                                        // MCS Index 0 of Protection frame for Transmission
wire   [6:0] mcsIndex0Tx;                                            // MCS Index 0 of PPDU for Transmission

// Interconnect between Tx Parameters Cache and H-Descriptor PHY Control Information
wire         useRIFSTx;                                              // Use RIFS for Transmission
wire         preTypeProtTx;                                          // Preamble Type of Protection frame for Transmission
wire         preTypeTx;                                              // Preamble Type of PPDU for Transmission
wire         dynBWTx;                                                // Dynamic Bandwidth for Transmission
wire         useBWSignalingTx;                                       // Use BW Signaling for Transmission
wire         smoothingProtTx;                                        // Smoothing of Protection frame for Transmission
wire         smoothingTx;                                            // Smoothing of PPDU for Transmission
wire         soundingTx;                                             // Sounding Protection frame for Transmission


// Interconnect between Tx Parameters Cache and H-Descriptor MAC Control Information 1
wire  [15:0] protFrmDur;                                             // Protection Frame Duration
wire         writeACK;                                               // Indicate SW expects the ACK frame for this frame 
wire         lowRateRetry;                                           // Lower Rate on Retries
wire         lstpProt;                                               // L-SIG TXOP Protection for protection frame
wire         lstp;                                                   // L-SIG TXOP Protection
wire   [1:0] expectedAck;                                            // Expected Acknowledgement
wire   [2:0] navProtFrmEx;                                           // NAV Protection Frame Exchange

// Interconnect between Tx Parameters Cache and H-Descriptor MAC Control Information 2
wire         dontGenerateMH;                                         // Indicates that HW should not generate the MAC Header by itself
wire         dontEncrypt;                                            // Indicates that HW should bypassed the encryption operation during tx.
wire         dontTouchFC;                                            // Indicates that HW should not update the Frame Control field,
wire         dontTouchDur;                                           // Indicates that HW should not update the Duration field
wire         dontTouchQoS;                                           // Indicates that HW should not update the QoS field 
wire         dontTouchHTC;                                           // Indicates that HW should not update the HTC field 
wire         dontTouchTSF;                                           // Indicates that HW should not update the TSF field 
wire         dontTouchDTIM;                                          // Indicates that HW should not update the DTIM Count field
wire         dontTouchFCS;                                           // Indicates that HW should not update the FCS field
wire         underBASetup;                                           // Indicates whether BA has been setup for this MPD
wire         aMPDU;                                                  // Indicates whether this Transmit Header Descriptor belong to an A-MPDU
wire   [1:0] whichDescriptor;                                        // Indicates what kind of a descriptor this is
wire   [9:0] nBlankMDelimiters;                                      // Indicates the number of blank MPDU delimiters that are inserted
wire         interruptEnTx;                                          // Interrupt Enable for Transmit DMA
wire   [3:0] fcSubtype;                                              // Indicates the fcSubtype field of the Frame Control field of the MPDU.
wire   [1:0] fcType;                                                 // Indicates the fcType field of the Frame Control field of the MPDU
wire         tsValid;                                                // Indicates if the fcType and fcSubtype fields have been populated correctly





// Interconnect between Tx Parameters Cache and P-Table PHY Control Information 1
wire   [2:0] txPCnTxProtPT;                                              // Number of Transmit Chains for Protection Frame
wire   [2:0] txPCnTxPT;                                                  // Number of Transmit Chains for PPDU
wire         txPCshortGIPT;                                              // Short Guard Interval for Transmission
wire   [7:0] txPCtxPwrLevelPT;                                           // Transmit Power Level
wire   [7:0] txPCtxPwrLevelProtPT;                                       // Transmit Power Level for Protection Frame
wire   [1:0] txPCstbcPT;                                                 // Space Time Block Coding
wire         txPCfecCodingPT;                                            // FEC Coding
wire   [1:0] txPCnumExtnSSPT;                                            // Number of Extension Spatial Streams
wire         txPCbfFrmExPT;                                              // Beam Forming Frame Exchange

// Interconnect between Tx Parameters Cache and P-Table PHY Control Information 2
wire         txPCbeamFormedPT;                                           // BeamFormed frame
wire   [7:0] txPCsmmIndexPT;                                             // Spatial Map Matrix Index
wire   [7:0] txPCantennaSetPT;                                           // Antenna Set

// Interconnect between Tx Parameters Cache and P-Table MAC Control Information 1
wire   [9:0] txPCkeySRAMIndex;                                           // Key Storage RAM Index
wire   [9:0] txPCkeySRAMIndexRA;                                         // Key Storage RAM Index for Receiver Addr

// Interconnect between Tx Parameters Cache and P-Table MAC Control Information 2
wire  [11:0] txPCrtsThreshold;                                           // RTS Threshold
wire   [7:0] txPCshortRetryLimit;                                        // Short Retry Limit
wire   [7:0] txPClongRetryLimit;                                         // Long Retry Limit

// Interconnect between Tx Parameters Cache and H-Descriptor Status Information
wire        txPClifetimeExpired;                                         // Indicates that the lifetime of this MPDU expired

// Interconnect between Tx Parameters Cache and H-Descriptor Frame Lenght
wire  [15:0] txPCMPDUFrameLengthTx;                                      // Length of the MPDU

// Interconnect between Tx Parameters Cache and H-Descriptor PHY Control Information 
wire   [2:0] txPCformatModProtTx;                                        // Format and Modulation of Protection frame for Transmission
wire   [2:0] txPCformatModTx;                                            // Format and Modulation of PPDU for Transmission
wire   [1:0] txPCbwProtTx;                                               // Band Width of Protection frame for Transmission
wire   [1:0] txPCbwTx;                                                   // Band Width of PPDU for Transmission
wire         txPCdozeNotAllowedTx;                                       // TXOP PS is not allowed
wire   [8:0] txPCpartialAIDTx;                                           // Partial AID
wire   [5:0] txPCgroupIDTx;                                              // Group ID

wire         txPCtxSingleVHTMPDU;                                        // Indicates that the AMPDU has only one MPDU

// Interconnect between Tx Parameters Cache and H-Descriptor Status Information
wire   [7:0] txPCnumMPDURetriesTPC;                                      // Indicates the number of MPDU retries already done  
wire   [7:0] txPCnumRTSRetriesTPC;                                       // Indicates the number of RTS retries already done  
wire  [19:0] txPCaMPDUFrameLengthTx;                                     // Length of the entire A-MPDU
wire  [19:0] txPCaMPDUOptFrameLength20Tx;                                // Length of the entire A-MPDU in case of BW drop 20Mhz
wire  [19:0] txPCaMPDUOptFrameLength40Tx;                                // Length of the entire A-MPDU in case of BW drop 40Mhz
wire  [19:0] txPCaMPDUOptFrameLength80Tx;                                // Length of the entire A-MPDU in case of BW drop 80Mhz
wire  [31:0] txPCmediumTimeUsedTPC;

// Interconnect between Tx Parameters Cache and H-Descriptor PHY Control Information 
wire   [6:0] txPCmcsIndex0ProtTx;                                        // MCS Index 0 of Protection frame for Transmission
wire   [6:0] txPCmcsIndex0Tx;                                            // MCS Index 0 of PPDU for Transmission

// Interconnect between Tx Parameters Cache and H-Descriptor PHY Control Information
wire         txPCuseRIFSTx;                                              // Use RIFS for Transmission
wire         txPCpreTypeProtTx;                                          // Preamble Type of Protection frame for Transmission
wire         txPCpreTypeTx;                                              // Preamble Type of PPDU for Transmission
wire         txPCdynBWTx;                                                // Dynamic Bandwidth for Transmission
wire         txPCuseBWSignalingTx;                                       // Use BW Signaling for Transmission
wire         txPCsmoothingProtTx;                                        // Smoothing of Protection frame for Transmission
wire         txPCsmoothingTx;                                            // Smoothing of PPDU for Transmission
wire         txPCsoundingTx;                                             // Sounding Protection frame for Transmission


// Interconnect between Tx Parameters Cache and H-Descriptor MAC Control Information 1
wire  [15:0] txPCprotFrmDur;                                             // Protection Frame Duration
wire         txPCwriteACK;                                               // Indicate SW expects the ACK frame for this frame 
wire         txPClowRateRetry;                                           // Lower Rate on Retries
wire         txPClstpProt;                                               // L-SIG TXOP Protection for protection frame
wire         txPClstp;                                                   // L-SIG TXOP Protection
wire   [1:0] txPCexpectedAck;                                            // Expected Acknowledgement
wire   [2:0] txPCnavProtFrmEx;                                           // NAV Protection Frame Exchange

wire         txPCcontinuousTx;              // Enable continuous transmit 


// Interconnect between Tx Parameters Cache and H-Descriptor MAC Control Information 2
wire         txPCdontGenerateMH;                                         // Indicates that HW should not generate the MAC Header by itself
wire         txPCdontEncrypt;                                            // Indicates that HW should bypassed the encryption operation during tx.
wire         txPCdontTouchFC;                                            // Indicates that HW should not update the Frame Control field,
wire         txPCdontTouchDur;                                           // Indicates that HW should not update the Duration field
wire         txPCdontTouchQoS;                                           // Indicates that HW should not update the QoS field 
wire         txPCdontTouchHTC;                                           // Indicates that HW should not update the HTC field 
wire         txPCdontTouchTSF;                                           // Indicates that HW should not update the TSF field 
wire         txPCdontTouchDTIM;                                          // Indicates that HW should not update the DTIM Count field
wire         txPCdontTouchFCS;                                           // Indicates that HW should not update the FCS field
wire         txPCunderBASetup;                                           // Indicates whether BA has been setup for this MPD
wire         txPCaMPDU;                                                  // Indicates whether this Transmit Header Descriptor belong to an A-MPDU
wire   [1:0] txPCwhichDescriptor;                                        // Indicates what kind of a descriptor this is
wire   [9:0] txPCnBlankMDelimiters;                                      // Indicates the number of blank MPDU delimiters that are inserted
wire         txPCinterruptEnTx;                                          // Interrupt Enable for Transmit DMA
wire   [3:0] txPCfcSubtype;                                              // Indicates the fcSubtype field of the Frame Control field of the MPDU.
wire   [1:0] txPCfcType;                                                 // Indicates the fcType field of the Frame Control field of the MPDU
wire         txPCtsValid;                                                // Indicates if the fcType and fcSubtype fields have been populated correctly

// mux signal to Interrupt Controller
wire         acBWDropTrigger;

// Interconnect between TX Controller and RX Controller
wire         respTxSmoothing;                                        // Response Transmission with Smoothing
wire   [7:0] respTxAntennaSet;                                       // Response Transmission with Antenna Set
wire   [7:0] respTxSMMIndex;                                         // Response Transmission with Spatial Map Matrix Index

wire         respTxPreType;                                          // Response Transmission with Preamble Type
                                                                     // 1'b0: SHORT
                                                                     // 1'b1: LONG

wire   [2:0] respTxFormatMod;        								 // Response Transmission with Format and Modulation
                                                     				 //   3'd0: NON-HT
				                                                     //   3'd1: NON-HT-DUP-OFDM
				                                                     //   3'd2: HT-MF
				                                                     //   3'd3: HT-GF
				                                                     //   3'd4: VHT
wire   [1:0] respTxNumExtnSS;                                        // Response Transmission with Number of Extension Spatial Streams
wire         respTxFECCoding;                                        // Response Transmission with FEC Coding 
wire   [2:0] respTxNTx;                                              // Response Transmission with Number of Transmit Chains for PPDU       
wire         respTxShortGI;                                          // Response Transmission with Short Guard Interval


// Interconnect between TX Controller and MAC Timer Unit
wire         tick1us_p;                                              // Pulse generated every us
wire         tick1usPIClk_p;                                         // Pulse generated every us resynchronized on macPIClk
wire  [63:0] tsfTimer;                                               // TSF timer value
wire         tickRIFS_p;                                             // A pulse to indicate the end of RIFS period  TBD
wire         tickSIFS_p;                                             // A pulse to indicate the end of SIFS period
wire         tickPIFS_p;                                             // A pulse to indicate the end of PIFS period
wire         rifsTO_p;                                               // Pulse when RIFS timeout occurs
wire         tick1tu_p;                                              // Pulse generated every TUs.
wire   [7:0] dtimCnt;                                                // DTIM count maintained in hardware
wire   [7:0] cfpCnt;                                                 // CFP count maintained in hardware TBD
wire         respTO_p;                                               // Indicates when the CTS/ACK Response TimeOut timer has expired.
wire         tick32us_p;                                             // Pulse generated every 32us.
wire         sec20ChannelIdleFlag;                                   // Secondary 20MHz channel idle for PIFS flag TBD
wire         sec40ChannelIdleFlag;                                   // Secondary 40MHz channel idle for PIFS flag TBD
wire         sec80ChannelIdleFlag;                                   // Secondary 80MHz channel idle for PIFS flag TBD
      
// Interconnect between TX Controller and MAC Controller interface
wire         sendData_p;                                             // Indication that data packet has to be sent
wire         sendRTS_p;                                              // Indication that an RTS packet has to be sent
wire         sendCTS_p;                                              // Indication that a CTS packet has to be sent
wire         sendACK_p;                                              // Indication that an ACK packet has to be sent
wire         sendCFEND_p;                                            // Indication that a CF-END packet has to be sent
wire         sendBA_p;                                               // Indication that an Block ACK packet has to be sent
wire         sendOnSIFS;                                             // If set; data is sent on tickSIFS else on tickSlot
wire         sendOnPIFS;                                             // If set; data is sent on tickPIFS

wire         skipMPDU_p;                                             // Indication that MPDU in TX FIFO has to be discarded
wire         skipMPDUDone_p;                                         // Indicates that MPDU contained in the TXFIFO has been discarded.

wire  [47:0] destAddr;                                               // Receiver address
wire  [47:0] srcAddr;                                                // Source address
wire  [15:0] duration;                                               // Duration
wire         retry;                                                  // Indicates that the trame is a retry.
wire   [3:0] txTID;                                                  // TID of the transmitted frame
wire   [1:0] typeTx;                                                 // TYPE of the transmitted frame
wire         typeTxValid;                                            // Indicates typeTx signal is valid
wire         txAMSDUPresent;                                         // A-MSDU Present
wire  [15:0] tsfDuration;                                            // Duration from the preamble until the first bit of TSF

wire   [6:0] txMCS;                                                  // MCS (Only used for HT frame)
wire  [11:0] txLegLength;                                            // Legacy Length of the PPDU         
wire  [ 3:0] txLegRate;                                              // Legacy Rate of the PPDU.         
wire   [1:0] txChBW;                                                 // Transmit a Frame with Channel Bandwidth 40MHz
wire         txBWSignaling;                                          // Transmission with BW Signaling
wire         txDynBW;                                                // Transmission with Dynamic BW
wire  [19:0] txHTLength;                                             // Length of the HT PPDU         
wire   [1:0] txSTBC;                                                 // Transmit a Frame with Space Time Block Coding
wire         txDisambiguityBit;                                      // Transmit a Frame with disambiguityBit
wire         txResp;                                                 // Transmit a Response Frame
wire         txFecCoding;                                            // Transmit with FEC coding
wire         txShortGI;                                              // Transmit with Short Guard Interval
wire         txFromReg;                                              // Transmit a HW generated frame based on Register
wire         txFromHD;                                               // Transmit a HW generated frame based on THD
wire         txFromFifo;                                             // Transmit a Frame from Tx FIFO
wire         txCFEND;                                                // Transmit a HW generated CFEND frame
wire         txDone_p;                                               // Indicates the completion of the transmission
wire         txBcMc;                                                 // Indicates than the transmitted frame has a group address.

wire         sentCFEND;                                              // Indicates that the transmitted frame is a CF-END
wire         sentRTS;                                                // Indicates that the transmitted frame is a RTS
wire         sentBAReq;                                              // Indicates that the transmitted frame is a BA-Request
wire         mpduDone_p;                                             // Indicates that the MPDU has been sent

// Interconnect between TX Controller and Encryption Engine interface
wire         cryptoKeySearchDone;                                    // Indicates that the Key Search is completed.
wire         txCryptoKeyValid;                                       // Indicates that the Key is valid
// FOLLOWING ALL TBD !!!
wire [7:0]   plainTxData;                                            // Plain (unencrypted) data from TX Controller
wire         plainTxDataValid;                                       // Validating signal for plain TX data
wire         cryptoDataReady;                                        // Flow control signal indicating readiness of crypto  
                                                                     // module for accepting input data 
wire [7:0]   encryptDataOut;                                         // Encrypted data output; for writing into FCS block
wire         encryptDataValid;                                       // Validating signal for the output encrypted data. 
                                                                     // This signal will be asserted only when 
                                                                     // fcsBusy input is low.
wire         initPRNG_p_tx;                                          // Initialize Pseudo Random Number Generator
wire         txError_p;                                              // Indication of error signal from TX Controller 
                                                                     // during transmission operation
wire         txCsIsIdle;                                             // State machine information from TX Controller
wire         txSBOXInit;                                             // Pulse to init the Encryption Engine SBOX for WEP and TKIP
wire         txSBOXInitDone;                                         // Indicates that the initialisation of the Encryption Engine is completed for WEP and TKIP.
wire         txICVEnable;                                             // Pulse to start outputing ICV for WEP and TKIP

wire         txWEP;                                                  // WEP Mode
wire [23:0]  txWEPIV;                                                // WEP IV
wire         txWEPIVValid;                                           // WEP IV Valid
wire         txTKIP;                                                 // Indication for TKIP encryption
wire [47:0]  txTkipSeqCntr;                                          // TKIP Sequence Counter for TKIP encryption

wire         StartCCMP;                                              // Start Tx/Rx CCMP
wire         txCCMP;                                                 // Indication for CCMP encryption
wire         txCCMPBusy;
wire         txCCMPMicDone;
wire         txCCMPStart;                                            // Tx controller start CCMP
wire         txCCMPDataWrEn_p;                                       // Write pulse for CCMP input buffer for TX
wire         txPushCCMPHdrInBuffer_p;                                // Write pulse for storing CCMP header
wire         txAddress4Pres;                                         // Tx flag indicating address 4 is present
wire         txQoSFrame;                                             // Tx flag indicating the current frame is a QoS Frame
wire         txCCMPHT;                                               // Tx HT flag
                                                                     // without encryption into Encr. Buffer

`ifdef RW_WAPI_EN
// WAPI Only
wire         wpiDone_p;
wire         wapiPassed_p;
wire         wapiFailed_p;
wire         encrTxWAPIBusy;
wire         txWAPI;                                                // WAPI Encrypt Mode
wire         rxWAPI;                                                // WAPI WAPI Decrypt Mode
wire         txWAPIStart;                                           // Tx controller start WAPI
wire         txWAPIMicDone;                                         // Get WAPI Mic Calculation Done
wire         txWAPIBusy;                                            // High when wpi is processing data
wire [15:0]  txWAPIFrameControl;                                    // MAC Header TX Frame Control Field
wire [47:0]  txWAPIAddr3;                                           // MAC Header TX Address 3 Field
wire [47:0]  txWAPIAddr4;                                           // MAC Header TX Address 4 Field
wire [15:0]  txWAPIQoSCF;                                           // MAC Header TX QoS Control Field
wire [15:0]  txWAPISeqControl;                                      // MAC Header TX Seauence Control Field
wire [7:0]   txWAPIKeyIdx;                                          // WAPI Header TX Key Index
wire [127:0] txWAPIPN;                                              // WAPI Header TX Packet Number (PN) Field

wire [15:0]  rxFrmCtrl;                                             // MAC Header RX Frame Control Field             
wire [47:0]  rxAddr3;                                               // MAC Header RX Address 3 Field                 
wire [47:0]  rxAddr4;                                               // MAC Header RX Address 4 Field                 
wire [15:0]  rxQoSControl;                                          // MAC Header RX QoS Control Field               
wire [15:0]  rxSeqCtrl;                                             // MAC Header RX Seauence Control Field          
wire [7:0]   rxWAPIKeyIndex;                                        // WAPI Header RX Key Index                      
wire [127:0] rxWAPIPN;                                              // WAPI Header RX Packet Number (PN) Field       
`endif //RW_WAPI_EN

wire         txPayLoadEnd_p;                                         // End of payload from TX or RX Controller
                                                                     // needed by CCMP
wire         ccmpHTMode;                                             // Flag for HT mode
                                                                     // Following TX inputs are used in CCMP engine 
                                                                     // for Nonce or AAD calculation
                                                                     // ========================================= 
wire [15:0]  tcPayLoadLen;                                           // Transmit payload length in TX Frame
wire [47:0]  txAddr1;                                                // Address1 field of TX frame
wire [47:0]  txAddr2;                                                // Address1 field of TX frame

wire [47:0]  tcSfc;                                                  // Transmit SFC field in TX Frame
wire         initDone_p;                                             // Indicated PRNG has finished initialization 
                                                                     // and transformation phases

wire [7:0]   txEncrData;                                             // Encrytped TKIP/WEP/CCMP data from Encrypt Engine to Tx Controller
wire         txEncrDataValid;                                        // Encrytped  TKIP/WEP/CCMP data valid from Encrypt Engine to Tx Controller

wire [7:0]   encrTxCCMPWriteData;                                    // Encrytped CCMP data from Encrypt Engine
wire         encrTxCCMPWriteDataValid;                               // Encrytped CCMP data valid from Encrypt Engine

// Interconnect between CSReg and Encryption Engine interface
wire [47:0]  macAddress;                                             // MAC address of the system

// Interconnect between Key Search Engine and Encryption Engine interface
wire         cryptoKeyValid;                                         // Key validating signal
wire [127:0] cryptoKey;                                              // Key to be used for encryption or decryption 
                                                                     // operations
`ifdef RW_WAPI_EN
wire [127:0] cryptoIntKey;                                           // Integrity key to be used for WAPI encryption or
                                                                     // decryption operations
`endif // RW_WAPI_EN
wire [2:0]   cipherType;                                             // Cipher Type Input from TX or RX Controller 
wire         cipherLen;                                              // Cipher Length Input from TX or RX Controller
wire         keySearchDone_p;                                        // Indication of key search completion
                                                
// Interconnect between TX Controller and FCS Block interface
wire         fcsEnableTx;                                            // indicates the begining of the transmission and enable the FCS block
wire         fcsStartTx_p;                                           // indicates the begining of the transmission and enable the FCS block
wire         fcsShiftTx;                                             // indicates FCS engine to append FCS calculated on data
wire         fcsDInValidTx;                                          // indicates that the data on fcsDInTx is valid and can be processed.
wire   [7:0] fcsDInTx;                                               // Data to the FCS block
wire         fcsPauseTx;                                             // indicates that the FCS block must stop the processing.

// Interconnect between MAC Controller and Rx Controller interface
wire         activeRx;                                               // Indicates Mac cotroller is in Rx state
wire         dataFrame;                                              // Type of frame received is DATA
wire         reservedRcved;                                          // Type of frame received is Reserved
wire         rxAck;                                                  // Force receive only ACK after Tx
wire         rxBA;                                                   // Force receive only BA after Tx
wire         rxCts;                                                  // Force receive only CTS after RTS Tx
wire         lSIGTXOPDetected;                                       // Flag indicates current received packet is LSIG TXOP protected
wire         forceWriteACK;                                          // Force the RX to pass the ACK to the Software

wire         ackRcved_p;                                             // ACK received
wire         rtsRcved_p;                                             // RTS received
wire         ctsRcved_p;                                             // CTS received
wire         cfEndRcved_p;                                           // CF-End received
wire         baRcved_p;                                              // BA received 
wire         barRcved_p;                                             // BAR received
wire         probRespRcved_p;                                        // Prob Response received
wire         needAckRcved_p;                                         // Data or management received with ACK needed
wire         bcMcRcved_p;                                            // Broadcast/Multicast
wire         bcnRcved_p;                                             // Beacon received
wire         notMineRcved_p;                                         // Frame received but not mine
wire         notMinePsPollRcved_p;                                   // PS-Poll received but not mine
wire         notMineRtsRcved_p;                                      // RTS received but not mine
wire         unknownRcved_p;                                         // Unknown frame received
wire         macHeaderCompleted;                                     // End of MAC Header reception
wire   [1:0] rxFCType;                                               // Indicates the fcType field of the received frame

wire         incorrectRcved_p;                                       // Frame not received correctly
wire         correctRcved_p;                                         // Frame received correctly

wire  [47:0] rxAddr2;                                                // Receiver addr
wire   [1:0] ackPolicy;                                              // Ack policy (Ack; No Ack; BA)
wire         rxMoreFrag;                                             // More Frag bit of the received frame
wire  [15:0] rxFrameDuration;                                        // Frame duration
wire  [31:0] rxHTCtrl;                                               // HT control field of the received frame
wire         rxMoreData;                                             // More data
wire         rxOrder;                                                // Order
wire         rxRetry;                                                // Indicates than the received frame has its retry bit set.
wire         bcMcRcved;                                              // Indicates than the received frame has a group address.
wire         notMineRcved;                                           // Indicates than the received frame is not destined to this device.
wire         rxAMSDUPresent;                                         // RX A-MSDU Present
wire [1:0]   rxAckPolicy;                                            // RX Ack policy (Ack, No Ack, BA)
wire [3:0]   rxTID;                                                  // RX TID
wire         acceptACKInt;                                           // Accept ACK frames
wire         rxBWSignalingTA;                                        // Indicate that the received frame has a Bandwidth Signaling TA

// Interconnect between MAC Controller and deaggregator interface
wire         ampduCorrectRcved_p;                                    // A-MPDU received correctly
wire         ampduIncorrectRcved_p;                                  // A-MPDU not received correctly
wire         rxSingleVHTMPDU;                                        // Detect EOF bit in AMPDU delimiter for a Single VHT MPDU 
wire         rxVector1Start_p;                                       // Indicate that the first byte of RX Vector has been received
wire   [5:0] rxMPDUCnt;                                              // Count the number of MPDU detected
wire   [7:0] incorrectDelCnt;                                        // Count the number of incorrect delimiter

// Interconnect between MAC Controller and Key Search Engine
wire  [47:0] macAddressKSR;                                          // MAC Addr returned by Key Search Engine
wire   [9:0] txKeySearchIndex;                                       // RAM Index to be searched
wire         txKeySearchIndexTrig_p;                                 // Trigger for searching RAM index and return contents (along with MAC addr)
wire   [9:0] keySearchIndex;                                         // RAM Index to be searched
wire         keySearchIndexTrig_p;                                   // Trigger for searching RAM index and return contents (along with MAC addr)

// Interconnect between RX Controller and NAV
wire         navClear_p;                                             // Clear NAV
wire         navUpdate_p;                                            // Update NAV with frame duration
wire         navCfpDurRemUpdate_p;                                   // Update NAV with CFP duration remaining
wire  [15:0] cfpDurRemaining;                                        // CFP duration remaining
wire         navLsigUpdate_p;                                        // Update NAV with LSIG TBD !!!

// Interconnect between MAC Timer unit and MAC Controller
wire  [15:0] frmDurWithoutMH;                                        // Indicates the duration if the Beacon or Probe Response from the end of the MAC header
wire         resetCommonCnt_p;                                       // Reset common count counter
wire         moveToActive_p;                                         // Core should now move to ACTIVE state
wire         moveToIdle_p;                                           // Core should now move to IDLE state
wire         noBeaconTxPeriod;                                       // Indicates that scheduled TX beacon will be suppressed
wire  [15:0] impQICnt;                                               // Quiet interval counter in 32 us
wire  [15:0] nextTBTTCnt;                                            // Next TBTT counter in 32 us
wire         tickEarlyTBTT_p;                                        // Pulse prior of tickTBTT_p
wire  [7:0]  sifsRemaining;                                          // us remaining before tick sifs pulse

// Interconnect between Doze Controller and MAC Controller
wire         moveToDoze_p;                                           // Core should now move to DOZE state
wire         dozeWakeUp_p;                                           // Wake up the Mac Controller 

// Interconnect between Doze Controller and MAC Timer unit
wire         wakeupListenInterval_p;                                 // Wakeup core at listen interval
wire         wakeupDTIM_p;                                           // Wakeup core at DTIM count null
wire         atimWindowOver_p;                                       // ATIM window over

// Interconnect between RX Controller and MAC Timer unit
wire         dtimUpdate_p;                                           // Update DTIM element
wire   [7:0] rxDtimCnt;                                              // DTIM counter received
wire         cfpUpdate_p;                                            // Update CFP element
wire   [7:0] rxCfpCnt;                                               // CFP counter received
wire         tsfUpdate_p;                                            // Update TSF
wire         tsfOffsetUpdate_p;                                      // Update TSF Offset
wire  [63:0] timeStamp;                                              // Timestamp
wire         olbcUpdate_p;                                           // Update OLBC counter
wire         lastRxWrong;                                            // Last received packet wrong

// Interconnect between RX Controller and Key Search Engine
wire   [9:0] rxKeyIndexReturn;                                       // Key Storage Index
wire  [47:0] macAddressIn;                                           // MAC address to be searched in RAM
wire         indexSearchTrig_p;                                      // Trigger for searching MAC address in RAM
wire         rxKeySearchIndexTrig_p;                                 // Trigger for searching parameter from index
wire   [9:0] rxKeySearchIndex;                                       // RAM Index to be searched

// Interconnect between RX Controller and Encryption Engine
wire         wepTkipPassed_p;                                        // Indicates WEP/TKIP decryption was a success
wire         wepTkipFailed_p;                                        // Indicates WEP/TKIP decryption was a failure
wire         ccmpPassed_p;                                           // Indicates CCMP description was a success
wire         ccmpFailed_p;                                           // Indicates CCMP description was a failure
wire [7:0]   plainDataOut;                                           // Decrypted data for writing into RX FIFO
wire         plainOutDataValid;                                      // Decrypted data valid
wire         plainOutDataEnd_p;                                      // End of Decrypted data pulse
wire         plainOutICVEnd_p;                                       // End of ICV field pulse
wire         plainOutFCSValid;                                       // FCS field valid
wire         rxControlIdle;                                          // RX Controller FSM in idle
reg          rxCsIsIdle;                                             // Signal to indicate whether core is in TX or RX mode
wire [47:0]  rxAddr1;                                                // Addr1
wire [23:0]  rxInitVector;                                           // IV
wire [47:0]  rxTkipSeqCntr;                                          // TKIP Sequence Counter for TKIP decryption
wire [15:0]  rxPayLoadLen;                                           // Frame length including ICV or MIC and FCS
wire         rxFifoReady;                                            // Flow control for receiving decrypted data
wire         rxError_p;                                              // Indicates received frame can be discarded
wire         encrRxBufFlush_p;                                       // Flush after end of reception
wire         initEncrRxCntrl_p;                                      // Starting decryption sequence
wire         rxCryptoKeyValid;                                       // Key validating signal
wire         nullKeyFound;                                           // Key search operation failed. Key not found in RAM
wire         encrBufferFull;                                         // Flag indicating the sattus of the encryption buffer
wire         pushRxDataInBuffer;                                     // Write pulse to Encryption buffer
wire [7:0]   wrDataToEncrBuffer;                                     // Write data to Encryption buffer
wire         rxCCMPAADwrEn_p;                                        // Write enable to CCMP for AAD writing
wire         writeFCSEn;                                             // Indication that FCS to be written in RX FIFO
wire         rxAddress4Pres;                                         // Rx flag indicating address 4 is present
wire         rxQoSFrame;                                             // Rx flag indicating the current frame is a QoS Frame

// Interconnect between RX Controller and A-MPDU Deaggregator
wire [11:0]  rxLegLength;                                            // Legacy length of received frame
wire [ 3:0]  rxLegRate;                                              // Legacy rate of received frame
wire [19:0]  rxHTLength;                                             // HT length of received frame
wire [ 6:0]  rxMCS;                                                  // MCS of received frame
wire         rxPreType;                                              // Preamble type of received frame
wire [ 2:0]  rxFormatMod;                                            // Format and modulation of received frame
wire [ 1:0]  rxChBW;                                                 // Channel bandwidth of received frame
wire         rxShortGI;                                              // Short Guard Interval of received frame
wire         rxSmoothing;                                            // Smoothing of received frame
wire         rxLSIGValid;                                            // L-SIG Valid of received frame of received frame
wire [ 1:0]  rxSTBC;                                                 // Space Time Block Coding of received frame
wire         rxSounding;                                             // Sounding of received frame
wire [ 1:0]  rxNumExtnSS;                                            // Number of Extension Spatial Streams of received frame
wire [ 1:0]  rxChBWInNonHT;                                          // Channel bandwidth in Non-HT extracted from the scrambler initialization sequence
wire         rxAggregation;                                          // MPDU aggregate of received frame
wire         rxFecCoding;                                            // FEC Coding of received frame
wire [ 2:0]  rxReserved1;                                            // Reserved of received frame
wire [ 7:0]  rxAntennaSet;                                           // Antenna set of received frame
wire [ 2:0]  rxnSTS;                                                 // nSTS Number of Spatial Steams of received frame
wire         rxDynBW;                                                // Dynamique Bandwidth of received frame
wire         rxDozeNotAllowed;                                       // TXOP PS not Allowed of received frame
wire [ 8:0]  rxPartialAID;                                           // rxPartialAID of received frame
wire [ 5:0]  rxGroupID;                                              // GroupID of received frame
wire [ 7:0]  rxRSSI1;                                                // RSSI for RxChain 1 of received frame
wire [ 7:0]  rxRSSI2;                                                // RSSI for RxChain 2 of received frame
wire [ 7:0]  rxRSSI3;                                                // RSSI for RxChain 3 of received frame
wire [ 7:0]  rxRSSI4;                                                // RSSI for RxChain 4 of received frame
wire [ 7:0]  rxReserved2;                                            // Reserved of received frame
wire [ 7:0]  rxRCPI;                                                 // Receive Channel Power Indicator of received frame
wire [ 7:0]  rxEVM1;                                                 // Error Vector Magnitude for space time stream 1 of received frame
wire [ 7:0]  rxEVM2;                                                 // Error Vector Magnitude for space time stream 2 of received frame
wire [ 7:0]  rxEVM3;                                                 // Error Vector Magnitude for space time stream 3 of received frame
wire [ 7:0]  rxEVM4;                                                 // Error Vector Magnitude for space time stream 4 of received frame
wire [ 7:0]  rxReserved3;                                            // Reserved of received frame
wire [ 7:0]  rxReserved4;                                            // Reserved of received frame
wire [ 7:0]  rxReserved5;                                            // Reserved of received frame
wire         rxVector1Valid_p;                                       // Rx vector 1 is available
wire         rxVector2Valid_p;                                       // Rx vector 2 is available
wire         rxEndOfFrame_p;                                         // Indicates the end of the frame in reception

wire   [7:0] rxData;                                                 // Rx data extracted from MAC-PHY interface FIFO
wire         rxDataValid;                                            // Rx data is valid
wire         rxDataStart_p;                                          // Start of data flow
wire         rxDataEnd_p;                                            // End of data flow
wire         rxDataError_p;                                          // Rx data error (length null)

wire  [15:0] rxByteCnt;                                              // Rx byte counter
wire  [15:0] rxMpduLength;                                           // Rx MPDU full length
wire         rxNDP;                                                  // Indicate that the received frame is a Null Data Packet
wire         correctDelimiter;                                       // Indicate that Correct delimiter is found
wire         rxCntrlReady;                                           // Rx controller ready to receive data
wire   [1:0] rxAMPDUCnt;                                             // Counter incremented at each A-MPDU reception

// Interconnect between RX Controller and BA Controller
wire         psBitmapUpdate_p;                                      // Update Bitmap request
wire         psBitmapDiscard_p;                                     // Discard Bitmap update request
wire         baEnable;                                              // Enable BA Controller procedure
wire         barRcved;                                              // BAR received
wire  [11:0] rxSN;                                                  // Sequence Number
wire  [11:0] rxBASSN;                                               // BA Starting Sequence Number
wire         rxQoSEnd_p;                                            // Rx QoS field end pulse

// Interconnect between RX Controller and FCS
wire         fcsStartRx_p;                                           // Start FCS calculation
wire         fcsEnableRx;                                            // Enable FCS

// Interconnect for FCS
wire         fcsOk;                                                  // FCS is ok
wire         fcsEnd_p;                                               // indicates the end of the transmission
wire         fcsBusy;                                                // indicates that the FCS block is busy cannot accept new data.
wire         fcsDOutValid;                                           // indicates that the fcsDOut is valid.
wire   [7:0] fcsDOut;                                                // Data from the FCS block

wire   [7:0] fcsDIn;                                                 // data input
wire         fcsDInValid;                                            // data input is valid

wire         fcsEnable;                                              // FCS enable
wire         fcsStart_p;                                             // Initialize CRC
wire         fcsShift;                                               // Shift CRC on fcsDOut controlled by TX Controller


wire         txRxn;                                                  // Indicates the mode between TX and Rx
                                                                     // 0 : RX
                                                                     // 1 : TX

// Interconnect between Key Search Engine and Crypto Engine
wire [2:0]   cTypeKSR;                                               // Cipher Type found at Index or value at
                                                                     // at MAC address found location
wire [3:0]   vlanIDKSR;                                              // Virtual LAN ID found at Index or value 
                                                                     // at MAC address found location
wire [1:0]   sppKSR;                                                 // SPP RAM value found at Index or value 
                                                                     // at MAC address found location
wire         useDefKeyKSR;                                           // Use Default Key Value found at Index 
                                                                     // or value at MAC address found location
wire         cLenKSR;                                                // Cipher length found at Index or value 
                                                                     // at MAC address found location
wire [127:0] cryptoKeyKSR;                                           // Value of crypto key at Index found

`ifdef RW_WAPI_EN
wire [127:0] cryptoIntKeyKSR;                                           // Value of integrity crypto key at Index found
`endif //RW_WAPI_EN                                                  

wire         rxKeyUseDefaultTrig_p;                                  // Tx search default key
wire   [5:0] rxKeyUseDefaultIndex;                                   // Tx search default index

wire         keyUseDefaultTrig_p;                                    // Tx search default key
wire   [5:0] keyUseDefaultIndex;                                     // Tx search default index

// Interconnect between BA Controller and Key Search Engine
wire                   [7:0] keyIndexReturnBA;                       // Returned Key Index
wire [`KEY_INDEX_WIDTH-1:0]  keyIndexReturn;                         // Returned Index
wire                         keyStorageValid_p;                      // Returned Index valid
wire                         keyStorageError_p;                      // Error indicating key NOT found / MAC address NOT found

// Interconnect between TX Controller and BA Controller
wire   [7:0] psBitmap;                                               // PS Bitmap field
wire         psBitmapValid;                                          // PS Bitmap field valid  
wire         psBitmapReady;                                          // PS Bitmap field request

// Interconnect between CSReg and Key Search Engine
wire [127:0] encrKeyRAM;                                             // Crypto key configured by software into Encryption registers
`ifdef RW_WAPI_EN
wire [127:0] encrIntKeyRAM;                                          // Integrity Crypto key configured by software into Encryption registers
`endif //RW_WAPI_EN
wire  [47:0] encrMACAddr;                                            // MAC address configured by software into Encryption registers
wire [`KEY_INDEX_WIDTH-1:0] keyIndexRAMInt;                          // Index of Key Storage RAM into which the encryption register contents are to be written
wire                        keyRegReadValid_p;                       // Pulse signal indicating completion of register read operation
wire  [47:0] encrMACAddrIn;                                          // Value of mac Addr read by register from KSRAM
wire [127:0] encrKeyRAMIn;                                           // Value of crypto key read by register from KSRAM
`ifdef RW_WAPI_EN
wire [127:0] encrIntKeyRAMIn;                                           // Value of crypto key read by register from KSRAM
`endif //RW_WAPI_EN
// Interconnect between MAC Controller and BackOff Module interface
wire         backOffDone_p;                                          // Indicates when a backOff has expired
wire  [15:0] acMOT;                                                  // Current AC Medium Occupancy timer
wire  [15:0] txOpLimit;                                              // Transmit Opportunity Limit for Current AC.
wire   [3:0] txDmaState;                                             // DMA state for the active channel.
wire         retryType;                                              // Indicates the type of retry
                                                                     //   0 : Short Retry Limit
                                                                     //   1 : Long Retry Limit
wire         txSuccessful_p;                                         // Indicates that the current frame has be correctly transmitted
wire         retry_p;                                                // Indicates that the current frame has to be retried
wire         retryLTReached_p;                                       // Indicates that the retry limit has been reached
wire         txInProgress;                                           // Tx Frame Exchange is ongoing
wire         endOfTxOp;                                              // Indicates the end of the TX OP.
wire         startTxFrameExGated;                                    // Start Transmission from register gated (set only when the startTxAC won the medium) 


// Interconnect between BackOff and MAC Timer Unit Module interface
wire  [ 7:0] slotCnt;                                                // Slot counter
wire         tickDMAEarlySlot_p;                                     // Pulse prior of tickEarlySlot_p
wire         tickEarlySlot_p;                                        // Pulse prior of tickSlot_p
wire         aifsFlag0;                                              // Flag when AIFS0 over
wire         aifsFlag1;                                              // Flag when AIFS1 over
wire         aifsFlag2;                                              // Flag when AIFS2 over
wire         aifsFlag3;                                              // Flag when AIFS3 over
wire         eifsFlag0;                                              // Flag when EIFS0 over
wire         eifsFlag1;                                              // Flag when EIFS1 over
wire         eifsFlag2;                                              // Flag when EIFS2 over
wire         eifsFlag3;                                              // Flag when EIFS3 over
wire  [11:0] aifsCnt0;                                               // AIFS0 counter
wire  [11:0] aifsCnt1;                                               // AIFS1 counter
wire  [11:0] aifsCnt2;                                               // AIFS2 counter
wire  [11:0] aifsCnt3;                                               // AIFS3 counter
wire         tickTBTT_p;                                             // Pulse every TBTTs
wire         tickSlot1us_p;                                          // Pulse every microseconds aligned on slotCnt
wire         tickDMAEarlyTBTT_p;                                     // Pulse prior of tickEarlyTBTT_p
wire         tickSlot_p;                                             // slot indicator      
wire         tickSlotTxController_p;                                 // slot indicator for the txController. This is tickSlot_p gated by txInProgress      


// Interconnect between NAV Module and MAC Controller
wire [15:0] ctsDuration;                                            // Indicates the duration of a CTS frame response of the received RTS
wire        ctsDurationValid_p;                                     // Indicates that the ctsDuration is valid
wire [15:0] ackDuration;                                            // Indicates the duration of a ACK frame response of the received PS-POLL
wire        ackDurationValid_p;                                     // Indicates that the ackDuration is valid
wire  [7:0] phyRxStartDelay;                                        // Receive Start Delay of the PHY

wire [15:0] navLsigDuration;                                         // Update NAV LSIG duration


// Interconnect between Time On Air Module and MAC Controller 
wire  [2:0] ppduPreTypeMC;                                           // PPDU Preamble Type from MAC Controller
                                                                     // This field indicates what type of preamble is
                                                                     wire [19:0] ppduLengthMC;                                            // PPDU Length from MAC Controller
                                                                     // This field gives the length of the PPDU for computing time on air.
wire  [6:0] ppduMCSIndexMC;                                          // PPDU LegRate or MCS Index from MAC Controller
                                                                     // This field indicates the rate at which this PPDU is transmitted. 
wire  [1:0] ppduBWMC;                                                // PPDU Bandwidth from MAC Controller
                                                                     // This field indicates that that the PPDU should be transmitted at 40 MHz.
wire  [1:0] ppduNumExtnSSMC;                                         // Number of Extension Spatial Streams      
wire  [1:0] ppduSTBCMC;                                              // Enable Space Time Block Coding          
wire        ppduShortGIMC;                                           // PPDU Short Guard Interval from MAC Controller
                                                                     // Indicates that the frame should be transmitted with Short GI.
wire        startComputationMC_p;                                    // Start Time on Air computation from MAC Controller
wire [15:0] timeOnAirMC;                                             // Time On Air result to MAC Controller
                                                                     // This field gives the time taken for frame transmission in microseconds (us)
                                                                     // computed from parameters given by the MAC Controller.
wire        timeOnAirValidMC;                                        // Time On Air Valid to MAC Controller
                                                                     // This field is set when the air time computation is completed.
wire        disambiguityMC;                                          // Value of the disambiguityBit in case of VHT frame with shortGI computed by the TxTimeCalculator
wire        woPreambleMC;                                            // Indicates that total duration should not include the preamble duration 

// Interconnect between MAC Timer unit and NAV
wire        channelBusy;                                             // Channel busy indicator
wire        channelIdle;                                             // channel idle indicator
wire        loadQuietDuration_p;                                     // load quiet duration
wire [15:0] quietDuration;                                           // quiet duration value
wire        channelToIdle_p;                                         // Channel idle pulse
wire        cfpOn;                                                   // CFP is in progress TBD
wire        rxDot11a;                                                // Last received packet is 802.11a
wire        navCfpMaxDurUpdate_p;                                    // Update NAV with CFP Max duration

// Internal Soft reset for mac core blocks
wire        intMacPIClkSoftRst_n;                                    // soft reset on PI Clk domain
wire        intMacWTClkSoftRst_n;                                    // soft reset on WT Clk domain
wire        intMacCoreClkSoftRst_n;                                  // soft reset on Core Clk domain

`ifdef RW_MAC_MIBCNTL_EN
// Mib controller interconnect between macController & MIB controller
wire [2 :0]   mibTIDIndex;                                           // If TIDN of the MIB is set to one then in that case address given out of RAM
                                                                     // shall be determined from tidIndex
wire          mibTrigger;                                            // Trigger From MAC to latch MIB fields at MIB-MAC interface

wire          mibdot11WEPExcludedCount;
wire          mibdot11FCSErrorCount;
wire          mibrwRxPHYErrorCount;
wire          mibrwQosUTransmittedMPDUCount;
wire          mibrwQosGTransmittedMPDUCount;
wire          mibdot11QosFailedCount;
wire          mibdot11QosRetryCount;
wire          mibdot11QosRTSSuccessCount;
wire          mibdot11QosRTSFailureCount;
wire          mibrwQosACKFailureCount;
wire          mibrwQosUReceivedMPDUCount;
wire          mibrwQosGReceivedMPDUCount;
wire          mibrwQosUReceivedOtherMPDU;
wire          mibdot11QosRetriesReceivedCount;
wire          mibrwUTransmittedAMSDUCount;
wire          mibrwGTransmittedAMSDUCount;
wire          mibdot11FailedAMSDUCount;
wire          mibdot11RetryAMSDUCount;
wire [15 : 0] mibdot11TransmittedOctetsInAMSDU;
wire          mibdot11AMSDUAckFailureCount;
wire          mibrwUReceivedAMSDUCount;
wire          mibrwGReceivedAMSDUCount;
wire          mibrwUReceivedOtherAMSDU;
wire [15 : 0] mibdot11ReceivedOctetsInAMSDUCount;
wire          mibdot11TransmittedAMPDUCount;
wire          mibdot11TransmittedMPDUInAMPDUCount;
wire [15 : 0] mibdot11TransmittedOctetsInAMPDUCount;
wire          mibrwUAMPDUReceivedCount;
wire          mibrwGAMPDUReceivedCount;
wire          mibrwOtherAMPDUReceivedCount;
wire          mibdot11MPDUInReceivedAMPDUCount;
wire [15 : 0] mibdot11ReceivedOctetsInAMPDUCount;
wire [7 : 0]  mibdot11AMPDUDelimiterCRCErrorCount;
wire          mibdot11ImplicitBARFailureCount;
wire          mibdot11ExplicitBARFailureCount;
wire          mibdot1120MHzFrameTransmittedCount;
wire          mibdot1140MHzFrameTransmittedCount;
wire          mibdot1180MHzFrameTransmittedCount;
wire          mibdot11160MHzFrameTransmittedCount;
wire          mibdot1120MHzFrameReceivedCount;
wire          mibdot1140MHzFrameReceivedCount;
wire          mibdot1180MHzFrameReceivedCount;
wire          mibdot11160MHzFrameReceivedCount;
wire          mibrw20MHzFailedTXOPCount;
wire          mibrw20MHzSuccessfulTXOPCount;
wire          mibrw40MHzFailedTXOPCount;
wire          mibrw40MHzSuccessfulTXOPCount;
wire          mibrw80MHzFailedTXOPCount;
wire          mibrw80MHzSuccessfulTXOPCount;
wire          mibrw160MHzFailedTXOPCount;
wire          mibrw160MHzSuccessfulTXOPCount;
wire          mibrwDynBWDropCount;
wire          mibrwStaBWFailedCount;
wire          mibdot11DualCTSSuccessCount;
wire          mibdot11STBCCTSSuccessCount;
wire          mibdot11STBCCTSFailureCount;
wire          mibdot11nonSTBCCTSSuccessCount;
wire          mibdot11nonSTBCCTSFailureCount;
wire          mibrwRxFIFOOverflowCount;
wire          mibrwTxUnderrunCount;
`endif // RW_MAC_MIBCNTL_EN

// Interconnect between BackOff & CSReg
wire         bckoffsetac3HasData;      
wire         bckoffsetac2HasData;      
wire         bckoffsetac1HasData;      
wire         bckoffsetac0HasData;      
wire         bckoffclearac3HasData;    
wire         bckoffclearac2HasData;    
wire         bckoffclearac1HasData;    
wire         bckoffclearac0HasData;    
wire         bckoffstatussetac3HasData;
wire         bckoffstatussetac2HasData;
wire         bckoffstatussetac1HasData;
wire         bckoffstatussetac0HasData;

// Interconnect between CSReg & MAC Controller
wire [3:0] nextStateCoreClkReg;
wire [1:0] txBWAfterDrop;

wire stopRxBackoff;

wire stopRxInt_p;
reg trigTxBcnDly;
reg trigTxAC3Dly;
reg trigTxAC2Dly;
reg trigTxAC1Dly;
reg trigTxAC0Dly;
wire trigTxBackoff;

wire intMacWTClkEn;                 // Clock Enable for macWTClk Clock
wire intMacCryptClkEn;              // Clock Enable for macCryptClk Clock

wire [6:0] debugPortAMPDURxC;
wire [6:0] debugPortAMPDUMC;

wire macCoreTxClkEnInt;
  
wire deaggregatorCsIsIdle;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// Soft reset for mac core blocks
assign intMacPIClkSoftRst_n   =  !hwFSMResetPIClk   && macPIClkSoftRst_n;
assign intMacWTClkSoftRst_n   =  !hwFSMResetWTClk   && macWTClkSoftRst_n;
assign intMacCoreClkSoftRst_n =  !hwFSMResetCoreClk && macCoreClkSoftRst_n;
assign macCoreTxClkSoftRst_n  =  intMacCoreClkSoftRst_n && !mpIfTxErr_p && !macPHYIFUnderRun;



//assign macPriClkEn    = 1'b1;     
//assign platformWakeUp = 1'b0; 
//assign macLPClkSwitch = 1'b0;  
//assign macWTClkEn    = intMacWTClkEn && macSecClkEn;
assign macWTClkEn    = macSecClkEn;
assign macCryptClkEn = intMacCryptClkEn && macSecClkEn;

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    macCoreRxClkEn <= 1'b1; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    macCoreRxClkEn <= 1'b1; 
  else
  begin 
    if (macPhyIfRxStart_p || !activeClkGating)
      macCoreRxClkEn <= 1'b1;
    else if (!macSecClkEn) 
      macCoreRxClkEn <= 1'b0;
    else if (rxCsIsIdle && deaggregatorCsIsIdle && rxFIFOEmptyWrClk && macPhyIfRxFifoEmpty) 
      macCoreRxClkEn <= 1'b0;
  end
end

assign macCoreTxClkEn = macSecClkEn && (!macCoreClkSoftRst_n || macCoreTxClkEnInt || trigTxBackoff);

assign mpIFClkEn      = macPriClkEn || !activeClkGating;

assign frameRxed_p = correctRcved_p || incorrectRcved_p;

assign txFIFORdFlush = retryFrame_p || (!trigTxAC0 && !trigTxAC1 && !trigTxAC2 && !trigTxAC3 && !trigTxBcn);


always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    trigTxAC0Dly <= 1'b0;
    trigTxAC1Dly <= 1'b0;
    trigTxAC2Dly <= 1'b0;
    trigTxAC3Dly <= 1'b0;
    trigTxBcnDly <= 1'b0;
  end
  else if (intMacCoreClkSoftRst_n == 1'b0)
  begin
    trigTxAC0Dly <= 1'b0;
    trigTxAC1Dly <= 1'b0;
    trigTxAC2Dly <= 1'b0;
    trigTxAC3Dly <= 1'b0;
    trigTxBcnDly <= 1'b0;
  end
  else 
  begin
    trigTxAC0Dly <= trigTxAC0;
    trigTxAC1Dly <= trigTxAC1;
    trigTxAC2Dly <= trigTxAC2;
    trigTxAC3Dly <= trigTxAC3;
    trigTxBcnDly <= trigTxBcn;
  end
end

// When the Backoff controller trigs the DMA, the RX is stopped to avoid beginning of
// a reception during the DMA processing.
assign stopRxBackoff = (trigTxAC0 || trigTxAC1 || trigTxAC2 || trigTxAC3 || trigTxBcn) && (!trigTxAC0Dly && !trigTxAC1Dly && !trigTxAC2Dly && !trigTxAC3Dly && !trigTxBcnDly);
assign trigTxBackoff = trigTxBcn | trigTxAC3 | trigTxAC2 | trigTxAC1 | trigTxAC0;


assign stopRx_p = stopRxInt_p || stopRxBackoff;

// !!! Auto instanciation does not work !!!
// Instanciation of txParametersCache
// Name of the instance : U_txParametersCache
// Name of the file containing this module : txParametersCache.v
txParametersCache U_txParametersCache (
		.macPITxClk                 (macPITxClk),
		.macPIClkHardRst_n          (macPIClkHardRst_n),
		.macPIClkSoftRst_n          (intMacPIClkSoftRst_n),
		.txCtrlRegWr                (txCtrlRegWr),
		.txCtrlRegData              (txCtrlRegData),
		.txCtrlRegPT                (txCtrlRegPT),
		.txCtrlRegHD                (txCtrlRegHD),
		.discardPrevHD_p            (discardPrevHD_p),
		.txCtrlRegBusy              (txCtrlRegBusy),
		.toggleHDSet_p              (txPCtoggleHDSet_p),
		.togglePTSet_p              (txPCtogglePTSet_p),
		.clearSets_p                (txPCclearSets_p),
		.txParameterHDReady_p       (txPCtxParameterHDReady_p),
		.txParameterPTReady_p       (txPCtxParameterPTReady_p),
		.txParameterNextPTReady_p   (txPCtxParameterNextPTReady_p),
		.nTxProtPT                  (txPCnTxProtPT),
		.nTxPT                      (txPCnTxPT),
		.shortGIPT                  (txPCshortGIPT),
    .txPwrLevelPT               (txPCtxPwrLevelPT),
    .txPwrLevelProtPT           (txPCtxPwrLevelProtPT),
		.stbcPT                     (txPCstbcPT),
		.fecCodingPT                (txPCfecCodingPT),
		.numExtnSSPT                (txPCnumExtnSSPT),
		.bfFrmExPT                  (txPCbfFrmExPT),
		.beamFormedPT               (txPCbeamFormedPT),
		.smmIndexPT                 (txPCsmmIndexPT),
		.antennaSetPT               (txPCantennaSetPT),
		.keySRAMIndex               (txPCkeySRAMIndex),
		.keySRAMIndexRA             (txPCkeySRAMIndexRA),
		.rtsThreshold               (txPCrtsThreshold),
		.shortRetryLimit            (txPCshortRetryLimit),
		.longRetryLimit             (txPClongRetryLimit),
		.aMPDUFrameLengthTx         (txPCaMPDUFrameLengthTx),
		.aMPDUOptFrameLength20Tx    (txPCaMPDUOptFrameLength20Tx),
		.aMPDUOptFrameLength40Tx    (txPCaMPDUOptFrameLength40Tx),
		.aMPDUOptFrameLength80Tx    (txPCaMPDUOptFrameLength80Tx),
		.txSingleVHTMPDU            (txPCtxSingleVHTMPDU),
		.MPDUFrameLengthTx          (txPCMPDUFrameLengthTx),
		.mcsIndex0ProtTx            (txPCmcsIndex0ProtTx),
		.mcsIndex0Tx                (txPCmcsIndex0Tx),
		.useRIFSTx                  (txPCuseRIFSTx),
		.continuousTx               (txPCcontinuousTx),
		.formatModProtTx            (txPCformatModProtTx),
		.formatModTx                (txPCformatModTx),
		.preTypeProtTx              (txPCpreTypeProtTx),
		.preTypeTx                  (txPCpreTypeTx),
		.bwProtTx                   (txPCbwProtTx),
		.bwTx                       (txPCbwTx),
		.partialAIDTx               (txPCpartialAIDTx),
		.groupIDTx                  (txPCgroupIDTx),
		.dozeNotAllowedTx           (txPCdozeNotAllowedTx),
		.dynBWTx                    (txPCdynBWTx),
		.useBWSignalingTx           (txPCuseBWSignalingTx),
		.smoothingProtTx            (txPCsmoothingProtTx),
		.smoothingTx                (txPCsmoothingTx),
		.soundingTx                 (txPCsoundingTx),
		.protFrmDur                 (txPCprotFrmDur),
		.writeACK                   (txPCwriteACK),
		.lowRateRetry               (txPClowRateRetry),
		.lstpProt                   (txPClstpProt),
		.lstp                       (txPClstp),
		.expectedAck                (txPCexpectedAck),
		.navProtFrmEx               (txPCnavProtFrmEx),
		.dontGenerateMH             (txPCdontGenerateMH),
		.dontEncrypt                (txPCdontEncrypt),
		.dontTouchFC                (txPCdontTouchFC),
		.dontTouchDur               (txPCdontTouchDur),
		.dontTouchQoS               (txPCdontTouchQoS),
		.dontTouchHTC               (txPCdontTouchHTC),
		.dontTouchTSF               (txPCdontTouchTSF),
		.dontTouchDTIM              (txPCdontTouchDTIM),
		.dontTouchFCS               (txPCdontTouchFCS),
		.underBASetup               (txPCunderBASetup),
		.aMPDUOut                   (txPCaMPDU),
		.whichDescriptor            (txPCwhichDescriptor),
		.nBlankMDelimiters          (txPCnBlankMDelimiters),
		.interruptEnTx              (txPCinterruptEnTx),
		.fcSubtype                  (txPCfcSubtype),
		.fcType                     (txPCfcType),
		.tsValid                    (txPCtsValid),
		.lifetimeExpired            (txPClifetimeExpired),
		.numMPDURetries             (txPCnumMPDURetriesTPC),
		.numRTSRetries              (txPCnumRTSRetriesTPC),
    .mediumTimeUsed             (txPCmediumTimeUsedTPC),
		.debugPortTxParametersCache (debugPortTxParametersCache)
		);

assign tickSlotTxController_p = tickSlot_p & txInProgress;
// Instanciation of txController
// Name of the instance : U_txController
// Name of the file containing this module : txController.v
txController U_txController (
    .macCoreClk                       (macCoreClk),
    .macCoreTxClk                     (macCoreTxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreTxClkSoftRst_n            (macCoreTxClkSoftRst_n),
		.sendData_p                       (sendData_p),
		.sendRTS_p                        (sendRTS_p),
		.sendCTS_p                        (sendCTS_p),
		.sendACK_p                        (sendACK_p),
		.sendCFEND_p                      (sendCFEND_p),
		.sendBA_p                         (sendBA_p),
		.skipMPDU_p                       (skipMPDU_p),
		.sendOnSIFS                       (sendOnSIFS),
		.sendOnPIFS                       (sendOnPIFS),
		.srcAddr                          (srcAddr),
		.destAddr                         (destAddr),
		.duration                         (duration),
		.retry                            (retry),
		.tsfDuration                      (tsfDuration),
		.txTID                            (txTID),
		.typeTx                           (typeTx),
		.typeTxValid                      (typeTxValid),
		.txAMSDUPresent                   (txAMSDUPresent),
		.txBcMc                           (txBcMc),
		.txMCS                            (txMCS),
		.txLegLength                      (txLegLength),
		.txLegRate                        (txLegRate),
		.txHTLength                       (txHTLength),
		.txSTBC                           (txSTBC),
		.txChBW                           (txChBW),
		.txDynBW                          (txDynBW),
		.txBWSignaling                    (txBWSignaling),
		.txDisambiguityBit                (txDisambiguityBit),
		.txResp                           (txResp),
		.txFromReg                        (txFromReg),
		.txFromHD                         (txFromHD),
		.txFromFifo                       (txFromFifo),
		.txCFEND                          (txCFEND),
		.txDone_p                         (txDone_p),
		.mpduDone_p                       (mpduDone_p),
		.sentCFEND                        (sentCFEND),
		.sentRTS                          (sentRTS),
		.sentBAReq                        (sentBAReq),
		.skipMPDUDone_p                   (skipMPDUDone_p),
		.cTypeRAM                         (cTypeKSR),
		.txCsIsIdle                       (txCsIsIdle),
		.txDataLength                     (tcPayLoadLen),
		.txCryptoKeyValid                 (txCryptoKeyValid),
		.txCCMPTKIPSeqCnt                 (tcSfc),
		.txPlainData                      (plainTxData),
		.txPlainDataValid                 (plainTxDataValid),
		.txPlainDataEnd                   (txPayLoadEnd_p),
		.txEncrData                       (txEncrData),
		.txEncrDataValid                  (txEncrDataValid),
		.txSBOXInit                       (txSBOXInit),
		.txSBOXInitDone                   (txSBOXInitDone),
		.txICVEnable                      (txICVEnable),
		.txWEP                            (txWEP),
		.txWEPIV                          (txWEPIV),
		.txWEPIVValid                     (txWEPIVValid),
		.txTKIP                           (txTKIP),
		.txCCMPBusy                       (txCCMPBusy),
		.txCCMPMicDone                    (txCCMPMicDone),
		.txCCMP                           (txCCMP),
		.txCCMPStart                      (txCCMPStart),
		.txCCMPHeaderValid                (txPushCCMPHdrInBuffer_p),
		.txCCMPDataValid                  (txCCMPDataWrEn_p),
		.txCCMPAdd4Pres                   (txAddress4Pres),
		.txCCMPQoSPres                    (txQoSFrame),
		.txCCMPAddr1                      (txAddr1),
		.txCCMPAddr2                      (txAddr2),
		.txCCMPHT                         (txCCMPHT),
`ifdef RW_WAPI_EN
    .txWAPI                           (txWAPI),            
    .txWAPIStart                      (txWAPIStart),
    .txWAPIMicDone                    (wpiDone_p),     
    .txWAPIBusy                       (txWAPIBusy),        
    .txWAPIFrameControl               (txWAPIFrameControl),
    .txWAPIAddr3                      (txWAPIAddr3),       
    .txWAPIAddr4                      (txWAPIAddr4),       
    .txWAPIQoSCF                      (txWAPIQoSCF),       
    .txWAPISeqControl                 (txWAPISeqControl),  
    .txWAPIKeyIdx                     (txWAPIKeyIdx),      
    .txWAPIPN                         (txWAPIPN),          
`endif //RW_WAPI_EN
		.fcsEnd_p                         (fcsEnd_p),
		.fcsBusy                          (fcsBusy),
		.fcsDOutValid                     (fcsDOutValid),
		.fcsDOut                          (fcsDOut),
		.fcsEnableTx                      (fcsEnableTx),
		.fcsStartTx_p                     (fcsStartTx_p),
		.fcsShiftTx                       (fcsShiftTx),
		.fcsDInValidTx                    (fcsDInValidTx),
		.fcsDInTx                         (fcsDInTx),
		.fcsPauseTx                       (fcsPauseTx),
		.txFIFOMPDUDelimiters             (txFIFOMPDUDelimiters),
		.txFIFORdData                     (txFIFORdData),
		.txFIFOEmpty                      (txFIFOEmpty),
		.txFIFODataValid                  (txFIFODataValid),
		.txFIFORead                       (txFIFORead),
		.txFIFOReadByFour                 (txFIFOReadByFour),
		.txFIFOReadByTwo                  (txFIFOReadByTwo),
		.txParameterHDReady_p             (txParameterHDReady_p),
		.MPDUFrameLengthTx                (MPDUFrameLengthTx),
		.useRIFSTx                        (useRIFSTx),
		.formatModProtTx                  (formatModProtTx),
		.formatModTx                      (formatModTx),
		.preTypeProtTx                    (preTypeProtTx),
		.preTypeTx                        (preTypeTx),
		.partialAIDTx                     (partialAIDTx),
		.groupIDTx                        (groupIDTx),
		.dozeNotAllowedTx                 (dozeNotAllowedTx),
		.smoothingProtTx                  (smoothingProtTx),
		.smoothingTx                      (smoothingTx),
		.soundingTx                       (soundingTx),
		.nTxProtPT                        (nTxProtPT),
		.nTxPT                            (nTxPT),
		.txShortGI                        (txShortGI),
		.txPwrLevelPT                     (txPwrLevelPT),
		.txPwrLevelProtPT                 (txPwrLevelProtPT),
		.stbcPT                           (stbcPT),
		.txFecCoding                      (txFecCoding),
		.numExtnSSPT                      (numExtnSSPT),
		.beamFormedPT                     (beamFormedPT),
		.smmIndexPT                       (smmIndexPT),
		.antennaSetPT                     (antennaSetPT),
		.dontGenerateMH                   (dontGenerateMH),
		.dontEncrypt                      (dontEncrypt),
		.dontTouchFC                      (dontTouchFC),
		.dontTouchDur                     (dontTouchDur),
		.dontTouchQoS                     (dontTouchQoS),
		.dontTouchHTC                     (dontTouchHTC),
		.dontTouchTSF                     (dontTouchTSF),
		.dontTouchDTIM                    (dontTouchDTIM),
		.dontTouchFCS                     (dontTouchFCS),
		.aMPDU                            (aMPDU),
		.whichDescriptor                  (whichDescriptor),
		.nBlankMDelimiters                (nBlankMDelimiters),
		.txSingleVHTMPDU                  (txSingleVHTMPDU),
		.respTxAntennaSet                 (respTxAntennaSet),
		.respTxSMMIndex                   (respTxSMMIndex),
		.respTxPreType                    (respTxPreType),
		.respTxFormatMod                  (respTxFormatMod),
		.respTxNumExtnSS                  (respTxNumExtnSS),
		.respTxFECCoding                  (respTxFECCoding),
		.respTxNTx                        (respTxNTx),
		.respTxShortGI                    (respTxShortGI),
		.rxTID                            (rxTID),
		.psBitmap                         (psBitmap),
		.psBitmapValid                    (psBitmapValid),
		.psBitmapReady                    (psBitmapReady),
		.tsf                              (tsfTimer),
		.tickSIFS_p                       (tickSIFS_p),
		.tickPIFS_p                       (tickPIFS_p),
		.tickSlot_p                       (tickSlotTxController_p),
		.dtimCnt                          (dtimCnt),
		.mpIfTxFifoFull                   (mpIfTxFifoFull),
		.mpIfTxErr_p                      (mpIfTxErr_p),
		.mpIfTxEn                         (mpIfTxEn),
		.macPhyIfRxCca                    (macPhyIfRxCca),
		.startTx_p                        (startTx_p),
		.stopTx_p                         (stopTx_p),
		.mpIfTxFifoData                   (mpIfTxFifoData),
		.mpIfTxFifoWrite                  (mpIfTxFifoWrite),
		.txPwrLevel                       (txPwrLevel),
		.chBW                             (chBW),
		.chOffset                         (chOffset),
		.smoothing                        (smoothing),
		.antennaSet                       (antennaSet),
		.beamFormed                       (beamFormed),
		.smmIndex                         (smmIndex),
		.mcs                              (mcs),
		.nSTS                             (nSTS),
		.preType                          (preType),
		.formatMod                        (formatMod),
		.numExtnSS                        (numExtnSS),
		.stbc                             (stbc),
		.disambiguityBit                  (disambiguityBit),
		.partialAID                       (partialAID),
		.groupID                          (groupID),
		.dozeNotAllowed                   (dozeNotAllowed),
		.fecCoding                        (fecCoding),
		.sounding                         (sounding),
		.legLength                        (legLength),
		.legRate                          (legRate),
		.service                          (service),
		.htLength                         (htLength),
		.nTx                              (nTx),
		.shortGI                          (shortGI),
		.aggreation                       (aggreation),
		.hwErr                            (hwErr),
		.bssID                            (bssID),
		.timOffset                        (timOffset),
		.pwrMgt                           (pwrMgt),
		.dsssMaxPwrLevel                  (dsssMaxPwrLevel),
		.ofdmMaxPwrLevel                  (ofdmMaxPwrLevel),
		.startTxSmoothing                 (startTxSmoothing),
		.startTxAntennaSet                (startTxAntennaSet),
		.startTxSMMIndex                  (startTxSMMIndex),
		.startTxPreType                   (startTxPreType),
		.startTxFormatMod                 (startTxFormatMod),
		.startTxNumExtnSS                 (startTxNumExtnSS),
		.bbServiceA                       (bbServiceA),
		.bbServiceB                       (bbServiceB),
		.startTxNTx                       (startTxNTx),
		.activeAC                         (activeAC),
		.txControlCs                      (txControlCs),
		.txControlLs                      (txControlLs),
		.debugPortTxFrameDebug1           (debugPortTxFrameDebug1),
		.debugPortTxFrameDebug2           (debugPortTxFrameDebug2)
		);

// Interconnect between Key Search Engine and TX Controller
assign cryptoKeySearchDone = keyStorageValid_p;

// Instanciation of macController
// Name of the instance : u_macController
// Name of the file containing this module : macController.v
macController U_macController (
		.macCoreClk                                 (macCoreClk),
		.macCoreClkHardRst_n                        (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n                        (intMacCoreClkSoftRst_n),
		.macCoreTxClkEn                             (macCoreTxClkEnInt),
		.statusUpdated_p                            (statusUpdated_p),
		.updateDMAStatus_p                          (updateDMAStatus_p),
		.swRTS_p                                    (swRTS_p),
		.txMpduDone_p                               (txMpduDone_p),
		.ampduFrm_p                                 (ampduFrm_p),
		.retryFrame_p                               (retryFrame_p),
		.mpduSuccess_p                              (mpduSuccess_p),
		.mpduFailed_p                               (mpduFailed_p),
		.rtsFailed_p                                (rtsFailed_p),
		.rtsSuccess_p                               (rtsSuccess_p),
		.retryLimitReached_p                        (retryLimitReached_p),
		.transmissionBW                             (transmissionBW),
		.whichDescriptorSW                          (whichDescriptorSW),
		.numMPDURetries                             (numMPDURetries),
		.numRTSRetries                              (numRTSRetries),
    .mediumTimeUsed                             (mediumTimeUsed),    
		.rxFrmDiscard                               (rxFrmDiscard),
		.txParameterHDReady_p                       (txParameterHDReady_p),
		.txParameterPTReady_p                       (txParameterPTReady_p),
		.txParameterNextPTReady_p                   (txParameterNextPTReady_p),
		.toggleHDSet_p                              (toggleHDSet_p),
		.togglePTSet_p                              (togglePTSet_p),
		.clearSets_p                                (clearSets_p),
		.protFrmDur                                 (protFrmDur),
		.writeACK                                   (writeACK),
		.lowRateRetry                               (lowRateRetry),
		.lstpProt                                   (lstpProt),
		.lstp                                       (lstp),
		.dontTouchDur                               (dontTouchDur),
		.expectedAck                                (expectedAck),
		.navProtFrmEx                               (navProtFrmEx),
		.useRIFSTx                                  (useRIFSTx),
		.formatModProtTx                            (formatModProtTx),
		.formatModTx                                (formatModTx),
		.preTypeProtTx                              (preTypeProtTx),
		.preTypeTx                                  (preTypeTx),
		.bwProtTx                                   (bwProtTx),
		.bwTx                                       (bwTx),
		.dynBWTx                                    (dynBWTx),
		.useBWSignalingTx                           (useBWSignalingTx),
		.smoothingProtTx                            (smoothingProtTx),
		.smoothingTx                                (smoothingTx),
		.soundingTx                                 (soundingTx),
		.nTxProtPT                                  (nTxProtPT),
		.nTxPT                                      (nTxPT),
		.shortGIPT                                  (shortGIPT),
		.fecCodingPT                                (fecCodingPT),
		.stbcPT                                     (stbcPT),
		.numExtnSSPT                                (numExtnSSPT),
		.smmIndexPT                                 (smmIndexPT),
		.keySRAMIndex                               (keySRAMIndex),
		.keySRAMIndexRA                             (keySRAMIndexRA),
		.aMPDU                                      (aMPDU),
		.txSingleVHTMPDU                            (txSingleVHTMPDU),
		.whichDescriptor                            (whichDescriptor),
		.fcSubtype                                  (fcSubtype),
		.fcType                                     (fcType),
		.tsValid                                    (tsValid),
		.rtsThreshold                               (rtsThreshold),
		.shortRetryLimit                            (shortRetryLimit),
		.longRetryLimit                             (longRetryLimit),
		.aMPDUFrameLengthTx                         (aMPDUFrameLengthTx),
		.aMPDUOptFrameLength20Tx                    (aMPDUOptFrameLength20Tx),
		.aMPDUOptFrameLength40Tx                    (aMPDUOptFrameLength40Tx),
		.aMPDUOptFrameLength80Tx                    (aMPDUOptFrameLength80Tx),
		.MPDUFrameLengthTx                          (MPDUFrameLengthTx),
    .mediumTimeUsedTPC                          (mediumTimeUsedTPC),
		.mcsIndex0ProtTx                            (mcsIndex0ProtTx),
		.mcsIndex0Tx                                (mcsIndex0Tx),
		.numMPDURetriesTPC                          (numMPDURetriesTPC),
		.numRTSRetriesTPC                           (numRTSRetriesTPC),
		.sendData_p                                 (sendData_p),
		.sendRTS_p                                  (sendRTS_p),
		.sendCTS_p                                  (sendCTS_p),
		.sendACK_p                                  (sendACK_p),
		.sendCFEND_p                                (sendCFEND_p),
		.sendBA_p                                   (sendBA_p),
		.sendOnSIFS                                 (sendOnSIFS),
		.sendOnPIFS                                 (sendOnPIFS),
		.skipMPDU_p                                 (skipMPDU_p),
		.srcAddr                                    (srcAddr),
		.destAddr                                   (destAddr),
		.duration                                   (duration),
		.retry                                      (retry),
		.tsfDuration                                (tsfDuration),
		.txMCS                                      (txMCS),
		.txLegLength                                (txLegLength),
		.txLegRate                                  (txLegRate),
		.txHTLength                                 (txHTLength),
		.txSTBC                                     (txSTBC),
		.txDisambiguityBit                          (txDisambiguityBit),
		.txChBW                                     (txChBW),
		.txDynBW                                    (txDynBW),
		.txBWSignaling                              (txBWSignaling),
		.txResp                                     (txResp),
		.txFromReg                                  (txFromReg),
		.txFromHD                                   (txFromHD),
		.txFromFifo                                 (txFromFifo),
		.txCFEND                                    (txCFEND),
		.txRxn                                      (txRxn),
		.txFecCoding                                (txFecCoding),
		.txShortGI                                  (txShortGI),
		.txDone_p                                   (txDone_p),
		.txTID                                      (txTID),
		.typeTx                                     (typeTx),
		.typeTxValid                                (typeTxValid),
		.txAMSDUPresent                             (txAMSDUPresent),
		.txBcMc                                     (txBcMc),
		.sentCFEND                                  (sentCFEND),
		.sentRTS                                    (sentRTS),
		.sentBAReq                                  (sentBAReq),
		.startTx_p                                  (startTx_p),
		.mpduDone_p                                 (mpduDone_p),
		.skipMPDUDone_p                             (skipMPDUDone_p),
		.respTxAntennaSet                           (respTxAntennaSet),
		.respTxSMMIndex                             (respTxSMMIndex),
		.respTxPreType                              (respTxPreType),
		.respTxFormatMod                            (respTxFormatMod),
		.respTxNumExtnSS                            (respTxNumExtnSS),
		.respTxFECCoding                            (respTxFECCoding),
		.respTxNTx                                  (respTxNTx),
		.respTxShortGI                              (respTxShortGI),
		.stopRx_p                                   (stopRxInt_p),
		.trigTxBackoff                              (trigTxBackoff),
		.activeRx                                   (activeRx),
		.rxAck                                      (rxAck),
		.rxBA                                       (rxBA),
		.rxCts                                      (rxCts),
		.forceWriteACK                              (forceWriteACK),
		.lSIGTXOPDetected                           (lSIGTXOPDetected),
		.dataFrame                                  (dataFrame),
		.reservedRcved                              (reservedRcved),
		.ackRcved_p                                 (ackRcved_p),
		.rtsRcved_p                                 (rtsRcved_p),
		.ctsRcved_p                                 (ctsRcved_p),
		.cfEndRcved_p                               (cfEndRcved_p),
		.baRcved_p                                  (baRcved_p),
		.barRcved_p                                 (barRcved_p),
		.needAckRcved_p                             (needAckRcved_p),
		.bcMcRcved_p                                (bcMcRcved_p),
		.bcnRcved_p                                 (bcnRcved_p),
		.probRespRcved_p                            (probRespRcved_p),
		.notMineRcved_p                             (notMineRcved_p),
		.notMineRtsRcved_p                          (notMineRtsRcved_p),
		.notMinePsPollRcved_p                       (notMinePsPollRcved_p),
		.unknownRcved_p                             (unknownRcved_p),
    .rxFCType                                   (rxFCType),
		.macHeaderCompleted                         (macHeaderCompleted),
		.incorrectRcved_p                           (incorrectRcved_p),
		.correctRcved_p                             (correctRcved_p),
		.rxCsIsIdle                                 (rxCsIsIdle),
		.rxAddr1                                    (rxAddr1),
		.rxAddr2                                    (rxAddr2),
		.rxMoreFrag                                 (rxMoreFrag),
		.rxAckPolicy                                (rxAckPolicy),
		.rxFrameDuration                            (rxFrameDuration),
		.rxHTCtrl                                   (rxHTCtrl),
		.rxTID                                      (rxTID),
		.rxAMSDUPresent                             (rxAMSDUPresent),
		.rxRetry                                    (rxRetry),
		.bcMcRcved                                  (bcMcRcved),
		.notMineRcved                               (notMineRcved),
		.rxBWSignalingTA                            (rxBWSignalingTA),
		.rxLegLength                                (rxLegLength),
		.rxHTLength                                 (rxHTLength[15:0]),
		.rxLegRate                                  (rxLegRate),
		.rxMCS                                      (rxMCS),
		.rxPreType                                  (rxPreType),
		.rxFormatMod                                (rxFormatMod),
		.rxDynBW                                    (rxDynBW),
		.rxSTBC                                     (rxSTBC),
		.rxChBW                                     (rxChBW),
		.rxShortGI                                  (rxShortGI),
		.rxLSIGValid                                (rxLSIGValid),
		.rxNumExtnSS                                (rxNumExtnSS),
		.rxChBWInNonHT                              (rxChBWInNonHT),
		.rxFecCoding                                (rxFecCoding),
		.rxAggregation                              (rxAggregation),
		.rxAntennaSet                               (rxAntennaSet),
		.ampduCorrectRcved_p                        (ampduCorrectRcved_p),
		.ampduIncorrectRcved_p                      (ampduIncorrectRcved_p),
		.rxSingleVHTMPDU                            (rxSingleVHTMPDU),
		.rxVector1Valid_p                           (rxVector1Valid_p),
		.rxEndOfFrame_p                             (rxEndOfFrame_p),
		.rxVector1Start_p                           (rxVector1Start_p),
		.rxMPDUCnt                                  (rxMPDUCnt),
		.incorrectDelCnt                            (incorrectDelCnt),
		.startRx                                    (startRx),
		.mpIfTxErr_p                                (mpIfTxErr_p),
		.macPhyIfRxCca                              (macPhyIfRxCca),
		.macPhyIfRxStart_p                          (macPhyIfRxStart_p),
		.macPhyIfRxErr_p                            (macPhyIfRxErr_p),
		.macPhyIfRxEnd_p                            (macPhyIfRxEnd_p),
		.macPhyIfRxFlush_p                          (macPhyIfRxFlush_p),
		.macPHYIFUnderRun                           (macPHYIFUnderRun),
		.macPhyIfRxEndForTiming_p                   (macPhyIfRxEndForTiming_p),
		.macPhyIfRifsRxDetected                     (macPhyIfRifsRxDetected),
		.mpifKeepRFon                               (mpifKeepRFon),
		.macAddressKSR                              (macAddressKSR),
		.txKeySearchIndexTrig_p                     (txKeySearchIndexTrig_p),
		.txKeySearchIndex                           (txKeySearchIndex),
		.txDmaState                                 (txDmaState),
		.txOpLimit                                  (txOpLimit),
		.backOffDone_p                              (backOffDone_p),
		.trigTxBcn                                  (trigTxBcn),
		.acMOT                                      (acMOT),
		.retryType                                  (retryType),
		.txSuccessful_p                             (txSuccessful_p),
		.retry_p                                    (retry_p),
		.retryLTReached_p                           (retryLTReached_p),
		.txInProgress                               (txInProgress),
		.endOfTxOp                                  (endOfTxOp),
		.timeOnAirMC                                (timeOnAirMC),
		.timeOnAirValidMC                           (timeOnAirValidMC),
		.disambiguityMC                             (disambiguityMC),
		.ppduLengthMC                               (ppduLengthMC),
		.ppduBWMC                                   (ppduBWMC),
		.ppduPreTypeMC                              (ppduPreTypeMC),
		.ppduNumExtnSSMC                            (ppduNumExtnSSMC),
		.ppduSTBCMC                                 (ppduSTBCMC),
		.ppduShortGIMC                              (ppduShortGIMC),
		.ppduMCSIndexMC                             (ppduMCSIndexMC),
		.woPreambleMC                               (woPreambleMC),
		.startComputationMC_p                       (startComputationMC_p),
		.tick1us_p                                  (tick1us_p),
		.impQICnt                                   (impQICnt),
		.sec20ChannelIdleFlag                       (sec20ChannelIdleFlag),
		.sec40ChannelIdleFlag                       (sec40ChannelIdleFlag),
		.sec80ChannelIdleFlag                       (sec80ChannelIdleFlag),
		.tickPIFS_p                                 (tickPIFS_p),
		.rifsTO_p                                   (rifsTO_p),
		.sifsRemaining                              (sifsRemaining),
		.frmDurWithoutMH                            (frmDurWithoutMH),
		.respTO_p                                   (respTO_p),
		.resetCommonCnt_p                           (resetCommonCnt_p),
		.moveToActive_p                             (moveToActive_p),
		.moveToIdle_p                               (moveToIdle_p),
		.channelBusy                                (channelBusy),
		.ctsDuration                                (ctsDuration),
		.ctsDurationValid_p                         (ctsDurationValid_p),
		.ackDuration                                (ackDuration),
		.ackDurationValid_p                         (ackDurationValid_p),
		.phyRxStartDelay                            (phyRxStartDelay),
		.navLsigDuration                            (navLsigDuration),
		.dozeWakeUp_p                               (dozeWakeUp_p),
		.moveToDoze_p                               (moveToDoze_p),
`ifdef RW_MAC_MIBCNTL_EN
		.mibdot11WEPExcludedCount                   (mibdot11WEPExcludedCount),
		.mibdot11FCSErrorCount                      (mibdot11FCSErrorCount),
		.mibrwRxPHYErrorCount                       (mibrwRxPHYErrorCount),
		.mibrwRxFIFOOverflowCount                   (mibrwRxFIFOOverflowCount),
		.mibrwTxUnderrunCount                       (mibrwTxUnderrunCount),
		.mibrwQosUTransmittedMPDUCount              (mibrwQosUTransmittedMPDUCount),
		.mibrwQosGTransmittedMPDUCount              (mibrwQosGTransmittedMPDUCount),
		.mibdot11QosFailedCount                     (mibdot11QosFailedCount),
		.mibdot11QosRetryCount                      (mibdot11QosRetryCount),
		.mibdot11QosRTSSuccessCount                 (mibdot11QosRTSSuccessCount),
		.mibdot11QosRTSFailureCount                 (mibdot11QosRTSFailureCount),
		.mibrwQosACKFailureCount                    (mibrwQosACKFailureCount),
		.mibrwQosUReceivedMPDUCount                 (mibrwQosUReceivedMPDUCount),
		.mibrwQosGReceivedMPDUCount                 (mibrwQosGReceivedMPDUCount),
		.mibrwQosUReceivedOtherMPDU                 (mibrwQosUReceivedOtherMPDU),
		.mibdot11QosRetriesReceivedCount            (mibdot11QosRetriesReceivedCount),
		.mibrwUTransmittedAMSDUCount                (mibrwUTransmittedAMSDUCount),
		.mibrwGTransmittedAMSDUCount                (mibrwGTransmittedAMSDUCount),
		.mibdot11FailedAMSDUCount                   (mibdot11FailedAMSDUCount),
		.mibdot11RetryAMSDUCount                    (mibdot11RetryAMSDUCount),
		.mibdot11TransmittedOctetsInAMSDU           (mibdot11TransmittedOctetsInAMSDU),
		.mibdot11AMSDUAckFailureCount               (mibdot11AMSDUAckFailureCount),
		.mibrwUReceivedAMSDUCount                   (mibrwUReceivedAMSDUCount),
		.mibrwGReceivedAMSDUCount                   (mibrwGReceivedAMSDUCount),
		.mibrwUReceivedOtherAMSDU                   (mibrwUReceivedOtherAMSDU),
		.mibdot11ReceivedOctetsInAMSDUCount         (mibdot11ReceivedOctetsInAMSDUCount),
		.mibdot11TransmittedAMPDUCount              (mibdot11TransmittedAMPDUCount),
		.mibdot11TransmittedMPDUInAMPDUCount        (mibdot11TransmittedMPDUInAMPDUCount),
		.mibdot11TransmittedOctetsInAMPDUCount      (mibdot11TransmittedOctetsInAMPDUCount),
		.mibrwUAMPDUReceivedCount                   (mibrwUAMPDUReceivedCount),
		.mibrwGAMPDUReceivedCount                   (mibrwGAMPDUReceivedCount),
		.mibrwOtherAMPDUReceivedCount               (mibrwOtherAMPDUReceivedCount),
		.mibdot11MPDUInReceivedAMPDUCount           (mibdot11MPDUInReceivedAMPDUCount),
		.mibdot11ReceivedOctetsInAMPDUCount         (mibdot11ReceivedOctetsInAMPDUCount),
		.mibdot11AMPDUDelimiterCRCErrorCount        (mibdot11AMPDUDelimiterCRCErrorCount),
		.mibdot11ImplicitBARFailureCount            (mibdot11ImplicitBARFailureCount),
		.mibdot11ExplicitBARFailureCount            (mibdot11ExplicitBARFailureCount),
		.mibdot1120MHzFrameTransmittedCount         (mibdot1120MHzFrameTransmittedCount),
		.mibdot1140MHzFrameTransmittedCount         (mibdot1140MHzFrameTransmittedCount),
		.mibdot1180MHzFrameTransmittedCount         (mibdot1180MHzFrameTransmittedCount),
		.mibdot11160MHzFrameTransmittedCount        (mibdot11160MHzFrameTransmittedCount),
		.mibdot1120MHzFrameReceivedCount            (mibdot1120MHzFrameReceivedCount),
		.mibdot1140MHzFrameReceivedCount            (mibdot1140MHzFrameReceivedCount),
		.mibdot1180MHzFrameReceivedCount            (mibdot1180MHzFrameReceivedCount),
		.mibdot11160MHzFrameReceivedCount           (mibdot11160MHzFrameReceivedCount),
		.mibrw20MHzFailedTXOPCount                  (mibrw20MHzFailedTXOPCount),
		.mibrw20MHzSuccessfulTXOPCount              (mibrw20MHzSuccessfulTXOPCount),
		.mibrw40MHzFailedTXOPCount                  (mibrw40MHzFailedTXOPCount),
		.mibrw40MHzSuccessfulTXOPCount              (mibrw40MHzSuccessfulTXOPCount),
		.mibrw80MHzFailedTXOPCount                  (mibrw80MHzFailedTXOPCount),
		.mibrw80MHzSuccessfulTXOPCount              (mibrw80MHzSuccessfulTXOPCount),
		.mibrw160MHzFailedTXOPCount                 (mibrw160MHzFailedTXOPCount),
		.mibrw160MHzSuccessfulTXOPCount             (mibrw160MHzSuccessfulTXOPCount),
		.mibrwDynBWDropCount                        (mibrwDynBWDropCount),
		.mibrwStaBWFailedCount                      (mibrwStaBWFailedCount),
		.mibdot11DualCTSSuccessCount                (mibdot11DualCTSSuccessCount),
		.mibdot11STBCCTSSuccessCount                (mibdot11STBCCTSSuccessCount),
		.mibdot11STBCCTSFailureCount                (mibdot11STBCCTSFailureCount),
		.mibdot11nonSTBCCTSSuccessCount             (mibdot11nonSTBCCTSSuccessCount),
		.mibdot11nonSTBCCTSFailureCount             (mibdot11nonSTBCCTSFailureCount),
		.mibTIDIndex                                (mibTIDIndex),
		.mibTrigger                                 (mibTrigger),
`endif // RW_MAC_MIBCNTL_EN
		.txopComplete                               (txopComplete),
		.acBWDropTrigger                            (acBWDropTrigger),
		.idleInterrupt                              (idleInterrupt),
		.hwErr                                      (hwErr),
`ifdef RW_WLAN_COEX_EN                
    .coexEnable                                 (coexEnable),
    .coexPTIBKData                              (coexPTIBKData),
    .coexPTIBEData                              (coexPTIBEData),
    .coexPTIVIData                              (coexPTIVIData),
    .coexPTIVOData                              (coexPTIVOData),
    .coexPTIBcnData                             (coexPTIBcnData),
    .coexPTIMgt                                 (coexPTIMgt),
    .coexPTICntl                                (coexPTICntl),
    .coexPTIAck                                 (coexPTIAck),
    .coexWlanTx                                 (coexWlanTx),
    .coexWlanRx                                 (coexWlanRx),
    .coexWlanTxAbort                            (coexWlanTxAbort),
    .coexWlanPTI                                (coexWlanPTI),
    .coexWlanPTIToggle                          (coexWlanPTIToggle),
    .coexWlanChanBw                             (coexWlanChanBw),
    .trigTxAC0                                  (trigTxAC0),
    .trigTxAC1                                  (trigTxAC1),
    .trigTxAC2                                  (trigTxAC2),
    .trigTxAC3                                  (trigTxAC3),
`endif // RW_WLAN_COEX_EN                
		.currentState                               (currentState),
		.nextState                                  (nextState),
		.nextStateIn                                (nextStateIn),
		.nextStateInValid                           (nextStateInValid),
		.bssBasicRateSet                            (bssBasicRateSet),
		.bssBasicHTMCSSetEM                         (bssBasicHTMCSSetEM),
		.bssBasicHTMCSSetUM                         (bssBasicHTMCSSetUM),
		.bssBasicVHTMCSSet                          (bssBasicVHTMCSSet),
		.slotTime                                   (slotTime),
		.rxStartDelayMIMO                           (rxStartDelayMIMO),
		.rxStartDelayShort                          (rxStartDelayShort),
		.rxStartDelayLong                           (rxStartDelayLong),
		.rxStartDelayOFDM                           (rxStartDelayOFDM),
		.ap                                         (ap),
		.bssType                                    (bssType),
		.rxRIFSEn                                   (rxRIFSEn),
		.bssID                                      (bssID),
		.macAddr                                    (macAddr),
		.cfEndSTBCDur                               (cfEndSTBCDur),
		.ctsSTBCDur                                 (ctsSTBCDur),
		.dualCTSProt                                (dualCTSProt),
		.basicSTBCMCS                               (basicSTBCMCS),
		.sifsA                                      (sifsA),
		.sifsB                                      (sifsB),
		.startTxFrameExGated                        (startTxFrameExGated),
		.startTxFrameExIn                           (startTxFrameExIn),
		.startTxFrameExInValid                      (startTxFrameExInValid),
		.startTxFrmExType                           (startTxFrmExType),
		.startTxKSRIndex                            (startTxKSRIndex),
		.startTxFormatMod                           (startTxFormatMod),
		.startTxMCSIndex0                           (startTxMCSIndex0),
		.startTxPreType                             (startTxPreType),
		.startTxBW                                  (startTxBW),
		.durControlFrm                              (durControlFrm),
		.startTxNumExtnSS                           (startTxNumExtnSS),
		.startTxSTBC                                (startTxSTBC),
		.startTxLSTP                                (startTxLSTP),
		.startTxShortGI                             (startTxShortGI),
		.startTxFecCoding                           (startTxFecCoding),
		.dynBWEn                                    (dynBWEn),
		.dropToLowerBW                              (dropToLowerBW),
		.numTryBWAcquisition                        (numTryBWAcquisition),
		.defaultBWTXOP                              (defaultBWTXOP),
		.defaultBWTXOPV                             (defaultBWTXOPV),
		.aPPDUMaxTime                               (aPPDUMaxTime),
		.maxSupportedBW                             (maxSupportedBW),
    .txBWAfterDrop                              (txBWAfterDrop),
		.supportLSTP                                (supportLSTP),
		.activeClkGating                            (activeClkGating),
		.disableACKResp                             (disableACKResp),
		.disableCTSResp                             (disableCTSResp),
		.disableBAResp                              (disableBAResp),
		.keepTXOPOpen                               (keepTXOPOpen),
		.remTXOPInDurField                          (remTXOPInDurField),
		.sendCFEnd                                  (sendCFEnd),
		.sendCFEndNow                               (sendCFEndNow),
		.sendCFEndNowInValid                        (sendCFEndNowInValid),
		.sendCFEndNowIn                             (sendCFEndNowIn),
		.debugPortMACController1                    (debugPortMACController1),
		.debugPortMACControllerRx                   (debugPortMACControllerRx),
		.debugPortMACControllerTx                   (debugPortMACControllerTx),
		.debugPortBWManagement                      (debugPortBWManagement),
		.debugPortAMPDUMC                           (debugPortAMPDUMC),
		.macControlCs                               (macControlCs),
		.macControlLs                               (macControlLs)
		);
    
assign ac3BWDropTrigger = trigTxAC3 && acBWDropTrigger;
assign ac2BWDropTrigger = trigTxAC2 && acBWDropTrigger;
assign ac1BWDropTrigger = trigTxAC1 && acBWDropTrigger;
assign ac0BWDropTrigger = trigTxAC0 && acBWDropTrigger;

// !!! Auto instanciation does not work !!!
// Instanciation of backoff
// Name of the instance : U_backoff
// Name of the file containing this module : backoff.v
backoff U_backoff (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n    (intMacCoreClkSoftRst_n),
		.acMOT                  (acMOT),
		.retryType              (retryType),
		.retry_p                (retry_p),
		.txSuccessful_p         (txSuccessful_p),
		.retryLTReached_p       (retryLTReached_p),
		.txInProgress           (txInProgress),
		.txDmaState             (txDmaState),
		.txOpLimit              (txOpLimit),
		.backOffDone_p          (backOffDone_p),
		.startTxFrameExGated    (startTxFrameExGated),
		.bcnRcved_p             (bcnRcved_p),
		.trigTxAC0              (trigTxAC0),
		.trigTxAC1              (trigTxAC1),
		.trigTxAC2              (trigTxAC2),
		.trigTxAC3              (trigTxAC3),
		.trigTxBcn              (trigTxBcn),
		.ac3ProtTrigger         (ac3ProtTrigger),
		.ac2ProtTrigger         (ac2ProtTrigger),
		.ac1ProtTrigger         (ac1ProtTrigger),
		.ac0ProtTrigger         (ac0ProtTrigger),
		.ap                     (ap),
		.currentState           (currentState),
		.cwMax0                 (cwMax0),
		.cwMin0                 (cwMin0),
		.cwMax1                 (cwMax1),
		.cwMin1                 (cwMin1),
		.cwMax2                 (cwMax2),
		.cwMin2                 (cwMin2),
		.cwMax3                 (cwMax3),
		.cwMin3                 (cwMin3),
		.txAC3State             (txAC3StateMC),
		.txAC2State             (txAC2StateMC),
		.txAC1State             (txAC1StateMC),
		.txAC0State             (txAC0StateMC),
		.txBcnState             (txBcnStateMC),
		.startTxFrameEx         (startTxFrameEx),
		.startTxAC              (startTxAC),
		.bssType                (bssType),
		.hccaTriggerTimer       (hccaTriggerTimer),
		.edcaTriggerTimer       (edcaTriggerTimer),
		.noBeaconTxPeriod       (noBeaconTxPeriod),
		.slotTime               (slotTime),
		.txOpLimit0             (txOpLimit0),
		.txOpLimit1             (txOpLimit1),
		.txOpLimit2             (txOpLimit2),
		.txOpLimit3             (txOpLimit3),
		.setac3HasData          (bckoffsetac3HasData),
		.setac2HasData          (bckoffsetac2HasData),
		.setac1HasData          (bckoffsetac1HasData),
		.setac0HasData          (bckoffsetac0HasData),
		.clearac3HasData        (bckoffclearac3HasData),
		.clearac2HasData        (bckoffclearac2HasData),
		.clearac1HasData        (bckoffclearac1HasData),
		.clearac0HasData        (bckoffclearac0HasData),
		.statussetac3HasData    (bckoffstatussetac3HasData),
		.statussetac2HasData    (bckoffstatussetac2HasData),
		.statussetac1HasData    (bckoffstatussetac1HasData),
		.statussetac0HasData    (bckoffstatussetac0HasData),
		.backoffOffset          (backoffOffset),
		.currentCW0             (currentCW0),
		.currentCW1             (currentCW1),
		.currentCW2             (currentCW2),
		.currentCW3             (currentCW3),
		.ac1MOT                 (ac1MOT),
		.ac0MOT                 (ac0MOT),
		.ac3MOT                 (ac3MOT),
		.ac2MOT                 (ac2MOT),
		.ac3QSRC                (ac3QSRC),
		.ac2QSRC                (ac2QSRC),
		.ac1QSRC                (ac1QSRC),
		.ac0QSRC                (ac0QSRC),
		.ac3QLRC                (ac3QLRC),
		.ac2QLRC                (ac2QLRC),
		.ac1QLRC                (ac1QLRC),
		.ac0QLRC                (ac0QLRC),
		.activeAC               (activeAC),
		.macPhyIfRxCca          (macPhyIfRxCca),
		.channelBusy            (channelBusy),
  `ifdef RW_WLAN_COEX_EN                
    .coexWlanTxAbort        (coexWlanTxAbort),
  `endif // RW_WLAN_COEX_EN                
		.slotCnt                (slotCnt),
		.tickDMAEarlySlot_p     (tickDMAEarlySlot_p),
		.tickEarlySlot_p        (tickEarlySlot_p),
		.aifsFlag0              (aifsFlag0),
		.aifsFlag1              (aifsFlag1),
		.aifsFlag2              (aifsFlag2),
		.aifsFlag3              (aifsFlag3),
		.eifsFlag0              (eifsFlag0),
		.eifsFlag1              (eifsFlag1),
		.eifsFlag2              (eifsFlag2),
		.eifsFlag3              (eifsFlag3),
		.aifsCnt0               (aifsCnt0),
		.aifsCnt1               (aifsCnt1),
		.aifsCnt2               (aifsCnt2),
		.aifsCnt3               (aifsCnt3),
		.tickEarlyTBTT_p        (tickEarlyTBTT_p),
		.tickDMAEarlyTBTT_p     (tickDMAEarlyTBTT_p),
		.tickSlot1us_p          (tickSlot1us_p), // TBD
		.tickSlot_p             (tickSlot_p),
		.debugPortBackoff       (debugPortBackoff),
		.debugPortBackoff2      (debugPortBackoff2),
		.debugPortBackoff3      (debugPortBackoff3)
    );


// Instanciation of txTimeCalculator
// Name of the instance : U_txTimeCalculator
// Name of the file containing this module : txTimeCalculator.v
txTimeCalculatorAC U_txTimeCalculator (
    .macPIClk                         (macPISlaveClk),
    .macPIClkHardRst_n                (macPIClkHardRst_n),
    .macCoreClk                       (macCoreClk),
    .macCoreClkHardRst_n              (macCoreClkHardRst_n),
    .disambiguityMC                   (disambiguityMC),
    .ppduLengthMC                     (ppduLengthMC),
    .ppduChBwMC                       (ppduBWMC),
    .ppduPreTypeMC                    (ppduPreTypeMC),
    .ppduNumExtnSSMC                  (ppduNumExtnSSMC),
    .ppduSTBCMC                       (ppduSTBCMC),
    .ppduShortGIMC                    (ppduShortGIMC),
    .ppduMCSIndexMC                   (ppduMCSIndexMC),
    .woPreambleMC                     (woPreambleMC),
    .startComputationMC_p             (startComputationMC_p),
    .timeOnAirMC                      (timeOnAirMC),
    .timeOnAirValidMC                 (timeOnAirValidMC),
    .ppduLength                       (ppduLength),
    .ppduChBw                         (ppduBW),
    .ppduPreType                      (ppduPreType),
    .ppduNumExtnSS                    (ppduNumExtnSS),
    .ppduSTBC                         (ppduSTBC),
    .ppduShortGI                      (ppduShortGI),
    .ppduMCSIndex                     (ppduMCSIndex),
    .computeDuration                  (computeDuration),
    .computeDurationIn                (computeDurationIn),
    .computeDurationInValid           (computeDurationInValid),
    .timeOnAir                        (timeOnAir),
    .timeOnAirValid                   (timeOnAirValid)
    );

// Instanciation of baController
// Name of the instance : U_baController
// Name of the file containing this module : baController.v
baController	U_baController(
		.macCoreClk                       (macCoreClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (intMacCoreClkSoftRst_n),
		.psBitmapReady                    (psBitmapReady),
		.psBitmap                         (psBitmap),
		.psBitmapValid                    (psBitmapValid),
		.psBitmapUpdate_p                 (psBitmapUpdate_p),
		.psBitmapDiscard_p                (psBitmapDiscard_p),
		.rxQoSEnd_p                       (rxQoSEnd_p),
    .barRcved_p                       (barRcved_p),
		.baEnable                         (baEnable),
		.barRcved                         (barRcved),
		.rxTID                            (rxTID),
		.rxSN                             (rxSN),
		.rxBASSN                          (rxBASSN),
		.keyIndexReturnBA                 (keyIndexReturnBA),
		.keyStorageValid_p                (keyStorageValid_p),
		.keyStorageError_p                (keyStorageError_p),
		.baPSBitmapReset                  (baPSBitmapReset),
		.baPSBitmapResetIn                (baPSBitmapResetIn),
		.baPSBitmapResetInValid           (baPSBitmapResetInValid),
		.psBitmapReadData                 (psBitmapReadData),
		.psBitmapEn                       (psBitmapEn),
		.psBitmapWriteEn                  (psBitmapWriteEn),
		.psBitmapAddr                     (psBitmapAddr),
		.psBitmapWriteData                (psBitmapWriteData),
		.debugPortBAController            (debugPortBAController),
		.debugPortBAController2           (debugPortBAController2),
		.debugPortBAController3           (debugPortBAController3)
		);

// Interconnect between baController and keySearchEngine
assign keyIndexReturnBA = {2'b0, keyIndexReturn};


// Instanciation of rxController
// Name of the instance : U_rxController
// Name of the file containing this module : rxController.v
rxController U_rxController (
		.macCoreRxClk                     (macCoreRxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
    .macCoreClkSoftRst_n              (intMacCoreClkSoftRst_n),
		.rxFrmDiscard                     (rxFrmDiscard),
    .rxDescAvailable                  (rxDescAvailable),
		.stopRx_p                         (stopRx_p),
		.activeRx                         (activeRx),
    .rxAck                            (rxAck),
    .rxBA                             (rxBA),
		.rxCts                            (rxCts),
		.lSIGTXOPDetected                 (lSIGTXOPDetected),
		.txInProgress                     (txInProgress),
		.dataFrame                        (dataFrame),
		.reservedRcved                    (reservedRcved),
		.ackRcved_p                       (ackRcved_p),
		.rtsRcved_p                       (rtsRcved_p),
		.ctsRcved_p                       (ctsRcved_p),
		.cfEndRcved_p                     (cfEndRcved_p),
		.baRcved_p                        (baRcved_p),
		.barRcved_p                       (barRcved_p),
		.needAckRcved_p                   (needAckRcved_p),
		.bcMcRcved_p                      (bcMcRcved_p),
		.bcnRcved_p                       (bcnRcved_p),
		.probRespRcved_p                  (probRespRcved_p),
		.notMineRcved_p                   (notMineRcved_p),
		.unknownRcved_p                   (unknownRcved_p),
		.macHeaderCompleted               (macHeaderCompleted),
    .rxFCType                         (rxFCType),
		.notMinePsPollRcved_p             (notMinePsPollRcved_p),
		.notMineRtsRcved_p                (notMineRtsRcved_p),
		.correctRcved_p                   (correctRcved_p),
		.incorrectRcved_p                 (incorrectRcved_p),
		.rxAddr2                          (rxAddr2),
`ifdef RW_WAPI_EN
    .rxFrmCtrl                        (rxFrmCtrl),     
    .rxAddr3                          (rxAddr3),       
    .rxAddr4                          (rxAddr4),       
    .rxQoSControl                     (rxQoSControl),  
    .rxSeqCtrl                        (rxSeqCtrl),     
    .rxWAPIKeyIndex                   (rxWAPIKeyIndex),
    .rxWAPIPN                         (rxWAPIPN),      
`endif //RW_WAPI_EN
		.rxAMSDUPresent                   (rxAMSDUPresent),
		.rxAckPolicy                      (rxAckPolicy),
		.rxTID                            (rxTID),
		.rxHTCtrl                         (rxHTCtrl),
		.rxMoreFrag                       (rxMoreFrag),
		.rxMoreData                       (rxMoreData),
		.rxOrder                          (rxOrder),
		.rxRetry                          (rxRetry),
		.bcMcRcved                        (bcMcRcved),
		.notMineRcved                     (notMineRcved),
		.rxBWSignalingTA                  (rxBWSignalingTA),
		.mpIfTxEn                         (mpIfTxEn),
		.backOffDone_p                    (backOffDone_p),
		.activeAC                         (activeAC),
		.timWakeUp                        (timWakeUp),
		.timSleep                         (timSleep),
		.navClear_p                       (navClear_p),
		.navUpdate_p                      (navUpdate_p),
		.rxFrameDuration                  (rxFrameDuration),
		.navCfpDurRemUpdate_p             (navCfpDurRemUpdate_p),
		.cfpDurRemaining                  (cfpDurRemaining),
		.navLsigUpdate_p                  (navLsigUpdate_p),
		.dtimUpdate_p                     (dtimUpdate_p),
		.dtimCnt                          (rxDtimCnt),
		.cfpUpdate_p                      (cfpUpdate_p),
		.cfpCnt                           (rxCfpCnt),
		.tsfUpdate_p                      (tsfUpdate_p),
		.tsfOffsetUpdate_p                (tsfOffsetUpdate_p),
		.timeStamp                        (timeStamp),
		.olbcUpdate_p                     (olbcUpdate_p),
 		.lastRxWrong                      (lastRxWrong),
		.wepTkipPassed_p                  (wepTkipPassed_p),
		.wepTkipFailed_p                  (wepTkipFailed_p),
		.ccmpPassed_p                     (ccmpPassed_p),
		.ccmpFailed_p                     (ccmpFailed_p),
`ifdef RW_WAPI_EN
    .rxWAPI                           (rxWAPI),        
    .wapiPassed_p                     (wapiPassed_p),
    .wapiFailed_p                     (wapiFailed_p),
`endif //RW_WAPI_EN
		.plainDataOut                     (plainDataOut),
		.plainOutDataValid                (plainOutDataValid),
		.plainOutDataEnd_p                (plainOutDataEnd_p),
		.plainOutICVEnd_p                 (plainOutICVEnd_p),
		.plainOutFCSValid                 (plainOutFCSValid),
		.rxControlIdle                    (rxControlIdle),
		.rxAddr1                          (rxAddr1),
		.rxInitVector                     (rxInitVector),
		.rxTkipSeqCntr                    (rxTkipSeqCntr),
		.rxPayLoadLen                     (rxPayLoadLen),
		.rxAddress4Pres                   (rxAddress4Pres),
		.rxQoSFrame                       (rxQoSFrame),
		.rxFifoReady                      (rxFifoReady),
		.rxError_p                        (rxError_p),
		.encrRxBufFlush_p                 (encrRxBufFlush_p),
		.initEncrRxCntrl_p                (initEncrRxCntrl_p),
		.rxCryptoKeyValid                 (rxCryptoKeyValid),
		.encrBufferFull                   (encrBufferFull),
		.nullKeyFound                     (nullKeyFound),
		.pushRxDataInBuffer               (pushRxDataInBuffer),
		.wrDataToEncrBuffer               (wrDataToEncrBuffer),
		.rxCCMPAADwrEn_p                  (rxCCMPAADwrEn_p),
		.keyStorageValid_p                (keyStorageValid_p),
		.keyStorageError_p                (keyStorageError_p),
		.rxKeyIndexReturn                 (rxKeyIndexReturn),
		.sppKSR                           (sppKSR),
		.cTypeKSR                         (cTypeKSR),
		.vlanIDKSR                        (vlanIDKSR),
		.useDefKeyKSR                     (useDefKeyKSR),
		.indexSearchTrig_p                (indexSearchTrig_p),
		.rxKeySearchIndexTrig_p           (rxKeySearchIndexTrig_p),
		.rxKeySearchIndex                 (rxKeySearchIndex),
		.macPhyIfRxErr_p                  (macPhyIfRxErr_p),
		.macPhyIfRxEndForTiming_p         (macPhyIfRxEndForTiming_p),
		.macPHYIFOverflow                 (macPHYIFOverflow),
		.rxLegLength                      (rxLegLength),
		.rxLegRate                        (rxLegRate),
		.rxHTLength                       (rxHTLength),
		.rxMCS                            (rxMCS),
		.rxPreType                        (rxPreType),
		.rxFormatMod                      (rxFormatMod),
		.rxChBW                           (rxChBW),
		.rxShortGI                        (rxShortGI),
		.rxSmoothing                      (rxSmoothing),
		.rxLSIGValid                      (rxLSIGValid),
		.rxSTBC                           (rxSTBC),
		.rxSounding                       (rxSounding),
		.rxNumExtnSS                      (rxNumExtnSS),
		.rxAggregation                    (rxAggregation),
		.rxFecCoding                      (rxFecCoding),
		.rxReserved1                      (rxReserved1),
		.rxAntennaSet                     (rxAntennaSet),
		.rxnSTS                           (rxnSTS),
		.rxDynBW                          (rxDynBW),
		.rxDozeNotAllowed                 (rxDozeNotAllowed),
		.rxPartialAID                     (rxPartialAID),
		.rxGroupID                        (rxGroupID),
		.rxRSSI1                          (rxRSSI1),
		.rxRSSI2                          (rxRSSI2),
		.rxRSSI3                          (rxRSSI3),
		.rxRSSI4                          (rxRSSI4),
		.rxReserved2                      (rxReserved2),
		.rxRCPI                           (rxRCPI),
		.rxEVM1                           (rxEVM1),
		.rxEVM2                           (rxEVM2),
		.rxEVM3                           (rxEVM3),
		.rxEVM4                           (rxEVM4),
		.rxReserved3                      (rxReserved3),
		.rxReserved4                      (rxReserved4),
		.rxReserved5                      (rxReserved5),
		.rxVector1Valid_p                 (rxVector1Valid_p),
		.rxVector2Valid_p                 (rxVector2Valid_p),
		.rxData                           (rxData),
		.rxDataValid                      (rxDataValid),
		.rxDataStart_p                    (rxDataStart_p),
		.rxDataEnd_p                      (rxDataEnd_p),
		.rxDataError_p                    (rxDataError_p),
		.rxEndOfFrame_p                   (rxEndOfFrame_p),
		.ampduIncorrectRcved_p            (ampduIncorrectRcved_p),
		.rxByteCnt                        (rxByteCnt),
		.rxMpduLength                     (rxMpduLength),
		.rxNDP                            (rxNDP),
		.correctDelimiter                 (correctDelimiter),
		.rxAMPDUCnt                       (rxAMPDUCnt),
		.rxMPDUCnt                        (rxMPDUCnt),
		.rxCntrlReady                     (rxCntrlReady),
		.psBitmapUpdate_p                 (psBitmapUpdate_p),
		.psBitmapDiscard_p                (psBitmapDiscard_p),
		.rxQoSEnd_p                       (rxQoSEnd_p),
		.baEnable                         (baEnable),
		.barRcved                         (barRcved),
		.rxSN                             (rxSN),
		.rxBASSN                          (rxBASSN),
		.currentState                     (currentState),
		.bssType                          (bssType),
		.ap                               (ap),
		.tsfMgtDisable                    (tsfMgtDisable),
		.tsfTimerHigh                     (tsfTimer[63:32]),
		.tsfTimerLow                      (tsfTimer[31:0]),
		.macAddr                          (macAddr),
		.macAddrMask                      (macAddrMask),
		.bssID                            (bssID),
		.bssIDMask                        (bssIDMask),
		.excUnencrypted                   (excUnencrypted),
		.dontDecrypt                      (dontDecrypt),
		.acceptMulticast                  (acceptMulticast),
		.acceptBroadcast                  (acceptBroadcast),
		.acceptOtherBSSID                 (acceptOtherBSSID),
		.acceptErrorFrames                (acceptErrorFrames),
		.acceptUnicast                    (acceptUnicast),
		.acceptMyUnicast                  (acceptMyUnicast),
		.acceptProbeReq                   (acceptProbeReq),
		.acceptProbeResp                  (acceptProbeResp),
		.acceptBeacon                     (acceptBeacon),
		.acceptAllBeacon                  (acceptAllBeacon),
		.acceptOtherMgmtFrames            (acceptOtherMgmtFrames),
		.acceptBAR                        (acceptBAR),
		.acceptBA                         (acceptBA),
		.acceptNotExpectedBA              (acceptNotExpectedBA),
		.acceptDecryptErrorFrames         (acceptDecryptErrorFrames),
		.acceptPSPoll                     (acceptPSPoll),
		.acceptRTS                        (acceptRTS),
		.acceptCTS                        (acceptCTS),
		.acceptACK                        (acceptACKInt),
		.acceptCFEnd                      (acceptCFEnd),
		.acceptOtherCntrlFrames           (acceptOtherCntrlFrames),
		.acceptData                       (acceptData),
		.acceptCFWOData                   (acceptCFWOData),
		.acceptQData                      (acceptQData),
		.acceptQCFWOData                  (acceptQCFWOData),
		.acceptQoSNull                    (acceptQoSNull),
		.acceptOtherDataFrames            (acceptOtherDataFrames),
		.acceptUnknown                    (acceptUnknown),
		.quietCount1In                    (quietCount1In),
		.quietPeriod1In                   (quietPeriod1In),
		.quietDuration1In                 (quietDuration1In),
		.quietOffset1In                   (quietOffset1In),
		.quietElement1InValid             (quietElement1InValid),
		.quietCount2In                    (quietCount2In),
		.quietPeriod2In                   (quietPeriod2In),
		.quietDuration2In                 (quietDuration2In),
		.quietOffset2In                   (quietOffset2In),
		.quietElement2InValid             (quietElement2InValid),
		.dtimPeriodIn                     (dtimPeriodIn),
		.dtimPeriodInValid                (dtimPeriodInValid),
		.cfpPeriodIn                      (cfpPeriodIn),
		.cfpPeriodInValid                 (cfpPeriodInValid),
		.dynBWEn                          (dynBWEn),
		.rxControlLs                      (rxControlLs),
		.rxControlCs                      (rxControlCs),
		.rxFIFOAlmostFull                 (rxFIFOAlmostFull),
		.rxFIFOFull                       (rxFIFOFull),
		.rxFIFOWrTag                      (rxFIFOWrTag),
		.rxFIFOWrData                     (rxFIFOWrData),
		.rxFIFOWrite                      (rxFIFOWrite),
		.rxFIFOOverFlow                   (rxFIFOOverFlow),
		.baRxTrigger                      (baRxTrigger),
		.hwErr                            (hwErr),
		.fcsOk                            (fcsOk),
		.fcsStartRx_p                     (fcsStartRx_p),
		.fcsEnableRx                      (fcsEnableRx),
		.debugPortRxController            (debugPortRxController),
		.debugPortAMPDURxC                (debugPortAMPDURxC),
		.debugPortRxFrameDebug1           (debugPortRxFrameDebug1),
		.debugPortRxFrameDebug2           (debugPortRxFrameDebug2),
		.debugPortrxFIFOCntrl             (debugPortrxFIFOCntrl),
		.debugPortDecryptFsm              (debugPortDecryptFsm)
		);

assign acceptACKInt = forceWriteACK || acceptACK;

// Interconnect between rxController and Key Search Engine
assign rxKeyIndexReturn = {4'b0, keyIndexReturn};

// TBD Interconnect between rxController and Encryption Engine
assign writeFCSEn        = 1'b1;

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    rxCsIsIdle <= 1'b0;
  else
    rxCsIsIdle <= rxControlIdle;
end

// Instanciation of macTimerUnit
// Name of the instance : U_macTimerUnit
// Name of the file containing this module : macTimerUnit.v
macTimerUnit U_macTimerUnit (
		.macCoreClk                       (macCoreClk),
		.macLPClk                         (macLPClk),
		.macLPClkSwitch                   (macLPClkSwitch),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (macCoreClkSoftRst_n),
		.sentCFEND                        (sentCFEND),
		.txDone_p                         (txDone_p),
		.mpIfTxEn                         (mpIfTxEn),
		.sec20ChannelIdleFlag             (sec20ChannelIdleFlag),
		.sec40ChannelIdleFlag             (sec40ChannelIdleFlag),
		.sec80ChannelIdleFlag             (sec80ChannelIdleFlag),
		.dtimCnt                          (dtimCnt),
		.cfpCnt                           (cfpCnt),
		.dtimUpdate_p                     (dtimUpdate_p),
		.rxDtimCnt                        (rxDtimCnt),
		.cfpUpdate_p                      (cfpUpdate_p),
		.rxCfpCnt                         (rxCfpCnt),
		.tsfUpdate_p                      (tsfUpdate_p),
		.tsfOffsetUpdate_p                (tsfOffsetUpdate_p),
		.timeStamp                        (timeStamp),
		.cfEndRcved_p                     (cfEndRcved_p),
		.rxTrig_p                         (rxTrig_p),
		.olbcUpdate_p                     (olbcUpdate_p),
		.lastRxWrong                      (lastRxWrong),
		.quietElement1InValid             (quietElement1InValid),
		.quietElement2InValid             (quietElement2InValid),
		.macPhyIfRxEndForTiming_p         (macPhyIfRxEndForTiming_p),
		.macPhyIfRxCca                    (macPhyIfRxCca),
		.macPhyIfRxCcaSec20               (macPhyIfRxCcaSec20),
		.macPhyIfRxCcaSec40               (macPhyIfRxCcaSec40),
		.macPhyIfRxCcaSec80               (macPhyIfRxCcaSec80),
		.channelToIdle_p                  (channelToIdle_p),
		.channelBusy                      (channelBusy),
		.cfpOn                            (cfpOn),
		.rxDot11a                         (rxDot11a),
		.navCfpMaxDurUpdate_p             (navCfpMaxDurUpdate_p),
		.loadQuietDuration_p              (loadQuietDuration_p),
		.quietDuration                    (quietDuration),
		.rxLegRate                        (rxLegRate),
		.rxFormatMod                      (rxFormatMod),
		.rxDataStart_p                    (rxDataStart_p),
		.frmDurWithoutMH                  (frmDurWithoutMH),
		.resetCommonCnt_p                 (resetCommonCnt_p),
		.moveToActive_p                   (moveToActive_p),
		.moveToIdle_p                     (moveToIdle_p),
		.respTO_p                         (respTO_p),
		.noBeaconTxPeriod                 (noBeaconTxPeriod),
		.impQICnt                         (impQICnt),
		.nextTBTTCnt                      (nextTBTTCnt),
		.tickDMAEarlyTBTT_p               (tickDMAEarlyTBTT_p),
		.tickEarlyTBTT_p                  (tickEarlyTBTT_p),
		.sifsRemaining                    (sifsRemaining),
		.hwFSMReset                       (hwFSMResetCoreClk),
		.currentState                     (currentState),
		.listenInterval                   (listenInterval),
		.wakeupDTIM                       (wakeupDTIM),
		.atimWAutoWakeUpTO                (atimW),
		.bssType                          (bssType),
		.ap                               (ap),
		.abgnMode                         (abgnMode),
		.cfpAware                         (cfpAware),
		.rxRIFSEn                         (rxRIFSEn),
		.beaconInt                        (beaconInt),
		.impTBTTPeriod                    (impTBTTPeriod),
		.impTBTTIn128Us                   (impTBTTIn128Us),
		.noBcnTxTime                      (noBcnTxTime),
		.dtimPeriod                       (dtimPeriod),
		.cfpPeriod                        (cfpPeriod),
		.dtimUpdatedBySW                  (dtimUpdatedBySW),
		.tsfTimerHigh                     (tsfTimerHigh),
		.tsfTimerLow                      (tsfTimerLow),
		.tsfUpdatedBySW                   (tsfUpdatedBySW),
		.olbcTimer                        (olbcTimer),
		.ofdmCount                        (ofdmCount),
		.dsssCount                        (dsssCount),
		.macCoreClkFreq                   (macCoreClkFreq),
		.txRFDelayInMACClk                (txRFDelayInMACClk),
		.txChainDelayInMACClk             (txChainDelayInMACClk),
		.slotTime                         (slotTime),
		.slotTimeInMACClk                 (slotTimeInMACClk),
		.macProcDelayInMACClk             (macProcDelayInMACClk),
		.txDelayRFOnInMACClk              (txDelayRFOnInMACClk),
		.rxRFDelayInMACClk                (rxRFDelayInMACClk),
		.rxCCADelay                       (rxCCADelay),
		.radioWakeUpTime                  (radioWakeUpTime),
		.sifsBInMACClk                    (sifsBInMACClk),
		.sifsAInMACClk                    (sifsAInMACClk),
		.sifsB                            (sifsB),
		.sifsA                            (sifsA),
		.txDMAProcDlyInMACClk             (txDMAProcDlyInMACClk),
		.rifsTOInMACClk                   (rifsTOInMACClk),
		.rifsInMACClk                     (rifsInMACClk),
		.txAbsoluteTimeout                (txAbsoluteTimeout),
		.txPacketTimeout                  (txPacketTimeout),
		.rxAbsoluteTimeout                (rxAbsoluteTimeout),
		.rxPacketTimeout                  (rxPacketTimeout),
		.aifsn0                           (aifsn0),
		.aifsn1                           (aifsn1),
		.aifsn2                           (aifsn2),
		.aifsn3                           (aifsn3),
		.quietCount1                      (quietCount1),
		.quietPeriod1                     (quietPeriod1),
		.quietDuration1                   (quietDuration1),
		.quietOffset1                     (quietOffset1),
		.quietCount2                      (quietCount2),
		.quietPeriod2                     (quietPeriod2),
		.quietDuration2                   (quietDuration2),
		.quietOffset2                     (quietOffset2),
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
		.monotonicCounter1                (monotonicCounter1),
		.monotonicCounterLow2             (monotonicCounterLow2),
		.monotonicCounterHigh2            (monotonicCounterHigh2),
		.ccaBusyDur                       (ccaBusyDur),
		.ccaBusyDurIn                     (ccaBusyDurIn),
		.ccaBusyDurInValid                (ccaBusyDurInValid),
		.ccaBusyDurSec20                  (ccaBusyDurSec20),
		.ccaBusyDurSec20In                (ccaBusyDurSec20In),
		.ccaBusyDurSec20InValid           (ccaBusyDurSec20InValid),
		.ccaBusyDurSec40                  (ccaBusyDurSec40),
		.ccaBusyDurSec40In                (ccaBusyDurSec40In),
		.ccaBusyDurSec40InValid           (ccaBusyDurSec40InValid),
		.ccaBusyDurSec80                  (ccaBusyDurSec80),
		.ccaBusyDurSec80In                (ccaBusyDurSec80In),
		.ccaBusyDurSec80InValid           (ccaBusyDurSec80InValid),
		.dtimUpdatedBySWIn                (dtimUpdatedBySWIn),
		.dtimUpdatedBySWInValid           (dtimUpdatedBySWInValid),
		.tsfTimer                         (tsfTimer),
		.tsfUpdatedBySWIn                 (tsfUpdatedBySWIn),
		.tsfUpdatedBySWInValid            (tsfUpdatedBySWInValid),
		.olbcOFDM                         (olbcOFDM),
		.olbcDSSS                         (olbcDSSS),
		.impPriTBTT                       (impPriTBTT),
		.impSecTBTT                       (impSecTBTT),
		.impPriDTIM                       (impPriDTIM),
		.impSecDTIM                       (impSecDTIM),
		.timerTxTrigger                   (timerTxTrigger),
		.timerRxTrigger                   (timerRxTrigger),
		.absTimers                        (absTimers),
		.tickDMAEarlySlot_p               (tickDMAEarlySlot_p),
		.tickEarlySlot_p                  (tickEarlySlot_p),
		.tickSlot_p                       (tickSlot_p),
		.slotCnt                          (slotCnt),
		.tickRIFS_p                       (tickRIFS_p),
		.tickSIFS_p                       (tickSIFS_p),
		.tickPIFS_p                       (tickPIFS_p),
		.rifsTO_p                         (rifsTO_p),
		.aifsCnt0                         (aifsCnt0),
		.aifsCnt1                         (aifsCnt1),
		.aifsCnt2                         (aifsCnt2),
		.aifsCnt3                         (aifsCnt3),
		.aifsFlag0                        (aifsFlag0),
		.aifsFlag1                        (aifsFlag1),
		.aifsFlag2                        (aifsFlag2),
		.aifsFlag3                        (aifsFlag3),
		.eifsFlag0                        (eifsFlag0),
		.eifsFlag1                        (eifsFlag1),
		.eifsFlag2                        (eifsFlag2),
		.eifsFlag3                        (eifsFlag3),
		.tickTBTT_p                       (tickTBTT_p),
		.tickSlot1us_p                    (tickSlot1us_p),
		.moveToDoze_p                     (moveToDoze_p),
		.wakeupListenInterval_p           (wakeupListenInterval_p),
		.wakeupDTIM_p                     (wakeupDTIM_p),
		.atimWindowOver_p                 (atimWindowOver_p),
		.tick1us_p                        (tick1us_p),
		.tick1tu_p                        (tick1tu_p),
		.debugPortMACTimerUnit            (debugPortMACTimerUnit),
		.debugPortMACTimerUnit2           (debugPortMACTimerUnit2),
		.debugPortMACTimerUnit3           (debugPortMACTimerUnit3)
		);


// Instanciation of deaggregator
// Name of the instance : U_deaggregator
// Name of the file containing this module : deaggregator.v
deaggregator U_deaggregator (
		.macCoreRxClk                     (macCoreRxClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (intMacCoreClkSoftRst_n),
		.startRx                          (startRx),
		.stopRx_p                         (stopRx_p),
		.rxVector1Valid_p                 (rxVector1Valid_p),
		.rxVector1Start_p                 (rxVector1Start_p),
		.rxEndOfFrame_p                   (rxEndOfFrame_p),
    .deaggregatorCsIsIdle             (deaggregatorCsIsIdle),
		.ampduCorrectRcved_p              (ampduCorrectRcved_p),
		.ampduIncorrectRcved_p            (ampduIncorrectRcved_p),
 		.rxSingleVHTMPDU                  (rxSingleVHTMPDU),
		.rxMPDUCnt                        (rxMPDUCnt),
		.incorrectDelCnt                  (incorrectDelCnt),
		.correctRcved_p                   (correctRcved_p),
		.rxCntrlReady                     (rxCntrlReady),
		.rxLegLength                      (rxLegLength),
		.rxLegRate                        (rxLegRate),
		.rxHTLength                       (rxHTLength),
		.rxMCS                            (rxMCS),
		.rxPreType                        (rxPreType),
		.rxFormatMod                      (rxFormatMod),
		.rxChBW                           (rxChBW),
		.rxShortGI                        (rxShortGI),
		.rxSmoothing                      (rxSmoothing),
		.rxLSIGValid                      (rxLSIGValid),
		.rxSTBC                           (rxSTBC),
		.rxSounding                       (rxSounding),
		.rxNumExtnSS                      (rxNumExtnSS),
		.rxChBWInNonHT                    (rxChBWInNonHT),
		.rxAggregation                    (rxAggregation),
		.rxFecCoding                      (rxFecCoding),
		.rxReserved1                      (rxReserved1),
		.rxAntennaSet                     (rxAntennaSet),
		.rxnSTS                           (rxnSTS),
		.rxDynBW                          (rxDynBW),
		.rxDozeNotAllowed                 (rxDozeNotAllowed),
		.rxPartialAID                     (rxPartialAID),
		.rxGroupID                        (rxGroupID),
		.rxRSSI1                          (rxRSSI1),
		.rxRSSI2                          (rxRSSI2),
		.rxRSSI3                          (rxRSSI3),
		.rxRSSI4                          (rxRSSI4),
		.rxReserved2                      (rxReserved2),
		.rxRCPI                           (rxRCPI),
		.rxEVM1                           (rxEVM1),
		.rxEVM2                           (rxEVM2),
		.rxEVM3                           (rxEVM3),
		.rxEVM4                           (rxEVM4),
		.rxReserved3                      (rxReserved3),
		.rxReserved4                      (rxReserved4),
		.rxReserved5                      (rxReserved5),
		.rxVector2Valid_p                 (rxVector2Valid_p),
		.rxData                           (rxData),
		.rxDataValid                      (rxDataValid),
		.rxDataStart_p                    (rxDataStart_p),
		.rxDataEnd_p                      (rxDataEnd_p),
		.rxDataError_p                    (rxDataError_p),
		.rxByteCnt                        (rxByteCnt),
		.rxMpduLength                     (rxMpduLength),
		.rxNDP                            (rxNDP),
		.correctDelimiter                 (correctDelimiter),
		.rxAMPDUCnt                       (rxAMPDUCnt),
		.macPhyIfRxFifoEmpty              (macPhyIfRxFifoEmpty),
		.macPhyIfRxFifoData               (macPhyIfRxFifoData),
		.macPhyIfRxErr_p                  (macPhyIfRxErr_p),
		.macPhyIfRxEnd_p                  (macPhyIfRxEnd_p),
		.macPhyIfRxFifoReadEn             (macPhyIfRxFifoReadEn),
		.maxAllowedLength                 (maxAllowedLength),
		.debugPortDeaggregator            (debugPortDeaggregator),
		.debugPortDeaggregator2           (debugPortDeaggregator2),
		.debugPortDeaggregatorFsm         (debugPortDeaggregatorFsm)
		);


// Instanciation of nav
// Name of the instance : U_nav
// Name of the file containing this module : nav.v
nav U_nav (
		.macCoreClk                       (macCoreClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (intMacCoreClkSoftRst_n),
		.tick1us_p                        (tick1us_p),
		.ctsDuration                      (ctsDuration),
		.ctsDurationValid_p               (ctsDurationValid_p),
		.ackDuration                      (ackDuration),
		.ackDurationValid_p               (ackDurationValid_p),
		.phyRxStartDelay                  (phyRxStartDelay),
		.moveToActive_p                   (moveToActive_p),
		.stopRx_p                         (stopRx_p),
		.navClear_p                       (navClear_p),
		.navUpdate_p                      (navUpdate_p),
		.rxFrameDuration                  (rxFrameDuration),
		.navCfpDurRemUpdate_p             (navCfpDurRemUpdate_p),
		.cfpDurRemaining                  (cfpDurRemaining),
		.navLsigUpdate_p                  (navLsigUpdate_p),
		.navLsigDuration                  (navLsigDuration),
		.notMinePsPollRcved_p             (notMinePsPollRcved_p),
		.incorrectRcved_p                 (incorrectRcved_p),
		.correctRcved_p                   (correctRcved_p),
		.loadQuietDuration_p              (loadQuietDuration_p),
		.quietDuration                    (quietDuration),
		.notMineRtsRcved_p                (notMineRtsRcved_p),
		.macPhyIfRxEndForTiming_p         (macPhyIfRxEndForTiming_p),
		.macPhyIfRxEnd_p                  (macPhyIfRxEnd_p),
		.macPhyIfRxErr_p                  (macPhyIfRxErr_p),
		.macPhyIfRxStart_p                (macPhyIfRxStart_p),
		.rxDot11a                         (rxDot11a),
		.navCfpMaxDurUpdate_p             (navCfpMaxDurUpdate_p),
		.channelToIdle_p                  (channelToIdle_p),
		.sifsB                            (sifsB),
		.sifsA                            (sifsA),
		.slotTime                         (slotTime),
		.abgnMode                         (abgnMode),
		.cfpMaxDuration                   (cfpMaxDuration),
		.probeDelay                       (probeDelay),
		.navCounter                       (navCounter),
		.navCounterIn                     (navCounterIn),
		.navCounterInValid                (navCounterInValid),
		.channelBusy                      (channelBusy),
		.channelIdle                      (channelIdle),
		.debugPortNAV                     (debugPortNAV)
		);


// Instanciation of fcs
// Name of the instance : U_fcs
// Name of the file containing this module : fcs.v
fcs U_fcs (
		.macCoreClk             (macCoreClk),
		.macCoreClkHardRst_n    (macCoreClkHardRst_n),
		.fcsDIn                 (fcsDIn),
		.fcsDInValid            (fcsDInValid),
		.fcsEnable              (fcsEnable),
		.fcsStart_p             (fcsStart_p),
		.fcsShift               (fcsShift),
		.fcsOk                  (fcsOk),
		.fcsDOut                (fcsDOut),
		.fcsDOutValid           (fcsDOutValid),
		.fcsBusy                (fcsBusy),
		.fcsEnd_p               (fcsEnd_p),
		.mpIfTxFifoFull         (mpIfTxFifoFull)
		);

assign fcsStart_p   = (txRxn) ? fcsStartTx_p  : fcsStartRx_p;
assign fcsEnable    = (txRxn) ? fcsEnableTx   : fcsEnableRx;
assign fcsDIn       = (txRxn) ? fcsDInTx      : rxData;
assign fcsDInValid  = (txRxn) ? fcsDInValidTx : rxDataValid;
assign fcsShift     = fcsShiftTx;
// Instanciation of dozeController
// Name of the instance : U_dozeController
// Name of the file containing this module : dozeController.v
dozeController U_dozeController (
		.macLPClk                         (macLPClk),
		.macCoreClk                       (macCoreClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (intMacCoreClkSoftRst_n),
		.moveToDoze_p                     (moveToDoze_p),
		.dozeWakeUp_p                     (dozeWakeUp_p),
    .absGenTimersInt                  (absGenTimersInt),
		.wakeupListenInterval_p           (wakeupListenInterval_p),
		.wakeupDTIM_p                     (wakeupDTIM_p),
		.atimWindowOver_p                 (atimWindowOver_p),
		.macPriClkEn                      (macPriClkEn),
		.macSecClkEn                      (macSecClkEn),
		.platformWakeUp                   (platformWakeUp),
		.macLPClkSwitch                   (macLPClkSwitch),
		.nextState                        (nextState),
		.enableLPClkSwitch                (enableLPClkSwitch),
		.wakeUpFromDoze                   (wakeUpFromDoze),
		.wakeUpSW                         (wakeUpSW),
		.activeClkGating                  (activeClkGating),
		.debugPortDozeController          (debugPortDozeController)
		);




// Instanciation of macCorePIResync
// Name of the instance : U_macCorePIResync
// Name of the file containing this module : macCorePIResync.v
macCorePIResync U_macCorePIResync (
		.macPIClkHardRst_n                (macPIClkHardRst_n),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (intMacCoreClkSoftRst_n),
		.macPIClk                         (macPIClk),
		.macPITxClk                       (macPITxClk),
		.macCoreClk                       (macCoreClk),
		.tick1us_p                        (tick1us_p),
		.tsfTimer                         (tsfTimer),
		.setac3HasData                    (setac3HasData),
		.setac2HasData                    (setac2HasData),
		.setac1HasData                    (setac1HasData),
		.setac0HasData                    (setac0HasData),
		.nextStatePlClkReg                (nextState),
		.latchNextStatePlClk_p            (latchNextState_p),
		.clearac3HasData                  (clearac3HasData),
		.clearac2HasData                  (clearac2HasData),
		.clearac1HasData                  (clearac1HasData),
		.clearac0HasData                  (clearac0HasData),
		.statussetac3HasData              (statussetac3HasData),
		.statussetac2HasData              (statussetac2HasData),
		.statussetac1HasData              (statussetac1HasData),
		.statussetac0HasData              (statussetac0HasData),
		.tsfTimerLowIn                    (tsfTimerLowIn),
		.tsfTimerLowInValid               (tsfTimerLowInValid),
		.tsfTimerHighIn                   (tsfTimerHighIn),
		.tsfTimerHighInValid              (tsfTimerHighInValid),
    .txBWAfterDropResync              (txBWAfterDropResync),
		.toggleHDSet_p                    (toggleHDSet_p),
		.togglePTSet_p                    (togglePTSet_p),
		.clearSets_p                      (clearSets_p),
		.txParameterHDReady_p             (txParameterHDReady_p),
		.txParameterPTReady_p             (txParameterPTReady_p),
		.txParameterNextPTReady_p         (txParameterNextPTReady_p),
		.nextStateCoreClkReg              (nextStateCoreClkReg),
    .acBWDropTrigger                  (acBWDropTrigger),
    .txBWAfterDrop                    (txBWAfterDrop),
		.txPCtoggleHDSet_p                (txPCtoggleHDSet_p),
		.txPCtogglePTSet_p                (txPCtogglePTSet_p),
		.txPCclearSets_p                  (txPCclearSets_p),
		.txPCtxParameterHDReady_p         (txPCtxParameterHDReady_p),
		.txPCtxParameterPTReady_p         (txPCtxParameterPTReady_p),
		.txPCtxParameterNextPTReady_p     (txPCtxParameterNextPTReady_p),

    .txPCnTxProtPT                    (txPCnTxProtPT),
    .txPCnTxPT                        (txPCnTxPT),
    .txPCshortGIPT                    (txPCshortGIPT),
    .txPCtxPwrLevelPT                 (txPCtxPwrLevelPT),
    .txPCtxPwrLevelProtPT             (txPCtxPwrLevelProtPT),
    .txPCstbcPT                       (txPCstbcPT),
    .txPCfecCodingPT                  (txPCfecCodingPT),
    .txPCnumExtnSSPT                  (txPCnumExtnSSPT),
    .txPCbfFrmExPT                    (txPCbfFrmExPT),
    .txPCbeamFormedPT                 (txPCbeamFormedPT),
    .txPCsmmIndexPT                   (txPCsmmIndexPT),
    .txPCantennaSetPT                 (txPCantennaSetPT),
    .txPCkeySRAMIndex                 (txPCkeySRAMIndex),
    .txPCkeySRAMIndexRA               (txPCkeySRAMIndexRA),
    .txPCrtsThreshold                 (txPCrtsThreshold),
    .txPCshortRetryLimit              (txPCshortRetryLimit),
    .txPClongRetryLimit               (txPClongRetryLimit),
    .txPCaMPDUFrameLengthTx           (txPCaMPDUFrameLengthTx),
    .txPCaMPDUOptFrameLength20Tx      (txPCaMPDUOptFrameLength20Tx),
    .txPCaMPDUOptFrameLength40Tx      (txPCaMPDUOptFrameLength40Tx),
    .txPCaMPDUOptFrameLength80Tx      (txPCaMPDUOptFrameLength80Tx),
    .txPCtxSingleVHTMPDU              (txPCtxSingleVHTMPDU),
    .txPCMPDUFrameLengthTx            (txPCMPDUFrameLengthTx),
    .txPCmcsIndex0ProtTx              (txPCmcsIndex0ProtTx),
    .txPCmcsIndex0Tx                  (txPCmcsIndex0Tx),
    .txPCuseRIFSTx                    (txPCuseRIFSTx),
    .txPCcontinuousTx                 (txPCcontinuousTx),
    .txPCformatModProtTx              (txPCformatModProtTx),
    .txPCformatModTx                  (txPCformatModTx),
    .txPCpreTypeProtTx                (txPCpreTypeProtTx),
    .txPCpreTypeTx                    (txPCpreTypeTx),
    .txPCbwProtTx                     (txPCbwProtTx),
    .txPCbwTx                         (txPCbwTx),
    .txPCpartialAIDTx                 (txPCpartialAIDTx),
    .txPCgroupIDTx                    (txPCgroupIDTx),
    .txPCdozeNotAllowedTx             (txPCdozeNotAllowedTx),
    .txPCdynBWTx                      (txPCdynBWTx),
    .txPCuseBWSignalingTx             (txPCuseBWSignalingTx),
    .txPCsmoothingProtTx              (txPCsmoothingProtTx),
    .txPCsmoothingTx                  (txPCsmoothingTx),
    .txPCsoundingTx                   (txPCsoundingTx),
    .txPCprotFrmDur                   (txPCprotFrmDur),
    .txPCwriteACK                     (txPCwriteACK),
    .txPClowRateRetry                 (txPClowRateRetry),
    .txPClstpProt                     (txPClstpProt),
    .txPClstp                         (txPClstp),
    .txPCexpectedAck                  (txPCexpectedAck),
    .txPCnavProtFrmEx                 (txPCnavProtFrmEx),
    .txPCdontGenerateMH               (txPCdontGenerateMH),
    .txPCdontEncrypt                  (txPCdontEncrypt),
    .txPCdontTouchFC                  (txPCdontTouchFC),
    .txPCdontTouchDur                 (txPCdontTouchDur),
    .txPCdontTouchQoS                 (txPCdontTouchQoS),
    .txPCdontTouchHTC                 (txPCdontTouchHTC),
    .txPCdontTouchTSF                 (txPCdontTouchTSF),
    .txPCdontTouchDTIM                (txPCdontTouchDTIM),
    .txPCdontTouchFCS                 (txPCdontTouchFCS),
    .txPCunderBASetup                 (txPCunderBASetup),
    .txPCaMPDUOut                     (txPCaMPDU),
    .txPCwhichDescriptor              (txPCwhichDescriptor),
    .txPCnBlankMDelimiters            (txPCnBlankMDelimiters),
    .txPCinterruptEnTx                (txPCinterruptEnTx),
    .txPCfcSubtype                    (txPCfcSubtype),
    .txPCfcType                       (txPCfcType),
    .txPCtsValid                      (txPCtsValid),
    .txPClifetimeExpired              (txPClifetimeExpired),
    .txPCnumMPDURetries               (txPCnumMPDURetriesTPC),
    .txPCnumRTSRetries                (txPCnumRTSRetriesTPC),
    .txPCmediumTimeUsed               (txPCmediumTimeUsedTPC),
    
    .nTxProtPT                        (nTxProtPT),
    .nTxPT                            (nTxPT),
    .shortGIPT                        (shortGIPT),
    .txPwrLevelPT                     (txPwrLevelPT),
    .txPwrLevelProtPT                 (txPwrLevelProtPT),
    .stbcPT                           (stbcPT),
    .fecCodingPT                      (fecCodingPT),
    .numExtnSSPT                      (numExtnSSPT),
    .bfFrmExPT                        (bfFrmExPT),
    .beamFormedPT                     (beamFormedPT),
    .smmIndexPT                       (smmIndexPT),
    .antennaSetPT                     (antennaSetPT),
    .keySRAMIndex                     (keySRAMIndex),
    .keySRAMIndexRA                   (keySRAMIndexRA),
    .rtsThreshold                     (rtsThreshold),
    .shortRetryLimit                  (shortRetryLimit),
    .longRetryLimit                   (longRetryLimit),
    .aMPDUFrameLengthTx               (aMPDUFrameLengthTx),
    .aMPDUOptFrameLength20Tx          (aMPDUOptFrameLength20Tx),
    .aMPDUOptFrameLength40Tx          (aMPDUOptFrameLength40Tx),
    .aMPDUOptFrameLength80Tx          (aMPDUOptFrameLength80Tx),
    .txSingleVHTMPDU                  (txSingleVHTMPDU),
    .MPDUFrameLengthTx                (MPDUFrameLengthTx),
    .mcsIndex0ProtTx                  (mcsIndex0ProtTx),
    .mcsIndex0Tx                      (mcsIndex0Tx),
    .useRIFSTx                        (useRIFSTx),
    .continuousTx                     (continuousTx),
    .formatModProtTx                  (formatModProtTx),
    .formatModTx                      (formatModTx),
    .preTypeProtTx                    (preTypeProtTx),
    .preTypeTx                        (preTypeTx),
    .bwProtTx                         (bwProtTx),
    .bwTx                             (bwTx),
    .partialAIDTx                     (partialAIDTx),
    .groupIDTx                        (groupIDTx),
    .dozeNotAllowedTx                 (dozeNotAllowedTx),
    .dynBWTx                          (dynBWTx),
    .useBWSignalingTx                 (useBWSignalingTx),
    .smoothingProtTx                  (smoothingProtTx),
    .smoothingTx                      (smoothingTx),
    .soundingTx                       (soundingTx),
    .protFrmDur                       (protFrmDur),
    .writeACK                         (writeACK),
    .lowRateRetry                     (lowRateRetry),
    .lstpProt                         (lstpProt),
    .lstp                             (lstp),
    .expectedAck                      (expectedAck),
    .navProtFrmEx                     (navProtFrmEx),
    .dontGenerateMH                   (dontGenerateMH),
    .dontEncrypt                      (dontEncrypt),
    .dontTouchFC                      (dontTouchFC),
    .dontTouchDur                     (dontTouchDur),
    .dontTouchQoS                     (dontTouchQoS),
    .dontTouchHTC                     (dontTouchHTC),
    .dontTouchTSF                     (dontTouchTSF),
    .dontTouchDTIM                    (dontTouchDTIM),
    .dontTouchFCS                     (dontTouchFCS),
    .underBASetup                     (underBASetup),
    .aMPDUOut                         (aMPDU),
    .whichDescriptor                  (whichDescriptor),
    .nBlankMDelimiters                (nBlankMDelimiters),
    .interruptEnTx                    (interruptEnTx),
    .fcSubtype                        (fcSubtype),
    .fcType                           (fcType),
    .tsValid                          (tsValid),
    .lifetimeExpired                  (lifetimeExpired),
    .numMPDURetries                   (numMPDURetriesTPC),
    .numRTSRetries                    (numRTSRetriesTPC),
    .mediumTimeUsed                   (mediumTimeUsedTPC),


		.bckoffstatussetac3HasData        (bckoffstatussetac3HasData),
		.bckoffstatussetac2HasData        (bckoffstatussetac2HasData),
		.bckoffstatussetac1HasData        (bckoffstatussetac1HasData),
		.bckoffstatussetac0HasData        (bckoffstatussetac0HasData),
		.bckoffsetac3HasData              (bckoffsetac3HasData),
		.bckoffsetac2HasData              (bckoffsetac2HasData),
		.bckoffsetac1HasData              (bckoffsetac1HasData),
		.bckoffsetac0HasData              (bckoffsetac0HasData),
		.bckoffclearac3HasData            (bckoffclearac3HasData),
		.bckoffclearac2HasData            (bckoffclearac2HasData),
		.bckoffclearac1HasData            (bckoffclearac1HasData),
		.bckoffclearac0HasData            (bckoffclearac0HasData)
		);


`ifdef RW_MAC_MIBCNTL_EN
// Instanciation of mibController
// Name of the instance : U_mibController
// Name of the file containing this module : mibController.v
mibController U_mibController (
		.mibdot11WEPExcludedCount                   (mibdot11WEPExcludedCount),
		.mibdot11FCSErrorCount                      (mibdot11FCSErrorCount),
		.mibrwRxPHYErrorCount                       (mibrwRxPHYErrorCount),
		.mibrwQosUTransmittedMPDUCount              (mibrwQosUTransmittedMPDUCount),
		.mibrwQosGTransmittedMPDUCount              (mibrwQosGTransmittedMPDUCount),
		.mibdot11QosFailedCount                     (mibdot11QosFailedCount),
		.mibdot11QosRetryCount                      (mibdot11QosRetryCount),
		.mibdot11QosRTSSuccessCount                 (mibdot11QosRTSSuccessCount),
		.mibdot11QosRTSFailureCount                 (mibdot11QosRTSFailureCount),
		.mibrwQosACKFailureCount                    (mibrwQosACKFailureCount),
		.mibrwQosUReceivedMPDUCount                 (mibrwQosUReceivedMPDUCount),
		.mibrwQosGReceivedMPDUCount                 (mibrwQosGReceivedMPDUCount),
		.mibrwQosUReceivedOtherMPDU                 (mibrwQosUReceivedOtherMPDU),
		.mibdot11QosRetriesReceivedCount            (mibdot11QosRetriesReceivedCount),
		.mibrwUTransmittedAMSDUCount                (mibrwUTransmittedAMSDUCount),
		.mibrwGTransmittedAMSDUCount                (mibrwGTransmittedAMSDUCount),
		.mibdot11FailedAMSDUCount                   (mibdot11FailedAMSDUCount),
		.mibdot11RetryAMSDUCount                    (mibdot11RetryAMSDUCount),
		.mibdot11TransmittedOctetsInAMSDU           (mibdot11TransmittedOctetsInAMSDU),
		.mibdot11AMSDUAckFailureCount               (mibdot11AMSDUAckFailureCount),
		.mibrwUReceivedAMSDUCount                   (mibrwUReceivedAMSDUCount),
		.mibrwGReceivedAMSDUCount                   (mibrwGReceivedAMSDUCount),
		.mibrwUReceivedOtherAMSDU                   (mibrwUReceivedOtherAMSDU),
		.mibdot11ReceivedOctetsInAMSDUCount         (mibdot11ReceivedOctetsInAMSDUCount),
		.mibdot11TransmittedAMPDUCount              (mibdot11TransmittedAMPDUCount),
		.mibdot11TransmittedMPDUInAMPDUCount        (mibdot11TransmittedMPDUInAMPDUCount),
		.mibdot11TransmittedOctetsInAMPDUCount      (mibdot11TransmittedOctetsInAMPDUCount),
		.mibrwUAMPDUReceivedCount                   (mibrwUAMPDUReceivedCount),
		.mibrwGAMPDUReceivedCount                   (mibrwGAMPDUReceivedCount),
		.mibrwOtherAMPDUReceivedCount               (mibrwOtherAMPDUReceivedCount),
		.mibdot11MPDUInReceivedAMPDUCount           (mibdot11MPDUInReceivedAMPDUCount),
		.mibdot11ReceivedOctetsInAMPDUCount         (mibdot11ReceivedOctetsInAMPDUCount),
		.mibdot11AMPDUDelimiterCRCErrorCount        (mibdot11AMPDUDelimiterCRCErrorCount),
		.mibdot11ImplicitBARFailureCount            (mibdot11ImplicitBARFailureCount),
		.mibdot11ExplicitBARFailureCount            (mibdot11ExplicitBARFailureCount),
		.mibdot1120MHzFrameTransmittedCount         (mibdot1120MHzFrameTransmittedCount),
		.mibdot1140MHzFrameTransmittedCount         (mibdot1140MHzFrameTransmittedCount),
		.mibdot1180MHzFrameTransmittedCount         (mibdot1180MHzFrameTransmittedCount),
		.mibdot11160MHzFrameTransmittedCount        (mibdot11160MHzFrameTransmittedCount),
		.mibdot1120MHzFrameReceivedCount            (mibdot1120MHzFrameReceivedCount),
		.mibdot1140MHzFrameReceivedCount            (mibdot1140MHzFrameReceivedCount),
		.mibdot1180MHzFrameReceivedCount            (mibdot1180MHzFrameReceivedCount),
		.mibdot11160MHzFrameReceivedCount           (mibdot11160MHzFrameReceivedCount),
		.mibrw20MHzFailedTXOPCount                  (mibrw20MHzFailedTXOPCount),
		.mibrw20MHzSuccessfulTXOPCount              (mibrw20MHzSuccessfulTXOPCount),
		.mibrw40MHzFailedTXOPCount                  (mibrw40MHzFailedTXOPCount),
		.mibrw40MHzSuccessfulTXOPCount              (mibrw40MHzSuccessfulTXOPCount),
		.mibrw80MHzFailedTXOPCount                  (mibrw80MHzFailedTXOPCount),
		.mibrw80MHzSuccessfulTXOPCount              (mibrw80MHzSuccessfulTXOPCount),
		.mibrw160MHzFailedTXOPCount                 (mibrw160MHzFailedTXOPCount),
		.mibrw160MHzSuccessfulTXOPCount             (mibrw160MHzSuccessfulTXOPCount),
		.mibrwDynBWDropCount                        (mibrwDynBWDropCount),
		.mibrwStaBWFailedCount                      (mibrwStaBWFailedCount),
		.mibdot11DualCTSSuccessCount                (mibdot11DualCTSSuccessCount),
		.mibdot11STBCCTSSuccessCount                (mibdot11STBCCTSSuccessCount),
		.mibdot11STBCCTSFailureCount                (mibdot11STBCCTSFailureCount),
		.mibdot11nonSTBCCTSSuccessCount             (mibdot11nonSTBCCTSSuccessCount),
		.mibdot11nonSTBCCTSFailureCount             (mibdot11nonSTBCCTSFailureCount),
		.mibrwRxFIFOOverflowCount                   (mibrwRxFIFOOverflowCount),
		.mibrwTxUnderrunCount                       (mibrwTxUnderrunCount),
		.macCoreClk                                 (macCoreClk),
		.macCoreClkHardRst_n                        (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n                        (intMacCoreClkSoftRst_n),
		.mibTIDIndex                                (mibTIDIndex),
		.mibTrigger                                 (mibTrigger),
		.mibTableReadData                           (mibTableReadData),
		.mibAddr                                    (mibAddr),
		.mibRd                                      (mibRd),
		.mibTableIndex                              (mibTableIndex),
		.mibIncrementMode                           (mibIncrementMode),
		.mibValue                                   (mibValue),
		.mibWrite                                   (mibWrite),
		.mibWriteInValid                            (mibWriteInValid),
		.mibWriteIn                                 (mibWriteIn),
		.mibTableReset                              (mibTableReset),
		.mibTableResetIn                            (mibTableResetIn),
		.mibTableResetInValid                       (mibTableResetInValid),
		.mibRdData                                  (mibRdData),
		.mibBusy                                    (mibBusy),
		.mibTableAddr                               (mibTableAddr),
		.mibTableWriteData                          (mibTableWriteData),
		.mibTableWriteEn                            (mibTableWriteEn),
		.mibTableEn                                 (mibTableEn)
		);
`endif // RW_MAC_MIBCNTL_EN


// Instanciation of keySearchEngine
// Name of the instance : U_keySearchEngine
// Name of the file containing this module : keySearchEngine.v
keySearchEngine U_keySearchEngine (
		.macCoreClk                       (macCoreClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (intMacCoreClkSoftRst_n),
		.keyStoRAMReset                   (keyStoRAMReset),
		.keyStoRAMResetIn                 (keyStoRAMResetIn),
		.keyStoRAMResetInValid            (keyStoRAMResetInValid),
		.encrKeyRAM                       (encrKeyRAM),
`ifdef RW_WAPI_EN
		.encrIntKeyRAM                    (encrIntKeyRAM),
`endif // RW_WAPI_EN
		.keyIndexRAM                      (keyIndexRAMInt),
		.encrMACAddr                      (encrMACAddr),
		.newWrite                         (newWrite),
		.newRead                          (newRead),
		.debugKSR                         (debugKSR),
		.newWriteInValid                  (newWriteInValid),
		.newReadInValid                   (newReadInValid),
		.cLenRAM                          (cLenRAM),
		.useDefKeyRAM                     (useDefKeyRAM),
		.sppRAM                           (sppRAM),
		.vlanIDRAM                        (vlanIDRAM),
		.cTypeRAM                         (cTypeRAM),
		.keyStorageError_p                (keyStorageError_p),
		.keySearchIndex                   (keySearchIndex[`KEY_INDEX_WIDTH-1:0]),
		.keySearchIndexTrig_p             (keySearchIndexTrig_p),
		.macAddressIn                     (macAddressIn),
		.indexSearchTrig_p                (indexSearchTrig_p),
		.keyStorageValid_p                (keyStorageValid_p),
		.keyRegReadValid_p                (keyRegReadValid_p),
		.keyIndexReturn                   (keyIndexReturn),
		.cTypeRAMIn                       (cTypeRAMIn),
		.vlanIDRAMIn                      (vlanIDRAMIn),
		.sppRAMIn                         (sppRAMIn),
		.useDefKeyRAMIn                   (useDefKeyRAMIn),
		.cLenRAMIn                        (cLenRAMIn),
		.encrMACAddrIn                    (encrMACAddrIn),
		.encrKeyRAMIn                     (encrKeyRAMIn),
`ifdef RW_WAPI_EN
		.encrIntKeyRAMIn                  (encrIntKeyRAMIn),
`endif // RW_WAPI_EN
		.cTypeKSR                         (cTypeKSR),
		.vlanIDKSR                        (vlanIDKSR),
		.sppKSR                           (sppKSR),
		.useDefKeyKSR                     (useDefKeyKSR),
		.cLenKSR                          (cLenKSR),
		.macAddressKSR                    (macAddressKSR),
`ifdef RW_WAPI_EN
    .cryptoIntKeyKSR                  (cryptoIntKeyKSR),
`endif // RW_WAPI_EN
		.cryptoKeyKSR                     (cryptoKeyKSR),
		.keyStorageReadData               (keyStorageReadData),
		.keyStorageWriteData              (keyStorageWriteData),
		.keyStorageAddr                   (keyStorageAddr),
		.keyStorageEn                     (keyStorageEn),
		.keyStorageWriteEn                (keyStorageWriteEn),
		.debugPortKeySearch               (debugPortKeySearch)
		);

// Interconnect between Key Search Engine and CSReg
assign encrKeyRAM        = {encrKeyRAMWord3, encrKeyRAMWord2, encrKeyRAMWord1, encrKeyRAMWord0};
assign encrKeyRAMWord3In = encrKeyRAMIn[127:96];
assign encrKeyRAMWord2In = encrKeyRAMIn[95:64];
assign encrKeyRAMWord1In = encrKeyRAMIn[63:32];
assign encrKeyRAMWord0In = encrKeyRAMIn[31:0];

`ifdef RW_WAPI_EN
// Interconnect between Key Search Engine and CSReg
assign encrIntKeyRAM        = {encrIntKeyRAMWord3, encrIntKeyRAMWord2, encrIntKeyRAMWord1, encrIntKeyRAMWord0};
assign encrIntKeyRAMWord3In = encrIntKeyRAMIn[127:96];
assign encrIntKeyRAMWord2In = encrIntKeyRAMIn[95:64];
assign encrIntKeyRAMWord1In = encrIntKeyRAMIn[63:32];
assign encrIntKeyRAMWord0In = encrIntKeyRAMIn[31:0];
`endif // RW_WAPI_EN

assign encrMACAddr      = {macAddrRAMHigh, macAddrRAMLow};
assign macAddrRAMHighIn = encrMACAddrIn[47:32];
assign macAddrRAMLowIn  = encrMACAddrIn[31:0];


assign keyIndexRAMInt = keyIndexRAM[`KEY_INDEX_WIDTH-1:0];

assign newWriteIn     = 1'b0;
assign newReadIn      = 1'b0;

assign cLenRAMInValid              = newReadInValid || newWriteInValid;
assign useDefKeyRAMInValid         = newReadInValid || newWriteInValid;
assign sppRAMInValid               = newReadInValid || newWriteInValid;
assign vlanIDRAMInValid            = newReadInValid || newWriteInValid;
assign cTypeRAMInValid             = newReadInValid || newWriteInValid;
assign encrKeyRAMWord3InValid      = newReadInValid || newWriteInValid;
assign encrKeyRAMWord2InValid      = newReadInValid || newWriteInValid;
assign encrKeyRAMWord1InValid      = newReadInValid || newWriteInValid;
assign encrKeyRAMWord0InValid      = newReadInValid || newWriteInValid;
`ifdef RW_WAPI_EN
assign encrIntKeyRAMWord3InValid   = newReadInValid || newWriteInValid;
assign encrIntKeyRAMWord2InValid   = newReadInValid || newWriteInValid;
assign encrIntKeyRAMWord1InValid   = newReadInValid || newWriteInValid;
assign encrIntKeyRAMWord0InValid   = newReadInValid || newWriteInValid;
`endif // RW_WAPI_EN
assign macAddrRAMHighInValid       = newReadInValid || newWriteInValid;
assign macAddrRAMLowInValid        = newReadInValid || newWriteInValid; 

// Interconnect between Key Search Engine and RX Controller
assign macAddressIn = rxAddr2;

// Interconnect between Key Search Engine and MAC/RX Controller
assign keySearchIndex       = (rxCsIsIdle) ? txKeySearchIndex : rxKeySearchIndex;
assign keySearchIndexTrig_p = (rxCsIsIdle) ? txKeySearchIndexTrig_p : rxKeySearchIndexTrig_p;

// Instanciation of encryptEngTop
// Name of the instance : U_encryptEngTop
// Name of the file containing this module : encryptEngTop.v
encryptEngTop U_encryptEngTop (
		.macCoreClk                       (macCoreClk),
		.macCryptClk                      (macCryptClk),
		.macWTClk                         (macWTClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macWTClkHardRst_n                (macWTClkHardRst_n),
		.macCoreClkSoftRst_n              (intMacCoreClkSoftRst_n),
		.macWTClkSoftRst_n                (intMacWTClkSoftRst_n),
		.macCryptClkEn                    (intMacCryptClkEn),
		.macWTClkEn                       (intMacWTClkEn),
		.plainTxData                      (plainTxData),
		.plainTxDataValid                 (plainTxDataValid),
		.cryptoDataReady                  (cryptoDataReady),
		.encryptDataOut                   (encryptDataOut),
		.encryptDataValid                 (encryptDataValid),
		.fcsBusy                          (fcsBusy),
		.txWEPIV                          (txWEPIV),
		.txWEPIVValid                     (txWEPIVValid),
		.initPRNG_p_tx                    (txSBOXInit),
		.icvStart_p_tx                    (initDone_p),
		.txError_p                        (txError_p),
		.txCsIsIdle                       (txCsIsIdle),
		.txTKIP                           (txTKIP),
		.txTkipSeqCntr                    (txTkipSeqCntr),
		.txCCMP                           (txCCMP),
		.txCCMPStart                      (txCCMPStart),
		.txCCMPDataWrEn_p                 (txCCMPDataWrEn_p),
		.txPushCCMPHdrInBuffer_p          (txPushCCMPHdrInBuffer_p),
		.txEnd_p                          (macPhyTxEnd_p),
		.txPayLoadEnd_p                   (txPayLoadEnd_p),
		.txAddress4Pres                   (txAddress4Pres),
		.txQoSFrame                       (txQoSFrame),
		.txTID                            (txTID),
		.txQoS7                           (txAMSDUPresent),
		.tcPayLoadLen                     (tcPayLoadLen),
		.txAddr1                          (txAddr1),
		.tcSfc                            (tcSfc),
		.ccmpHTMode                       (ccmpHTMode),
		.sppKSR                           (sppKSR),
		.encrTxCCMPBusy                   (txCCMPBusy),
		.encrTxCCMPMicDone                (txCCMPMicDone),
		.initSBOXDone                     (txSBOXInitDone),
		.initDone_p                       (initDone_p),
		.rxCsIsIdle                       (rxCsIsIdle),
		.rxAddr1                          (rxAddr1),
		.rxAddr2                          (rxAddr2),
		.rxInitVector                     (rxInitVector),
		.rxTkipSeqCntr                    (rxTkipSeqCntr),
		.rxPayLoadLen                     (rxPayLoadLen),
		.rxFifoReady                      (rxFifoReady),
		.rxError_p                        (rxError_p),
		.encrRxBufFlush_p                 (encrRxBufFlush_p),
		.writeFCSEn                       (writeFCSEn),
		.rxDataEnd_p                      (rxDataEnd_p),
		.rxAddress4Pres                   (rxAddress4Pres),
		.rxQoSFrame                       (rxQoSFrame),
		.rxTID                            (rxTID),
		.rxQoS7                           (rxAMSDUPresent),
		.initEncrRxCntrl_p                (initEncrRxCntrl_p),
		.cryptoKeyValid                   (cryptoKeyValid),
		.nullKeyFound                     (nullKeyFound),
		.pushRxDataInBuffer               (pushRxDataInBuffer),
		.wrDataToEncrBuffer               (wrDataToEncrBuffer),
		.rxCCMPAADwrEn_p                  (rxCCMPAADwrEn_p),
		.plainDataOut                     (plainDataOut),
		.plainOutDataValid                (plainOutDataValid),
		.plainOutDataEnd_p                (plainOutDataEnd_p),
		.plainOutICVEnd_p                 (plainOutICVEnd_p),
		.plainOutFCSValid                 (plainOutFCSValid),
		.wepTkipPassed_p                  (wepTkipPassed_p),
		.wepTkipFailed_p                  (wepTkipFailed_p),
		.ccmpPassed_p                     (ccmpPassed_p),
		.ccmpFailed_p                     (ccmpFailed_p),
		.wrFIFOEn_c                       (),
		.encrBufferFull                   (encrBufferFull),
		.encrBufferEmpty                  (),
		.macAddress                       (macAddress),
		.encrRxFIFOReset                  (encrRxFIFOReset),
		.encrRxFIFOResetIn                (encrRxFIFOResetIn),
		.encrRxFIFOResetInValid           (encrRxFIFOResetInValid),
		.activeClkGating                  (activeClkGating),
`ifdef RW_WAPI_EN
		.txWAPI                           (txWAPI),        
		.txWAPIStart                      (txWAPIStart),   
		.rxWAPI                           (rxWAPI),        
		.cryptoIntKey                     (cryptoIntKey),  
		.wpiDone_p                        (wpiDone_p),     
		.wapiPassed_p                     (wapiPassed_p),
		.wapiFailed_p                     (wapiFailed_p),
		.encrTxWAPIBusy                   (txWAPIBusy),
		.txFrameControl                   (txWAPIFrameControl),
		.txAddr3                          (txWAPIAddr3),       
		.txAddr4                          (txWAPIAddr4),       
		.txQosCF                          (txWAPIQoSCF),       
		.txSeqControl                     (txWAPISeqControl),  
		.txKeyIdx                         (txWAPIKeyIdx),      
		.txPN                             (txWAPIPN),          
		.rxFrameControl                   (rxFrmCtrl),
		.rxAddr3                          (rxAddr3),       
		.rxAddr4                          (rxAddr4),       
		.rxQosCF                          (rxQoSControl),  
		.rxSeqControl                     (rxSeqCtrl),     
		.rxKeyIdx                         (rxWAPIKeyIndex),
		.rxPN                             (rxWAPIPN),      
`endif // RW_WAPI_EN
		.cryptoKey                        (cryptoKey),
		.cipherType                       (cipherType),
		.cipherLen                        (cipherLen),
		.sBoxAReadData                    (sBoxAReadData),
		.sBoxBReadData                    (sBoxBReadData),
		.sBoxAAddr                        (sBoxAAddr),
		.sBoxBAddr                        (sBoxBAddr),
		.sBoxAWriteData                   (sBoxAWriteData),
		.sBoxBWriteData                   (sBoxBWriteData),
		.sBoxAWriteEn                     (sBoxAWriteEn),
		.sBoxBWriteEn                     (sBoxBWriteEn),
		.sBoxAEn                          (sBoxAEn),
		.sBoxBEn                          (sBoxBEn),
		.encrRxFIFOWriteEn                (encrRxFIFOWriteEn),
		.encrRxFIFOWriteAddr              (encrRxFIFOWriteAddr),
		.encrRxFIFOWriteData              (encrRxFIFOWriteData),
		.encrRxFIFOReadData               (encrRxFIFOReadData),
		.encrRxFIFOReadEn                 (encrRxFIFOReadEn),
		.encrRxFIFOReadAddr               (encrRxFIFOReadAddr),
		.debugUseDefaultKeyKSR            (useDefKeyKSR),
 		.debugKeyIndexTrig                (keySearchIndexTrig_p),
		.debugKeyIndexKSR                 (keySearchIndex[5:0]),
    `ifdef RW_WAPI_EN
    .debugPortWapi                    (debugPortWapi),
    `endif //RW_WAPI_EN
		.debugPortEncryptionEngine        (debugPortEncryptionEngine)
		);


// Interconnect between Encryption Engine and Key Search Engine
assign cryptoKeyValid  = (rxCsIsIdle) ? txCryptoKeyValid : rxCryptoKeyValid;
`ifdef RW_WAPI_EN
assign cryptoIntKey    = cryptoIntKeyKSR;
`endif // RW_WAPI_EN
assign cryptoKey       = cryptoKeyKSR;
assign cipherType      = cTypeKSR;
assign cipherLen       = cLenKSR;
assign keySearchDone_p = keyStorageValid_p;

//// Interconnect between Encryption Engine and CSReg
//assign macAddress      = macAddr;
// Interconnect between Encryption Engine and txController addr2 decoder
assign macAddress      = txAddr2;

// Interconnect between Encryption Engine and MAC PHY interface
assign txError_p       = mpIfTxErr_p;

// Interconnect between Encryption Engine and Tx controller (MPDU)
assign ccmpHTMode      = (rxCsIsIdle) ? txCCMPHT : (rxFormatMod[2:1] != 2'b0) ? 1'b1 : 1'b0 ;
assign txTkipSeqCntr   = {tcSfc[7:0],tcSfc[15:8],tcSfc[23:16],tcSfc[31:24],tcSfc[39:32],tcSfc[47:40]};
//assign txEncrData      = txCCMP       ? encrTxCCMPWriteData      : encryptDataOut;
//assign txEncrDataValid = txCCMP       ? encrTxCCMPWriteDataValid : encryptDataValid;
assign txEncrData      = encryptDataOut;
assign txEncrDataValid = encryptDataValid;
//assign StartCCMP       = (rxCsIsIdle) ? txCCMPStart : initEncrRxCntrl_p;





// Instanciation of pulse2PulseSynchro
// Name of the instance : U_tick1us_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_tick1us_p_synchro (
                .srcclk             (macCoreClk),
                .srcresetn          (macCoreClkHardRst_n),
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (tick1us_p),
                .dstdata            (tick1usPIClk_p)
                );

always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
    nextTBTT <= 16'b0;
  else if (tick1usPIClk_p) 
    nextTBTT <= nextTBTTCnt;
end   


// DebugPort 
assign debugPortMediumAccess = {quietElement1InValid || quietElement2InValid,
                                macPhyIfRxCca,
                                channelBusy,
                                loadQuietDuration_p,
                                backOffDone_p,
                                retry_p || txSuccessful_p || retryLTReached_p,
                                txopComplete,
                                retryFrame_p,
                                impQICnt[3:0],
                                nextTBTTCnt[3:0]};


assign debugPortAMPDU = {debugPortAMPDUMC,debugPortAMPDURxC};

endmodule
