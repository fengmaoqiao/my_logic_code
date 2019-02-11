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
// Description      :Top module for DMA. This is an internal DMA engine which
//                   parses the linked list queued by SW in the SRAM and moves
//                   data from SRAM to TX FIFO and passes status information
//                   on transmission through the linked list descriptors to SW
//                   For receive it moves the data from the RX FIFO to the 
//                   SRAM and indicates the location of the buffer in the 
//                   descriptors queued by SW
//                   
//                   Modules instantiated in design.
//                   1. txListProc.v   -> Transmit List Processor
//                   2. rxListProc.v   -> Receive List Processor
//                   3. dmaArbiter.v   -> Arbiter 
//                   4. txPrimCtrl.v   -> Transmit Primary Controller code 
//                   5. rxPrimCtrl.v   -> Receive Primary Controller code 
//                   6. rxPrimCtrl.v   -> Receive Primary Controller code 
//                   7. txPrimCtrlSelLogic.v -> selection logic for 5 tx prim
//                                              controller channels
//                   8. rdWrCtrl.v     -> Interacts with AHB master IF to fetch
//                                        data from SRAM
//                   9. txStatusUpdater.v -> Updates status in descriptors in 
//                                           SRAM for transmitted data                  
//                                     
// Simulation Notes : System verilog assertions can be enabled with RW_ASSERT_ON
//                    Then a system verilog capable simulation is needed
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

module dmaEngine ( 
   
   
   
   //Clocks and reset
   input  wire        macPITxClk,                    // Tx clock
   input  wire        macPIRxClk,                    // Rx clock
   input  wire        macPIClk,                      // main clock
   input  wire        macPITxClkHardRst_n,           // Tx hard reset
   input  wire        macPIRxClkHardRst_n,           // Rx hard reset
   input  wire        macPIClkHardRst_n,             // main hard reset
   input  wire        macPITxClkSoftRst_n,           // Tx soft reset
   input  wire        macPIRxClkSoftRst_n,           // Rx soft reset
   input  wire        macPIClkSoftRst_n,             // main soft reset

   //$port_g host If port
   output wire [31:0] dmaHIFAddressIn,               // Address for the single transfer or starting address for a burst
   output wire        dmaHIFRead,                    // Signal indicating a read.
   output wire        dmaHIFWrite,                   // Signal indicating a write
   output wire [ 2:0] dmaHIFSize,                    // Signal indicating the write size
   output wire [31:0] dmaHIFWriteDataIn,             // The data to be written into addressed location 
   //
   input  wire        dmaHIFError,                   // Asserted if an error response is received.
   input  wire [31:0] dmaHIFReadDataOut,             // data read from AHB
   input  wire        dmaHIFReadDataValid,           // read data data valid
   input  wire        dmaHIFReady,                   // Asserted when next data has to be pushed.
   input  wire        dmaHIFTransComplete,           // Asserted when next data last data has been pushed



   //$port_g NAV controller
   input  wire        trigTxAC0,                     // Trigger from the MAC Controller to indicate DMA to
                                                     // start fetching frames associated with AC0
   input  wire        trigTxAC1,                     // Trigger from the MAC Controller to indicate DMA to
                                                     // start fetching frames associated with AC1
   input  wire        trigTxAC2,                     // Trigger from the MAC Controller to indicate DMA to
                                                     // start fetching frames associated with AC2
   input  wire        trigTxAC3,                     // Trigger from the MAC Controller to indicate DMA to
                                                     // start fetching frames associated with AC3
   input  wire        trigTxBcn,                     // Trigger from the MAC Controller to indicate DMA to
                                                     // start fetching frames associated with Beacon
   input  wire        frameRxed_p,                   // MAC Controller indicates a frame is successfully
                                                     // received

   //$port_g Rx Fifo port
   output wire        rxFifoRd,                      // Write signal to RX FIFO
   //
   input  wire        rxFifoEmpty,                   // FIFO empty indication
   input  wire        rxFifoAlmEmpty,                // FIFO alsmost empty indication
   input  wire  [3:0] rxTagFifoRdData,               // Data from TAG FIFO
   input  wire [31:0] rxFifoRdData,                  // Data read from RX FIFO

   //$port_g Tx Fifo
   input  wire        txFifoAlmostFull,              // Tx FIFO almost Full indication
   input  wire        txFifoFull,                    // Tx FIFO Full indication 
   input  wire        txFifoEmpty,                   // Tx FIFO empty indication 
   // 
   output wire        txFifoWr,                      // write signal to TX FIFO
   output wire [31:0] txFifoWrData,                  // write data to Tx FIFO
   output wire        flushTxFifo,                   // Flush signal to TX FIFo
   output wire  [5:0] txTagFifoWrData,               // Data to write to TX TAG FIFO

   output wire        txFIFOFlushDone_p,             //Signal indicating the completion of the txFifo Flush

   //$port_g macController port
   input  wire        updateDMAStatus_p,             // trigs the DMA Status update.

   input  wire        swRTS_p,                       // Asserted high if the current transmitted packet is a
                                                     // RTS frame prepared by SW
   input  wire        txMpduDone_p,                  // Asserted high after every transmission of MPDU in an
                                                     // AMPDU frame
   input  wire        retryFrame_p,                  // If the transmitted frame has to be retried then this
                                                     // signal is asserted.
   input  wire        mpduSuccess_p,                 // If the transmitted frame was successful. Not asserted
                                                     // for RTS frames
   input  wire        mpduFailed_p,                  // If the transmitted frame was not successful. Not asserted
                                                     // if the RTS frame failed
   input  wire        rtsFailed_p,                   // If the transmitted frame was a RTS frame and did not
                                                     // receive a CTS frame within the CTS timeout
   input  wire        rtsSuccess_p,                  // If the transmitted frame was a RTS frame and successfully
                                                     // received a CTS in reponse.
   input  wire        retryLimitReached_p,           // If the transmitted frame was not successful and has reached
                                                     // the retry limit.Is asserted for both RTS and other MPDU's
   input  wire        ampduFrm_p,                    // Asserted high if the transmitted packet was an AMPDU
                                                     // frame
   input  wire [1:0]  transmissionBW,                // Indicates whether the frame was transmitted with 20MHz or 40Mhz BW
   input  wire [7:0]  numMPDURetries,                // Indicates the number of retries for this MPDU. Valid when
                                                     // rtsFailed_p rtsSuccess_p mpduSuccess_p mpduFailed_p or
                                                     // retryLimitReached 
   input  wire [7:0]  numRTSRetries,                 // indicates the the number of times the RTS has been sent.
                                                     // Valid when rtsFailed_p rtsSuccess_p mpduSuccess_p 
                                                     // mpduFailed_p or retryLimitReached 
   input  wire [31:0] mediumTimeUsed,                // Indicates the medium Time Used for current transmission
                                                     // Valid when DMA status is being updated
   input  wire [ 3:0] whichDescriptorSW,             // Indicates the value of the partAMorMSDU field Controller

   //$port_g rxController interface
   output wire        rxFrmDiscard,                // Discard the current rx frame : no more descriptor and rxFlowCntrlEn == 1
   output wire        rxDescAvailable,             // Indicate to rxController that Current frame has a all necessaries descripstor
   input  wire        rxFrmDiscardRet,             // Return signal on rxFrmDiscard from macCLk domain to macPIClk domain

   //$port_g registers interface
   input  wire        rxFlowCntrlEn,                 // rx Flow Control Enable
   input  wire [31:0] tsfTimerValue,                 // TsfTimer value
   
   input  wire        underRunDetected_p,            // Frame Length mismatch detected by the MAC Controller
   input  wire        txNewTailAC0,                  // Registers
                                                     // Indicates the status of the txAC0NewTail bit of the
                                                     // DMA Control register
   input  wire        txNewTailAC1,                  // Indicates the status of the txAC1NewTail bit of the
                                                     // DMA Control register
   input  wire        txNewTailAC2,                  // Indicates the status of the txAC2NewTail bit of the
                                                     // DMA Control register
   input  wire        txNewTailAC3,                  // Indicates the status of the txAC3NewTail bit of the
                                                     // DMA Control register
   input  wire        txNewTailBcn,                  // Indicates the status of the txNewTailBcn bit of the
                                                     // DMA Control register
   input  wire        txNewHeadAC0,                  // Indicates the status of the txNewHeadAC0 bit of the
                                                     // DMA Control register
   input  wire        txNewHeadAC1,                  // Indicates the status of the txNewHeadAC1 bit of the
                                                     // DMA Control register
   input  wire        txNewHeadAC2,                  // Indicates the status of the txNewHeadAC2 bit of the
                                                     // DMA Control register
   input  wire        txNewHeadAC3,                  // Indicates the status of the txNewHeadAC3 bit of the
                                                     // DMA Control register
   input  wire        txNewHeadBcn,                  // Indicates the status of the txNewHeadBcn bit of the
                                                     // DMA Control register
   input  wire        rxNewTailHdr,                  // Indicates the status of the rxHeaderNewTail bit of the
                                                     // DMA Control register
   input  wire        rxNewTailPld,                  // Indicates the status of the rxPayloadNewTail bit of the
                                                     // DMA Control register
   input  wire        rxNewHeadHdr,                  // Indicates the status of the rxHeaderNewHead bit of the
                                                     // DMA Control register
   input  wire        rxNewHeadPld,                  // Indicates the status of the rxPayloadNewHead bit of the 
                                                     // DMA Control register
   input  wire        haltAC0AfterTXOP,              // Indicates the status of the haltAC0AfterTXOP bit of the
                                                     // DMA Control register
   input  wire        haltAC1AfterTXOP,              // Indicates the status of the haltAC1AfterTXOP bit of the
                                                     // DMA Control register
   input  wire        haltAC2AfterTXOP,              // Indicates the status of the haltAC2AfterTXOP bit of the
                                                     // DMA Control register
   input  wire        haltAC3AfterTXOP,              // Indicates the status of the haltAC3AfterTXOP bit of the 
                                                     // DMA Control register                                    
   input  wire        haltBcnAfterTXOP,              // Indicates the status of the haltBcnAfterTXOP bit of the
                                                     // DMA Control register
   input  wire [31:0] txAC0HeadPtr,                  // Transmit AC0 List Head Pointer
   input  wire [31:0] txAC1HeadPtr,                  // Transmit AC1 List Head Pointer
   input  wire [31:0] txAC2HeadPtr,                  // Transmit AC2 List Head Pointer
   input  wire [31:0] txAC3HeadPtr,                  // Transmit AC3 List Head Pointer
   input  wire [31:0] txBcnHeadPtr,                  // Transmit Beacon List Head Pointer
   input  wire [31:0] rxHdrHeadPtr,                  // Header channel head pointer
   input  wire [31:0] rxPldHeadPtr,                  // Payload channel head pointer
   input  wire  [7:0] rxPayloadUsedCount,            // Received Payload Used Count
   input  wire        txCtrlRegBusy,                 // TX Control Registers
                                                     // Indicates there are 2 sets of parameters
                                                     // already in the tx Parameter Cache module
                                                     // and not to fetch more
   input  wire        txStateActiveMC,               // Flag indicating that the macCoreClk Domain see a DMA ACTIVE state

   //
   output wire        txCtrlRegWr,                   // TX parameter Cache module signals
                                                     // Write signal to the Tx Parameter Cache
   output wire        txCtrlRegPT,                   // Indicates currently Policy table information is
                                                     // being passed
   output wire        txCtrlRegHD,                   // Indicates currently Header descriptor information
                                                     // is being passed
   output wire        txBcnLenMismatch,              // Transmit Beacon Length Mismatch
   output wire        txAC0LenMismatch,              // Transmit AC0 Length Mismatch
   output wire        txAC1LenMismatch,              // Transmit AC1 Length Mismatch
   output wire        txAC2LenMismatch,              // Transmit AC2 Length Mismatch
   output wire        txAC3LenMismatch,              // Transmit AC3 Length Mismatch
   output wire        txBcnUPatternErr,              // Transmit Beacon Unique Pattern Error
   output wire        txAC0UPatternErr,              // Transmit AC0 Unique Pattern Error
   output wire        txAC1UPatternErr,              // Transmit AC1 Unique Pattern Erro
   output wire        txAC2UPatternErr,              // Transmit AC2 Unique Pattern Error
   output wire        txAC3UPatternErr,              // Transmit AC3 Unique Pattern Error
   output wire        txBcnNextPointerErr,           // Transmit Beacon Next Pointer Error
   output wire        txAC0NextPointerErr,           // Transmit AC0 Next Pointer Error
   output wire        txAC1NextPointerErr,           // Transmit AC1 Next Pointer Error
   output wire        txAC2NextPointerErr,           // Transmit AC2 Next Pointer Error
   output wire        txAC3NextPointerErr,           // Transmit AC3 Next Pointer Error
   output wire        txBcnPTAddressErr,             // Transmit Beacon Policy Table Address Error
   output wire        txAC0PTAddressErr,             // Transmit AC0 Policy Table Address Error
   output wire        txAC1PTAddressErr,             // Transmit AC1 Policy Table Address Error
   output wire        txAC2PTAddressErr,             // Transmit AC2 Policy Table Address Error
   output wire        txAC3PTAddressErr,             // Transmit AC3 Policy Table Address Error
   output wire        txBcnBusErr,                   // Transmit Beacon Bus Error
   output wire        txAC0BusErr,                   // Transmit AC0 Bus Error
   output wire        txAC1BusErr,                   // Transmit AC1 Bus Error
   output wire        txAC2BusErr,                   // Transmit AC2 Bus Error
   output wire        txAC3BusErr,                   // Transmit AC3 Bus Error
   output wire        txBcnNewHeadErr,               // Transmit Beacon New Head Error
   output wire        txAC0NewHeadErr,               // Transmit AC0 New Head Error
   output wire        txAC1NewHeadErr,               // Transmit AC1 New Head Error
   output wire        txAC2NewHeadErr,               // Transmit AC2 New Head Error
   output wire        txAC3NewHeadErr,               // Transmit AC3 New Head Error
   output wire        rxHdrUPatternErr,              // Receive Header Unique Pattern Error
   output wire        rxPayUPatternErr,              // Receive Payload Unique Pattern Error
   output wire        rxHdrNextPointerErr,           // Receive Header Next Pointer Error
   output wire        rxPayNextPointerErr,           // Receive Payload Next Pointer Error
   output wire        rxHdrBusErr,                   // Receive Header Bus Error
   output wire        rxPayBusErr,                   // Receive Payload Bus Error
   output wire        rxHdrNewHeadErr,               // Receive Header New Head Error
   output wire        rxPayNewHeadErr,               // Receive Payload New Head Error
   output wire        ptError,                       // Transmit PolicyTable Error
   output wire        txBcnStartup,                  // Transmit Beacon Startup
   output wire        txAC0Startup,                  // Transmit AC0 New Head Error
   output wire        txAC1Startup,                  // Transmit AC1 New Head Error
   output wire        txAC2Startup,                  // Transmit AC2 New Head Error
   output wire        txAC3Startup,                  // Transmit AC3 New Head Error
   output wire        txBcnEndQ,                     // Transmit Beacon End of Queue
   output wire        txAC0EndQ,                     // Transmit AC0 End of Queue
   output wire        txAC1EndQ,                     // Transmit AC1 End of Queue
   output wire        txAC2EndQ,                     // Transmit AC2 End of Queue
   output wire        txAC3EndQ,                     // Transmit AC3 End of Queue
   output wire        txBcnHaltAfterTXOP,            // Transmit Beacon Halt After TXOP
   output wire        txAC0HaltAfterTXOP,            // Transmit AC0 Halt After TXOP
   output wire        txAC1HaltAfterTXOP,            // Transmit AC1 Halt After TXOP
   output wire        txAC2HaltAfterTXOP,            // Transmit AC2 Halt After TXOP
   output wire        txAC3HaltAfterTXOP,            // Transmit AC3 Halt After TXOP
   output wire        statusUpdated_p,               // Indication from the DMA that status have been updated.
   
   // Tx Status pointers
   output wire [31:0] ac0StatusPointer,              // Status ptr of AC0 channel
   output wire [31:0] ac1StatusPointer,              // status ptr of AC1 channel
   output wire [31:0] ac2StatusPointer,              // status ptr of AC2 channel
   output wire [31:0] ac3StatusPointer,              // Status ptr of AC3 channel
   output wire [31:0] bcnStatusPointer,              // status ptr of beacon channel
   output wire [31:0] currentPtr,                    // the current pointer of the txListProcessor
   
   //Rx Status Pointers
   output wire [31:0] hdrStatusPointer,              // status pointer of header channel
   output wire [31:0] pldStatusPointer,              // status pointer of payload channel
   output wire [31:0] rxPayCurrentPointer,           // Keeps track of the payload linked list
   


   //Signal to TX Parameter Cache module. 
   output wire        discardPrevHD_p,               // Indicates to discard the recently
                                                     // fetch Header Descriptor
   output wire        rstAC0NewTail,                 // Reset signal to reset the txAC0NewTail bit in
                                                     // the DMA Control register
   output wire        rstAC1NewTail,                 // Reset signal to reset the txAC1NewTail bit in
                                                     // the DMA Control register
   output wire        rstAC2NewTail,                 // Reset signal to reset the txAC2NewTail bit in
                                                     // the DMA Control register
   output wire        rstAC3NewTail,                 // Reset signal to reset the txAC3NewTail bit in
                                                     // the DMA Control register
   output wire        rstBcnNewTail,                 // Reset signal to reset the txBcnNewTail bit in
                                                     // the DMA Control register
   output wire        rstAC0NewHead,                 // Reset signal to reset the txAC0NewHead bit in
                                                     // the DMA Control register
   output wire        rstAC1NewHead,                 // Reset signal to reset the txAC1NewHead bit in
                                                     // the DMA Control register
   output wire        rstAC2NewHead,                 // Reset signal to reset the txAC2NewHead bit in
                                                     // the DMA Control register
   output wire        rstAC3NewHead,                 // Reset signal to reset the txAC3NewHead bit in
                                                     // the DMA Control register
   output wire        rstBcnNewHead,                 // Reset signal to reset the txBcnNewHead bit in
                                                     // the DMA Control register
   output wire        rstNewTailHdr,                 // Reset signal to reset the rxHeaderNewTail bit in
                                                     // the DMA Control register
   output wire        rstNewHeadHdr,                 // Reset signal to reset the rxHeaderNewHead bit in
                                                     // the DMA Control register
   output wire        rstNewTailPld,                 // Reset signal to reset the rxPayloadNewTail bit in
                                                     // the DMA Control register
   output wire        rstNewHeadPld,                 // Reset signal to reset the rxPayloadNewHead bit in
                                                     // the DMA Control register
   output wire  [3:0] txAC0State,                    // DMA state for AC0 channel. Registers will be updated with
                                                     // this information
   output wire  [3:0] txAC1State,                    // DMA state for AC1 channel. Registers will be updated with
                                                     // this information
   output wire  [3:0] txAC2State,                    // DMA state for AC2 channel. Registers will be updated with
                                                     // this information
   output wire  [3:0] txAC3State,                    // DMA state for AC3 channel. Registers will be updated with
                                                     // this information
   output wire  [3:0] txBcnState,                    // DMA state for Beacon channel. Registers will be updated with
                                                     // this information
   output wire  [3:0] rxHeaderState,                 // DMA state for Receive Header channel. Registers will be updated
                                                     // with this information
   output wire  [3:0] rxPayloadState,                // DMA state for Payload Header channel. Registers will be updated
                                                     // with this information
   // debug output
   output wire  [4:0] txListProcCs,                  // Current State counter                                                
   output wire  [4:0] rxListProcCs,                  // Current State counter                                                
   output wire        statusUpdaterFull,             // Indicate the status updater is full
   output wire [15:0] debugPortDMA3,                 // txListProc Debug Port
   output wire [15:0] debugPortDMA5,                 // dmaEngine Debug Port
   output wire [15:0] debugPortDMA6,                 // txListProc Debug Port
   output wire [15:0] debugPortDMAStatus,            // dmaEngine Status Debug Port
   output wire [15:0] debugPortDMATxStatus,          // txStatusUpdater Debug Port
   output wire        dmaInternalError,              // Generate a pulse when an internal error occured

   //Interrupt Controller
   output wire        interruptEnTx,                 // Interrupt Enable information in THD
   output wire        bufferInterruptTx,              //bufferInterruptTx bit in Status quadlets in TPD

   //Transmit Channel error
   output wire        bcnTxDMADead,                  // bcnTxDMADead output mask interruption
   output wire        ac3TxDMADead,                  // ac3TxDMADead output mask interruption
   output wire        ac2TxDMADead,                  // ac2TxDMADead output mask interruption
   output wire        ac1TxDMADead,                  // ac1TxDMADead output mask interruption
   output wire        ac0TxDMADead,                  // ac0TxDMADead output mask interruption

   //Receive Channel error
   output wire        rxPayloadDMADead,              // rxPayloadDMADead output mask interruption
   output wire        rxHeaderDMADead,               // rxHeaderDMADead output mask interruption
   output wire        rxDMAEmpty,                    // RX DMA Empty Interrupt
   output wire        tx0Trigger,                    // trigger for transmission interrupt for AC0,
   output wire        tx1Trigger,                    // trigger for transmission interrupt for AC1,
   output wire        tx2Trigger,                    // trigger for transmission interrupt for AC2,
   output wire        tx3Trigger,                    // trigger for transmission interrupt for AC3,
   output wire        bcnTrigger,                    // trigger for transmission interrupt for Beacon,
   output wire        rxTrigger,                     // Trigger for receive interrupt
   output wire        counterRxTrigger,              // Interrupt indicating that the processed number of payload descriptor
                                                     // if bigger or equal to 
   output wire        rxTrig_p,                      // Indicate that the RX Descriptor Done has been written
   output wire        rxListProcCsIsIdle,            // Data read from RX FIFO

   // Debug Purpose
   output wire [15:0] debugPortTxRxListA,
   output wire [15:0] debugPortDmaRdWrCtlr
);

// 


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////


// Rx List Processor port
wire [31:0] rxListStartAddress;                      // Starting Address from the system memory to read or write the data
wire        rxListRead;                              // Read enable
wire        rxListWrite;                             // Write enable
wire [ 2:0] rxListSize;                              // Access size
wire [31:0] rxListWriteData;                         // Written data
wire        rxListLast;                              // Last access flag
wire        rxListNextData;                          // Data written, push the next data        
wire [31:0] rxListReadData;                          // Read data
wire        rxListReadDataValid;                     // Read data Valid
wire        rxListError;                             // Transfer Error
wire        rxListTransComplete;                     // transaction done

//Tx List Processor port
wire [31:0] txListStartAddress;                      // Starting Address from the system memory to read or write the data
wire        txListRead;                              // Read enable
wire [ 2:0] txListSize;                              // Access size
wire        txListWrite;                              // Read enable
wire [31:0] txListWriteData;                         // Written data
wire        txListLast;                              // Last access flag
wire        txListNextData;                          // Next data to be written can be pushed
wire [31:0] txListReadData;                          // Read data
wire        txListReadDataValid;                     // Read data Valid
wire        txListError;                             // Transfer Error
wire        txListTransComplete;                     // transaction done
wire        txListProcIdle;                          // indicate the list processor is idle

//$port_g Tx Status updater port
wire [31:0] staUpdStartAddress;                      // Starting Address from the system memory to read or write the data
wire        staUpdWrite;                             // Write enable
wire [31:0] staUpdWriteData;                         // Written data
wire        staUpdNextData;                          // Data written, push the next data        
wire        staUpdError;                             // Transfer Error
wire        staUpdTransComplete;                     // transaction done

wire        txListProcReq;                           // Request to arbiter from transmit list proc
wire        rxListProcReq;                           // request to arbiter from receive list proc

//internals
wire        trigAC0Halt_p;    
wire        trigAC0Dead_p;                           // trigger AC0 prim ctlr to HALTED
wire        ac0TrigTxListProc;                       // trigger AC0 prim ctlr to DEAD
// wire  [3:0] txAC0State;                           // trigger for tx list proc from AC0 prim ctlr
                                                     // state of the AC0 primary controller
wire        trigAC1Halt_p;    
wire        trigAC1Dead_p;                           // trigger AC1 prim ctlr to HALTED
wire        ac1TrigTxListProc;                       // trigger AC1 prim ctlr to DEAD
// wire  [3:0] txAC1State;                           // trigger for tx list proc from AC1 prim ctlr 
                                                     // state of the AC1 primary controller

wire        trigAC2Halt_p;    
wire        trigAC2Dead_p;                           // trigger AC2 prim ctlr to HALTED
wire        ac2TrigTxListProc;                       // trigger AC2 prim ctlr to DEAD
// wire  [3:0] txAC2State;                           // trigger for tx list proc from AC2 prim ctlr
                                                     // state of the AC2 primary controller
wire        trigAC3Halt_p;    
wire        trigAC3Dead_p;                           // trigger AC3 prim ctlr to HALTED
wire        ac3TrigTxListProc;                       // trigger AC3 prim ctlr to DEAD
// wire  [3:0] txAC3State;                           // trigger for tx list proc from AC3 prim ctlr
                                                     // state of the AC3 primary controller
wire        trigBcnHalt_p;    
wire        trigBcnDead_p;                           // trigger Bcn prim ctlr to HALTED
wire        bcnTrigTxListProc;                       // trigger Bcn prim ctlr to DEAD
                                                     // trigger for tx list proc from Bcn prim ctlr
wire        trigHalt_p;                              // from tx List proc to halt active channel. 
wire        trigDead_p;                              // from tx List Proc to move active channel 2 dead

wire [31:0] statusPointer;                           // status ptr of active channel to tx list proc

                                                     
wire        nxtMpduDescValidAc0;                     // next MPDU Desc ptr for AC0 channel is valid
wire        nxtMpduDescValidAc1;                     // next MPDU Desc ptr for AC1 channel is valid
wire        nxtMpduDescValidAc2;                     // next MPDU Desc ptr for AC2 channel is valid
wire        nxtMpduDescValidAc3;                     // next MPDU Desc ptr for AC3 channel is valid
wire        nxtMpduDescValidBcn;                     // next MPDU Desc ptr for BCN channel is valid
wire        updAc0StaPtr_p;                          // Pulse to update status ptr of AC0 channel
wire        updAc1StaPtr_p;                          // Pulse to update status ptr of AC1 channel
wire        updAc2StaPtr_p;                          // Pulse to update status ptr of AC2 channel
wire        updAc3StaPtr_p;                          // Pulse to update status ptr of AC3 channel
wire        updBcnStaPtr_p;                          // Pulse to update status ptr of BCN channel
wire        lifetimeExpired_p;                       // lifetime expired indication 

wire [31:0] nxtAtomFrmPtr;                           // status ptr will be updated to this location
                                                     // if the recently transmitted frame was an 
                                                     // AMPDU frame

wire [31:0] updateStatusPtr;                         // the status ptr is updated to this location

// wire        rxBusError;                              // Bus error during a transfer req by rx list proc

wire        updHdrStaPtr_p;                          // Update status pointer signal for header channel
wire        updPldStaPtr_p;                          // update status ptr signal for payload channel
wire [31:0] nxtPldDescPtr;                           // next Desc ptr for the payload channel
wire [31:0] nxtHdrDescPtr;                           // next descr ptr for the header channel
wire        nxtAtomFrmPtrValidAc0;
wire        nxtAtomFrmPtrValidAc1;
wire        nxtAtomFrmPtrValidAc2;
wire        nxtAtomFrmPtrValidAc3;
wire        nxtMpduDescValid;
wire        nxtAtomFrmPtrValidBcn;
wire        atomicFrmValid_p;                        // indicates next atomic frm ptr is valid
wire        trigTxListProc;
wire        mpduCtrFull;
wire        prevFrmRts;
wire        txListProcGrant;
wire        txStaUpdaterReq;
wire        txStaUpdaterGrant;
wire        txFIFOFlushDMA;
wire        storeParameters_p;
wire        storeAMPDUParameters_p;
wire        rxListProcGrant;
wire        trigHdrPassive_p;
wire        trigPldPassive_p;
wire        trigHdrHalt_p;
wire        trigPldHalt_p;
wire        trigHdrActive_p;
wire        trigPldActive_p;
wire        trigHdrDead_p;
wire        stopDma_p;
wire        trigPldDead_p;
wire        trigBcnDeadListProc_p;
wire        trigAc0DeadListProc_p;
wire        trigAc1DeadListProc_p;
wire        trigAc2DeadListProc_p;
wire        trigAc3DeadListProc_p;
wire        trigDeadBCNStaUpd_p;
wire        trigDeadAC0StaUpd_p;
wire        trigDeadAC1StaUpd_p;
wire        trigDeadAC2StaUpd_p;
wire        trigDeadAC3StaUpd_p;
wire        patternError;
wire        abortTx_p;                               // Indication to TX List Proc to abort all        
                                                     // current transactions due to either             
                                                     // end of TXOP or data under run error            
                                                     // detected                                       
wire        updStatusPtr_p;
wire        noFrm2Update;                            // Indicates there are no frames whose status     
                                                     // is expected                                    

wire        trigNxtAtomFrm_p;                        // Indicates to the TxList Proc should            
                                                     // updated to the next atomic frame xchange       
wire [31:0] statusPtr2Upd;

reg         trigTxAC0Delayed;                        // Delayed version of trig from MAC for queue 0   
reg         trigTxAC1Delayed;                        // Delayed version of trig from MAC for queue 1   
reg         trigTxAC2Delayed;                        // Delayed version of trig from MAC for queue 2   
reg         trigTxAC3Delayed;                        // Delayed version of trig from MAC for queue 3   
reg         trigTxBcnDelayed;                        // Delayed version of trig from MAC for queue Bcn 
wire        plyTblValid;                             // Transmit Policy Table Address Valid            

wire        rdWrCtlrIdle;                            // read/Write controller status

wire [31:0] statusInformationReg;                    // value of status information register

wire [15:0] rxListProcDebug;
wire [15:0] txStatusDebug;

reg         rxListProcGrantCapt;

wire [15:0] debugPortRxListA;
wire [15:0] debugPortTxListA;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// Instanciation of txPrimCtrl
// Name of the instance : U_txPrimCtrl
// Name of the file containing this module : txPrimCtrl.v
txPrimCtrl U_txAC0PrimCtrl (
    .macPITxClk             (macPIClk),
    .macPITxClkHardRst_n    (macPIClkHardRst_n),
    .macPITxClkSoftRst_n    (macPIClkSoftRst_n),
    .trigTxPCHalt_p         (trigAC0Halt_p),
    .trigTxPCDead_p         (trigAC0Dead_p),
    .trigTxPCActive         (trigTxAC0),
    .txNewTail              (txNewTailAC0),
    .nxtAtomFrmPtrValid     (nxtAtomFrmPtrValidAc0),
    .nxtMpduDescPtrValid    (nxtMpduDescValidAc0),
    .txNewHead              (txNewHeadAC0),
    .haltAfterTxop          (haltAC0AfterTXOP),
    .updPCStaPtr_p          (updAc0StaPtr_p),
    .txHeadPtr              (txAC0HeadPtr),
    .nxtDescPtr             (updateStatusPtr),
    .pcStatusPtr            (ac0StatusPointer),
    .pcTrigTxListProc       (ac0TrigTxListProc),
    .rstNewHead_p           (rstAC0NewHead),
    .rstNewTail_p           (rstAC0NewTail),
    .txNewHeadErr           (txAC0NewHeadErr),
    .txStartup              (txAC0Startup),
    .txEndQ                 (txAC0EndQ),
    .txHaltAfterTXOP        (txAC0HaltAfterTXOP),
    .txDMADead              (ac0TxDMADead),
    .txDmaPCState           (txAC0State),
    .txStateActiveMC        (txStateActiveMC)
);

//TX Primary Controller instantiation for AC1                   
txPrimCtrl U_txAC1PrimCtrl (
    .macPITxClk             (macPIClk),
    .macPITxClkHardRst_n    (macPIClkHardRst_n),
    .macPITxClkSoftRst_n    (macPIClkSoftRst_n),
    .trigTxPCHalt_p         (trigAC1Halt_p),
    .trigTxPCDead_p         (trigAC1Dead_p),
    .trigTxPCActive         (trigTxAC1),
    .txNewTail              (txNewTailAC1),
    .nxtAtomFrmPtrValid     (nxtAtomFrmPtrValidAc1),
    .nxtMpduDescPtrValid    (nxtMpduDescValidAc1),
    .txNewHead              (txNewHeadAC1),
    .haltAfterTxop          (haltAC1AfterTXOP),
    .updPCStaPtr_p          (updAc1StaPtr_p),
    .txHeadPtr              (txAC1HeadPtr),
    .nxtDescPtr             (updateStatusPtr),
    .pcStatusPtr            (ac1StatusPointer),
    .pcTrigTxListProc       (ac1TrigTxListProc),
    .rstNewHead_p           (rstAC1NewHead),
    .rstNewTail_p           (rstAC1NewTail),
    .txNewHeadErr           (txAC1NewHeadErr),
    .txStartup              (txAC1Startup),
    .txEndQ                 (txAC1EndQ),
    .txHaltAfterTXOP        (txAC1HaltAfterTXOP),
    .txDMADead              (ac1TxDMADead),
    .txDmaPCState           (txAC1State),
    .txStateActiveMC        (txStateActiveMC)
);

//TX Primary Controller instantiation for AC2
txPrimCtrl U_txAC2PrimCtrl (
    .macPITxClk             (macPIClk),
    .macPITxClkHardRst_n    (macPIClkHardRst_n),
    .macPITxClkSoftRst_n    (macPIClkSoftRst_n),
    .trigTxPCHalt_p         (trigAC2Halt_p),
    .trigTxPCDead_p         (trigAC2Dead_p),
    .trigTxPCActive         (trigTxAC2),
    .txNewTail              (txNewTailAC2),
    .nxtAtomFrmPtrValid     (nxtAtomFrmPtrValidAc2),
    .nxtMpduDescPtrValid    (nxtMpduDescValidAc2),
    .txNewHead              (txNewHeadAC2),
    .haltAfterTxop          (haltAC2AfterTXOP),
    .updPCStaPtr_p          (updAc2StaPtr_p),
    .txHeadPtr              (txAC2HeadPtr),
    .nxtDescPtr             (updateStatusPtr),
    .pcStatusPtr            (ac2StatusPointer),
    .pcTrigTxListProc       (ac2TrigTxListProc),
    .rstNewHead_p           (rstAC2NewHead),
    .rstNewTail_p           (rstAC2NewTail),
    .txNewHeadErr           (txAC2NewHeadErr),
    .txStartup              (txAC2Startup),
    .txEndQ                 (txAC2EndQ),
    .txHaltAfterTXOP        (txAC2HaltAfterTXOP),
    .txDMADead              (ac2TxDMADead),
    .txDmaPCState           (txAC2State),
    .txStateActiveMC        (txStateActiveMC)
);

//TX Primary Controller instantiation for AC3
txPrimCtrl U_txAC3PrimCtrl (
    .macPITxClk             (macPIClk),
    .macPITxClkHardRst_n    (macPIClkHardRst_n),
    .macPITxClkSoftRst_n    (macPIClkSoftRst_n),
    .trigTxPCHalt_p         (trigAC3Halt_p),
    .trigTxPCDead_p         (trigAC3Dead_p),
    .trigTxPCActive         (trigTxAC3),
    .txNewTail              (txNewTailAC3),
    .nxtAtomFrmPtrValid     (nxtAtomFrmPtrValidAc3),
    .nxtMpduDescPtrValid    (nxtMpduDescValidAc3),
    .txNewHead              (txNewHeadAC3),
    .haltAfterTxop          (haltAC3AfterTXOP),
    .updPCStaPtr_p          (updAc3StaPtr_p),
    .txHeadPtr              (txAC3HeadPtr),
    .nxtDescPtr             (updateStatusPtr),
    .pcStatusPtr            (ac3StatusPointer),
    .pcTrigTxListProc       (ac3TrigTxListProc),
    .rstNewHead_p           (rstAC3NewHead),
    .rstNewTail_p           (rstAC3NewTail),
    .txNewHeadErr           (txAC3NewHeadErr),
    .txStartup              (txAC3Startup),
    .txEndQ                 (txAC3EndQ),
    .txHaltAfterTXOP        (txAC3HaltAfterTXOP),
    .txDMADead              (ac3TxDMADead),
    .txDmaPCState           (txAC3State),
    .txStateActiveMC        (txStateActiveMC)
);

//TX Primary Controller instantiation for Beacon
txPrimCtrl U_txBcnPrimCtrl (
    .macPITxClk             (macPIClk),
    .macPITxClkHardRst_n    (macPIClkHardRst_n),
    .macPITxClkSoftRst_n    (macPIClkSoftRst_n),
    .trigTxPCHalt_p         (trigBcnHalt_p),
    .trigTxPCDead_p         (trigBcnDead_p),
    .trigTxPCActive         (trigTxBcn),
    .txNewTail              (txNewTailBcn),
    .nxtAtomFrmPtrValid     (nxtAtomFrmPtrValidBcn),
    .nxtMpduDescPtrValid    (nxtMpduDescValidBcn),
    .txNewHead              (txNewHeadBcn),
    .haltAfterTxop          (haltBcnAfterTXOP),
    .updPCStaPtr_p          (updBcnStaPtr_p),
    .txHeadPtr              (txBcnHeadPtr),
    .nxtDescPtr             (updateStatusPtr),
    .pcStatusPtr            (bcnStatusPointer),
    .pcTrigTxListProc       (bcnTrigTxListProc),
    .rstNewHead_p           (rstBcnNewHead),
    .rstNewTail_p           (rstBcnNewTail),
    .txNewHeadErr           (txBcnNewHeadErr),
    .txStartup              (txBcnStartup),
    .txHaltAfterTXOP        (txBcnHaltAfterTXOP),
    .txEndQ                 (txBcnEndQ),
    .txDMADead              (bcnTxDMADead),
    .txDmaPCState           (txBcnState),
    .txStateActiveMC        (txStateActiveMC)
);

//TX Primary Controller Selection Logic
txPrimCtrlSelLogic  U_txPrimCtrlSelLogic (
    .macPITxClk             (macPIClk),
    .macPITxClkHardRst_n    (macPIClkHardRst_n),
    .macPITxClkSoftRst_n    (macPIClkSoftRst_n),
    .trigHalt_p             (trigHalt_p),
    .trigDead_p             (trigDead_p),
    .underRunDetected_p     (underRunDetected_p),
    .patternError           (patternError),
    .dmaHIFError            (dmaHIFError),  
    .nxtAtomFrmPtrValid     (atomicFrmValid_p),
    .nxtMpduDescValid       (nxtMpduDescValid),
    .bcnStatusPointer       (bcnStatusPointer),
    .bcnTrigTxListProc      (bcnTrigTxListProc),
    .ac0StatusPointer       (ac0StatusPointer),
    .ac0TrigTxListProc      (ac0TrigTxListProc),
    .ac1StatusPointer       (ac1StatusPointer),
    .ac1TrigTxListProc      (ac1TrigTxListProc),
    .ac2StatusPointer       (ac2StatusPointer),
    .ac2TrigTxListProc      (ac2TrigTxListProc),
    .ac3StatusPointer       (ac3StatusPointer),
    .ac3TrigTxListProc      (ac3TrigTxListProc),
    .plyTblValid            (plyTblValid),
    .statusPointer          (statusPointer),
    .trigTxListProc         (trigTxListProc),
    .trigBcnHalt_p          (trigBcnHalt_p),
    .trigBcnDead_p          (trigBcnDeadListProc_p),
    .nxtAtomFrmPtrValidBcn  (nxtAtomFrmPtrValidBcn),
    .nxtMpduDescValidBcn    (nxtMpduDescValidBcn), 
    .trigAc0Halt_p          (trigAC0Halt_p),
    .trigAc0Dead_p          (trigAc0DeadListProc_p),
    .nxtAtomFrmPtrValidAc0  (nxtAtomFrmPtrValidAc0),
    .nxtMpduDescValidAc0    (nxtMpduDescValidAc0), 
    .trigAc1Halt_p          (trigAC1Halt_p),
    .trigAc1Dead_p          (trigAc1DeadListProc_p),
    .nxtAtomFrmPtrValidAc1  (nxtAtomFrmPtrValidAc1),
    .nxtMpduDescValidAc1    (nxtMpduDescValidAc1), 
    .trigAc2Halt_p          (trigAC2Halt_p),
    .trigAc2Dead_p          (trigAc2DeadListProc_p),
    .nxtAtomFrmPtrValidAc2  (nxtAtomFrmPtrValidAc2),
    .nxtMpduDescValidAc2    (nxtMpduDescValidAc2), 
    .trigAc3Halt_p          (trigAC3Halt_p),
    .trigAc3Dead_p          (trigAc3DeadListProc_p),
    .nxtAtomFrmPtrValidAc3  (nxtAtomFrmPtrValidAc3),
    .nxtMpduDescValidAc3    (nxtMpduDescValidAc3),
    .txBcnLenMismatch       (txBcnLenMismatch), 
    .txAC0LenMismatch       (txAC0LenMismatch), 
    .txAC1LenMismatch       (txAC1LenMismatch), 
    .txAC2LenMismatch       (txAC2LenMismatch), 
    .txAC3LenMismatch       (txAC3LenMismatch),     
    .txBcnUPatternErr       (txBcnUPatternErr),     
    .txAC0UPatternErr       (txAC0UPatternErr),     
    .txAC1UPatternErr       (txAC1UPatternErr),     
    .txAC2UPatternErr       (txAC2UPatternErr),     
    .txAC3UPatternErr       (txAC3UPatternErr),     
    .txBcnNextPointerErr    (txBcnNextPointerErr),  
    .txAC0NextPointerErr    (txAC0NextPointerErr),  
    .txAC1NextPointerErr    (txAC1NextPointerErr),  
    .txAC2NextPointerErr    (txAC2NextPointerErr),  
    .txAC3NextPointerErr    (txAC3NextPointerErr),  
    .txBcnPTAddressErr      (txBcnPTAddressErr),     
    .txAC0PTAddressErr      (txAC0PTAddressErr),    
    .txAC1PTAddressErr      (txAC1PTAddressErr),    
    .txAC2PTAddressErr      (txAC2PTAddressErr),    
    .txAC3PTAddressErr      (txAC3PTAddressErr),    
    .txBcnBusErr            (txBcnBusErr),          
    .txAC0BusErr            (txAC0BusErr),          
    .txAC1BusErr            (txAC1BusErr),          
    .txAC2BusErr            (txAC2BusErr),          
    .txAC3BusErr            (txAC3BusErr)
);


// Instanciation of txListProc
// Name of the instance : U_txListProc
// Name of the file containing this module : txListProc.v
txListProc U_txListProc (
		.macPITxClk             (macPITxClk),
		.macPITxClkHardRst_n    (macPITxClkHardRst_n),
		.macPITxClkSoftRst_n    (macPITxClkSoftRst_n),
		.statusPointer          (statusPointer),
		.trigTxListProc         (trigTxListProc),
		.abortTx_p              (abortTx_p),
		.trigHalt_p             (trigHalt_p),
		.trigDead_p             (trigDead_p),
		.lifetimeExpired_p      (lifetimeExpired_p),
		.txFIFOFlushDone_p      (txFIFOFlushDone_p),
		.txFIFOFlushDMA         (txFIFOFlushDMA),
		.discardPrevHD_p        (discardPrevHD_p),
		.nxtMpduDescValid       (nxtMpduDescValid),
		.atomicFrmValid_p       (atomicFrmValid_p),
		.plyTblValid            (plyTblValid),
		.nxtAtomFrmPtr          (nxtAtomFrmPtr),
		.patternError           (patternError),
		.ptError                (ptError),
		.txFifoEmpty            (txFifoEmpty),
		.txFifoAlmostFull       (txFifoAlmostFull),
		.txFifoFull             (txFifoFull),
		.txFifoWr               (txFifoWr),
		.txFifoWrData           (txFifoWrData),
		.txTagFifoWrData        (txTagFifoWrData),
		.noFrm2Update           (noFrm2Update),
		.txCtrlRegBusy          (txCtrlRegBusy),
		.updateDMAStatus_p      (updateDMAStatus_p),
		.retryFrame_p           (retryFrame_p),
		.trigNxtAtomFrm_p       (trigNxtAtomFrm_p),
		.mpduCtrFull            (mpduCtrFull),
		.prevFrmRts             (prevFrmRts),
		.tsfTimerValue          (tsfTimerValue),
		.storeParameters_p      (storeParameters_p),
		.storeAMPDUParameters_p (storeAMPDUParameters_p),
		.updStatusPtr_p         (updStatusPtr_p),
		.statusPtr2Upd          (statusPtr2Upd),
		.currentPtr             (currentPtr),
		.statusInformationReg   (statusInformationReg),
		.txCtrlRegWr            (txCtrlRegWr),
		.txCtrlRegHD            (txCtrlRegHD),
		.txCtrlRegPT            (txCtrlRegPT),
		.interruptEnTx          (interruptEnTx),
 		.bufferInterruptTx      (bufferInterruptTx),
		.txListProcGrant        (txListProcGrant),
		.txListProcReq          (txListProcReq),
		.txListProcCs           (txListProcCs),
		.txListNextData         (txListNextData),
		.txListReadData         (txListReadData),
		.txListReadDataValid    (txListReadDataValid),
		.txListError            (txListError),
		.txListRead             (txListRead),
		.txListWrite            (txListWrite),
		.txListSize             (txListSize),
		.txListWriteData        (txListWriteData),
 		.txListLast             (txListLast),
		.txListTransComplete    (txListTransComplete),
		.txListStartAddress     (txListStartAddress),
		.txListProcIdle         (txListProcIdle),
		.staUpdTransComplete    (staUpdTransComplete),
		.debugPortDMA3          (debugPortDMA3),
		.debugPortDMA6          (debugPortDMA6),
		.debugPortTxListA       (debugPortTxListA)
		);

// Instanciation of txStatusUpdater
// Name of the instance : U_txStatusUpdater
// Name of the file containing this module : txStatusUpdater.v
txStatusUpdater U_txStatusUpdater (
		.macPITxClk                       (macPITxClk),
		.macPITxClkHardRst_n              (macPITxClkHardRst_n),
		.macPITxClkSoftRst_n              (macPITxClkSoftRst_n),
		.ac0TrigTxListProc                (ac0TrigTxListProc),
		.ac1TrigTxListProc                (ac1TrigTxListProc),
		.ac2TrigTxListProc                (ac2TrigTxListProc),
		.ac3TrigTxListProc                (ac3TrigTxListProc),
		.bcnTrigTxListProc                (bcnTrigTxListProc),
		.whichDescriptorSW                (whichDescriptorSW),
		.trigDeadBCNStaUpd_p              (trigDeadBCNStaUpd_p),
		.trigDeadAC0StaUpd_p              (trigDeadAC0StaUpd_p),
		.trigDeadAC1StaUpd_p              (trigDeadAC1StaUpd_p),
		.trigDeadAC2StaUpd_p              (trigDeadAC2StaUpd_p),
		.trigDeadAC3StaUpd_p              (trigDeadAC3StaUpd_p),
		.updBcnStaPtr_p                   (updBcnStaPtr_p),
		.updAc0StaPtr_p                   (updAc0StaPtr_p),
		.updAc1StaPtr_p                   (updAc1StaPtr_p),
		.updAc2StaPtr_p                   (updAc2StaPtr_p),
		.updAc3StaPtr_p                   (updAc3StaPtr_p),
		.updateStatusPtr                  (updateStatusPtr),
		.statusPtr2Upd                    (statusPtr2Upd),
		.updStatusPtr_p                   (updStatusPtr_p),
		.interruptEnTx                    (interruptEnTx),
		.lifetimeExpired_p                (lifetimeExpired_p),
		.storeParameters_p                (storeParameters_p),
		.storeAMPDUParameters_p           (storeAMPDUParameters_p),
		.retryLimitReached_p              (retryLimitReached_p),
		.statusPointer                    (statusPointer),
		.currentPtr                       (currentPtr),
		.statusInformationReg             (statusInformationReg),
		.nxtAtomFrmPtr                    (nxtAtomFrmPtr),
		.mpduCtrFull                      (mpduCtrFull),
		.prevFrmRts                       (prevFrmRts),
		.trigNxtAtomFrm_p                 (trigNxtAtomFrm_p),
		.statusUpdated_p                  (statusUpdated_p),
		.txListProcIdle                   (txListProcIdle),
		.noFrm2Update                     (noFrm2Update),
		.nxtMpduDescValid                 (nxtMpduDescValid),
		.updateDMAStatus_p                (updateDMAStatus_p),
		.rtsSuccess_p                     (rtsSuccess_p),
		.retryFrame_p                     (retryFrame_p),
		.rtsFailed_p                      (rtsFailed_p),
		.mpduSuccess_p                    (mpduSuccess_p),
		.mpduFailed_p                     (mpduFailed_p),
		.txMpduDone_p                     (txMpduDone_p),
		.transmissionBW                   (transmissionBW),
		.swRTS_p                          (swRTS_p),
		.ampduFrm_p                       (ampduFrm_p),
		.numMPDURetries                   (numMPDURetries),
		.numRTSRetries                    (numRTSRetries),
        .mediumTimeUsed                   (mediumTimeUsed),
		.flushTxFifo                      (flushTxFifo),
		.txStaUpdaterReq                  (txStaUpdaterReq), 
		.txStaUpdaterGrant                (txStaUpdaterGrant),
		.staUpdStartAddress               (staUpdStartAddress),
		.staUpdWrite                      (staUpdWrite),
		.staUpdWriteData                  (staUpdWriteData),
		.staUpdError                      (staUpdError),
		.staUpdNextData                   (staUpdNextData),
		.staUpdTransComplete              (staUpdTransComplete),
		.tx0Trigger                       (tx0Trigger),
		.tx1Trigger                       (tx1Trigger),
		.tx2Trigger                       (tx2Trigger),
		.tx3Trigger                       (tx3Trigger),
		.bcnTrigger                       (bcnTrigger),
		.txStatusDebug                    (txStatusDebug),
		.debugPortDMATxStatus             (debugPortDMATxStatus)
		);

// Instanciation of rxListProc
// Name of the instance : U_rxListProc
// Name of the file containing this module : rxListProc.v
rxListProc U_rxListProc (
		.macPIRxClk             (macPIRxClk),
		.macPIRxClkHardRst_n    (macPIRxClkHardRst_n),
		.macPIRxClkSoftRst_n    (macPIRxClkSoftRst_n),
		.rxFifoRd               (rxFifoRd),
		.rxFifoEmpty            (rxFifoEmpty),
		.rxFifoAlmEmpty         (rxFifoAlmEmpty),
		.rxTagFifoRdData        (rxTagFifoRdData),
		.rxFifoRdData           (rxFifoRdData),
		.rxListStartAddress     (rxListStartAddress),
		.rxListRead             (rxListRead),
		.rxListWrite            (rxListWrite),
		.rxListSize             (rxListSize),
		.rxListWriteData        (rxListWriteData),
		.rxListLast             (rxListLast),
		.rxListError            (rxListError),
		.rxListNextData         (rxListNextData),
		.rxListReadData         (rxListReadData),
		.rxListReadDataValid    (rxListReadDataValid),
		.rxListTransComplete    (rxListTransComplete),
		.rxListProcReq          (rxListProcReq),
		.rxListProcGrant        (rxListProcGrant),
		.hdrStatusPointer       (hdrStatusPointer),
		.rxHeaderState          (rxHeaderState),
		.rxPayloadState         (rxPayloadState),
 		.rxHeaderNewTail        (rstNewTailHdr),
		.rxPayloadNewTail       (rstNewTailPld),
		.trigHdrPassive_p       (trigHdrPassive_p),
		.trigHdrHalt_p          (trigHdrHalt_p),
		.trigHdrActive_p        (trigHdrActive_p),
		.trigHdrDead_p          (trigHdrDead_p),
		.updHdrStaPtr_p         (updHdrStaPtr_p),
		.nxtHdrDescPtr          (nxtHdrDescPtr),
		.rxHdrUPatternErr       (rxHdrUPatternErr),
		.rxHdrBusErr            (rxHdrBusErr),
		.rxHdrNextPointerErr    (rxHdrNextPointerErr),
		.pldStatusPointer       (pldStatusPointer),
		.trigPldPassive_p       (trigPldPassive_p),
		.trigPldHalt_p          (trigPldHalt_p),
		.trigPldActive_p        (trigPldActive_p),
		.trigPldDead_p          (trigPldDead_p),
		.updPldStaPtr_p         (updPldStaPtr_p),
		.nxtPldDescPtr          (nxtPldDescPtr),
		.rxPayUPatternErr       (rxPayUPatternErr),
		.rxPayBusErr            (rxPayBusErr),
		.rxPayNextPointerErr    (rxPayNextPointerErr),
		.frameRxed_p            (frameRxed_p),
		.rxListProcCsIsIdle     (rxListProcCsIsIdle),
		.rxFrmDiscard           (rxFrmDiscard),
		.rxDescAvailable        (rxDescAvailable),
		.rxFrmDiscardRet        (rxFrmDiscardRet),
		.rxTrigger              (rxTrigger),
		.counterRxTrigger       (counterRxTrigger),
		.rxTrig_p               (rxTrig_p),
		.rxFlowCntrlEn          (rxFlowCntrlEn),
		.rxPayloadUsedCount     (rxPayloadUsedCount),
		.rxPayCurrentPointer    (rxPayCurrentPointer),
		.rxListProcCs           (rxListProcCs),
		.rxListProcDebug        (rxListProcDebug),
		.debugPortRxListA       (debugPortRxListA)
		);


//Instantiation of Primary Controller for header channel
rxPrimCtrl U_rxHdrPrimCtrl (
    .macPIRxClk             (macPIClk),
    .macPIRxClkHardRst_n    (macPIClkHardRst_n),
    .macPIRxClkSoftRst_n    (macPIClkSoftRst_n),
    .trigHalt_p             (trigHdrHalt_p),
    .trigPassive_p          (trigHdrPassive_p),
    .trigActive_p           (trigHdrActive_p),
    .trigDead_p             (trigHdrDead_p),
    .rxNewTail              (rxNewTailHdr),
    .rxNewHead              (rxNewHeadHdr),
    .updStaPtr_p            (updHdrStaPtr_p),
    .rxHeadPtr              (rxHdrHeadPtr),
    .nxtDescPtr             (nxtHdrDescPtr),
    .rstNewTail             (rstNewTailHdr),
    .rstNewHead             (rstNewHeadHdr),
    .statusPtr              (hdrStatusPointer),
    .rxNewHeadErr           (rxHdrNewHeadErr),
    .rxDMADead              (rxHeaderDMADead),
    .rxDmaPCState           (rxHeaderState)
);

//Instantiation of Primary Controller for Payload channel
rxPrimCtrl U_rxPldPrimCtrl (
    .macPIRxClk             (macPIClk),
    .macPIRxClkHardRst_n    (macPIClkHardRst_n),
    .macPIRxClkSoftRst_n    (macPIClkSoftRst_n),
    .trigHalt_p             (trigPldHalt_p),
    .trigPassive_p          (trigPldPassive_p),
    .trigActive_p           (trigPldActive_p),
    .trigDead_p             (trigPldDead_p),
    .rxNewTail              (rxNewTailPld),
    .rxNewHead              (rxNewHeadPld),
    .updStaPtr_p            (updPldStaPtr_p),
    .rxHeadPtr              (rxPldHeadPtr),
    .nxtDescPtr             (nxtPldDescPtr),
    .rstNewTail             (rstNewTailPld),
    .rstNewHead             (rstNewHeadPld),
    .statusPtr              (pldStatusPointer),
    .rxNewHeadErr           (rxPayNewHeadErr),
    .rxDMADead              (rxPayloadDMADead),
    .rxDmaPCState           (rxPayloadState)
);

// Instanciation of dmaArbiter
// Name of the instance : U_dmaArbiter
// Name of the file containing this module : dmaArbiter.v
dmaArbiter U_dmaArbiter (
		.macPIClk               (macPIClk),
		.macPIClkHardRst_n      (macPIClkHardRst_n),
		.macPIClkSoftRst_n      (macPIClkSoftRst_n),
		.rdWrCtlrIdle           (rdWrCtlrIdle),
		.rxListProcReq          (rxListProcReq),
		.rxListProcGrant        (rxListProcGrant),
		.txStaUpdaterReq        (txStaUpdaterReq),
		.txStaUpdaterGrant      (txStaUpdaterGrant),
		.txListProcReq          (txListProcReq),
		.txListProcGrant        (txListProcGrant)
		);



// Instanciation of rdWrCtlr
// Name of the instance : U_rdWrCtlr
// Name of the file containing this module : rdWrCtlr.v
rdWrCtlr U_rdWrCtlr (
		.macPIClk               (macPIClk),
		.macPIClkHardRst_n      (macPIClkHardRst_n),
		.macPIClkSoftRst_n      (macPIClkSoftRst_n),
		.dmaHIFAddressIn        (dmaHIFAddressIn),
		.dmaHIFRead             (dmaHIFRead),
		.dmaHIFWrite            (dmaHIFWrite),
		.dmaHIFSize             (dmaHIFSize),
		.dmaHIFWriteDataIn      (dmaHIFWriteDataIn),
		.dmaHIFError            (dmaHIFError),
		.dmaHIFReadDataOut      (dmaHIFReadDataOut),
		.dmaHIFReadDataValid    (dmaHIFReadDataValid),
		.dmaHIFReady            (dmaHIFReady),
		.dmaHIFTransComplete    (dmaHIFTransComplete),
		.rdWrCtlrIdle           (rdWrCtlrIdle),
		.rxListStartAddress     (rxListStartAddress),
		.rxListRead             (rxListRead),
		.rxListWrite            (rxListWrite),
		.rxListSize             (rxListSize),
		.rxListWriteData        (rxListWriteData),
		.rxListLast             (rxListLast),
		.rxListError            (rxListError),
		.rxListNextData         (rxListNextData),
		.rxListReadData         (rxListReadData),
		.rxListReadDataValid    (rxListReadDataValid),
		.rxListTransComplete    (rxListTransComplete),
		.txListStartAddress     (txListStartAddress),
		.txListRead             (txListRead),
		.txListWrite            (txListWrite),
		.txListSize             (txListSize),
		.txListWriteData        (txListWriteData),
		.txListLast             (txListLast),
		.txListError            (txListError),
		.txListNextData         (txListNextData),
		.txListReadData         (txListReadData),
		.txListReadDataValid    (txListReadDataValid),
		.txListTransComplete    (txListTransComplete),
		.staUpdStartAddress     (staUpdStartAddress),
		.staUpdWrite            (staUpdWrite),
		.staUpdWriteData        (staUpdWriteData),
		.staUpdError            (staUpdError),
		.staUpdNextData         (staUpdNextData),
		.staUpdTransComplete    (staUpdTransComplete),
		.debugPortDmaRdWrCtlr   (debugPortDmaRdWrCtlr)
		);


//Delayed Version of trigger for start of TXOP from 
//MAC Controller for channel 0
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    trigTxAC0Delayed <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    trigTxAC0Delayed <= 1'b0;
  else
    trigTxAC0Delayed <= trigTxAC0;
end
   
//Delayed Version of trigger for start of TXOP from 
//MAC Controller for channel 1
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    trigTxAC1Delayed <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    trigTxAC1Delayed <= 1'b0;
  else
    trigTxAC1Delayed <= trigTxAC1;
end

//Delayed Version of trigger for start of TXOP from 
//MAC Controller for channel 2
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    trigTxAC2Delayed <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    trigTxAC2Delayed <= 1'b0;
  else
    trigTxAC2Delayed <= trigTxAC2;
end

//Delayed Version of trigger for start of TXOP from 
//MAC Controller for channel 3
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    trigTxAC3Delayed <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    trigTxAC3Delayed <= 1'b0;
  else
    trigTxAC3Delayed <= trigTxAC3;
end

//Delayed Version of trigger for start of TXOP from 
//MAC Controller for channel Bcn
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    trigTxBcnDelayed <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    trigTxBcnDelayed <= 1'b0;
  else
    trigTxBcnDelayed <= trigTxBcn;
end

//This is a pulse signal which is generated each time any 
//Primary controller FSM moves from PASSIVE TO ACTIVE
assign stopDma_p = (~trigTxAC0 & trigTxAC0Delayed) | 
                   (~trigTxAC1 & trigTxAC1Delayed) |
                   (~trigTxAC2 & trigTxAC2Delayed) |
                   (~trigTxAC3 & trigTxAC3Delayed) |
                   (~trigTxBcn & trigTxBcnDelayed) ; 

assign abortTx_p = stopDma_p | underRunDetected_p;

//signal used in generation of pulse of flushing the 
//FIFO.THe fifo is flushed in two occasions. when there
//is a new TXOP and when the frame has to be retried 
assign flushTxFifo = txFIFOFlushDMA | trigDead_p | underRunDetected_p;

//dmaHIF Transaction error is passed to the receive list processor
//if it is the active master
// assign rxBusError = dmaHIFError & rxListProcGrant;


//Trigger the primary Beacon channel when either the Transmit List
//Proc issues the trigger to DEAD or the Status Updater issues it
assign trigBcnDead_p = trigBcnDeadListProc_p | trigDeadBCNStaUpd_p;

//Trigger the primary AC0 channel when either the Transmit List
//Proc issues the trigger to DEAD or the Status Updater issues it
assign trigAC0Dead_p = trigAc0DeadListProc_p | trigDeadAC0StaUpd_p;

//Trigger the primary AC1 channel when either the Transmit List
//Proc issues the trigger to DEAD or the Status Updater issues it
assign trigAC1Dead_p = trigAc1DeadListProc_p | trigDeadAC1StaUpd_p;

//Trigger the primary AC2 channel when either the Transmit List
//Proc issues the trigger to DEAD or the Status Updater issues it
assign trigAC2Dead_p = trigAc2DeadListProc_p | trigDeadAC2StaUpd_p;

//Trigger the primary AC3 channel when either the Transmit List
//Proc issues the trigger to DEAD or the Status Updater issues it
assign trigAC3Dead_p = trigAc3DeadListProc_p | trigDeadAC3StaUpd_p;

assign rxDMAEmpty = trigHdrHalt_p | trigPldHalt_p;

assign statusUpdaterFull = mpduCtrFull;


////////////////////////////////////////////////////////////////////////////////
// Debug Interface
////////////////////////////////////////////////////////////////////////////////



assign debugPortDMA5 = {trigTxBcn,
                        trigTxAC0,
                        trigTxAC1,
                        trigTxAC2,
                        trigTxAC3,
                        txFIFOFlushDMA,
                        stopDma_p,
                        underRunDetected_p,
                        trigBcnDead_p,
                        trigAC0Dead_p,
                        trigAC1Dead_p,
                        trigAC2Dead_p,
                        trigAC3Dead_p,
                        trigHdrHalt_p,
                        trigPldHalt_p,
                        statusUpdaterFull};


// DMA Status debug interface.
// This allows to monitor through the debug interface, the DMA Header Descriptors (Tx & Rx) update. 
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
    rxListProcGrantCapt <= 1'b0;
  else if (rxListProcGrant)
    rxListProcGrantCapt <= 1'b1;
  else if (txStaUpdaterGrant)
    rxListProcGrantCapt <= 1'b0;
end

assign debugPortDMAStatus = ((rxListProcGrantCapt || rxListProcGrant) && !txStaUpdaterGrant) ? rxListProcDebug : txStatusDebug;

assign dmaInternalError = trigDead_p | underRunDetected_p | patternError | trigHdrDead_p | trigPldDead_p | ptError;

assign debugPortTxRxListA = (debugPortDmaRdWrCtlr[1:0] == 2'b10) ? debugPortTxListA :
                            (debugPortDmaRdWrCtlr[1:0] == 2'b01) ? debugPortRxListA :
                                                                   16'h0            ;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


`ifdef RW_ASSERT_ON
// System Verilog Assertions
////////////////////////////

//FIFO Assertions
//$rw_sva Checks FIFO is not written after txFifoAlmostFull
property txFifoWrCheck;
disable iff (!macPITxClkHardRst_n | !macPITxClkSoftRst_n)
@(posedge macPITxClk) txFifoFull |-> !txFifoWr;
endproperty
txFifoWrCheck1: assert property (txFifoWrCheck);

//$rw_sva Checks if RX FIFO is read after empty
property rxFifoRdCheck;
disable iff (!macPIRxClkHardRst_n | !macPIRxClkSoftRst_n)
@(posedge macPIRxClk) rxFifoEmpty |-> !rxFifoRd;
endproperty
rxFifoRdCheck1: assert property (rxFifoRdCheck); 

//$rw_sva checks if FIFO is flushed on retry
property retryFifoFlushCheck;
disable iff (!macPITxClkHardRst_n | !macPITxClkSoftRst_n)
@(posedge macPITxClk) $rose(updateDMAStatus_p) && retryFrame_p |=> flushTxFifo ;
endproperty
retryFifoFlushCheck1: assert property(retryFifoFlushCheck);

//$rw_sva checks if FIFO is flushed on end of TXOP
property txopEndFifoFlushCheck;
disable iff (!macPIClkHardRst_n | !macPIClkSoftRst_n)
@(posedge macPIClk) ($fell(trigTxAC0) | $fell(trigTxAC1) |
                      $fell(trigTxAC2) | $fell(trigTxAC3) |
                      $fell(trigTxBcn)) |=> flushTxFifo;
endproperty
txopEndFifoFlushCheck1: assert property(txopEndFifoFlushCheck);

//$rw_sva Check if only one AC is triggered
property singleChannelTriggerCheck;
disable iff (!macPITxClkHardRst_n | !macPITxClkSoftRst_n)
@(posedge macPIClk) 
 (trigTxAC0 || trigTxAC1 || trigTxAC2 || trigTxAC3 || trigTxBcn) |->  (trigTxAC0 ^^ trigTxAC1 ^^ trigTxAC2 ^^ trigTxAC3 ^^ trigTxBcn);
endproperty
singleChannelTriggerCheck1: assert property (singleChannelTriggerCheck);

// Cover Points Definitions
///////////////////////////

////////////////////////////////////////////////////////////////////////////
// Tx DMA is in the HALTED state and it receives a newHead bit indication.
// (header descriptor pointer is valid).
////////////////////////////////////////////////////////////////////////////
property receiveNewHeadWhenHalted(state,newHead,headPtr);
@(posedge macPIClk) ((state == 1) && $rose(newHead) && (headPtr[1:0] == 0) && (headPtr != 0));
endproperty

//$rw_sva Count number of newHead with DMA state Halted for Beacon channel
countReceiveNewHeadWhenHaltedBcn: cover property (receiveNewHeadWhenHalted(txBcnState,txNewHeadBcn,txBcnHeadPtr));

//$rw_sva Count number of newHead with DMA state Halted for AC0 channel
countReceiveNewHeadWhenHaltedAc0: cover property (receiveNewHeadWhenHalted(txAC0State,txNewHeadAC0,txAC0HeadPtr));

//$rw_sva Count number of newHead with DMA state Halted for AC1 channel
countReceiveNewHeadWhenHaltedAc1: cover property (receiveNewHeadWhenHalted(txAC1State,txNewHeadAC1,txAC1HeadPtr));

//$rw_sva Count number of newHead with DMA state Halted for AC2 channel
countReceiveNewHeadWhenHaltedAc2: cover property (receiveNewHeadWhenHalted(txAC2State,txNewHeadAC2,txAC2HeadPtr));

//$rw_sva Count number of newHead with DMA state Halted for AC3 channel
countReceiveNewHeadWhenHaltedAc3: cover property (receiveNewHeadWhenHalted(txAC3State,txNewHeadAC3,txAC3HeadPtr));

//$rw_sva Count number of newHead with DMA state Halted for RX Header channel
countReceiveNewHeadWhenHaltedRxHeader: cover property (receiveNewHeadWhenHalted(rxHeaderState,rxNewHeadHdr,rxHdrHeadPtr));

//$rw_sva Count number of newHead with DMA state Halted for RX Payload channel
countReceiveNewHeadWhenHaltedRxPayload: cover property (receiveNewHeadWhenHalted(rxPayloadState,rxNewHeadPld,rxPldHeadPtr));

////////////////////////////////////////////////////////////////////////////
// Tx DMA is in the HALTED state and it receives a newTail bit indication.
// (next atomic frm exch seq pointer is valid)
////////////////////////////////////////////////////////////////////////////
property receiveNewTailWhenHaltedTx(state,newHead,nextAtomicFrmPtrValid);
@(posedge macPIClk) ((state == 1) && $rose(newHead) && nextAtomicFrmPtrValid);
endproperty

property receiveNewTailWhenHaltedRx(state,newHead,nextAtomicFrmPtr);
@(posedge macPIClk) ((state == 1) && $rose(newHead) && (nextAtomicFrmPtr[1:0] == 0) && (nextAtomicFrmPtr != 0));
endproperty

//$rw_sva Count number of newTail with DMA state Halted for Beacon channel
countReceiveNewTailWhenHaltedBcn: cover property (receiveNewTailWhenHaltedTx(txBcnState,txNewTailBcn,nxtAtomFrmPtrValidBcn));

//$rw_sva Count number of newTail with DMA state Halted for AC0 channel
countReceiveNewTailWhenHaltedAc0: cover property (receiveNewTailWhenHaltedTx(txAC0State,txNewTailAC0,nxtAtomFrmPtrValidAc0));

//$rw_sva Count number of newTail with DMA state Halted for AC1 channel
countReceiveNewTailWhenHaltedAc1: cover property (receiveNewTailWhenHaltedTx(txAC1State,txNewTailAC1,nxtAtomFrmPtrValidAc1));

//$rw_sva Count number of newTail with DMA state Halted for AC2 channel
countReceiveNewTailWhenHaltedAc2: cover property (receiveNewTailWhenHaltedTx(txAC2State,txNewTailAC2,nxtAtomFrmPtrValidAc2));

//$rw_sva Count number of newTail with DMA state Halted for AC3 channel
countReceiveNewTailWhenHaltedAc3: cover property (receiveNewTailWhenHaltedTx(txAC3State,txNewTailAC3,nxtAtomFrmPtrValidAc3));

//$rw_sva Count number of newTail with DMA state Halted for RX Header channel
countReceiveNewTailWhenHaltedRxHeader: cover property (receiveNewTailWhenHaltedRx(rxHeaderState,rxNewTailHdr,nxtHdrDescPtr));

//$rw_sva Count number of newTail with DMA state Halted for RX Payload channel
countReceiveNewTailWhenHaltedRxPayload: cover property (receiveNewTailWhenHaltedRx(rxPayloadState,rxNewTailPld,nxtPldDescPtr));


////////////////////////////////////////////////////////////////////////////
// Tx DMA is in the ACTIVE state and it receives a newHead bit indication.
// (header descriptor pointer is valid).
////////////////////////////////////////////////////////////////////////////
property receiveNewHeadWhenActive(state,newHead,headPtr);
@(posedge macPITxClk) ((state == 4) && $rose(newHead) && (headPtr[1:0] == 0) && (headPtr != 0));
endproperty

//$rw_sva Count number of newHead with DMA state ACTIVE for Beacon channel
countReceiveNewHeadWhenActiveBcn: cover property (receiveNewHeadWhenActive(txBcnState,txNewHeadBcn,txBcnHeadPtr));

//$rw_sva Count number of newHead with DMA state ACTIVE for AC0 channel
countReceiveNewHeadWhenActiveAc0: cover property (receiveNewHeadWhenActive(txAC0State,txNewHeadAC0,txAC0HeadPtr));

//$rw_sva Count number of newHead with DMA state ACTIVE for AC1 channel
countReceiveNewHeadWhenActiveAc1: cover property (receiveNewHeadWhenActive(txAC1State,txNewHeadAC1,txAC1HeadPtr));

//$rw_sva Count number of newHead with DMA state ACTIVE for AC2 channel
countReceiveNewHeadWhenActiveAc2: cover property (receiveNewHeadWhenActive(txAC2State,txNewHeadAC2,txAC2HeadPtr));

//$rw_sva Count number of newHead with DMA state ACTIVE for AC3 channel
countReceiveNewHeadWhenActiveAc3: cover property (receiveNewHeadWhenActive(txAC3State,txNewHeadAC3,txAC3HeadPtr));

//$rw_sva Count number of newHead with DMA state ACTIVE for RX Header channel
countReceiveNewHeadWhenActiveRxHeader: cover property (receiveNewHeadWhenActive(rxHeaderState,rxNewHeadHdr,rxHdrHeadPtr));

//$rw_sva Count number of newHead with DMA state ACTIVE for RX Payload channel
countReceiveNewHeadWhenActiveRxPayload: cover property (receiveNewHeadWhenActive(rxPayloadState,rxNewHeadPld,rxPldHeadPtr));

////////////////////////////////////////////////////////////////////////////
// Tx DMA is in the ACTIVE state and it receives a newTail bit indication.
// (next atomic frm exch seq pointer is valid)
////////////////////////////////////////////////////////////////////////////
property receiveNewTailWhenActiveTx(state,newHead,nextAtomicFrmPtrValid);
@(posedge macPITxClk) ((state == 4) && $rose(newHead) && nextAtomicFrmPtrValid);
endproperty

property receiveNewTailWhenActiveRx(state,newHead,nextAtomicFrmPtr);
@(posedge macPIClk) ((state == 4) && $rose(newHead) && (nextAtomicFrmPtr[1:0] == 0) && (nextAtomicFrmPtr != 0));
endproperty

//$rw_sva Count number of newTail with DMA state ACTIVE for Beacon channel
countReceiveNewTailWhenActiveBcn: cover property (receiveNewTailWhenActiveTx(txBcnState,txNewTailBcn,nxtAtomFrmPtrValidBcn));

//$rw_sva Count number of newTail with DMA state ACTIVE for AC0 channel
countReceiveNewTailWhenActiveAc0: cover property (receiveNewTailWhenActiveTx(txAC0State,txNewTailAC0,nxtAtomFrmPtrValidAc0));

//$rw_sva Count number of newTail with DMA state ACTIVE for AC1 channel
countReceiveNewTailWhenActiveAc1: cover property (receiveNewTailWhenActiveTx(txAC1State,txNewTailAC1,nxtAtomFrmPtrValidAc1));

//$rw_sva Count number of newTail with DMA state ACTIVE for AC2 channel
countReceiveNewTailWhenActiveAc2: cover property (receiveNewTailWhenActiveTx(txAC2State,txNewTailAC2,nxtAtomFrmPtrValidAc2));

//$rw_sva Count number of newTail with DMA state ACTIVE for AC3 channel
countReceiveNewTailWhenActiveAc3: cover property (receiveNewTailWhenActiveTx(txAC3State,txNewTailAC3,nxtAtomFrmPtrValidAc3));

//$rw_sva Count number of newTail with DMA state ACTIVE for RX Header channel
countReceiveNewTailWhenActiveRxHeader: cover property (receiveNewTailWhenActiveRx(rxHeaderState,rxNewTailHdr,nxtHdrDescPtr));

//$rw_sva Count number of newTail with DMA state ACTIVE for RX Payload channel
countReceiveNewTailWhenActiveRxPayload: cover property (receiveNewTailWhenActiveRx(rxPayloadState,rxNewTailPld,nxtPldDescPtr));

////////////////////////////////////////////////////////////////////////////
// The TxDMA can be in HALTED, PASSIVE and ACTIVE and then receives an Rx indication
////////////////////////////////////////////////////////////////////////////
property receiveRxIndicationWhenHalted(state,rxIndication);
@(posedge macPIClk) ((state == 4) && $rose(rxIndication));
endproperty

property receiveRxIndicationWhenPassive(state,rxIndication);
@(posedge macPIClk) ((state == 2) && $rose(rxIndication));
endproperty

property receiveRxIndicationWhenActive(state,rxIndication);
@(posedge macPIClk) ((state == 1) && $rose(rxIndication));
endproperty

//$rw_sva Count number of rxIndication with DMA state HALTED for Beacon channel
countReceiveRxIndicationWhenHaltedBcn: cover property (receiveRxIndicationWhenHalted(txBcnState,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state HALTED for AC0 channel
countReceiveRxIndicationWhenHaltedAC0: cover property (receiveRxIndicationWhenHalted(txAC0State,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state HALTED for AC1 channel
countReceiveRxIndicationWhenHaltedAC1: cover property (receiveRxIndicationWhenHalted(txAC1State,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state HALTED for AC2 channel
countReceiveRxIndicationWhenHaltedAC2: cover property (receiveRxIndicationWhenHalted(txAC2State,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state HALTED for AC3 channel
countReceiveRxIndicationWhenHaltedAC3: cover property (receiveRxIndicationWhenHalted(txAC3State,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state PASSIVE for Beacon channel
countReceiveRxIndicationWhenPassiveBcn: cover property (receiveRxIndicationWhenPassive(txBcnState,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state PASSIVE for AC0 channel
countReceiveRxIndicationWhenPassiveAC0: cover property (receiveRxIndicationWhenPassive(txAC0State,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state PASSIVE for AC1 channel
countReceiveRxIndicationWhenPassiveAC1: cover property (receiveRxIndicationWhenPassive(txAC1State,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state PASSIVE for AC2 channel
countReceiveRxIndicationWhenPassiveAC2: cover property (receiveRxIndicationWhenPassive(txAC2State,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state PASSIVE for AC3 channel
countReceiveRxIndicationWhenPassiveAC3: cover property (receiveRxIndicationWhenPassive(txAC3State,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state ACTIVE for Beacon channel
countReceiveRxIndicationWhenActiveBcn: cover property (receiveRxIndicationWhenHalted(txBcnState,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state ACTIVE for AC0 channel
countReceiveRxIndicationWhenActiveAC0: cover property (receiveRxIndicationWhenHalted(txAC0State,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state ACTIVE for AC1 channel
countReceiveRxIndicationWhenActiveAC1: cover property (receiveRxIndicationWhenHalted(txAC1State,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state ACTIVE for AC2 channel
countReceiveRxIndicationWhenActiveAC2: cover property (receiveRxIndicationWhenHalted(txAC2State,rxHeaderState[2]));

//$rw_sva Count number of rxIndication with DMA state ACTIVE for AC3 channel
countReceiveRxIndicationWhenActiveAC3: cover property (receiveRxIndicationWhenHalted(txAC3State,rxHeaderState[2]));


////////////////////////////////////////////////////////////////////////////
// More than one newHead bit set at the same time.
////////////////////////////////////////////////////////////////////////////
//$rw_sva Count number of simultaneous txNewHead 
property receiveMorethanOneNewHead;
@(posedge macPIClk) (($rose(txNewHeadAC0) && $rose(txNewHeadAC1)) ||
                     ($rose(txNewHeadAC0) && $rose(txNewHeadAC2)) ||
                     ($rose(txNewHeadAC0) && $rose(txNewHeadAC3)) ||
                     ($rose(txNewHeadAC0) && $rose(txNewHeadBcn)) ||
                     ($rose(txNewHeadAC1) && $rose(txNewHeadAC2)) ||
                     ($rose(txNewHeadAC1) && $rose(txNewHeadAC3)) ||
                     ($rose(txNewHeadAC1) && $rose(txNewHeadBcn)) ||
                     ($rose(txNewHeadAC2) && $rose(txNewHeadAC3)) ||
                     ($rose(txNewHeadAC2) && $rose(txNewHeadBcn)) ||
                     ($rose(txNewHeadAC3) && $rose(txNewHeadBcn)));
endproperty
countReceiveMorethanOneNewHead: cover property (receiveMorethanOneNewHead);

////////////////////////////////////////////////////////////////////////////
// Create retry limit reached for an intermediate fragment of an MSDU. 
// The nextAtomicFrmEx Seq points to another MPDU/MSDU/RTS.
// This is applicable for all the AC queues.
////////////////////////////////////////////////////////////////////////////
property retryLimitReachedWithValidNxtAtomicFrmPtr(nextAtomicFrmPtrValid);
@(posedge macPITxClk) ($rose(retryLimitReached_p) && nextAtomicFrmPtrValid);
endproperty

//$rw_sva Count number of retry limit reached with valid next atomic frame pointer for Bcn channel
countRetryLimitReachedWithValidNxtAtomicFrmPtrBcn: cover property (retryLimitReachedWithValidNxtAtomicFrmPtr(nxtAtomFrmPtrValidBcn));

//$rw_sva Count number of retry limit reached with valid next atomic frame pointer for AC0 channel
countRetryLimitReachedWithValidNxtAtomicFrmPtrAC0: cover property (retryLimitReachedWithValidNxtAtomicFrmPtr(nxtAtomFrmPtrValidAc0));

//$rw_sva Count number of retry limit reached with valid next atomic frame pointer for AC1 channel
countRetryLimitReachedWithValidNxtAtomicFrmPtrAC1: cover property (retryLimitReachedWithValidNxtAtomicFrmPtr(nxtAtomFrmPtrValidAc1));

//$rw_sva Count number of retry limit reached with valid next atomic frame pointer for AC2 channel
countRetryLimitReachedWithValidNxtAtomicFrmPtrAC2: cover property (retryLimitReachedWithValidNxtAtomicFrmPtr(nxtAtomFrmPtrValidAc2));

//$rw_sva Count number of retry limit reached with valid next atomic frame pointer for AC3 channel
countRetryLimitReachedWithValidNxtAtomicFrmPtrAC3: cover property (retryLimitReachedWithValidNxtAtomicFrmPtr(nxtAtomFrmPtrValidAc3));



////////////////////////////////////////////////////////////////////////////
// newHead bit is set for Tx channel when DUT receives a packet
////////////////////////////////////////////////////////////////////////////
//$rw_sva Count number of newHead for Tx channel when DUT receives a packet
property newHeadwhenRx;
@(posedge macPIClk) (($rose(txNewHeadAC0) || $rose(txNewHeadAC1) || $rose(txNewHeadAC2) || $rose(txNewHeadAC3) || $rose(txNewHeadBcn)) &&
                     ((rxHeaderState == 4) || (rxPayloadState == 4))
                     );
endproperty
countnewHeadwhenRx: cover property (newHeadwhenRx);

////////////////////////////////////////////////////////////////////////////
// newTail bit is set for Tx channel when DUT receives a packet
////////////////////////////////////////////////////////////////////////////
//$rw_sva Count number of newTail for Tx channel when DUT receives a packet
property newTailwhenRx;
@(posedge macPIClk) (($rose(txNewTailAC0) || $rose(txNewTailAC1) || $rose(txNewTailAC2) || $rose(txNewTailAC3) || $rose(txNewTailBcn)) &&
                     ((rxHeaderState == 4) || (rxPayloadState == 4))
                     );
endproperty
countnewTailwhenRx: cover property (newTailwhenRx);

////////////////////////////////////////////////////////////////////////////
// newHead bit is set for Tx DMA when it is in HALTED state and the Rx DMA is PASSIVE.
////////////////////////////////////////////////////////////////////////////
property newHeadWithTxHaltedWhenRxInPassive(state,txNewHead);
@(posedge macPIClk) ((state == 4) && $rose(txNewHead) && (rxHeaderState == 2) && (rxPayloadState == 2));
endproperty

//$rw_sva Count number of newHead bit is set for Tx DMA Bcn when it is in HALTED state and the Rx DMA is PASSIVE.
countnewHeadWithTxBcnHaltedWhenRxInPassive: cover property (newHeadWithTxHaltedWhenRxInPassive(txBcnState,txNewHeadBcn));

//$rw_sva Count number of newHead bit is set for Tx DMA AC0 when it is in HALTED state and the Rx DMA is PASSIVE.
countnewHeadWithTxAC0HaltedWhenRxInPassive: cover property (newHeadWithTxHaltedWhenRxInPassive(txAC0State,txNewHeadAC0));

//$rw_sva Count number of newHead bit is set for Tx DMA AC1 when it is in HALTED state and the Rx DMA is PASSIVE.
countnewHeadWithTxAC1HaltedWhenRxInPassive: cover property (newHeadWithTxHaltedWhenRxInPassive(txAC1State,txNewHeadAC1));

//$rw_sva Count number of newHead bit is set for Tx DMA AC2 when it is in HALTED state and the Rx DMA is PASSIVE.
countnewHeadWithTxAC2HaltedWhenRxInPassive: cover property (newHeadWithTxHaltedWhenRxInPassive(txAC2State,txNewHeadAC2));

//$rw_sva Count number of newHead bit is set for Tx DMA AC0 when it is in HALTED state and the Rx DMA is PASSIVE.
countnewHeadWithTxAC3HaltedWhenRxInPassive: cover property (newHeadWithTxHaltedWhenRxInPassive(txAC3State,txNewHeadAC3));

////////////////////////////////////////////////////////////////////////////
// newHead bit is set for Tx DMA when it is in PASSIVE state and the Rx DMA is PASSIVE.
////////////////////////////////////////////////////////////////////////////
property newHeadWithTxPassiveWhenRxInPassive(state,txNewHead);
@(posedge macPIClk) ((state == 4) && $rose(txNewHead) && (rxHeaderState == 2) && (rxPayloadState == 2));
endproperty

//$rw_sva Count number of newHead bit is set for Tx DMA Bcn when it is in PASSIVE state and the Rx DMA is PASSIVE.
countnewHeadWithTxBcnPassiveWhenRxInPassive: cover property (newHeadWithTxPassiveWhenRxInPassive(txBcnState,txNewHeadBcn));

//$rw_sva Count number of newHead bit is set for Tx DMA AC0 when it is in PASSIVE state and the Rx DMA is PASSIVE.
countnewHeadWithTxAC0PassiveWhenRxInPassive: cover property (newHeadWithTxPassiveWhenRxInPassive(txAC0State,txNewHeadAC0));

//$rw_sva Count number of newHead bit is set for Tx DMA AC1 when it is in PASSIVE state and the Rx DMA is PASSIVE.
countnewHeadWithTxAC1PassiveWhenRxInPassive: cover property (newHeadWithTxPassiveWhenRxInPassive(txAC1State,txNewHeadAC1));

//$rw_sva Count number of newHead bit is set for Tx DMA AC2 when it is in PASSIVE state and the Rx DMA is PASSIVE.
countnewHeadWithTxAC2PassiveWhenRxInPassive: cover property (newHeadWithTxPassiveWhenRxInPassive(txAC2State,txNewHeadAC2));

//$rw_sva Count number of newHead bit is set for Tx DMA AC0 when it is in PASSIVE state and the Rx DMA is PASSIVE.
countnewHeadWithTxAC3PassiveWhenRxInPassive: cover property (newHeadWithTxPassiveWhenRxInPassive(txAC3State,txNewHeadAC3));

////////////////////////////////////////////////////////////////////////////
// newHead bit is set for Tx DMA when it is in ACTIVE state and the Rx DMA is PASSIVE.
////////////////////////////////////////////////////////////////////////////
property newHeadWithTxActiveWhenRxInPassive(state,txNewHead);
@(posedge macPITxClk) ((state == 4) && $rose(txNewHead) && (rxHeaderState == 2) && (rxPayloadState == 2));
endproperty

//$rw_sva Count number of newHead bit is set for Tx DMA Bcn when it is in ACTIVE state and the Rx DMA is PASSIVE.
countnewHeadWithTxBcnActiveWhenRxInPassive: cover property (newHeadWithTxActiveWhenRxInPassive(txBcnState,txNewHeadBcn));

//$rw_sva Count number of newHead bit is set for Tx DMA AC0 when it is in ACTIVE state and the Rx DMA is PASSIVE.
countnewHeadWithTxAC0ActiveWhenRxInPassive: cover property (newHeadWithTxActiveWhenRxInPassive(txAC0State,txNewHeadAC0));

//$rw_sva Count number of newHead bit is set for Tx DMA AC1 when it is in ACTIVE state and the Rx DMA is PASSIVE.
countnewHeadWithTxAC1ActiveWhenRxInPassive: cover property (newHeadWithTxActiveWhenRxInPassive(txAC1State,txNewHeadAC1));

//$rw_sva Count number of newHead bit is set for Tx DMA AC2 when it is in ACTIVE state and the Rx DMA is PASSIVE.
countnewHeadWithTxAC2ActiveWhenRxInPassive: cover property (newHeadWithTxActiveWhenRxInPassive(txAC2State,txNewHeadAC2));

//$rw_sva Count number of newHead bit is set for Tx DMA AC0 when it is in ACTIVE state and the Rx DMA is PASSIVE.
countnewHeadWithTxAC3ActiveWhenRxInPassive: cover property (newHeadWithTxActiveWhenRxInPassive(txAC3State,txNewHeadAC3));

////////////////////////////////////////////////////////////////////////////
// The last frame in the queue undergoing retry limit reached/msdulifetimeexpired/rts retry limit reached/
////////////////////////////////////////////////////////////////////////////
property endOfQueueWithRetryLimitReachedOrLifeTime(state,nxtAtomFrmPtrValid,trigger_p);
@(posedge macPITxClk) ((state == 4) && !nxtAtomFrmPtrValid && $rose(trigger_p));
endproperty

//$rw_sva Count number of last frame in the queue undergoing retry limit reached for Bcn Channel.
countEndOfQueueWithRetryLimitReachedBcn: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txBcnState,nxtAtomFrmPtrValidBcn,mpduFailed_p && retryLimitReached_p));

//$rw_sva Count number of last frame in the queue undergoing retry limit reached for AC0 Channel.
countEndOfQueueWithRetryLimitReachedAC0: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txAC0State,nxtAtomFrmPtrValidAc0,mpduFailed_p && retryLimitReached_p));

//$rw_sva Count number of last frame in the queue undergoing retry limit reached for AC1 Channel.
countEndOfQueueWithRetryLimitReachedAC1: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txAC1State,nxtAtomFrmPtrValidAc1,mpduFailed_p && retryLimitReached_p));

//$rw_sva Count number of last frame in the queue undergoing retry limit reached for AC2 Channel.
countEndOfQueueWithRetryLimitReachedAC2: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txAC2State,nxtAtomFrmPtrValidAc2,mpduFailed_p && retryLimitReached_p));

//$rw_sva Count number of last frame in the queue undergoing retry limit reached for AC3 Channel.
countEndOfQueueWithRetryLimitReachedAC3: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txAC3State,nxtAtomFrmPtrValidAc3,mpduFailed_p && retryLimitReached_p));

//$rw_sva Count number of last frame in the queue undergoing RTS retry limit reached for Bcn Channel.
countEndOfQueueWithRTSRetryLimitReachedBcn: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txBcnState,nxtAtomFrmPtrValidBcn,rtsFailed_p && retryLimitReached_p));

//$rw_sva Count number of last frame in the queue undergoing RTS retry limit reached for AC0 Channel.
countEndOfQueueWithRTSRetryLimitReachedAC0: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txAC0State,nxtAtomFrmPtrValidAc0,rtsFailed_p && retryLimitReached_p));

//$rw_sva Count number of last frame in the queue undergoing RTS retry limit reached for AC1 Channel.
countEndOfQueueWithRTSRetryLimitReachedAC1: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txAC1State,nxtAtomFrmPtrValidAc1,rtsFailed_p && retryLimitReached_p));

//$rw_sva Count number of last frame in the queue undergoing RTS retry limit reached for AC2 Channel.
countEndOfQueueWithRTSRetryLimitReachedAC2: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txAC2State,nxtAtomFrmPtrValidAc2,rtsFailed_p && retryLimitReached_p));

//$rw_sva Count number of last frame in the queue undergoing RTS retry limit reached for AC3 Channel.
countEndOfQueueWithRTSRetryLimitReachedAC3: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txAC3State,nxtAtomFrmPtrValidAc3,rtsFailed_p && retryLimitReached_p));

//$rw_sva Count number of last frame in the queue undergoing msdulifetimeexpired for Bcn Channel.
countEndOfQueueWithLifetimeExpiredBcn: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txBcnState,nxtAtomFrmPtrValidBcn,lifetimeExpired_p));

//$rw_sva Count number of last frame in the queue undergoing msdulifetimeexpired for AC0 Channel.
countEndOfQueueWithLifetimeExpiredAC0: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txAC0State,nxtAtomFrmPtrValidAc0,lifetimeExpired_p));

//$rw_sva Count number of last frame in the queue undergoing msdulifetimeexpired for AC1 Channel.
countEndOfQueueWithLifetimeExpiredAC1: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txAC1State,nxtAtomFrmPtrValidAc1,lifetimeExpired_p));

//$rw_sva Count number of last frame in the queue undergoing msdulifetimeexpired for AC2 Channel.
countEndOfQueueWithLifetimeExpiredAC2: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txAC2State,nxtAtomFrmPtrValidAc2,lifetimeExpired_p));

//$rw_sva Count number of last frame in the queue undergoing msdulifetimeexpired for AC3 Channel.
countEndOfQueueWithLifetimeExpiredAC3: cover property (endOfQueueWithRetryLimitReachedOrLifeTime(txAC3State,nxtAtomFrmPtrValidAc3,lifetimeExpired_p));

`endif

endmodule