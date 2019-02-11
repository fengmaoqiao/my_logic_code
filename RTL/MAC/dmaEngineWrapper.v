module dmaEngineWrapper ( 
   //input wires
   //Clocks
   //Secondary clock for TX DMA modules. 
   //Synchronized to macPIClk domain. 
   input wire        macPITxClk,

   //Secondary clock for RX DMA modules. 
   //Synchronized to macPIClk domain.
   input wire        macPIRxClk,

   //source clock signals not resynchronized
   input  wire       macCoreClk,              // mac core clock             

   //source clock signals not resynchronized
   input  wire       macCoreRxClk,              // mac core Rx clock             

   //Primary clock for the common modules
   input wire        macPIClk,

   //Resets
   //Hard Reset synchronized to macPITxClk domain
   input wire        macPITxClkHardRst_n,

   //Hard Reset synchronized to macPIRxClk domain
   input wire        macPIRxClkHardRst_n,

   //Hard Reset synchronized to macPIClk domain
   input wire        macPIClkHardRst_n,

   //Hard Reset synchronized to macCoreClk domain
   input  wire       macCoreClkHardRst_n,       // mac core Tx clock reset       

   //Soft Reset synchronized to macPITxClk domain
   input wire        macPITxClkSoftRst_n,

   //Soft Reset synchronized to macPIRxClk domain
   input wire        macPIRxClkSoftRst_n,

   //Soft Reset synchronized to macPIClk domain
   input wire        macPIClkSoftRst_n,

   //dmaHIF Master Interface
   //Data read from the SRAM during a dmaHIF read transfer
   input wire [31:0] dmaHIFReadDataOut,

   //Data in dmaHIFReadData is valid when this signal is 
   //asserted HIGH 
   input wire        dmaHIFReadDataValid,

   //Driven high to indicate that either the single or 
   //burst transfer is complete
   input wire        dmaHIFTransComplete,

   //Driven high when the next data needs to pushed on the interface
   input wire        dmaHIFReady,
   
   //Driven high when the error response is received from 
   //the external addressed dmaHIF slave for the transfer 
   //initiated
   input wire        dmaHIFError,

   //MAC Controller
   //Trigger from the MAC Controller to indicate DMA to 
   //start fetching frames associated with AC0
   input wire        trigTxAC0,

   //Trigger from the MAC Controller to indicate DMA to 
   //start fetching frames associated with AC1
   input wire        trigTxAC1,

   //Trigger from the MAC Controller to indicate DMA to 
   //start fetching frames associated with AC2
   input wire        trigTxAC2,

   //Trigger from the MAC Controller to indicate DMA to 
   //start fetching frames associated with AC3
   input wire        trigTxAC3,

   //Trigger from the MAC Controller to indicate DMA to 
   //start fetching frames associated with Beacon
   input wire        trigTxBcn,

   //MAC Controller indicates a frame is successfully 
   //received
   input wire        frameRxed_p,
   output wire       rxListProcCsIsIdle,  // rxListProc FSM is in IDLE state

   //TSF Timer value
   input wire [31:0] tsfTimerValue,

   // trigs the DMA Status update.
   input wire        updateDMAStatus_p,

   //Asserted high if the current transmitted packet is a
   //RTS frame prepared by SW
   input wire        swRTS_p,

   //Asserted high after every transmission of MPDU in an 
   //AMPDU frame
   input wire        txMpduDone_p,

   //Asserted high if the transmitted packet was an AMPDU 
   //frame
   input wire        ampduFrm_p,

   //If the transmitted frame has to be retried then this 
   //signal is asserted.
   input wire        retryFrame_p,

   //If the transmitted frame was successful. Not asserted
   //for RTS frames
   input wire        mpduSuccess_p,

   //If the transmitted frame was not successful. Not asserted
   //if the RTS frame failed
   input wire        mpduFailed_p,

   //If the transmitted frame was a RTS frame and did not 
   //receive a CTS frame within the CTS timeout
   input wire        rtsFailed_p,

   //If the transmitted frame was a RTS frame and successfully
   //received a CTS in reponse.
   input wire        rtsSuccess_p,

   //If the transmitted frame was not successful and has reached
   //the retry limit.Is asserted for both RTS and other MPDU's
   input wire        retryLimitReached_p,

   //Indicates whether the frame was transmitted with 20MHz, 40Mhz, 80MHz or 160Mhz BW
   input wire [1:0]  transmissionBW,

   //Indicates the number of retries for this MPDU. Valid when 
   //rtsFailed_p rtsSuccess_p mpduSuccess_p mpduFailed_p or 
   //retryLimitReached 
   input wire [7:0]  numMPDURetries,

   //indicates the the number of times the RTS has been sent.
   //Valid when rtsFailed_p rtsSuccess_p mpduSuccess_p 
   //mpduFailed_p or retryLimitReached 
   input wire [7:0]  numRTSRetries,
   
   // Updated value of medium time used for this MPDU or A-MPDU.
   input wire [31:0] mediumTimeUsed,

   //rxController interface Discard the current rx frame : no more descriptor and rxFlowCntrlEn == 1
   output wire        rxFrmDiscard,
   // Indicate to rxController that Current frame has a all necessaries descripstor
   output wire        rxDescAvailable,

   //registers interface rx Flow Control Enable
   input  wire        rxFlowCntrlEn,

   input  wire [ 3:0] whichDescriptorSW,             // Indicates the value of the partAMorMSDU field Controller

   //Frame Length mismatch detected by the MAC Controller
   input wire         macPHYIFUnderRun,


   // TXBCNHEADPTRREG register.
   input wire [31 : 0] txBcnHeadPtr   , //Transmit Beacon List Head Pointer

    // TXAC0HEADPTRREG register.
   input wire [31 : 0] txAC0HeadPtr   , //Transmit AC0 List Head Pointer

    // TXAC1HEADPTRREG register.
   input wire [31 : 0] txAC1HeadPtr   , //Transmit AC1 List Head Pointer

    // TXAC2HEADPTRREG register.
   input wire [31 : 0] txAC2HeadPtr   , //Transmit AC2 List Head Pointer

    // TXAC3HEADPTRREG register.
   input wire [31 : 0] txAC3HeadPtr   , //Transmit AC3 List Head Pointer 

    // RXHEADERHEADPTRREG register.
   input wire [29 : 0] rxHeaderHeadPtr, //Header channel head pointer
   input wire          rxHeaderHeadPtrValid, //Header channel head pointer valid

    // RXPAYLOADHEADPTRREG register.
   input wire [29 : 0] rxPayloadHeadPtr,  //Payload channel head pointer

   input wire          rxPayloadHeadPtrValid,  //Payload channel head pointer valid
   input wire  [7 : 0] rxPayloadUsedCount,     // Received Payload Used Count

   //TX Control Registers
   //Indicates there are 2 sets of parameters 
   //already in the tx Parameter Cache module
   //and not to fetch more
   input wire        txCtrlRegBusy,

   //TX FIFO
   //FIFO Full indication
   input wire        txFifoAlmostFull,
   input wire        txFifoFull,

   //FIFO Empty indication
   input wire        txFifoEmpty,
   output wire       txFIFOFlushDone_p,
                   
   //RX FIFO
   //FIFO empty indication
   input wire        rxFifoEmpty,
   //FIFO almost empty indication
   input wire        rxFIFOAlmEmpty,

   //Data read from RX FIFO
   input wire [31:0] rxFifoRdData,


   //RX TAG FIFO
   //Data from TAG FIFO
   input wire  [3:0] rxTagFifoRdData,


   //output wires
   //dmaHIF Master Interface      
   //Active High pulse indicating that a read transfer
   //has to be initiated on the dmaHIF
   output wire        dmaHIFRead,

   //Active High pulse indicating that a write transfer
   //has to be initiated on the dmaHIF
   output wire        dmaHIFWrite,

   //Indicates teh type of burst to be performed on teh dmaHIF
   output wire  [2:0] dmaHIFSize,

   //Address put out by the read write controller to the 
   //dmaHIF master interface. Starting address for the transfer
   //is provided by this bus
   output wire [31:0] dmaHIFAddressIn,

   //Data to be written to the SRAM is passed by the read write
   //controller to the dmaHIF master interface
   output wire [31:0] dmaHIFWriteDataIn,

   //TX parameter Cache module signals
   //Write signal to the Tx Parameter Cache
   output wire        txCtrlRegWr,

   //Indicates currently Policy table information is
   //being passed
   output wire        txCtrlRegPT,

   //Indicates currently Header descriptor information
   //is being passed
   output wire        txCtrlRegHD,

   //Signal to TX Parameter Cache module. 
   //Indicates to discard the recently 
   //fetch Header Descriptor
   output wire        discardPrevHD_p,

   //DMA state for AC0 channel. Registers will be updated with
   //this information
   output wire  [1:0] txAC0State,

   //DMA state for AC1 channel. Registers will be updated with
   //this information
   output wire  [1:0] txAC1State,

   //DMA state for AC2 channel. Registers will be updated with
   //this information
   output wire  [1:0] txAC2State,

   //DMA state for AC3 channel. Registers will be updated with
   //this information
   output wire  [1:0] txAC3State,

   //DMA state for Beacon channel. Registers will be updated with
   //this information
   output wire  [1:0] txBcnState,

   //DMA state for Receive Header channel. Registers will be updated
   //with this information
   output wire  [1:0] rxHeaderState,

   //DMA state for Payload Header channel. Registers will be updated
   //with this information
   output wire  [1:0] rxPayloadState,




   //DMA state for AC0 channel. Registers will be updated with
   //this information
   output reg  [3:0] txAC0StateMC,

   //DMA state for AC1 channel. Registers will be updated with
   //this information
   output reg  [3:0] txAC1StateMC,

   //DMA state for AC2 channel. Registers will be updated with
   //this information
   output reg  [3:0] txAC2StateMC,

   //DMA state for AC3 channel. Registers will be updated with
   //this information
   output reg  [3:0] txAC3StateMC,

   //DMA state for Beacon channel. Registers will be updated with
   //this information
   output reg  [3:0] txBcnStateMC,

   // Transmit Beacon Length Mismatch
   output wire        txBcnLenMismatch, 
   // Transmit AC0 Length Mismatch
   output wire        txAC0LenMismatch, 
   // Transmit AC1 Length Mismatch
   output wire        txAC1LenMismatch, 
   // Transmit AC2 Length Mismatch
   output wire        txAC2LenMismatch, 
   // Transmit AC3 Length Mismatch
   output wire        txAC3LenMismatch,     
   // Transmit Beacon Unique Pattern Error
   output wire        txBcnUPatternErr,     
   // Transmit AC0 Unique Pattern Error
   output wire        txAC0UPatternErr,     
   // Transmit AC1 Unique Pattern Error
   output wire        txAC1UPatternErr,     
   // Transmit AC2 Unique Pattern Error
   output wire        txAC2UPatternErr,     
   // Transmit AC3 Unique Pattern Error
   output wire        txAC3UPatternErr,     
   // Transmit Beacon Next Pointer Error
   output wire        txBcnNextPointerErr,  
   // Transmit AC0 Next Pointer Error
   output wire        txAC0NextPointerErr,  
   // Transmit AC1 Next Pointer Error
   output wire        txAC1NextPointerErr,  
   // Transmit AC2 Next Pointer Error
   output wire        txAC2NextPointerErr,  
   // Transmit AC3 Next Pointer Error
   output wire        txAC3NextPointerErr,  
   // Transmit Beacon Policy Table Address Error
   output wire        txBcnPTAddressErr,       
   // Transmit AC0 Policy Table Address Error
   output wire        txAC0PTAddressErr,    
   // Transmit AC1 Policy Table Address Error
   output wire        txAC1PTAddressErr,    
   // Transmit AC2 Policy Table Address Error
   output wire        txAC2PTAddressErr,    
   // Transmit AC3 Policy Table Address Error
   output wire        txAC3PTAddressErr,    
   // Transmit Beacon Bus Error
   output wire        txBcnBusErr,          
   // Transmit AC0 Bus Error
   output wire        txAC0BusErr,          
   // Transmit AC1 Bus Error
   output wire        txAC1BusErr,          
   // Transmit AC2 Bus Error
   output wire        txAC2BusErr,          
   // Transmit AC3 Bus Error
   output wire        txAC3BusErr,          
   // Transmit Beacon New Head Error
   output wire        txBcnNewHeadErr,      
   // Transmit AC0 New Head Error
   output wire        txAC0NewHeadErr,      
   // Transmit AC1 New Head Error
   output wire        txAC1NewHeadErr,      
   // Transmit AC2 New Head Error
   output wire        txAC2NewHeadErr,      
   // Transmit AC3 New Head Error
   output wire        txAC3NewHeadErr,    
    
   // Receive Header Unique Pattern Error  
   output wire        rxHdrUPatternErr,    
   // Receive Payload Unique Pattern Error
   output wire        rxPayUPatternErr,    
   // Receive Header Next Pointer Error
   output wire        rxHdrNextPointerErr, 
   // Receive Payload Next Pointer Error
   output wire        rxPayNextPointerErr, 
   // Receive Header Bus Error
   output wire        rxHdrBusErr,         
   // Receive Payload Bus Error
   output wire        rxPayBusErr,         
   // Receive Header New Head Error
   output wire        rxHdrNewHeadErr,     
   // Receive Payload New Head Error
   output wire        rxPayNewHeadErr,    
   // Transmit PolicyTable Error
   output wire        ptError,
   // Transmit Beacon Startup      
   output wire        txBcnStartup,       
   // Transmit AC0 New Head Error
   output wire        txAC0Startup,       
   // Transmit AC1 New Head Error
   output wire        txAC1Startup,       
   // Transmit AC2 New Head Error
   output wire        txAC2Startup,       
   // Transmit AC3 New Head Error
   output wire        txAC3Startup,       
   // Transmit Beacon End of Queue
   output wire        txBcnEndQ,          
   // Transmit AC0 End of Queue
   output wire        txAC0EndQ,          
   // Transmit AC1 End of Queue
   output wire        txAC1EndQ,          
   // Transmit AC2 End of Queue
   output wire        txAC2EndQ,          
   // Transmit AC3 End of Queue
   output wire        txAC3EndQ,          
   // Transmit Beacon Halt After TXOP
   output wire        txBcnHaltAfterTXOP, 
   // Transmit AC0 Halt After TXOP
   output wire        txAC0HaltAfterTXOP, 
   // Transmit AC1 Halt After TXOP
   output wire        txAC1HaltAfterTXOP, 
   // Transmit AC2 Halt After TXOP
   output wire        txAC2HaltAfterTXOP, 
   // Transmit AC3 Halt After TXOP
   output wire        txAC3HaltAfterTXOP, 

   output wire [15:0] debugPortDMA1,
   output wire [15:0] debugPortDMA2,
   output wire [15:0] debugPortDMA3,
   output wire [15:0] debugPortDMA4,
   output wire [15:0] debugPortDMA5,
   output wire [15:0] debugPortDMA6,
   output wire [15:0] debugPortDMAStatus,
   output wire [15:0] debugPortDMATxStatus,
   output wire [15:0] debugPortTxRxListA,
   output wire [15:0] debugPortDmaRdWrCtlr,

   output wire        dmaInternalError,// Generate a pulse when an internal error occured

   // Indication from the DMA that status have been updated.
   output wire        statusUpdated_p,

   //TX FIFO
   //Read signal to TX FIFO
   output wire        txFifoWr,

   //Read signal to TX FIFO
   output wire [31:0] txFIFOWrData,

   //Flush signal to TX FIFo
   output wire        flushTxFifo,

   //RX FIFO
   //Write signal to RX FIFO
   output wire        rxFifoRd,

   //TX TAG FIFO
   //Data to write to TX TAG FIFO
   output wire  [5:0] txTagFifoWrData,

   //Interrupt Controller
   //Transmit Channel error
   output wire        bcnTxDMADead,   // bcnTxDMADead output mask interruption
   output wire        ac3TxDMADead,   // ac3TxDMADead output mask interruption
   output wire        ac2TxDMADead,   // ac2TxDMADead output mask interruption
   output wire        ac1TxDMADead,   // ac1TxDMADead output mask interruption
   output wire        ac0TxDMADead,   // ac0TxDMADead output mask interruption

   //Receive Channel error
   output wire        rxPayloadDMADead,   // rxPayloadDMADead output mask interruption
   output wire        rxHeaderDMADead,    // rxHeaderDMADead output mask interruption

   output wire        rxDMAEmpty,         //RX DMA Empty Interrupt
   output wire        ac0TxTrigger,       //trigger for transmission interrupt for AC0,
   output wire        ac1TxTrigger,       //trigger for transmission interrupt for AC1,
   output wire        ac2TxTrigger,       //trigger for transmission interrupt for AC2,
   output wire        ac3TxTrigger,       //trigger for transmission interrupt for AC3,
   output wire        bcnTxTrigger,       //trigger for transmission interrupt for Beacon,

   output wire        ac0TxBufTrigger,    //trigger for Payload Buffer transmission interrupt for AC0,
   output wire        ac1TxBufTrigger,    //trigger for Payload Buffer transmission interrupt for AC1,
   output wire        ac2TxBufTrigger,    //trigger for Payload Buffer transmission interrupt for AC2,
   output wire        ac3TxBufTrigger,    //trigger for Payload Buffer transmission interrupt for AC3,
   output wire        bcnTxBufTrigger,    //trigger for Payload Buffer transmission interrupt for Beacon,

   //$port_g Trigger for receive interrupt
   output wire        rxTrigger,                  // Rx interrupt required in the RHD
   output wire        counterRxTrigger,           // Interrupt indicating that the processed number of payload descriptor
                                                  // if bigger or equal to 
   output wire        rxTrig_p,                   // Indicate that the RX Descriptor Done has been written

   // Tx Status pointers
   output wire [31:0] ac0StatusPointer,           // Status ptr of AC0 channel
   output wire [31:0] ac1StatusPointer,           // status ptr of AC1 channel
   output wire [31:0] ac2StatusPointer,           // status ptr of AC2 channel
   output wire [31:0] ac3StatusPointer,           // Status ptr of AC3 channel
   output wire [31:0] bcnStatusPointer,           // status ptr of beacon channel
   output wire [31:0] txCurrentPointer,           // status of the current pointer
   
   
   //Rx Status Pointers
   output wire [31:0] rxHdrStatPointer,           // status pointer of header channel
   output wire [31:0] rxPayStatPointer,           // status pointer of payload channel
   output wire [31:0] rxPayCurrentPointer,        // Keeps track of the payload linked list

   //
   output wire statussettxAC0NewTail            , //Status signal of txAC0NewTail bit in
                                                  //the DMA Control register
   output wire statussettxAC1NewTail            , //Status signal of txAC1NewTail bit in
                                                  //the DMA Control register
   output wire statussettxAC2NewTail            , //Status signal of txAC2NewTail bit in
                                                  //the DMA Control register
   output wire statussettxAC3NewTail            , //Status signal of txAC3NewTail bit in
                                                  //the DMA Control register
   output wire statussettxBcnNewTail            , //Status signal of txBcnNewTail bit in
                                                  //the DMA Control register
   output wire statussettxAC0NewHead            , //Status signal of txAC0NewHead bit in
                                                  //the DMA Control register
   output wire statussettxAC1NewHead            , //Status signal of txAC1NewHead bit in
                                                  //the DMA Control register
   output wire statussettxAC2NewHead            , //Status signal of txAC2NewHead bit in
                                                  //the DMA Control register
   output wire statussettxAC3NewHead            , //Status signal of txAC3NewHead bit in
                                                  //the DMA Control register
   output wire statussettxBcnNewHead            , //Status signal of txBcnNewHead bit in
                                                  //the DMA Control register
   output wire statussetrxHeaderNewTail         , //Status signal of rxHeaderNewTail bit in
                                                  //the DMA Control register
   output wire statussetrxHeaderNewHead         , //Status signal of rxHeaderNewHead bit in
                                                  //the DMA Control register
   output wire statussetrxPayloadNewTail        , //Status signal of rxPayloadNewTail bit in
                                                  //the DMA Control register
   output wire statussetrxPayloadNewHead        , //Status signal of rxPayloadNewHead bit in
                                                  //the DMA Control register


   output wire statussethaltBcnAfterTXOP        ,
   
   output wire statussethaltAC3AfterTXOP        ,
   
   output wire statussethaltAC2AfterTXOP        ,
   
   output wire statussethaltAC1AfterTXOP        ,
   
   output wire statussethaltAC0AfterTXOP        ,
   



   input wire  settxAC0NewTail                  ,   //Set signal to Set the txAC0NewTail bit in
                                                    //the DMA Control register
   input wire  settxAC1NewTail                  ,   //Set signal to Set the txAC1NewTail bit in
                                                    //the DMA Control register
   input wire  settxAC2NewTail                  ,   //Set signal to Set the txAC2NewTail bit in
                                                    //the DMA Control register
   input wire  settxAC3NewTail                  ,   //Set signal to Set the txAC3NewTail bit in
                                                    //the DMA Control register
   input wire  settxBcnNewTail                  ,   //Set signal to Set the txBcnNewTail bit in
                                                    //the DMA Control register
   input wire  settxAC0NewHead                  ,   //Set signal to Set the txAC0NewHead bit in
                                                    //the DMA Control register
   input wire  settxAC1NewHead                  ,   //Set signal to Set the txAC1NewHead bit in
                                                    //the DMA Control register
   input wire  settxAC2NewHead                  ,   //Set signal to Set the txAC2NewHead bit in
                                                    //the DMA Control register
   input wire  settxAC3NewHead                  ,   //Set signal to Set the txAC3NewHead bit in
                                                    //the DMA Control register
   input wire  settxBcnNewHead                  ,   //Set signal to Set the txBcnNewHead bit in
                                                    //the DMA Control register
   input wire  setrxHeaderNewTail               ,   //Set signal to Set the rxHeaderNewTail bit in
                                                    //the DMA Control register
   input wire  setrxHeaderNewHead               ,   //Set signal to Set the rxHeaderNewHead bit in
                                                    //the DMA Control register
   input wire  setrxPayloadNewTail              ,   //Set signal to Set the rxPayloadNewTail bit in
                                                    //the DMA Control register
   input wire  setrxPayloadNewHead              ,   //Set signal to Set the rxPayloadNewHead bit in
                                                    //the DMA Control register
   input wire  sethaltBcnAfterTXOP              ,
   
   input wire  sethaltAC3AfterTXOP              ,
   
   input wire  sethaltAC2AfterTXOP              ,
   
   input wire  sethaltAC1AfterTXOP              ,
   
   input wire  sethaltAC0AfterTXOP              ,
   

   input wire  cleartxAC0NewTail                ,   //Clear signal to Clear the txAC0NewTail bit in
                                                    //the DMA Control register
   input wire  cleartxAC1NewTail                ,   //Clear signal to Clear the txAC1NewTail bit in
                                                    //the DMA Control register
   input wire  cleartxAC2NewTail                ,   //Clear signal to Clear the txAC2NewTail bit in
                                                    //the DMA Control register
   input wire  cleartxAC3NewTail                ,   //Clear signal to Clear the txAC3NewTail bit in
                                                    //the DMA Control register
   input wire  cleartxBcnNewTail                ,   //Clear signal to Clear the txBcnNewTail bit in
                                                    //the DMA Control register
   input wire  cleartxAC0NewHead                ,   //Clear signal to Clear the txAC0NewHead bit in
                                                    //the DMA Control register
   input wire  cleartxAC1NewHead                ,   //Clear signal to Clear the txAC1NewHead bit in
                                                    //the DMA Control register
   input wire  cleartxAC2NewHead                ,   //Clear signal to Clear the txAC2NewHead bit in
                                                    //the DMA Control register
   input wire  cleartxAC3NewHead                ,   //Clear signal to Clear the txAC3NewHead bit in
                                                    //the DMA Control register
   input wire  cleartxBcnNewHead                ,   //Clear signal to Clear the txBcnNewHead bit in
                                                    //the DMA Control register
   input wire  clearrxHeaderNewTail             ,   //Clear signal to Clear the rxHeaderNewTail bit in
                                                    //the DMA Control register
   input wire  clearrxHeaderNewHead             ,   //Clear signal to Clear the rxHeaderNewHead bit in
                                                    //the DMA Control register
   input wire  clearrxPayloadNewTail            ,   //Clear signal to Clear the rxPayloadNewTail bit in
                                                    //the DMA Control register
   input wire  clearrxPayloadNewHead            ,   //Clear signal to Clear the rxPayloadNewHead bit in
                                                    //the DMA Control register
   input wire  clearhaltBcnAfterTXOP            ,
   
   input wire  clearhaltAC3AfterTXOP            ,
   
   input wire  clearhaltAC2AfterTXOP            ,
   
   input wire  clearhaltAC1AfterTXOP            ,
   
   input wire  clearhaltAC0AfterTXOP            
   
   
   
      );


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

reg        haltAC0AfterTXOP;
reg        haltAC1AfterTXOP;
reg        haltAC2AfterTXOP;
reg        haltAC3AfterTXOP;
reg        haltBcnAfterTXOP;

wire       bufferInterruptTx;     //

reg        txNewTailAC0;
reg        txNewTailAC1;
reg        txNewTailAC2;
reg        txNewTailAC3;
reg        txNewTailBcn;
reg        txNewHeadAC0;
reg        txNewHeadAC1;
reg        txNewHeadAC2;
reg        txNewHeadAC3;
reg        txNewHeadBcn;
reg        txNewHeadAC0_waitIdle;
reg        txNewHeadAC1_waitIdle;
reg        txNewHeadAC2_waitIdle;
reg        txNewHeadAC3_waitIdle;
reg        txNewHeadBcn_waitIdle;
reg        rxNewHeadHdr;
reg        rxNewTailHdr;
reg        rxNewTailPld;
reg        rxNewHeadPld;

wire       rstAC0NewTail;
wire       rstAC1NewTail;
wire       rstAC2NewTail;
wire       rstAC3NewTail;
wire       rstBcnNewTail;
wire       rstAC0NewHead;
wire       rstAC1NewHead;
wire       rstAC2NewHead;
wire       rstAC3NewHead;
wire       rstBcnNewHead;
wire       rstNewTailHdr;
wire       rstNewHeadHdr;
wire       rstNewTailPld;
wire       rstNewHeadPld;


// resynchronized signals
wire        trigTxAC0sync;
wire        trigTxAC1sync;
wire        trigTxAC2sync;
wire        trigTxAC3sync;
wire        trigTxBcnsync;
wire        underRunDetected_p;


//Transmit AC0 List Head Pointer
//Header channel head pointer
wire [31:0] intrxHdrHeadPtr;

//Payload channel head pointer
wire [31:0] intrxPldHeadPtr;

// resynchronized signals
wire        dmaframeRxed_p;                // frameRxed_p resynchronized with macPIClk      
wire        dmarxListProcCsIsIdle;         // rxListProcCsIsIdle from DMAEngine before resynchronization to macCoreClock domain
reg         swRTSResync_p;                 // swRTS_p resynchronized with macPIClk        
wire        txMpduDoneResync_p;            // txMpduDone_p resynchronized with macPIClk   
reg         txMpduDoneResyncDly_p;         // txMpduDoneResyncDly_p is txMpduDoneResync_p delayed of 1cc
reg         ampduFrmResync_p;              // ampduFrm_p resynchronized with macPIClk     
reg         retryFrameResync_p;            // retryFrame_p resynchronized with macPIClk   
reg         mpduSuccessResync_p;           // mpduSuccess_p resynchronized with macPIClk  
reg         mpduFailedResync_p;            // mpduFailed_p resynchronized with macPIClk   
reg         rtsFailedResync_p;             // rtsFailed_p resynchronized with macPIClk    
reg         rtsSuccessResync_p;            // rtsSuccess_p resynchronized with macPIClk   
reg         retryLimitReachedResync_p;     // retryLimitReached_p resynchronized with macPIClk 

reg  [1:0]  transmissionBWResync;          // transmissionBW resynchronized with macPIClk
reg  [7:0]  numMPDURetriesResync;          // numMPDURetries resynchronized with macPIClk
reg  [7:0]  numRTSRetriesResync;           // numRTSRetries resynchronized with macPIClk
reg  [31:0] mediumTimeUsedResync;          // mediumTimeUsed resynchronized with macPIClk


reg  [3:0]  whichDescriptorSWResync;       // whichDescriptorSW resynchronized with macPIClk
wire        updateDMAStatusResync_p;       // updateDMAStatus_p resynchronized with macPIClk
reg         updateDMAStatusResyncDly_p;    // updateDMAStatusResyncDly_p is updateDMAStatusResync_p delayed of 1cc
reg         updateDMAStatusResyncDly2_p;    // updateDMAStatusResyncDly_p is updateDMAStatusResync_p delayed of 1cc

wire        rxFlowCntrlEnResync;           // Resync from macCore register domain
// signals for debug
wire        oredNewHead;                // indicate a newhead trigger
wire        oredNewTail;                // indicate a newTail trigger
wire        txInterrupt;                // 
wire        rxInterrupt;                // 

// Internal DMA States signals for resynchronization and 
// One Hot to Binary conversion
wire  [3:0] txAC0StateInt;              // DMA state for AC0 channel.            
wire  [3:0] txAC1StateInt;              // DMA state for AC1 channel.            
wire  [3:0] txAC2StateInt;              // DMA state for AC2 channel.            
wire  [3:0] txAC3StateInt;              // DMA state for AC3 channel.            
wire  [3:0] txBcnStateInt;              // DMA state for Beacon channel.         
wire  [3:0] rxHeaderStateInt;           // DMA state for Receive Header channel. 
wire  [3:0] rxPayloadStateInt;          // DMA state for Payload Header channel. 

wire        statusUpdatedInt_p;         // statusUpdated_p before resynchronizationon macCoreClk

wire  [4:0] txListProcCs;               // Current State counter
wire  [4:0] rxListProcCs;               // Current State counter
wire        interruptEnTx;              // Interrupt Enable information in THD
wire        statusUpdaterFull;          // Indicate the status updater is full

wire        bcnTxDMADead_int;
wire        ac3TxDMADead_int;
wire        ac2TxDMADead_int;
wire        ac1TxDMADead_int;
wire        ac0TxDMADead_int;
wire        dmaInternalError_int;// Generate a pulse when an internal error occured

wire        rxTrigInt_p;               // Indicate that the RX Descriptor Done has been written in macPIClk

wire        rxFrmDiscardResync;
wire        rxDescAvailableResync;
wire        rxFrmDiscardRet;

reg   [3:0] txAC0StateMC_resync;
reg   [3:0] txAC1StateMC_resync;
reg   [3:0] txAC2StateMC_resync;
reg   [3:0] txAC3StateMC_resync;
reg   [3:0] txBcnStateMC_resync;

reg   [3:0] txAC0StateMC_ff1;
reg   [3:0] txAC1StateMC_ff1;
reg   [3:0] txAC2StateMC_ff1;
reg   [3:0] txAC3StateMC_ff1;
reg   [3:0] txBcnStateMC_ff1;

reg   [3:0] txAC0StateMC_ff2;
reg   [3:0] txAC1StateMC_ff2;
reg   [3:0] txAC2StateMC_ff2;
reg   [3:0] txAC3StateMC_ff2;
reg   [3:0] txBcnStateMC_ff2;

wire        txStateActiveMC;
wire        txStateActive;
wire        txStateActiveMC_resync;
  
wire        dmaTxFIFOFlushDone_p;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////
// Conversion function between One Hot encoding to binay.
//////////////////////////////////////////////////////////////////
function [1:0] convOneHotToBin ;
input   [3:0] onehot ;
begin
  case (onehot)
    4'b0001 : convOneHotToBin = 2'd0;
    4'b0010 : convOneHotToBin = 2'd1;
    4'b0100 : convOneHotToBin = 2'd2;
    4'b1000 : convOneHotToBin = 2'd3;
    default : convOneHotToBin = 2'd0;
  endcase
end
endfunction


//////////////////////////////////////////////////////////////////

assign intrxHdrHeadPtr  =  {rxHeaderHeadPtr  ,1'b0,rxHeaderHeadPtrValid};
assign intrxPldHeadPtr  =  {rxPayloadHeadPtr ,1'b0,rxPayloadHeadPtrValid};




/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    txNewTailAC0 <= 1'b0;
  end
  else if(macPIClkSoftRst_n == 1'b0)
  begin
    txNewTailAC0 <= 1'b0;
  end
  else 
  begin
    if ( (rstAC0NewTail == 1'b1) || (cleartxAC0NewTail)) begin
      txNewTailAC0 <= 1'b0;
    end
    else if (settxAC0NewTail == 1'b1) begin
      txNewTailAC0 <= 1'b1;
    end
  end
end

assign statussettxAC0NewTail  = txNewTailAC0;


/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    txNewTailAC1 <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    txNewTailAC1 <= 1'b0;
  end
  else 
  begin
    if ( (rstAC1NewTail == 1'b1) || (cleartxAC1NewTail)) begin
      txNewTailAC1 <= 1'b0;
    end
    else if (settxAC1NewTail == 1'b1) begin
      txNewTailAC1 <= 1'b1;
    end
  end
end

assign statussettxAC1NewTail  = txNewTailAC1;

/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    txNewTailAC2 <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    txNewTailAC2 <= 1'b0;
  end 
  else 
  begin
    if ( (rstAC2NewTail == 1'b1) || (cleartxAC2NewTail)) begin
      txNewTailAC2 <= 1'b0;
    end
    else if (settxAC2NewTail == 1'b1) begin
      txNewTailAC2 <= 1'b1;
    end
  end
end

assign statussettxAC2NewTail  = txNewTailAC2;

/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    txNewTailAC3 <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    txNewTailAC3 <= 1'b0;
  end
  else 
  begin
    if ( (rstAC3NewTail == 1'b1) || (cleartxAC3NewTail)) begin
      txNewTailAC3 <= 1'b0;
    end
    else if (settxAC3NewTail == 1'b1) begin
      txNewTailAC3 <= 1'b1;
    end
  end
end

assign statussettxAC3NewTail  = txNewTailAC3;


/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    txNewTailBcn <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    txNewTailBcn <= 1'b0;
  end
  else 
  begin
    if ( (rstBcnNewTail == 1'b1) || (cleartxBcnNewTail)) begin
      txNewTailBcn <= 1'b0;
    end
    else if (settxBcnNewTail == 1'b1) begin
      txNewTailBcn <= 1'b1;
    end
  end
end

assign statussettxBcnNewTail  = txNewTailBcn;

/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    txNewHeadAC0          <= 1'b0;
    txNewHeadAC0_waitIdle <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    txNewHeadAC0          <= 1'b0;
    txNewHeadAC0_waitIdle <= 1'b0;
  end
  else 
  begin
    if ((rstAC0NewHead == 1'b1) || (cleartxAC0NewHead))
    begin
      txNewHeadAC0          <= 1'b0;
      txNewHeadAC0_waitIdle <= 1'b0;
    end
    else if ((txAC0StateInt[3:0] == 4'h1) || (txAC0StateInt[3:0] == 4'h2))
    begin
      if ((settxAC0NewHead == 1'b1) || (txNewHeadAC0_waitIdle == 1'b1))
      begin
        txNewHeadAC0          <= 1'b1;
        txNewHeadAC0_waitIdle <= 1'b0;
      end
    end
    else if ((settxAC0NewHead == 1'b1) && (txAC0StateInt[3:0] == 4'h4))
    begin
      txNewHeadAC0_waitIdle <= 1'b1;
    end
  end
end

assign statussettxAC0NewHead  = txNewHeadAC0;


/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    txNewHeadAC1          <= 1'b0;
    txNewHeadAC1_waitIdle <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    txNewHeadAC1          <= 1'b0;
    txNewHeadAC1_waitIdle <= 1'b0;
  end
  else 
  begin
    if ((rstAC1NewHead == 1'b1) || (cleartxAC1NewHead))
    begin
      txNewHeadAC1          <= 1'b0;
      txNewHeadAC1_waitIdle <= 1'b0;
    end
    else if ((txAC1StateInt[3:0] == 4'h1) || (txAC1StateInt[3:0] == 4'h2))
    begin
      if ((settxAC1NewHead == 1'b1) || (txNewHeadAC1_waitIdle == 1'b1))
      begin
        txNewHeadAC1          <= 1'b1;
        txNewHeadAC1_waitIdle <= 1'b0;
      end
    end
    else if ((settxAC1NewHead == 1'b1)  && (txAC1StateInt[3:0] == 4'h4))
    begin
        txNewHeadAC1_waitIdle <= 1'b1;
    end
  end
end

assign statussettxAC1NewHead  = txNewHeadAC1;

/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    txNewHeadAC2          <= 1'b0;
    txNewHeadAC2_waitIdle <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    txNewHeadAC2          <= 1'b0;
    txNewHeadAC2_waitIdle <= 1'b0;
  end
  else 
  begin
    if ((rstAC2NewHead == 1'b1) || (cleartxAC2NewHead))
    begin
      txNewHeadAC2          <= 1'b0;
      txNewHeadAC2_waitIdle <= 1'b0;
    end
    else if ((txAC2StateInt[3:0] == 4'h1) || (txAC2StateInt[3:0] == 4'h2))
    begin
      if ((settxAC2NewHead == 1'b1) || (txNewHeadAC2_waitIdle == 1'b1))
      begin
        txNewHeadAC2          <= 1'b1;
        txNewHeadAC2_waitIdle <= 1'b0;
      end
    end
    else if ((settxAC2NewHead == 1'b1)  && (txAC2StateInt[3:0] == 4'h4))
    begin
        txNewHeadAC2_waitIdle <= 1'b1;
    end
  end
end

assign statussettxAC2NewHead  = txNewHeadAC2;

/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    txNewHeadAC3          <= 1'b0;
    txNewHeadAC3_waitIdle <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    txNewHeadAC3          <= 1'b0;
    txNewHeadAC3_waitIdle <= 1'b0;
  end
  else 
  begin
    if ((rstAC3NewHead == 1'b1) || (cleartxAC3NewHead)) 
    begin
      txNewHeadAC3          <= 1'b0;
      txNewHeadAC3_waitIdle <= 1'b0;
    end
    else if ((txAC3StateInt[3:0] == 4'h1) || (txAC3StateInt[3:0] == 4'h2))
    begin
      if ((settxAC3NewHead == 1'b1) || (txNewHeadAC3_waitIdle == 1'b1))
      begin
        txNewHeadAC3          <= 1'b1;
        txNewHeadAC3_waitIdle <= 1'b0;
      end
    end
    else if ((settxAC3NewHead == 1'b1) && (txAC3StateInt[3:0] == 4'h4))
    begin
        txNewHeadAC3_waitIdle <= 1'b1;
    end
  end
end

assign statussettxAC3NewHead  = txNewHeadAC3;


/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    txNewHeadBcn          <= 1'b0;
    txNewHeadBcn_waitIdle <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    txNewHeadBcn          <= 1'b0;
    txNewHeadBcn_waitIdle <= 1'b0;
  end
  else 
  begin
    if ((rstBcnNewHead == 1'b1) || (cleartxBcnNewHead))
    begin
      txNewHeadBcn          <= 1'b0;
      txNewHeadBcn_waitIdle <= 1'b0;
    end
    else if ((txBcnStateInt[3:0] == 4'h1) || (txBcnStateInt[3:0] == 4'h2))
    begin
      if ((settxBcnNewHead == 1'b1) || (txNewHeadBcn_waitIdle == 1'b1))
      begin
        txNewHeadBcn          <= 1'b1;
        txNewHeadBcn_waitIdle <= 1'b0;
      end
    end
    else if ((settxBcnNewHead == 1'b1)  && (txBcnStateInt[3:0] == 4'h4))
    begin
        txNewHeadBcn_waitIdle <= 1'b1;
    end
  end
end

// assign statussettxBcnNewHead  = txNewHeadBcn;
assign statussettxBcnNewHead  = txNewHeadBcn || txNewHeadBcn_waitIdle;


/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    rxNewTailHdr <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    rxNewTailHdr <= 1'b0;
  end
  else 
  begin
    if ( (rstNewTailHdr == 1'b1) || (clearrxHeaderNewTail)) begin
      rxNewTailHdr <= 1'b0;
    end
    else if (setrxHeaderNewTail == 1'b1) begin
      rxNewTailHdr <= 1'b1;
    end
  end
end
assign statussetrxHeaderNewTail  = rxNewTailHdr;

/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    rxNewHeadHdr <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    rxNewHeadHdr <= 1'b0;
  end
  else 
  begin
    if ( (rstNewHeadHdr == 1'b1) || (clearrxHeaderNewHead)) begin
      rxNewHeadHdr <= 1'b0;
    end
    else if (setrxHeaderNewHead == 1'b1) begin
      rxNewHeadHdr <= 1'b1;
    end
  end
end
assign statussetrxHeaderNewHead  = rxNewHeadHdr;


/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    rxNewTailPld <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    rxNewTailPld <= 1'b0;
  end
  else 
  begin
    if ( (rstNewTailPld == 1'b1) || (clearrxPayloadNewTail)) begin
      rxNewTailPld <= 1'b0;
    end
    else if (setrxPayloadNewTail == 1'b1) begin
      rxNewTailPld <= 1'b1;
    end
  end
end
assign statussetrxPayloadNewTail  = rxNewTailPld;

/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    rxNewHeadPld <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    rxNewHeadPld <= 1'b0;
  end
  else 
  begin
    if ( (rstNewHeadPld == 1'b1) || (clearrxPayloadNewHead)) begin
      rxNewHeadPld <= 1'b0;
    end
    else if (setrxPayloadNewHead == 1'b1) begin
      rxNewHeadPld <= 1'b1;
    end
  end
end
assign statussetrxPayloadNewHead  = rxNewHeadPld;

/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    haltAC0AfterTXOP <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    haltAC0AfterTXOP <= 1'b0;
  end
  else 
  begin
    if (clearhaltAC0AfterTXOP) begin
      haltAC0AfterTXOP <= 1'b0;
    end
    else if (sethaltAC0AfterTXOP == 1'b1) begin
      haltAC0AfterTXOP <= 1'b1;
    end
  end
end
assign statussethaltAC0AfterTXOP  = haltAC0AfterTXOP;

/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    haltAC1AfterTXOP <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    haltAC1AfterTXOP <= 1'b0;
  end
  else 
  begin
    if (clearhaltAC1AfterTXOP) begin
      haltAC1AfterTXOP <= 1'b0;
    end
    else if (sethaltAC1AfterTXOP == 1'b1) begin
      haltAC1AfterTXOP <= 1'b1;
    end
  end
end
assign statussethaltAC1AfterTXOP  = haltAC1AfterTXOP;

/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    haltAC2AfterTXOP <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    haltAC2AfterTXOP <= 1'b0;
  end
  else 
  begin
    if (clearhaltAC2AfterTXOP) begin
      haltAC2AfterTXOP <= 1'b0;
    end
    else if (sethaltAC2AfterTXOP == 1'b1) begin
      haltAC2AfterTXOP <= 1'b1;
    end
  end
end
assign statussethaltAC2AfterTXOP  = haltAC2AfterTXOP;

/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    haltAC3AfterTXOP <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    haltAC3AfterTXOP <= 1'b0;
  end
  else 
  begin
    if (clearhaltAC3AfterTXOP) begin
      haltAC3AfterTXOP <= 1'b0;
    end
    else if (sethaltAC3AfterTXOP == 1'b1) begin
      haltAC3AfterTXOP <= 1'b1;
    end
  end
end
assign statussethaltAC3AfterTXOP  = haltAC3AfterTXOP;

/////////////////////////////////////////////////////////////////
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    haltBcnAfterTXOP <= 1'b0;
  end
  else if (macPIClkSoftRst_n == 1'b0)
  begin
    haltBcnAfterTXOP <= 1'b0;
  end
  else 
  begin
    if (clearhaltBcnAfterTXOP) begin
      haltBcnAfterTXOP <= 1'b0;
    end
    else if (sethaltBcnAfterTXOP == 1'b1) begin
      haltBcnAfterTXOP <= 1'b1;
    end
  end
end
assign statussethaltBcnAfterTXOP  = haltBcnAfterTXOP;



/////////////////////////////////////////////////////////////////
// clock domain reynchronization
/////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////
/// rxController Flow Control
////////////////////////////////////////////////////

// Instanciation of simpleSynchro
// Name of the instance : U_rxFrmDiscard_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_rxFrmDiscard_synchro (
                .dstclk             (macCoreRxClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (rxFrmDiscardResync),
                .dstdata            (rxFrmDiscard)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_rxDescAvailable_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_rxDescAvailable_synchro (
                .dstclk             (macCoreRxClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (rxDescAvailableResync),
                .dstdata            (rxDescAvailable)
                );

// Loop Back Here to avoid port map goes and return
// Instanciation of simpleSynchro
// Name of the instance : U_rxFrmDiscardRet_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_rxFrmDiscardRet_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (rxFrmDiscard),
                .dstdata            (rxFrmDiscardRet)
                );

// Resync rxFlowCntrlEn from macCore register domain
// Instanciation of simpleSynchro
// Name of the instance : U_rxFlowCntrlEn_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_rxFlowCntrlEn_synchro (
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (rxFlowCntrlEn),
                .dstdata            (rxFlowCntrlEnResync)
                );


// Instanciation of pulse2PulseSynchro
// Name of the instance : U_txFIFOFlushDone_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_txFIFOFlushDone_p_synchro (
                .srcclk             (macPIClk),
                .srcresetn          (macPIClkHardRst_n),
                .dstclk             (macCoreClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (dmaTxFIFOFlushDone_p),
                .dstdata            (txFIFOFlushDone_p)
                );


////////////////////////////////////////////////////
/// BackOff/AC Selection Interface
////////////////////////////////////////////////////


// Instanciation of simpleSynchro
// Name of the instance : U_trigTxAC0_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_trigTxAC0_synchro (
                .dstclk             (macPITxClk),
                .dstresetn          (macPITxClkHardRst_n),
                .srcdata            (trigTxAC0),
                .dstdata            (trigTxAC0sync)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_trigTxAC1_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_trigTxAC1_synchro (
                .dstclk             (macPITxClk),
                .dstresetn          (macPITxClkHardRst_n),
                .srcdata            (trigTxAC1),
                .dstdata            (trigTxAC1sync)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_trigTxAC2_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_trigTxAC2_synchro (
                .dstclk             (macPITxClk),
                .dstresetn          (macPITxClkHardRst_n),
                .srcdata            (trigTxAC2),
                .dstdata            (trigTxAC2sync)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_trigTxAC3_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_trigTxAC3_synchro (
                .dstclk             (macPITxClk),
                .dstresetn          (macPITxClkHardRst_n),
                .srcdata            (trigTxAC3),
                .dstdata            (trigTxAC3sync)
                );

// Instanciation of simpleSynchro
// Name of the instance : U_trigTxACBcn_synchro
// Name of the file containing this module : simpleSynchro.v
simpleSynchro U_trigTxACBcn_synchro (
                .dstclk             (macPITxClk),
                .dstresetn          (macPITxClkHardRst_n),
                .srcdata            (trigTxBcn),
                .dstdata            (trigTxBcnsync)
                );

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_rxUnderRun_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_rxUnderRun_synchro (
                .srcclk             (macCoreRxClk),
                .srcresetn          (macCoreClkHardRst_n),
                .dstclk             (macPITxClk),
                .dstresetn          (macPITxClkHardRst_n),
                .srcdata            (macPHYIFUnderRun),
                .dstdata            (underRunDetected_p)
                );


// Avoid glitches resync matters
always @(posedge macCoreClk, negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    txAC0StateMC_resync <= 4'b0;
    txAC1StateMC_resync <= 4'b0;
    txAC2StateMC_resync <= 4'b0;
    txAC3StateMC_resync <= 4'b0;
    txBcnStateMC_resync <= 4'b0;

    txAC0StateMC_ff1 <= 4'b0;
    txAC1StateMC_ff1 <= 4'b0;
    txAC2StateMC_ff1 <= 4'b0;
    txAC3StateMC_ff1 <= 4'b0;
    txBcnStateMC_ff1 <= 4'b0;

    txAC0StateMC_ff2 <= 4'b0;
    txAC1StateMC_ff2 <= 4'b0;
    txAC2StateMC_ff2 <= 4'b0;
    txAC3StateMC_ff2 <= 4'b0;
    txBcnStateMC_ff2 <= 4'b0;

    txAC0StateMC     <= 4'b0;
    txAC1StateMC     <= 4'b0;
    txAC2StateMC     <= 4'b0;
    txAC3StateMC     <= 4'b0;
    txBcnStateMC     <= 4'b0;
  end
  else
  begin
    txAC0StateMC_resync <= txAC0StateInt;
    txAC1StateMC_resync <= txAC1StateInt;
    txAC2StateMC_resync <= txAC2StateInt;
    txAC3StateMC_resync <= txAC3StateInt;
    txBcnStateMC_resync <= txBcnStateInt;

    txAC0StateMC_ff1    <= txAC0StateMC_resync;
    txAC1StateMC_ff1    <= txAC1StateMC_resync;
    txAC2StateMC_ff1    <= txAC2StateMC_resync;
    txAC3StateMC_ff1    <= txAC3StateMC_resync;
    txBcnStateMC_ff1    <= txBcnStateMC_resync;

    if(txAC0StateMC_ff1 == txAC0StateMC_resync)
      txAC0StateMC <= txAC0StateMC_ff1;

    if(txAC1StateMC_ff1 == txAC1StateMC_resync)
      txAC1StateMC <= txAC1StateMC_ff1;

    if(txAC2StateMC_ff1 == txAC2StateMC_resync)
      txAC2StateMC <= txAC2StateMC_ff1;

    if(txAC3StateMC_ff1 == txAC3StateMC_resync)
      txAC3StateMC <= txAC3StateMC_ff1;

    if(txBcnStateMC_ff1 == txBcnStateMC_resync)
      txBcnStateMC <= txBcnStateMC_ff1;

  end
end

assign txStateActiveMC = ((trigTxAC0 == 1'b1) && (txAC0StateMC == 4'h4)) ||
                         ((trigTxAC1 == 1'b1) && (txAC1StateMC == 4'h4)) ||
                         ((trigTxAC2 == 1'b1) && (txAC2StateMC == 4'h4)) ||
                         ((trigTxAC3 == 1'b1) && (txAC3StateMC == 4'h4)) ||
                         ((trigTxBcn == 1'b1) && (txBcnStateMC == 4'h4))    ;

assign txStateActive   = ((trigTxAC0sync == 1'b1) && (txAC0StateInt == 4'h4)) ||
                         ((trigTxAC1sync == 1'b1) && (txAC1StateInt == 4'h4)) ||
                         ((trigTxAC2sync == 1'b1) && (txAC2StateInt == 4'h4)) ||
                         ((trigTxAC3sync == 1'b1) && (txAC3StateInt == 4'h4)) ||
                         ((trigTxBcnsync == 1'b1) && (txBcnStateInt == 4'h4))    ;


simpleSynchro U_txStateActiveMC_synchro (
                .dstclk             (macPITxClk),
                .dstresetn          (macPITxClkHardRst_n),
                .srcdata            (txStateActiveMC),
                .dstdata            (txStateActiveMC_resync)
                );

////////////////////////////////////////////////////
/// MAC Controller Interface
////////////////////////////////////////////////////

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_frameRxed_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_frameRxed_p_synchro (
                .srcclk             (macCoreClk),
                .srcresetn          (macCoreClkHardRst_n),
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (frameRxed_p),
                .dstdata            (dmaframeRxed_p)
                );

simpleSynchro U_rxListProcCsIsIdle_synchro (
                .dstclk             (macCoreClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (dmarxListProcCsIsIdle),
                .dstdata            (rxListProcCsIsIdle)
                );



// Instanciation of pulse2PulseSynchro
// Name of the instance : U_updateDMAStatus_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_updateDMAStatus_p_synchro (
                .srcclk             (macCoreClk),
                .srcresetn          (macCoreClkHardRst_n),
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (updateDMAStatus_p),
                .dstdata            (updateDMAStatusResync_p)
                );


// Instanciation of pulse2PulseSynchro
// Name of the instance : U_statusUpdated_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_statusUpdated_p_synchro (
                .srcclk             (macPIClk),
                .srcresetn          (macPIClkHardRst_n),
                .dstclk             (macCoreClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (statusUpdatedInt_p),
                .dstdata            (statusUpdated_p)
                );

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_rxTrig_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_rxTrig_p_synchro (
                .srcclk             (macPIClk),
                .srcresetn          (macPIClkHardRst_n),
                .dstclk             (macCoreClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (rxTrigInt_p),
                .dstdata            (rxTrig_p)
                );


always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    retryLimitReachedResync_p <= 1'b0;
    rtsSuccessResync_p  <= 1'b0;
    rtsFailedResync_p   <= 1'b0;
    mpduFailedResync_p  <= 1'b0;
    mpduSuccessResync_p <= 1'b0;
    retryFrameResync_p  <= 1'b0;
    ampduFrmResync_p    <= 1'b0;
    swRTSResync_p       <= 1'b0;
    numMPDURetriesResync<= 8'b0;
    numRTSRetriesResync <= 8'b0;
    mediumTimeUsedResync<= 31'b0;
    updateDMAStatusResyncDly_p<= 1'b0;
    updateDMAStatusResyncDly2_p<= 1'b0;
  end
  else if ((macPIClkSoftRst_n == 1'b0) || statusUpdatedInt_p)
  begin
    retryLimitReachedResync_p <= 1'b0;
    rtsSuccessResync_p  <= 1'b0;
    rtsFailedResync_p   <= 1'b0;
    mpduFailedResync_p  <= 1'b0;
    mpduSuccessResync_p <= 1'b0;
    retryFrameResync_p  <= 1'b0;
    ampduFrmResync_p    <= 1'b0;
    swRTSResync_p       <= 1'b0;
    numMPDURetriesResync<= 8'b0;
    numRTSRetriesResync <= 8'b0;
    mediumTimeUsedResync<= 31'b0;
    updateDMAStatusResyncDly_p<= 1'b0;
    updateDMAStatusResyncDly2_p<= 1'b0;
    
  end
  else if (updateDMAStatusResync_p)
  begin
    updateDMAStatusResyncDly_p<= 1'b1;
    retryLimitReachedResync_p <= retryLimitReached_p;
    rtsSuccessResync_p <= rtsSuccess_p;
    rtsFailedResync_p <= rtsFailed_p;
    mpduFailedResync_p <= mpduFailed_p;
    mpduSuccessResync_p <= mpduSuccess_p;
    retryFrameResync_p <= retryFrame_p;
    ampduFrmResync_p <= ampduFrm_p;
    swRTSResync_p <= swRTS_p;
    numMPDURetriesResync <= numMPDURetries;
    numRTSRetriesResync <= numRTSRetries;
    mediumTimeUsedResync<= mediumTimeUsed;
  end
  else
  begin
    updateDMAStatusResyncDly_p<= 1'b0;
    updateDMAStatusResyncDly2_p<= updateDMAStatusResyncDly_p;
  end  
end   

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_txMpduDone_p_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_txMpduDone_p_synchro (
                .srcclk             (macCoreClk),
                .srcresetn          (macCoreClkHardRst_n),
                .dstclk             (macPIClk),
                .dstresetn          (macPIClkHardRst_n),
                .srcdata            (txMpduDone_p),
                .dstdata            (txMpduDoneResync_p)
                );


always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
    txMpduDoneResyncDly_p<= 1'b0;
  else 
    txMpduDoneResyncDly_p<= txMpduDoneResync_p;
end   

always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
    whichDescriptorSWResync <= 4'b0;
  else if (macPIClkSoftRst_n == 1'b0)
    whichDescriptorSWResync <= 4'b0;
  else if (txMpduDoneResync_p || updateDMAStatusResync_p)
    whichDescriptorSWResync <= whichDescriptorSW;
end   

always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
    transmissionBWResync <= 2'b0;
  else if (macPIClkSoftRst_n == 1'b0)
    transmissionBWResync <= 2'b0;
  else if (txMpduDoneResync_p || updateDMAStatusResync_p)
    transmissionBWResync <= transmissionBW;
end   



// Instanciation of dmaEngine
// Name of the instance : U_dmaEngine
// Name of the file containing this module : dmaEngine.v
dmaEngine U_dmaEngine (
		.macPITxClk                       (macPITxClk),
		.macPIRxClk                       (macPIRxClk),
		.macPIClk                         (macPIClk),
		.macPITxClkHardRst_n              (macPITxClkHardRst_n),
		.macPIRxClkHardRst_n              (macPIRxClkHardRst_n),
		.macPIClkHardRst_n                (macPIClkHardRst_n),
		.macPITxClkSoftRst_n              (macPITxClkSoftRst_n),
		.macPIRxClkSoftRst_n              (macPIRxClkSoftRst_n),
		.macPIClkSoftRst_n                (macPIClkSoftRst_n),
		.dmaHIFReadDataOut                (dmaHIFReadDataOut),
		.dmaHIFReadDataValid              (dmaHIFReadDataValid),
		.dmaHIFReady                      (dmaHIFReady),
		.dmaHIFTransComplete              (dmaHIFTransComplete),
		.dmaHIFError                      (dmaHIFError),
		.trigTxAC0                        (trigTxAC0sync),
		.trigTxAC1                        (trigTxAC1sync),
		.trigTxAC2                        (trigTxAC2sync),
		.trigTxAC3                        (trigTxAC3sync),
		.trigTxBcn                        (trigTxBcnsync),
		.frameRxed_p                      (dmaframeRxed_p),
		.rxListProcCsIsIdle               (dmarxListProcCsIsIdle),
		.tsfTimerValue                    (tsfTimerValue),
		.updateDMAStatus_p                (updateDMAStatusResyncDly2_p),
		.swRTS_p                          (swRTSResync_p),
		.txMpduDone_p                     (txMpduDoneResyncDly_p),
		.ampduFrm_p                       (ampduFrmResync_p),
		.retryFrame_p                     (retryFrameResync_p),
		.mpduSuccess_p                    (mpduSuccessResync_p),
		.mpduFailed_p                     (mpduFailedResync_p),
		.rtsFailed_p                      (rtsFailedResync_p),
		.rtsSuccess_p                     (rtsSuccessResync_p),
		.retryLimitReached_p              (retryLimitReachedResync_p),
		.transmissionBW                   (transmissionBWResync),
		.numMPDURetries                   (numMPDURetriesResync),
		.numRTSRetries                    (numRTSRetriesResync),
		.mediumTimeUsed                   (mediumTimeUsedResync),
		.whichDescriptorSW                (whichDescriptorSWResync),
		.rxFrmDiscard                     (rxFrmDiscardResync),
		.rxDescAvailable                  (rxDescAvailableResync),
		.rxFrmDiscardRet                  (rxFrmDiscardRet),
		.rxFlowCntrlEn                    (rxFlowCntrlEnResync),
		.underRunDetected_p               (underRunDetected_p),
		.txNewTailAC0                     (txNewTailAC0),
		.txNewTailAC1                     (txNewTailAC1),
		.txNewTailAC2                     (txNewTailAC2),
		.txNewTailAC3                     (txNewTailAC3),
		.txNewTailBcn                     (txNewTailBcn),
		.txNewHeadAC0                     (txNewHeadAC0),
		.txNewHeadAC1                     (txNewHeadAC1),
		.txNewHeadAC2                     (txNewHeadAC2),
		.txNewHeadAC3                     (txNewHeadAC3),
		.txNewHeadBcn                     (txNewHeadBcn),
		.rxNewTailHdr                     (rxNewTailHdr),
		.rxNewTailPld                     (rxNewTailPld),
		.rxNewHeadHdr                     (rxNewHeadHdr),
		.rxNewHeadPld                     (rxNewHeadPld),
		.haltAC0AfterTXOP                 (haltAC0AfterTXOP),
		.haltAC1AfterTXOP                 (haltAC1AfterTXOP),
		.haltAC2AfterTXOP                 (haltAC2AfterTXOP),
		.haltAC3AfterTXOP                 (haltAC3AfterTXOP),
		.haltBcnAfterTXOP                 (haltBcnAfterTXOP),
		.txAC0HeadPtr                     (txAC0HeadPtr),
		.txAC1HeadPtr                     (txAC1HeadPtr),
		.txAC2HeadPtr                     (txAC2HeadPtr),
		.txAC3HeadPtr                     (txAC3HeadPtr),
		.txBcnHeadPtr                     (txBcnHeadPtr),
		.rxHdrHeadPtr                     (intrxHdrHeadPtr),
		.rxPldHeadPtr                     (intrxPldHeadPtr),
		.rxPayloadUsedCount               (rxPayloadUsedCount),
		.txCtrlRegBusy                    (txCtrlRegBusy),
		.txStateActiveMC                  (txStateActiveMC_resync && txStateActive),
		.txFifoAlmostFull                 (txFifoAlmostFull),
		.txFifoFull                       (txFifoFull),
		.txFifoEmpty                      (txFifoEmpty),
		.rxFifoEmpty                      (rxFifoEmpty),
		.rxFifoAlmEmpty                   (rxFIFOAlmEmpty),
		.rxFifoRdData                     (rxFifoRdData),
		.rxTagFifoRdData                  (rxTagFifoRdData),
		.dmaHIFRead                       (dmaHIFRead),
		.dmaHIFWrite                      (dmaHIFWrite),
		.dmaHIFSize                       (dmaHIFSize),
		.dmaHIFAddressIn                  (dmaHIFAddressIn),
		.dmaHIFWriteDataIn                (dmaHIFWriteDataIn),
		.txCtrlRegWr                      (txCtrlRegWr),
		.txCtrlRegPT                      (txCtrlRegPT),
		.txCtrlRegHD                      (txCtrlRegHD),
		.discardPrevHD_p                  (discardPrevHD_p),
		.rstAC0NewTail                    (rstAC0NewTail),
		.rstAC1NewTail                    (rstAC1NewTail),
		.rstAC2NewTail                    (rstAC2NewTail),
		.rstAC3NewTail                    (rstAC3NewTail),
		.rstBcnNewTail                    (rstBcnNewTail),
		.rstAC0NewHead                    (rstAC0NewHead),
		.rstAC1NewHead                    (rstAC1NewHead),
		.rstAC2NewHead                    (rstAC2NewHead),
		.rstAC3NewHead                    (rstAC3NewHead),
		.rstBcnNewHead                    (rstBcnNewHead),
		.rstNewTailHdr                    (rstNewTailHdr),
		.rstNewHeadHdr                    (rstNewHeadHdr),
		.rstNewTailPld                    (rstNewTailPld),
		.rstNewHeadPld                    (rstNewHeadPld),
		.txAC0State                       (txAC0StateInt),
		.txAC1State                       (txAC1StateInt),
		.txAC2State                       (txAC2StateInt),
		.txAC3State                       (txAC3StateInt),
		.txBcnState                       (txBcnStateInt),
		.rxHeaderState                    (rxHeaderStateInt),
		.rxPayloadState                   (rxPayloadStateInt),
    .txBcnLenMismatch                 (txBcnLenMismatch), 
    .txAC0LenMismatch                 (txAC0LenMismatch), 
    .txAC1LenMismatch                 (txAC1LenMismatch), 
    .txAC2LenMismatch                 (txAC2LenMismatch), 
    .txAC3LenMismatch                 (txAC3LenMismatch),    
    .txBcnUPatternErr                 (txBcnUPatternErr),    
    .txAC0UPatternErr                 (txAC0UPatternErr),    
    .txAC1UPatternErr                 (txAC1UPatternErr),    
    .txAC2UPatternErr                 (txAC2UPatternErr),    
    .txAC3UPatternErr                 (txAC3UPatternErr),    
    .txBcnNextPointerErr              (txBcnNextPointerErr), 
    .txAC0NextPointerErr              (txAC0NextPointerErr), 
    .txAC1NextPointerErr              (txAC1NextPointerErr), 
    .txAC2NextPointerErr              (txAC2NextPointerErr), 
    .txAC3NextPointerErr              (txAC3NextPointerErr), 
    .txBcnPTAddressErr                (txBcnPTAddressErr),   
    .txAC0PTAddressErr                (txAC0PTAddressErr),   
    .txAC1PTAddressErr                (txAC1PTAddressErr),   
    .txAC2PTAddressErr                (txAC2PTAddressErr),   
    .txAC3PTAddressErr                (txAC3PTAddressErr),   
    .txBcnBusErr                      (txBcnBusErr),         
    .txAC0BusErr                      (txAC0BusErr),         
    .txAC1BusErr                      (txAC1BusErr),         
    .txAC2BusErr                      (txAC2BusErr),         
    .txAC3BusErr                      (txAC3BusErr),         
    .txBcnNewHeadErr                  (txBcnNewHeadErr),     
    .txAC0NewHeadErr                  (txAC0NewHeadErr),     
    .txAC1NewHeadErr                  (txAC1NewHeadErr),     
    .txAC2NewHeadErr                  (txAC2NewHeadErr),     
    .txAC3NewHeadErr                  (txAC3NewHeadErr), 
    .rxHdrUPatternErr                 (rxHdrUPatternErr),   
    .rxPayUPatternErr                 (rxPayUPatternErr),   
    .rxHdrNextPointerErr              (rxHdrNextPointerErr),
    .rxPayNextPointerErr              (rxPayNextPointerErr),
    .rxHdrBusErr                      (rxHdrBusErr),        
    .rxPayBusErr                      (rxPayBusErr),        
    .rxHdrNewHeadErr                  (rxHdrNewHeadErr),    
    .rxPayNewHeadErr                  (rxPayNewHeadErr),
    .ptError                          (ptError),
    .txBcnStartup                     (txBcnStartup),       
    .txAC0Startup                     (txAC0Startup),       
    .txAC1Startup                     (txAC1Startup),       
    .txAC2Startup                     (txAC2Startup),       
    .txAC3Startup                     (txAC3Startup),       
    .txBcnEndQ                        (txBcnEndQ),          
    .txAC0EndQ                        (txAC0EndQ),          
    .txAC1EndQ                        (txAC1EndQ),          
    .txAC2EndQ                        (txAC2EndQ),          
    .txAC3EndQ                        (txAC3EndQ),          
    .txBcnHaltAfterTXOP               (txBcnHaltAfterTXOP),   
    .txAC0HaltAfterTXOP               (txAC0HaltAfterTXOP), 
    .txAC1HaltAfterTXOP               (txAC1HaltAfterTXOP), 
    .txAC2HaltAfterTXOP               (txAC2HaltAfterTXOP), 
    .txAC3HaltAfterTXOP               (txAC3HaltAfterTXOP),   
    .statusUpdated_p                  (statusUpdatedInt_p),
		.txFifoWr                         (txFifoWr),
		.txFifoWrData                     (txFIFOWrData),
		.flushTxFifo                      (flushTxFifo),
		.txFIFOFlushDone_p                (dmaTxFIFOFlushDone_p),
		.rxFifoRd                         (rxFifoRd),
		.txTagFifoWrData                  (txTagFifoWrData),
		.txListProcCs                     (txListProcCs),
		.rxListProcCs                     (rxListProcCs),
		.interruptEnTx                    (interruptEnTx),
		.bufferInterruptTx                (bufferInterruptTx),
		.statusUpdaterFull                (statusUpdaterFull),
		.bcnTxDMADead                     (bcnTxDMADead_int),
		.ac3TxDMADead                     (ac3TxDMADead_int),
		.ac2TxDMADead                     (ac2TxDMADead_int),
		.ac1TxDMADead                     (ac1TxDMADead_int),
		.ac0TxDMADead                     (ac0TxDMADead_int),
		.rxPayloadDMADead                 (rxPayloadDMADead),
		.rxHeaderDMADead                  (rxHeaderDMADead),
		.rxDMAEmpty                       (rxDMAEmpty),
		.tx0Trigger                       (ac0TxTrigger),
		.tx1Trigger                       (ac1TxTrigger),
		.tx2Trigger                       (ac2TxTrigger),
		.tx3Trigger                       (ac3TxTrigger),
		.bcnTrigger                       (bcnTxTrigger),
		.rxTrigger                        (rxTrigger),
		.counterRxTrigger                 (counterRxTrigger),
		.rxTrig_p                         (rxTrigInt_p),
		.ac0StatusPointer                 (ac0StatusPointer),
		.ac1StatusPointer                 (ac1StatusPointer),
		.ac2StatusPointer                 (ac2StatusPointer),
		.ac3StatusPointer                 (ac3StatusPointer),
		.bcnStatusPointer                 (bcnStatusPointer),
		.currentPtr                       (txCurrentPointer),
		.hdrStatusPointer                 (rxHdrStatPointer),
		.pldStatusPointer                 (rxPayStatPointer),
		.rxPayCurrentPointer              (rxPayCurrentPointer),
		.debugPortDMA3                    (debugPortDMA3),
		.debugPortDMA5                    (debugPortDMA5),
		.debugPortDMA6                    (debugPortDMA6),
		.debugPortDMAStatus               (debugPortDMAStatus),
		.debugPortDMATxStatus             (debugPortDMATxStatus),
		.debugPortTxRxListA               (debugPortTxRxListA),
		.debugPortDmaRdWrCtlr             (debugPortDmaRdWrCtlr),
		.dmaInternalError                 (dmaInternalError_int)
 
		);




assign ac0TxBufTrigger = bufferInterruptTx & trigTxAC0sync;
assign ac1TxBufTrigger = bufferInterruptTx & trigTxAC1sync;
assign ac2TxBufTrigger = bufferInterruptTx & trigTxAC2sync;
assign ac3TxBufTrigger = bufferInterruptTx & trigTxAC3sync;
assign bcnTxBufTrigger = bufferInterruptTx & trigTxBcnsync;


// Conversion between One Hot encoding of the FSM state and the binay encoding of the CSReg.
//DMA state for AC0 channel.
assign txAC0State     = convOneHotToBin(txAC0StateInt);
//DMA state for AC1 channel.
assign txAC1State     = convOneHotToBin(txAC1StateInt);
//DMA state for AC2 channel.
assign txAC2State     = convOneHotToBin(txAC2StateInt);
//DMA state for AC3 channel.
assign txAC3State     = convOneHotToBin(txAC3StateInt);
//DMA state for Beacon channel.
assign txBcnState     = convOneHotToBin(txBcnStateInt);
//DMA state for Receive Header channel.
assign rxHeaderState  = convOneHotToBin(rxHeaderStateInt);
//DMA state for Payload Header channel.
assign rxPayloadState = convOneHotToBin(rxPayloadStateInt);

//Oring NewHead 
assign oredNewHead    = txNewHeadAC0 | txNewHeadAC1 | txNewHeadAC2 | txNewHeadAC3 | txNewHeadBcn;
//Oring NewTail 
assign oredNewTail    = txNewTailAC0 | txNewTailAC1 | txNewTailAC2 | txNewTailAC3 | txNewTailBcn;

assign txInterrupt    =  ac0TxTrigger |
                         ac1TxTrigger |
                         ac2TxTrigger |
                         ac3TxTrigger |
                         bcnTxTrigger ;

assign rxInterrupt    =  rxTrigger;

assign bcnTxDMADead   =  bcnTxDMADead_int | (trigTxBcnsync & underRunDetected_p);
assign ac3TxDMADead   =  ac3TxDMADead_int | (trigTxAC3sync & underRunDetected_p);
assign ac2TxDMADead   =  ac2TxDMADead_int | (trigTxAC2sync & underRunDetected_p);
assign ac1TxDMADead   =  ac1TxDMADead_int | (trigTxAC1sync & underRunDetected_p);
assign ac0TxDMADead   =  ac0TxDMADead_int | (trigTxAC0sync & underRunDetected_p);

assign debugPortDMA1 = {oredNewHead,oredNewTail,rxPayloadState,rxHeaderState,txBcnState,txAC3State,txAC2State,txAC1State,txAC0State};
assign debugPortDMA2 = {statusUpdaterFull,rxListProcCs,interruptEnTx,rxInterrupt,txInterrupt,oredNewTail,oredNewHead,txListProcCs};
assign debugPortDMA4 = {dmaHIFRead,
                        txCtrlRegHD || txCtrlRegPT,
                        txCtrlRegBusy,
                        txCtrlRegWr,
                        discardPrevHD_p,
                        txFifoAlmostFull,
                        txFifoFull,
                        txFifoEmpty,
                        txFifoWr,
                        flushTxFifo,
                        txTagFifoWrData}; // 6bits

// Instanciation of pulse2PulseSynchro
// Name of the instance : U_dmaInternalError_synchro
// Name of the file containing this module : pulse2PulseSynchro.v
pulse2PulseSynchro U_dmaInternalError_synchro (
                .srcclk             (macPIClk),
                .srcresetn          (macPIClkHardRst_n),
                .dstclk             (macCoreClk),
                .dstresetn          (macCoreClkHardRst_n),
                .srcdata            (dmaInternalError_int),
                .dstdata            (dmaInternalError)
                );
   

endmodule